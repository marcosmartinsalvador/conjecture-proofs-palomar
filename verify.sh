#!/usr/bin/env bash
# Checks the Palomar packages in this repository, the way the Palomar registry will.
#
#   ./verify.sh                 every package
#   ./verify.sh <folder> ...    only these
#
# First it checks the rule the registry applies to the whole repository: every .lean
# file in it starts with `module` and has at most 10,000 lines.
#
# Then, for each package, three things:
#   1. Source rules: the same rule for the package's own files, and Challenge.lean has
#      at most 1,000 lines and 100 KiB.
#   2. Same statement: the statement in Challenge.lean, and the statement and proof in
#      Solution.lean, are the text of conjectures/<folder>/Statement.lean and
#      Proof.lean in marcosmartinsalvador/conjecture-proofs, apart from the import
#      lines and the comment edits listed below. This needs a checkout of that
#      repository: next to this one (../conjecture-proofs), or wherever the variable
#      CONJECTURE_PROOFS points. Without one this check is skipped, and says so.
#   3. `lake comparator`: the theorem in Solution.lean proves the statement in
#      Challenge.lean, with only the three standard axioms, and is accepted by Lean's
#      kernel and by the two independent kernels shipped with Lean (NanoDa, con-ron).
#
# Needs Linux, Lean (elan), python3 and bubblewrap (`bwrap`), which `lake comparator`
# uses as its sandbox. The first run of a package downloads Mathlib's prebuilt files
# into <folder>/.lake (about 7 GB each).
set -euo pipefail
cd "$(dirname "$0")"
here="$(pwd)"

for tool in bwrap lake lean python3; do
  command -v "$tool" >/dev/null 2>&1 || { echo "error: $tool is needed and was not found" >&2; exit 2; }
done

if [ "$#" -gt 0 ]; then packages=("$@"); else
  packages=(); for d in */; do [ -f "$d/comparator.json" ] && packages+=("${d%/}"); done
fi

failed=0

# The whole repository: nothing from it is run.
python3 - "$here" <<'PY' || failed=1
import pathlib, sys

here = pathlib.Path(sys.argv[1])
bad = 0
sources = sorted(p for p in here.rglob("*.lean") if ".lake" not in p.parts and ".git" not in p.parts)
for path in sources:
    text = path.read_text(encoding="utf-8")
    name = path.relative_to(here)
    rows = text.count("\n") + int(bool(text) and not text.endswith("\n"))
    if path.is_symlink():
        bad += 1; print(f"FAILED  {name} is a symbolic link")
    if not text.startswith("module\n"):
        bad += 1; print(f"FAILED  {name} does not start with the module header")
    if rows > 10_000:
        bad += 1; print(f"FAILED  {name} has more than 10,000 lines")
if not bad:
    print(f"ok      whole repository: {len(sources)} Lean files, all with the module header")
sys.exit(1 if bad else 0)
PY

for pkg in "${packages[@]}"; do
  echo "=== $pkg"
  [ -f "$here/$pkg/comparator.json" ] || { echo "error: no package $pkg" >&2; failed=1; continue; }

  # 1 and 2: plain text checks. Nothing from the package is run.
  python3 - "$here" "$pkg" <<'PY' || { failed=1; continue; }
import os, pathlib, sys

here, pkg = pathlib.Path(sys.argv[1]), sys.argv[2]
project = here / pkg
header = "module\n\npublic import Mathlib\n\n@[expose] public section\n\n"
marker = "/-- **The compared theorem.**"
divider = (
    "/-! ## The proof\n\n"
    "Everything above this line is the statement, word for word as in `Challenge.lean`.\n"
    "Everything below is the proof. -/\n"
)
# Comments that point at working files which are not in this folder were reworded.
# Nothing that Lean checks is touched.
comment_edits = {
    "delta_primitive_two_primes": [(
        "Statement of the conjecture. It is proved in `Proof.lean`; the proof on paper is in\n"
        "`PROOF_NOTES.md` and the paper's exact wording in `source.md` (all in this folder).\n",
        "Statement of the conjecture. It is proved in `Solution.lean`. The paper's wording is\n"
        "quoted below.\n",
    )],
}
ok = True

def fail(message):
    global ok
    ok = False
    print(f"FAILED  {message}")

def lines(text):
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))

def without_imports(path):
    rows = path.read_text(encoding="utf-8").split("\n")
    i = 0
    while i < len(rows) and (rows[i].startswith("import ") or not rows[i].strip()):
        i += 1
    return "\n".join(rows[i:])

sources = sorted(p for p in project.rglob("*.lean") if ".lake" not in p.parts)
for path in sources:
    text = path.read_text(encoding="utf-8")
    name = path.relative_to(here)
    if path.is_symlink():
        fail(f"{name} is a symbolic link")
    if not text.startswith("module\n"):
        fail(f"{name} does not start with the module header")
    if lines(text) > 10_000:
        fail(f"{name} has more than 10,000 lines")
challenge = (project / "Challenge.lean").read_text(encoding="utf-8")
solution = (project / "Solution.lean").read_text(encoding="utf-8")
if lines(challenge) > 1_000 or len(challenge.encode()) > 100 * 1024:
    fail("Challenge.lean is over 1,000 lines or 100 KiB")
if ok:
    print(f"ok      source rules: {len(sources)} Lean files with module headers, "
          f"Challenge.lean {lines(challenge)} lines, Solution.lean {lines(solution)} lines")

home = pathlib.Path(os.environ.get("CONJECTURE_PROOFS") or here.parent / "conjecture-proofs")
original = home / "conjectures" / pkg
if not (original / "Statement.lean").is_file():
    print(f"skipped same-statement check: no checkout of conjecture-proofs at {home} "
          "(set CONJECTURE_PROOFS to one)")
else:
    statement = without_imports(original / "Statement.lean")
    proof = without_imports(original / "Proof.lean")
    edits = comment_edits.get(pkg, [])
    for old, new in edits:
        if statement.count(old) != 1:
            fail("a listed comment edit does not apply to Statement.lean")
        statement = statement.replace(old, new)
    same = True
    if not (challenge.startswith(header + statement + "\n" + marker)
            and challenge.count(marker) == 1
            and challenge.endswith("-/\ntheorem result : Claim := by\n  sorry\n")):
        same = False
        fail("Challenge.lean is not the header, Statement.lean, and `theorem result : Claim := by sorry`")
    if solution != header + statement + "\n" + divider + "\n" + proof:
        same = False
        fail("Solution.lean is not the header, Statement.lean, and Proof.lean")
    if same:
        note = f" apart from {len(edits)} reworded comment" if edits else ""
        print(f"ok      same statement and proof text as conjectures/{pkg}/{note}")
sys.exit(0 if ok else 1)
PY

  # 3: lake comparator, with the toolchain's own NanoDa and con-ron kernels registered
  # by full path, as the registry does (it ignores `enable_nanoda` in comparator.json).
  cd "$here/$pkg"
  prefix="$(lean --print-prefix)"
  for kernel in nanoda_bin con-ron; do
    [ -x "$prefix/bin/$kernel" ] || { echo "error: this Lean toolchain does not ship $kernel" >&2; exit 2; }
  done
  config="$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")"
  python3 - comparator.json "$config" "$prefix" <<'PY'
import json, pathlib, sys

source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY
  lake exe cache get >/dev/null 2>&1 || { echo "error: could not fetch Mathlib's prebuilt files" >&2; rm -f "$config"; exit 2; }
  if lake comparator --config "$config"; then
    echo "ok      lake comparator accepted $pkg"
  else
    echo "FAILED  lake comparator did not accept $pkg"
    failed=1
  fi
  rm -f "$config"
  cd "$here"
done

if [ "$failed" -eq 0 ]; then echo "ALL OK (${#packages[@]} packages)"; else echo "SOME CHECKS FAILED"; fi
exit "$failed"
