module

public import Mathlib

@[expose] public section

/-- A 2-sparse system over the field with two elements whose graph is the cycle `C_n`.

The variables are `x i` for `i` in `ℤ/n`. Edge number `i` joins the vertices `i` and `i + 1`,
and carries one equation `f i (x i) (x (i + 1)) = 0`, where `f i` is any function of two
variables over `ℤ/2` (these are exactly the 16 polynomial functions in two variables).

The system `f` is consistent when one assignment `x` satisfies all `n` equations. -/
def Consistent (n : ℕ) (f : ZMod n → ZMod 2 → ZMod 2 → ZMod 2) : Prop :=
  ∃ x : ZMod n → ZMod 2, ∀ i : ZMod n, f i (x i) (x (i + 1)) = 0

/-- The consistency probability `q(C_n)` of Horak and Semaev: the number of consistent
systems on the cycle divided by the number `2 ^ (4 n) = 16 ^ n` of all systems. -/
noncomputable def qCycle (n : ℕ) : ℝ :=
  (Nat.card {f : ZMod n → ZMod 2 → ZMod 2 → ZMod 2 // Consistent n f} : ℝ) / 16 ^ n

/-- The conjecture at the end of P. Horak, I. Semaev, "Inconsistency Probability of Sparse
Equations over F2", arXiv:2603.24890v1, says that for the cycle `C_n`
`q(C_n) = s ^ n + t ^ n - 1 / 4 ^ n - 1 / 8 ^ (n - 1)` with `s, t = (17 ± √97) / 32`.

`Claim` settles it for every cycle (`n ≥ 3`): the exact value is
`q(C_n) = s ^ n + t ^ n - 1 / 4 ^ n - 1 / (2 * 8 ^ n)`,
so the formula as printed in the paper is false for every `n ≥ 3`
(its last term is 16 times too large). -/
def Claim : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    qCycle n
        = ((17 + Real.sqrt 97) / 32) ^ n + ((17 - Real.sqrt 97) / 32) ^ n
          - 1 / 4 ^ n - 1 / (2 * 8 ^ n)
      ∧ qCycle n
        ≠ ((17 + Real.sqrt 97) / 32) ^ n + ((17 - Real.sqrt 97) / 32) ^ n
          - 1 / 4 ^ n - 1 / 8 ^ (n - 1)

/-- **The compared theorem.** For every `n ≥ 3` the consistency probability of the cycle is
`q(C_n) = s ^ n + t ^ n - 1 / 4 ^ n - 1 / (2 * 8 ^ n)` with `s, t = (17 ± √97) / 32`, and it
is not equal to the formula printed in the source, whose last term is `1 / 8 ^ (n - 1)`.
The proof is in `Solution.lean`. -/
theorem result : Claim := by
  sorry
