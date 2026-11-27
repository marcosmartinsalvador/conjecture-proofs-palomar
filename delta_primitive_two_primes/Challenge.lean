module

public import Mathlib

@[expose] public section

/-!
Statement of the conjecture. It is proved in `Solution.lean`. The paper's wording is
quoted below.

V. N. Schvollner, "The Delta property: a bridge between split graphs and Number Theory",
arXiv:2605.25264v1, the conjecture at the end of the subsection "Integers of the form p^k q":

  Let n be a natural number of the form p^x q^y, where p and q are distinct primes and
  x, y are natural numbers. If n is Delta-primitive, then n is 24 or 40.

In the paper the natural numbers start at 1, so x and y are at least 1.
-/

/-- `D*_n`: the differences `|a - b|` of complementary divisors `a * b = n`. -/
def Dstar (n : ℕ) : Set ℕ :=
  {d : ℕ | ∃ a b : ℕ, a * b = n ∧ (d : ℤ) = |(a : ℤ) - (b : ℤ)|}

/-- `D+_n`: the sums of two nonzero elements of `D*_n`. -/
def Dplus (n : ℕ) : Set ℕ :=
  {s : ℕ | ∃ x ∈ Dstar n, ∃ y ∈ Dstar n, x ≠ 0 ∧ y ≠ 0 ∧ s = x + y}

/-- `n` has the Delta property: `D*_n` and `D+_n` meet. -/
def HasDelta (n : ℕ) : Prop := (Dstar n ∩ Dplus n).Nonempty

/-- `n` is Delta-primitive: it has the Delta property and is not `α^2 * m` with
`α, m ≥ 2` and `m` having the Delta property. -/
def DeltaPrimitive (n : ℕ) : Prop :=
  HasDelta n ∧ ¬ ∃ α m : ℕ, 2 ≤ α ∧ 2 ≤ m ∧ n = α ^ 2 * m ∧ HasDelta m

def Claim : Prop :=
  ∀ p q x y : ℕ, p.Prime → q.Prime → p ≠ q → 1 ≤ x → 1 ≤ y →
    DeltaPrimitive (p ^ x * q ^ y) → p ^ x * q ^ y = 24 ∨ p ^ x * q ^ y = 40

/-- **The compared theorem.** If `n = p ^ x * q ^ y`, with `p ≠ q` primes and `x, y ≥ 1`, is
Delta-primitive, then `n` is 24 or 40. The proof is in `Solution.lean`. -/
theorem result : Claim := by
  sorry
