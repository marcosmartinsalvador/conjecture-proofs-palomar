module

public import Mathlib

@[expose] public section

/-!
# Kourovka Notebook, problem 20.52 (D. MacHale): a partial answer

Source: "Unsolved Problems in Group Theory. The Kourovka Notebook", No. 21,
arXiv:1401.0300v50, problem 20.52:

"A famous result of Burnside states that if k(G) is the number of conjugacy classes of a
finite group G of odd order, then |G| - k(G) is divisible by 16.  Is it true that for every
integer m > 0 there exists a finite non-abelian group G(m) of odd order such that
|G(m)| - k(G(m)) = 16m?"

The claim below is a partial answer, not a solution: such a group exists for every odd `m`
and for every `m` in which 2 occurs to an odd power (m = 2, 6, 8, 10, 14, 18, 22, 24, ...).
Nothing is claimed for the other `m` (those in which 2 occurs to an even power at least 2).
-/

/-- `m` is attained: there is a finite non-abelian group `G` of odd order with
`|G| - k(G) = 16 m`, where `k(G)` is the number of conjugacy classes of `G`.
(As `k(G) ≤ |G|`, the equation is written without subtraction.) -/
def Attained (m : ℕ) : Prop :=
  ∃ (G : Type) (_ : Group G), Finite G ∧ Odd (Nat.card G) ∧ (∃ x y : G, x * y ≠ y * x) ∧
    Nat.card G = Nat.card (ConjClasses G) + 16 * m

/-- Every `m > 0` that is odd, or in which 2 occurs to an odd power, is attained. -/
def Claim : Prop :=
  ∀ m : ℕ, 0 < m → (Odd m ∨ Odd (padicValNat 2 m)) → Attained m

/-- **The compared theorem.** For every `m > 0` that is odd, or in which 2 occurs to an odd
power, there is a finite non-abelian group `G` of odd order with `|G| - k(G) = 16 m`.
The proof is in `Solution.lean`. -/
theorem result : Claim := by
  sorry
