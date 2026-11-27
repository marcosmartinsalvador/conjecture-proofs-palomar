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

/-! ## The proof

Everything above this line is the statement, word for word as in `Challenge.lean`.
Everything below is the proof. -/

/-!
# The consistency probability of a random 2-sparse system on a cycle

Plan of the proof.

* Every equation `f i (x i) (x (i+1)) = 0` is recorded as a 2x2 Boolean matrix
  (`toB`): entry `(a, b)` says that the pair `(a, b)` is allowed.
* A system on the cycle is consistent exactly when the Boolean product of its `n`
  matrices has a nonzero diagonal entry (`consistent_iff`).
* The number of sequences of `n ≥ 1` Boolean matrices with a given product `m` is
  the explicit expression `G m n` (`sum_prodB`); the induction step is the finite
  identity `step_identity`.
* Adding up over the twelve matrices with a nonzero diagonal gives the count, and
  `2 u (n+1) - 17 u n = ((17+√97)/2)^n + ((17-√97)/2)^n` gives the closed form.
-/

namespace CycleProof

/-- 2x2 Boolean matrices `(m00, m01, m10, m11)`. -/
abbrev BM := Bool × Bool × Bool × Bool

/-- Boolean matrix product. -/
def mulB (a b : BM) : BM :=
  ((a.1 && b.1) || (a.2.1 && b.2.2.1), (a.1 && b.2.1) || (a.2.1 && b.2.2.2),
   (a.2.2.1 && b.1) || (a.2.2.2 && b.2.2.1), (a.2.2.1 && b.2.1) || (a.2.2.2 && b.2.2.2))

/-- The identity matrix. -/
def oneB : BM := (true, false, false, true)

/-- The product of a sequence of Boolean matrices. -/
def prodB : (n : ℕ) → (Fin n → BM) → BM
  | 0, _ => oneB
  | n + 1, g => mulB (g 0) (prodB n (Fin.tail g))

/-- The sequence `u 0 = 0, u 1 = 1, u (n+2) = 17 u (n+1) - 48 u n`. -/
def u : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 => 17 * u (n + 1) - 48 * u n

/-- The number of sequences of length `n ≥ 1` with product `m`. -/
def G (m : BM) (n : ℕ) : ℚ :=
  match m with
  | (false, false, false, false) => 16 ^ n + 2 * u n - u (n + 1)
  | (true, false, false, false) | (false, true, false, false)
  | (false, false, true, false) | (false, false, false, true) =>
      (15 * u n - u (n + 1) + 4 ^ n) / 2
  | (true, true, false, false) | (false, false, true, true)
  | (true, false, true, false) | (false, true, false, true) =>
      -12 * u n + u (n + 1) - 4 ^ n
  | (true, false, false, true) | (false, true, true, false) => 2 ^ n / 2
  | (true, true, true, false) | (true, true, false, true)
  | (true, false, true, true) | (false, true, true, true) => (4 ^ n - 2 ^ n) / 2
  | (true, true, true, true) => 16 * u n - u (n + 1) + 2 ^ n

/-- The induction step, as one finite identity (256 terms on the left). -/
theorem step_identity (n : ℕ) (φ : BM → ℚ) :
    ∑ a : BM, ∑ b : BM, G b (n + 1) * φ (mulB a b) = ∑ m : BM, G m (n + 2) * φ m := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mulB, G, u,
    Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false, Bool.false_or]
  ring

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → BM) → ℚ) :
    ∑ g : Fin (n + 1) → BM, F g = ∑ a : BM, ∑ h : Fin n → BM, F (Fin.cons a h) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => BM)).sum_comp F, Fintype.sum_prod_type]
  rfl

theorem prodB_cons {n : ℕ} (a : BM) (h : Fin n → BM) :
    prodB (n + 1) (Fin.cons a h) = mulB a (prodB n h) := by
  simp [prodB, Fin.tail_cons]

theorem G_one : ∀ m : BM, G m 1 = 1 := by
  rintro ⟨_ | _, _ | _, _ | _, _ | _⟩ <;> norm_num [G, u]

theorem mulB_one : ∀ a : BM, mulB a oneB = a := by decide

/-- The number of sequences of `n + 1` Boolean matrices with product `m` is `G m (n + 1)`,
stated with a test function `φ`. -/
theorem sum_prodB (n : ℕ) : ∀ φ : BM → ℚ,
    ∑ g : Fin (n + 1) → BM, φ (prodB (n + 1) g) = ∑ m : BM, G m (n + 1) * φ m := by
  induction n with
  | zero =>
    intro φ
    rw [sum_cons]
    simp only [prodB, mulB_one, Finset.univ_unique, Finset.sum_singleton]
    simp [G_one]
  | succ n ih =>
    intro φ
    rw [sum_cons]
    simp only [prodB_cons]
    have h : ∀ a : BM, ∑ h : Fin (n + 1) → BM, φ (mulB a (prodB (n + 1) h))
        = ∑ m : BM, G m (n + 1) * φ (mulB a m) := fun a => ih (fun b => φ (mulB a b))
    simp only [h]
    exact step_identity n φ

/-- A Boolean matrix has a nonzero diagonal entry. -/
def diagB (m : BM) : Bool := m.1 || m.2.2.2

/-- The number of sequences of length `n + 1` whose product has a nonzero diagonal. -/
theorem count_diag (n : ℕ) :
    ((Finset.univ.filter (fun g : Fin (n + 1) → BM => diagB (prodB (n + 1) g) = true)).card : ℚ)
      = 2 * u (n + 2) - 17 * u (n + 1) - 4 ^ (n + 1) - 2 ^ (n + 1) / 2 := by
  rw [← Finset.sum_boole]
  have h : (∑ g : Fin (n + 1) → BM, if diagB (prodB (n + 1) g) = true then (1 : ℚ) else 0)
      = ∑ m : BM, G m (n + 1) * (if diagB m = true then 1 else 0) :=
    sum_prodB n (fun m => if diagB m = true then 1 else 0)
  rw [h]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, G, diagB]
  simp
  ring

/-! ### From systems of equations to Boolean matrices -/

/-- The equation of an edge as a Boolean matrix: entry `(a, b)` is true when `r a b = 0`. -/
def toB (r : ZMod 2 → ZMod 2 → ZMod 2) : BM :=
  (decide (r 0 0 = 0), decide (r 0 1 = 0), decide (r 1 0 = 0), decide (r 1 1 = 0))

/-- Entry `(a, c)` of a Boolean matrix. -/
def entry (m : BM) (a c : ZMod 2) : Bool :=
  if a = 0 then (if c = 0 then m.1 else m.2.1) else (if c = 0 then m.2.2.1 else m.2.2.2)

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem one_ne_zero_zmod2 : (1 : ZMod 2) ≠ 0 := by decide

theorem entry_toB (r : ZMod 2 → ZMod 2 → ZMod 2) (a c : ZMod 2) :
    entry (toB r) a c = true ↔ r a c = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl <;>
    simp [entry, toB]

theorem entry_mul : ∀ (p q : BM) (a c : ZMod 2),
    entry (mulB p q) a c = true ↔ ∃ b : ZMod 2, entry p a b = true ∧ entry q b c = true := by
  decide

theorem entry_one : ∀ a c : ZMod 2, entry oneB a c = true ↔ a = c := by decide

theorem diag_iff : ∀ m : BM, (∃ a : ZMod 2, entry m a a = true) ↔ diagB m = true := by decide

/-- Entry `(a, c)` of a product of `n` matrices: there is a path `x 0 = a, ..., x n = c`
all of whose steps are allowed. -/
theorem entry_prod (n : ℕ) : ∀ (g : Fin n → BM) (a c : ZMod 2),
    entry (prodB n g) a c = true ↔
      ∃ x : Fin (n + 1) → ZMod 2, x 0 = a ∧ x (Fin.last n) = c ∧
        ∀ i : Fin n, entry (g i) (x i.castSucc) (x i.succ) = true := by
  induction n with
  | zero =>
    intro g a c
    simp only [prodB, entry_one]
    constructor
    · rintro rfl
      exact ⟨fun _ => a, rfl, rfl, fun i => i.elim0⟩
    · rintro ⟨x, h0, h1, -⟩
      rw [← h0, ← h1]
      rfl
  | succ n ih =>
    intro g a c
    simp only [prodB, entry_mul, ih]
    constructor
    · rintro ⟨b, hab, y, hy0, hyl, hy⟩
      refine ⟨Fin.cons a y, by simp, ?_, ?_⟩
      · rw [← Fin.succ_last, Fin.cons_succ]
        exact hyl
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [hy0] using hab
        · have h := hy j
          rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
          exact h
    · rintro ⟨x, hx0, hxl, hx⟩
      refine ⟨x 1, ?_, Fin.tail x, rfl, ?_, ?_⟩
      · have h := hx 0
        rw [Fin.castSucc_zero, hx0] at h
        exact h
      · rw [← hxl, ← Fin.succ_last]
        rfl
      · intro i
        have h := hx i.succ
        rw [← Fin.succ_castSucc] at h
        exact h

/-- The successor on `Fin (k + 1)` read along the path `snoc x (x 0)`. -/
theorem snoc_succ {k : ℕ} (x : Fin (k + 1) → ZMod 2) (i : Fin (k + 1)) :
    (Fin.snoc x (x 0) : Fin (k + 2) → ZMod 2) i.succ = x (i + 1) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.succ_last, Fin.snoc_last, Fin.last_add_one]
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.coeSucc_eq_succ]

/-- A system on the cycle is consistent exactly when the product of its matrices has a
nonzero diagonal entry. -/
theorem consistent_iff (k : ℕ) (f : Fin (k + 1) → ZMod 2 → ZMod 2 → ZMod 2) :
    (∃ x : Fin (k + 1) → ZMod 2, ∀ i : Fin (k + 1), f i (x i) (x (i + 1)) = 0) ↔
      diagB (prodB (k + 1) (fun i => toB (f i))) = true := by
  rw [← diag_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x 0, (entry_prod _ _ _ _).2 ⟨Fin.snoc x (x 0), ?_, ?_, ?_⟩⟩
    · show (Fin.snoc x (x 0) : Fin (k + 2) → ZMod 2) (Fin.castSucc 0) = x 0
      rw [Fin.snoc_castSucc]
    · rw [Fin.snoc_last]
    · intro i
      rw [entry_toB, Fin.snoc_castSucc, snoc_succ]
      exact hx i
  · rintro ⟨a, ha⟩
    obtain ⟨y, hy0, hyl, hy⟩ := (entry_prod _ _ _ _).1 ha
    refine ⟨Fin.init y, fun i => ?_⟩
    have h := hy i
    rw [entry_toB] at h
    have hsn : (Fin.snoc (Fin.init y) (Fin.init y 0) : Fin (k + 2) → ZMod 2) = y := by
      have h0 : Fin.init y 0 = y (Fin.last (k + 1)) := by
        rw [hyl, ← hy0]
        rfl
      rw [h0, Fin.snoc_init_self]
    have h2 := snoc_succ (Fin.init y) i
    rw [hsn] at h2
    rw [← h2]
    exact h

/-! ### Counting -/

theorem toB_injective : Function.Injective toB := by
  intro r r' h
  simp only [toB, Prod.mk.injEq, decide_eq_decide] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  have key : ∀ x y : ZMod 2, (x = 0 ↔ y = 0) → x = y := by decide
  funext a c
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl
  · exact key _ _ h00
  · exact key _ _ h01
  · exact key _ _ h10
  · exact key _ _ h11

theorem toB_bijective : Function.Bijective toB :=
  (Fintype.bijective_iff_injective_and_card toB).2 ⟨toB_injective, by simp [ZMod.card]⟩

/-- The number of consistent systems on the cycle with `k + 1` edges. -/
theorem card_consistent (k : ℕ) :
    Nat.card {f : ZMod (k + 1) → ZMod 2 → ZMod 2 → ZMod 2 // Consistent (k + 1) f}
      = (Finset.univ.filter
          (fun g : Fin (k + 1) → BM => diagB (prodB (k + 1) g) = true)).card := by
  have e : {f : ZMod (k + 1) → ZMod 2 → ZMod 2 → ZMod 2 // Consistent (k + 1) f}
      ≃ {g : Fin (k + 1) → BM // diagB (prodB (k + 1) g) = true} :=
    Equiv.subtypeEquiv
      (Equiv.arrowCongr (Equiv.refl (Fin (k + 1))) (Equiv.ofBijective toB toB_bijective))
      (fun f => consistent_iff k f)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ### The closed form -/

theorem u_succ_succ (n : ℕ) : u (n + 2) = 17 * u (n + 1) - 48 * u n := by
  rw [u]

theorem u_real (n : ℕ) :
    2 * (u (n + 1) : ℝ) - 17 * (u n : ℝ)
        = ((17 + Real.sqrt 97) / 2) ^ n + ((17 - Real.sqrt 97) / 2) ^ n
      ∧ 2 * (u (n + 2) : ℝ) - 17 * (u (n + 1) : ℝ)
        = ((17 + Real.sqrt 97) / 2) ^ (n + 1) + ((17 - Real.sqrt 97) / 2) ^ (n + 1) := by
  have h97 : Real.sqrt 97 ^ 2 = 97 := Real.sq_sqrt (by norm_num)
  have hL : ((17 + Real.sqrt 97) / 2) ^ 2 = 17 * ((17 + Real.sqrt 97) / 2) - 48 := by
    linear_combination (1 / 4) * h97
  have hM : ((17 - Real.sqrt 97) / 2) ^ 2 = 17 * ((17 - Real.sqrt 97) / 2) - 48 := by
    linear_combination (1 / 4) * h97
  induction n with
  | zero =>
    constructor
    · norm_num [u]
    · norm_num [u]
      ring
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hu : (u (n + 1 + 2) : ℝ) = 17 * (u (n + 1 + 1) : ℝ) - 48 * (u (n + 1) : ℝ) := by
      rw [u_succ_succ]
      push_cast
      ring
    have hu2 : (u (n + 2) : ℝ) = 17 * (u (n + 1) : ℝ) - 48 * (u n : ℝ) := by
      rw [u_succ_succ]
      push_cast
      ring
    rw [hu]
    linear_combination 17 * h2 - 48 * h1 - 17 * hu2
      - ((17 + Real.sqrt 97) / 2) ^ n * hL - ((17 - Real.sqrt 97) / 2) ^ n * hM

/-- The exact value of the consistency probability of the cycle with `k + 1` edges. -/
theorem qCycle_eq (k : ℕ) :
    qCycle (k + 1)
      = ((17 + Real.sqrt 97) / 32) ^ (k + 1) + ((17 - Real.sqrt 97) / 32) ^ (k + 1)
        - 1 / 4 ^ (k + 1) - 1 / (2 * 8 ^ (k + 1)) := by
  unfold qCycle
  rw [card_consistent k]
  have hc : (((Finset.univ.filter
      (fun g : Fin (k + 1) → BM => diagB (prodB (k + 1) g) = true)).card : ℕ) : ℝ)
      = 2 * (u (k + 2) : ℝ) - 17 * (u (k + 1) : ℝ) - 4 ^ (k + 1) - 2 ^ (k + 1) / 2 := by
    have h := congrArg (Rat.cast (K := ℝ)) (count_diag k)
    push_cast at h
    exact h
  rw [hc, (u_real (k + 1)).1]
  have h1 : ((17 + Real.sqrt 97) / 32) ^ (k + 1)
      = ((17 + Real.sqrt 97) / 2) ^ (k + 1) / 16 ^ (k + 1) := by
    rw [← div_pow]
    congr 1
    ring
  have h2 : ((17 - Real.sqrt 97) / 32) ^ (k + 1)
      = ((17 - Real.sqrt 97) / 2) ^ (k + 1) / 16 ^ (k + 1) := by
    rw [← div_pow]
    congr 1
    ring
  have h3 : (1 : ℝ) / 4 ^ (k + 1) = 4 ^ (k + 1) / 16 ^ (k + 1) := by
    rw [show (16 : ℝ) = 4 * 4 by norm_num, mul_pow]
    field_simp
  have h4 : (1 : ℝ) / (2 * 8 ^ (k + 1)) = 2 ^ (k + 1) / 2 / 16 ^ (k + 1) := by
    rw [show (16 : ℝ) = 2 * 8 by norm_num, mul_pow]
    field_simp
  rw [h1, h2, h3, h4]
  ring

end CycleProof

open CycleProof in
theorem result : Claim := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := qCycle_eq k
  refine ⟨h, ?_⟩
  rw [h]
  intro heq
  have hpos : (0 : ℝ) < 8 ^ k := by positivity
  have h8 : (1 : ℝ) / (2 * 8 ^ (k + 1)) = 1 / 8 ^ (k + 1 - 1) := by linarith
  rw [Nat.add_sub_cancel, pow_succ] at h8
  field_simp at h8
  linarith
