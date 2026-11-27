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

/-! ## The proof

Everything above this line is the statement, word for word as in `Challenge.lean`.
Everything below is the proof. -/

/-!
# Kourovka 20.52, the odd half

For `u` in `Z/n` with `u^2 + u + 1 = 0` and `n` prime to 3, the group
`G = (Z/n × Z/a) ⋊ Z/3` (the generator of `Z/3` multiplies `Z/n` by `u`) has
`a^2 (n^2 + 8n)` commuting pairs, so `k(G) = a (n + 8) / 3` and
`|G| - k(G) = 8 a (n - 1) / 3`.

* Part 1: the group.
* Part 2: counting commuting pairs.
* Part 3: `n = 12 y^2 + 1`, `u = 6 y^2 + 3 y` with `y` a power of two, and `n = 7`, `u = 2`.
-/

namespace K2052

variable {n a : ℕ}

/-! ## Part 1: the group -/

/-- `pw u s` is `u ^ s` for `s` in `Z/3`. -/
def pw (u : ZMod n) (s : ZMod 3) : ZMod n := u ^ s.val

theorem cube {u : ZMod n} (hu : u ^ 2 + u + 1 = 0) : u ^ 3 = 1 := by
  linear_combination (u - 1) * hu

theorem pow_mod3 {u : ZMod n} (h3 : u ^ 3 = 1) (k : ℕ) : u ^ (k % 3) = u ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, h3, one_pow, one_mul]

theorem pw_add {u : ZMod n} (h3 : u ^ 3 = 1) (s t : ZMod 3) :
    pw u (s + t) = pw u s * pw u t := by
  unfold pw
  rw [ZMod.val_add, pow_mod3 h3, pow_add]

theorem pw_zero (u : ZMod n) : pw u 0 = 1 := by
  simp [pw]

theorem pw_one (u : ZMod n) : pw u 1 = u := by
  have h : (1 : ZMod 3).val = 1 := by decide
  unfold pw
  rw [h, pow_one]

theorem pw_two (u : ZMod n) : pw u 2 = u ^ 2 := by
  have h : (2 : ZMod 3).val = 2 := by decide
  unfold pw
  rw [h]

/-- The underlying set of `(Z/n × Z/a) ⋊ Z/3`.  The parameter `u` fixes the product. -/
@[ext] structure Grp (n a : ℕ) (u : ZMod n) where
  x : ZMod n
  y : ZMod a
  s : ZMod 3

variable {u : ZMod n}

instance : Mul (Grp n a u) := ⟨fun p q => ⟨p.x + pw u p.s * q.x, p.y + q.y, p.s + q.s⟩⟩
instance : One (Grp n a u) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (Grp n a u) := ⟨fun p => ⟨-(pw u (-p.s) * p.x), -p.y, -p.s⟩⟩

@[simp] theorem mul_x (p q : Grp n a u) : (p * q).x = p.x + pw u p.s * q.x := rfl
@[simp] theorem mul_y (p q : Grp n a u) : (p * q).y = p.y + q.y := rfl
@[simp] theorem mul_s (p q : Grp n a u) : (p * q).s = p.s + q.s := rfl
@[simp] theorem one_x : (1 : Grp n a u).x = 0 := rfl
@[simp] theorem one_y : (1 : Grp n a u).y = 0 := rfl
@[simp] theorem one_s : (1 : Grp n a u).s = 0 := rfl
@[simp] theorem inv_x (p : Grp n a u) : (p⁻¹).x = -(pw u (-p.s) * p.x) := rfl
@[simp] theorem inv_y (p : Grp n a u) : (p⁻¹).y = -p.y := rfl
@[simp] theorem inv_s (p : Grp n a u) : (p⁻¹).s = -p.s := rfl

instance instGroup [hf : Fact (u ^ 2 + u + 1 = 0)] : Group (Grp n a u) :=
  Group.ofLeftAxioms
    (fun p q r => by
      ext
      · simp only [mul_x, mul_s, pw_add (cube hf.out)]; ring
      · simp only [mul_y]; ring
      · simp only [mul_s]; ring)
    (fun p => by
      ext
      · simp only [mul_x, one_x, one_s, pw_zero]; ring
      · simp only [mul_y, one_y]; ring
      · simp only [mul_s, one_s]; ring)
    (fun p => by
      ext
      · simp only [mul_x, inv_x, inv_s, one_x]; ring
      · simp only [mul_y, inv_y, one_y]; ring
      · simp only [mul_s, inv_s, one_s]; ring)

/-- The underlying set as a product. -/
def equivProd : Grp n a u ≃ ZMod n × ZMod a × ZMod 3 where
  toFun g := (g.x, g.y, g.s)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [NeZero n] [NeZero a] : Finite (Grp n a u) := Finite.of_equiv _ equivProd.symm

theorem card_grp : Nat.card (Grp n a u) = n * a * 3 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod, Nat.card_zmod, Nat.card_zmod,
    Nat.card_zmod]
  ring

/-! ## Part 2: commuting pairs -/

/-- `cc u s = 1 - u ^ s`. -/
def cc (u : ZMod n) (s : ZMod 3) : ZMod n := 1 - pw u s

theorem comm_iff [Fact (u ^ 2 + u + 1 = 0)] (p q : Grp n a u) :
    Commute p q ↔ cc u q.s * p.x = cc u p.s * q.x := by
  unfold cc
  constructor
  · intro h
    have h1 := congrArg Grp.x h.eq
    simp only [mul_x] at h1
    linear_combination h1
  · intro h
    show p * q = q * p
    ext
    · simp only [mul_x]; linear_combination h
    · simp only [mul_y]; ring
    · simp only [mul_s]; ring

theorem unit_cc (hu : u ^ 2 + u + 1 = 0) (h3n : Nat.Coprime 3 n) (s : ZMod 3) (hs : s ≠ 0) :
    IsUnit (cc u s) := by
  have h3 : IsUnit ((1 - u) * (1 - u ^ 2)) := by
    have e : (1 - u) * (1 - u ^ 2) = ((3 : ℕ) : ZMod n) := by
      push_cast
      linear_combination (u - 2) * hu
    rw [e]
    exact (ZMod.isUnit_iff_coprime 3 n).mpr h3n
  have hs' : s = 1 ∨ s = 2 := by
    revert s
    decide
  unfold cc
  rcases hs' with rfl | rfl
  · rw [pw_one]
    exact isUnit_of_mul_isUnit_left h3
  · rw [pw_two]
    exact isUnit_of_mul_isUnit_right h3

/-- The pairs `(x, x')` with `c_t x = c_s x'`. -/
abbrev Fib (u : ZMod n) (st : ZMod 3 × ZMod 3) : Type :=
  {xx : ZMod n × ZMod n // cc u st.2 * xx.1 = cc u st.1 * xx.2}

theorem card_sol_right (w v : ZMod n) (hv : IsUnit v) :
    Nat.card {xx : ZMod n × ZMod n // w * xx.1 = v * xx.2} = n := by
  obtain ⟨v', rfl⟩ := hv
  have e : {xx : ZMod n × ZMod n // w * xx.1 = ↑v' * xx.2} ≃ ZMod n :=
    { toFun := fun xx => xx.1.1
      invFun := fun x => ⟨(x, ↑v'⁻¹ * (w * x)), by simp⟩
      left_inv := by
        rintro ⟨⟨x, x'⟩, h⟩
        have h' : w * x = ↑v' * x' := h
        simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
        rw [h']
        simp
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_zmod]

theorem card_sol_left (w v : ZMod n) (hw : IsUnit w) :
    Nat.card {xx : ZMod n × ZMod n // w * xx.1 = v * xx.2} = n := by
  have e : {xx : ZMod n × ZMod n // w * xx.1 = v * xx.2} ≃
      {xx : ZMod n × ZMod n // v * xx.1 = w * xx.2} :=
    { toFun := fun xx => ⟨(xx.1.2, xx.1.1), xx.2.symm⟩
      invFun := fun xx => ⟨(xx.1.2, xx.1.1), xx.2.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (card_sol_right v w hw)

theorem card_sol_zero :
    Nat.card {xx : ZMod n × ZMod n // (0 : ZMod n) * xx.1 = 0 * xx.2} = n * n := by
  have e : {xx : ZMod n × ZMod n // (0 : ZMod n) * xx.1 = 0 * xx.2} ≃ ZMod n × ZMod n :=
    Equiv.subtypeUnivEquiv (fun xx => by simp)
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]

theorem card_fib (hu : u ^ 2 + u + 1 = 0) (h3n : Nat.Coprime 3 n) (st : ZMod 3 × ZMod 3) :
    Nat.card (Fib u st) = if st = (0, 0) then n * n else n := by
  obtain ⟨s, t⟩ := st
  by_cases hs : s = 0
  · by_cases ht : t = 0
    · subst hs ht
      rw [ite_eq_left rfl]
      have h0 : cc u 0 = 0 := by simp [cc, pw_zero]
      show Nat.card {xx : ZMod n × ZMod n // cc u 0 * xx.1 = cc u 0 * xx.2} = n * n
      rw [h0]
      exact card_sol_zero
    · rw [ite_eq_right (by simp [ht])]
      exact card_sol_left _ _ (unit_cc hu h3n t ht)
  · rw [ite_eq_right (by simp [hs])]
    exact card_sol_right _ _ (unit_cc hu h3n s hs)

theorem sum_nine (A B : ℕ) :
    (∑ st : ZMod 3 × ZMod 3, if st = (0, 0) then A else B) = A + 8 * B := by
  have h1 : (Finset.univ.filter fun st : ZMod 3 × ZMod 3 => st = (0, 0)).card = 1 := by decide
  have h8 : (Finset.univ.filter fun st : ZMod 3 × ZMod 3 => ¬ st = (0, 0)).card = 8 := by decide
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h1, h8]
  simp

theorem card_comm [NeZero n] [NeZero a] [hf : Fact (u ^ 2 + u + 1 = 0)]
    (h3n : Nat.Coprime 3 n) :
    Nat.card {pq : Grp n a u × Grp n a u // Commute pq.1 pq.2} = a * a * (n * n + 8 * n) := by
  have e : {pq : Grp n a u × Grp n a u // Commute pq.1 pq.2} ≃
      (ZMod a × ZMod a) × (Σ st : ZMod 3 × ZMod 3, Fib u st) :=
    { toFun := fun pq => ((pq.1.1.y, pq.1.2.y),
        ⟨(pq.1.1.s, pq.1.2.s), ⟨(pq.1.1.x, pq.1.2.x), (comm_iff _ _).mp pq.2⟩⟩)
      invFun := fun z => ⟨(⟨z.2.2.1.1, z.1.1, z.2.1.1⟩, ⟨z.2.2.1.2, z.1.2, z.2.1.2⟩),
        (comm_iff _ _).mpr z.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_zmod, Nat.card_sigma]
  simp only [card_fib hf.out h3n]
  rw [sum_nine]

/-! ## Part 3: the groups -/

theorem attained_of (n a m : ℕ) (u : ZMod n) (hn : 1 < n) (hnodd : Odd n) (ha : Odd a)
    (h3n : Nat.Coprime 3 n) (hu : u ^ 2 + u + 1 = 0) (hm : a * n = 6 * m + a) :
    Attained m := by
  have : NeZero n := ⟨by omega⟩
  have : NeZero a := ⟨by rcases ha with ⟨k, rfl⟩; omega⟩
  have : Fact (1 < n) := ⟨hn⟩
  have : Fact (u ^ 2 + u + 1 = 0) := ⟨hu⟩
  refine ⟨Grp n a u, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [card_grp]
    exact (hnodd.mul ha).mul (by decide)
  · refine ⟨⟨1, 0, 0⟩, ⟨0, 0, 1⟩, ?_⟩
    intro h
    have h1 := congrArg Grp.x h
    simp only [mul_x, pw_zero, pw_one] at h1
    have hu1 : u = 1 := by linear_combination -h1
    have h3u : IsUnit ((3 : ℕ) : ZMod n) := (ZMod.isUnit_iff_coprime 3 n).mpr h3n
    have e3 : ((3 : ℕ) : ZMod n) = 0 := by
      push_cast
      linear_combination hu - (u + 2) * hu1
    rw [e3] at h3u
    exact not_isUnit_zero h3u
  · have hc := card_comm_eq_card_conjClasses_mul_card (Grp n a u)
    rw [card_comm h3n, card_grp] at hc
    rw [card_grp]
    generalize Nat.card (ConjClasses (Grp n a u)) = K at hc ⊢
    have hpos : 0 < n * a := by
      have : 0 < a := by rcases ha with ⟨k, rfl⟩; omega
      positivity
    have h2 : a * (n + 8) = K * 3 := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc n * a * (a * (n + 8)) = a * a * (n * n + 8 * n) := by ring
        _ = K * (n * a * 3) := hc
        _ = n * a * (K * 3) := by ring
    have e1 : n * a * 3 = 3 * (a * n) := by ring
    have e2 : a * (n + 8) = a * n + 8 * a := by ring
    rw [e1]
    rw [e2] at h2
    generalize a * n = P at hm h2 ⊢
    omega

end K2052

open K2052 in
theorem result : Claim := by
  intro m hm h
  rcases h with hodd | hval
  · exact attained_of 7 m m 2 (by norm_num) (by decide) hodd (by decide) (by decide) (by ring)
  · obtain ⟨k, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
    have hb0 : b ≠ 0 := by rcases hb with ⟨c, rfl⟩; omega
    have hk : padicValNat 2 (2 ^ k * b) = k := by
      rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ (by norm_num)) hb0,
        Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hb.not_two_dvd_nat, add_zero]
    rw [hk] at hval
    obtain ⟨i, rfl⟩ := hval
    obtain ⟨y, hy⟩ : ∃ y, y = 2 ^ i := ⟨_, rfl⟩
    have hy0 : 0 < y := by rw [hy]; positivity
    have h2 : 2 ^ (2 * i + 1) = 2 * y ^ 2 := by rw [hy]; ring
    rw [h2]
    refine attained_of (12 * y ^ 2 + 1) b (2 * y ^ 2 * b)
      ((6 * y ^ 2 + 3 * y : ℕ) : ZMod (12 * y ^ 2 + 1)) ?_ ?_ hb ?_ ?_ ?_
    · nlinarith
    · exact ⟨6 * y ^ 2, by ring⟩
    · rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    · have e : (6 * y ^ 2 + 3 * y) ^ 2 + (6 * y ^ 2 + 3 * y) + 1
          = (12 * y ^ 2 + 1) * (3 * y ^ 2 + 3 * y + 1) := by ring
      have e' : (((6 * y ^ 2 + 3 * y) ^ 2 + (6 * y ^ 2 + 3 * y) + 1 : ℕ) :
          ZMod (12 * y ^ 2 + 1)) = 0 := by
        rw [e, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      exact_mod_cast e'
    · ring
