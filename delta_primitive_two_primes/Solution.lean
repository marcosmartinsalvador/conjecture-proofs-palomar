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

/-! ## The proof

Everything above this line is the statement, word for word as in `Challenge.lean`.
Everything below is the proof. -/

/-!
Proof that 24 and 40 are the only Delta-primitive numbers of the form `p^x * q^y`.

Outline (details in `PROOF_NOTES.md`). Write `P = p^x`, `Q = q^y`, `n = P * Q`. The Delta
property gives three pairs of complementary divisors `(a, b)` whose differences satisfy
`|e1| = |e2| + |e3|`.

* If a prime divides all six divisors, `n / r^2` has the Delta property (`descent`), so `n`
  is not primitive. Hence at most one pair has both members divisible by `p`, and the same
  for `q` (`not_two_both`).
* The pair `{1, n}` cannot occur (`no_one`).
* Every other pair is `{P, Q}`, or `{p^i, p^i' * Q}`, or `{q^j, q^j' * P}`, or has both
  members divisible by `p` and by `q` (`classify`).
* The few combinations that survive are settled by arithmetic: `two_fs_arith` gives `24` and
  `40`, and `star` gives `216 = 3^2 * 24`, which is not primitive.
-/

namespace DeltaTwoPrimes

/-! ### The Delta property as a statement about three pairs of divisors -/

theorem exists_triple {n : ℕ} (h : HasDelta n) :
    ∃ a1 b1 a2 b2 a3 b3 : ℕ, a1 * b1 = n ∧ a2 * b2 = n ∧ a3 * b3 = n ∧
      |(a1 : ℤ) - b1| = |(a2 : ℤ) - b2| + |(a3 : ℤ) - b3| ∧
      (a2 : ℤ) - b2 ≠ 0 ∧ (a3 : ℤ) - b3 ≠ 0 := by
  obtain ⟨d, ⟨a1, b1, h1, hd⟩, s, ⟨a2, b2, h2, hs⟩, t, ⟨a3, b3, h3, ht⟩, hs0, ht0, hst⟩ := h
  refine ⟨a1, b1, a2, b2, a3, b3, h1, h2, h3, ?_, ?_, ?_⟩
  · rw [← hd, ← hs, ← ht, hst]
    push_cast
    ring
  · intro h0
    rw [h0, abs_zero] at hs
    exact hs0 (by exact_mod_cast hs)
  · intro h0
    rw [h0, abs_zero] at ht
    exact ht0 (by exact_mod_cast ht)

theorem hasDelta_of_triple {n a1 b1 a2 b2 a3 b3 : ℕ} (h1 : a1 * b1 = n) (h2 : a2 * b2 = n)
    (h3 : a3 * b3 = n) (he : |(a1 : ℤ) - b1| = |(a2 : ℤ) - b2| + |(a3 : ℤ) - b3|)
    (h20 : (a2 : ℤ) - b2 ≠ 0) (h30 : (a3 : ℤ) - b3 ≠ 0) : HasDelta n := by
  refine ⟨((a1 : ℤ) - b1).natAbs, ⟨a1, b1, h1, by simp⟩, ((a2 : ℤ) - b2).natAbs,
    ⟨a2, b2, h2, by simp⟩, ((a3 : ℤ) - b3).natAbs, ⟨a3, b3, h3, by simp⟩, ?_, ?_, ?_⟩
  · simpa using h20
  · simpa using h30
  · zify
    simpa using he

theorem hasDelta_24 : HasDelta 24 :=
  hasDelta_of_triple (a1 := 2) (b1 := 12) (a2 := 3) (b2 := 8) (a3 := 3) (b3 := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem not_hasDelta_one : ¬ HasDelta 1 := by
  intro h
  obtain ⟨a1, b1, a2, b2, a3, b3, -, h2, -, -, h20, -⟩ := exists_triple h
  have ha : a2 = 1 := Nat.eq_one_of_mul_eq_one_right h2
  have hb : b2 = 1 := Nat.eq_one_of_mul_eq_one_left h2
  subst ha hb
  exact h20 (by norm_num)

/-! ### Easy facts about a pair of complementary divisors -/

theorem pair_bounds {n a b : ℕ} (hn : 0 < n) (h : a * b = n) :
    (a = 1 ∧ b = n) ∨ (a = n ∧ b = 1) ∨ (2 ≤ a ∧ 2 ≤ b ∧ 2 * a ≤ n ∧ 2 * b ≤ n) := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h
    omega
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h
    omega
  by_cases ha1 : a = 1
  · left
    subst ha1
    exact ⟨rfl, by simpa using h⟩
  by_cases hb1 : b = 1
  · right
    left
    subst hb1
    exact ⟨by simpa using h, rfl⟩
  right
  right
  have h2a : 2 ≤ a := by omega
  have h2b : 2 ≤ b := by omega
  refine ⟨h2a, h2b, ?_, ?_⟩ <;> nlinarith

/-- The pair `{1, n}` does not occur in a Delta triple. -/
theorem no_one {n a1 b1 a2 b2 a3 b3 : ℕ} (hn : 0 < n) (h1 : a1 * b1 = n) (h2 : a2 * b2 = n)
    (h3 : a3 * b3 = n) (he : |(a1 : ℤ) - b1| = |(a2 : ℤ) - b2| + |(a3 : ℤ) - b3|)
    (h20 : (a2 : ℤ) - b2 ≠ 0) (h30 : (a3 : ℤ) - b3 ≠ 0) :
    (a1 ≠ 1 ∧ b1 ≠ 1) ∧ (a2 ≠ 1 ∧ b2 ≠ 1) ∧ (a3 ≠ 1 ∧ b3 ≠ 1) := by
  have p1 := pair_bounds hn h1
  have p2 := pair_bounds hn h2
  have p3 := pair_bounds hn h3
  have c1 := abs_cases ((a1 : ℤ) - b1)
  have c2 := abs_cases ((a2 : ℤ) - b2)
  have c3 := abs_cases ((a3 : ℤ) - b3)
  omega

/-- If `r` divides all six divisors of a Delta triple of `n`, then `n / r^2` has the Delta
property. -/
theorem descent {n r a1 b1 a2 b2 a3 b3 : ℕ} (hr : 0 < r) (h1 : a1 * b1 = n) (h2 : a2 * b2 = n)
    (h3 : a3 * b3 = n) (he : |(a1 : ℤ) - b1| = |(a2 : ℤ) - b2| + |(a3 : ℤ) - b3|)
    (h20 : (a2 : ℤ) - b2 ≠ 0) (h30 : (a3 : ℤ) - b3 ≠ 0)
    (d1 : r ∣ a1 ∧ r ∣ b1) (d2 : r ∣ a2 ∧ r ∣ b2) (d3 : r ∣ a3 ∧ r ∣ b3) :
    ∃ m : ℕ, n = r ^ 2 * m ∧ HasDelta m := by
  obtain ⟨⟨a1', rfl⟩, ⟨b1', rfl⟩⟩ := d1
  obtain ⟨⟨a2', rfl⟩, ⟨b2', rfl⟩⟩ := d2
  obtain ⟨⟨a3', rfl⟩, ⟨b3', rfl⟩⟩ := d3
  have hr2 : 0 < r ^ 2 := by positivity
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  refine ⟨a1' * b1', by rw [← h1]; ring, ?_⟩
  have e2 : a2' * b2' = a1' * b1' := by
    apply Nat.eq_of_mul_eq_mul_left hr2
    calc r ^ 2 * (a2' * b2') = r * a2' * (r * b2') := by ring
      _ = n := h2
      _ = r * a1' * (r * b1') := h1.symm
      _ = r ^ 2 * (a1' * b1') := by ring
  have e3 : a3' * b3' = a1' * b1' := by
    apply Nat.eq_of_mul_eq_mul_left hr2
    calc r ^ 2 * (a3' * b3') = r * a3' * (r * b3') := by ring
      _ = n := h3
      _ = r * a1' * (r * b1') := h1.symm
      _ = r ^ 2 * (a1' * b1') := by ring
  have key : ∀ a b : ℕ, |((r * a : ℕ) : ℤ) - ((r * b : ℕ) : ℤ)| = r * |(a : ℤ) - b| := by
    intro a b
    push_cast
    rw [← mul_sub, abs_mul, abs_of_pos hrZ]
  rw [key, key, key, ← mul_add] at he
  have he' := mul_left_cancel₀ hrZ.ne' he
  refine hasDelta_of_triple rfl e2 e3 he' ?_ ?_
  · intro h0
    apply h20
    push_cast
    rw [← mul_sub, h0, mul_zero]
  · intro h0
    apply h30
    push_cast
    rw [← mul_sub, h0, mul_zero]

/-! ### The symmetric form of the relation between the three differences -/

/-- One of the three numbers is, up to signs, the sum of the other two. -/
abbrev SumRel (e1 e2 e3 : ℤ) : Prop :=
  e1 + e2 + e3 = 0 ∨ e1 + e2 - e3 = 0 ∨ e1 - e2 + e3 = 0 ∨ -e1 + e2 + e3 = 0

theorem sumRel_of_abs {e1 e2 e3 : ℤ} (h : |e1| = |e2| + |e3|) : SumRel e1 e2 e3 := by
  have c1 := abs_cases e1
  have c2 := abs_cases e2
  have c3 := abs_cases e3
  unfold SumRel
  omega

theorem SumRel.swap12 {e1 e2 e3 : ℤ} (h : SumRel e1 e2 e3) : SumRel e2 e1 e3 := by
  unfold SumRel at *
  omega

theorem SumRel.swap23 {e1 e2 e3 : ℤ} (h : SumRel e1 e2 e3) : SumRel e1 e3 e2 := by
  unfold SumRel at *
  omega

theorem SumRel.of_signs {e1 e2 e3 X1 X2 X3 : ℤ} (h : SumRel e1 e2 e3)
    (h1 : e1 = X1 ∨ e1 = -X1) (h2 : e2 = X2 ∨ e2 = -X2) (h3 : e3 = X3 ∨ e3 = -X3) :
    SumRel X1 X2 X3 := by
  unfold SumRel at *
  omega

theorem SumRel.dvd3 {r e1 e2 e3 : ℤ} (h : SumRel e1 e2 e3) (d1 : r ∣ e1) (d2 : r ∣ e2) :
    r ∣ e3 := by
  rcases h with h | h | h | h
  · have e : e3 = -(e1 + e2) := by linarith
    rw [e]
    exact dvd_neg.mpr (dvd_add d1 d2)
  · have e : e3 = e1 + e2 := by linarith
    rw [e]
    exact dvd_add d1 d2
  · have e : e3 = e2 - e1 := by linarith
    rw [e]
    exact dvd_sub d2 d1
  · have e : e3 = e1 - e2 := by linarith
    rw [e]
    exact dvd_sub d1 d2

/-! ### Step 2: a prime divides both members of at most one pair -/

theorem both_third {n r a1 b1 a2 b2 a3 b3 : ℕ} (hr : r.Prime) (h1 : a1 * b1 = n)
    (h3 : a3 * b3 = n) (hrel : SumRel ((a1 : ℤ) - b1) ((a2 : ℤ) - b2) ((a3 : ℤ) - b3))
    (d1 : r ∣ a1 ∧ r ∣ b1) (d2 : r ∣ a2 ∧ r ∣ b2) : r ∣ a3 ∧ r ∣ b3 := by
  have z1 : (r : ℤ) ∣ (a1 : ℤ) - b1 :=
    dvd_sub (Int.natCast_dvd_natCast.mpr d1.1) (Int.natCast_dvd_natCast.mpr d1.2)
  have z2 : (r : ℤ) ∣ (a2 : ℤ) - b2 :=
    dvd_sub (Int.natCast_dvd_natCast.mpr d2.1) (Int.natCast_dvd_natCast.mpr d2.2)
  have z3 : (r : ℤ) ∣ (a3 : ℤ) - b3 := hrel.dvd3 z1 z2
  have hn : r ∣ a3 * b3 := by
    rw [h3, ← h1]
    exact Dvd.dvd.mul_right d1.1 _
  rcases hr.dvd_mul.mp hn with h | h
  · refine ⟨h, ?_⟩
    have hz : (r : ℤ) ∣ (a3 : ℤ) - ((a3 : ℤ) - b3) :=
      dvd_sub (Int.natCast_dvd_natCast.mpr h) z3
    rw [sub_sub_cancel] at hz
    exact Int.natCast_dvd_natCast.mp hz
  · refine ⟨?_, h⟩
    have hz : (r : ℤ) ∣ (a3 : ℤ) - b3 + b3 := dvd_add z3 (Int.natCast_dvd_natCast.mpr h)
    rw [sub_add_cancel] at hz
    exact Int.natCast_dvd_natCast.mp hz

theorem not_two_both {n r a1 b1 a2 b2 a3 b3 : ℕ} (hr : r.Prime) (hn : 0 < n)
    (hprim : ¬ ∃ α m : ℕ, 2 ≤ α ∧ 2 ≤ m ∧ n = α ^ 2 * m ∧ HasDelta m)
    (h1 : a1 * b1 = n) (h2 : a2 * b2 = n) (h3 : a3 * b3 = n)
    (he : |(a1 : ℤ) - b1| = |(a2 : ℤ) - b2| + |(a3 : ℤ) - b3|)
    (h20 : (a2 : ℤ) - b2 ≠ 0) (h30 : (a3 : ℤ) - b3 ≠ 0) :
    ¬ ((r ∣ a1 ∧ r ∣ b1) ∧ (r ∣ a2 ∧ r ∣ b2)) ∧ ¬ ((r ∣ a1 ∧ r ∣ b1) ∧ (r ∣ a3 ∧ r ∣ b3)) ∧
      ¬ ((r ∣ a2 ∧ r ∣ b2) ∧ (r ∣ a3 ∧ r ∣ b3)) := by
  have hrel := sumRel_of_abs he
  have all : (r ∣ a1 ∧ r ∣ b1) → (r ∣ a2 ∧ r ∣ b2) → (r ∣ a3 ∧ r ∣ b3) → False := by
    intro d1 d2 d3
    obtain ⟨m, hm, hDm⟩ := descent hr.pos h1 h2 h3 he h20 h30 d1 d2 d3
    refine hprim ⟨r, m, hr.two_le, ?_, hm, hDm⟩
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m
      · rw [mul_zero] at hm
        omega
      · exact absurd hDm not_hasDelta_one
    · exact hge
  refine ⟨fun ⟨d1, d2⟩ => all d1 d2 (both_third hr h1 h3 hrel d1 d2),
    fun ⟨d1, d3⟩ => all d1 (both_third hr h1 h2 hrel.swap23 d1 d3) d3,
    fun ⟨d2, d3⟩ => all (both_third hr h2 h1 hrel.swap12.swap23 d2 d3) d2 d3⟩

/-! ### Step 4: the shapes of a pair of complementary divisors of `p^x * q^y` -/

theorem two_le_pow {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) : 2 ≤ p ^ i :=
  le_trans hp.two_le (Nat.le_self_pow (by omega) p)

theorem pair_shape {p q x y a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : a * b = p ^ x * q ^ y) :
    ∃ i i' j j' : ℕ, i + i' = x ∧ j + j' = y ∧ a = p ^ i * q ^ j ∧ b = p ^ i' * q ^ j' := by
  have hda : a ∣ p ^ x * q ^ y := Dvd.intro _ h
  obtain ⟨k₁, k₂, hk₁, hk₂, rfl⟩ := (Nat.dvd_mul).mp hda
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hk₁
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hq).mp hk₂
  refine ⟨i, x - i, j, y - j, by omega, by omega, rfl, ?_⟩
  have hpos : 0 < p ^ i * q ^ j := Nat.mul_pos (pow_pos hp.pos i) (pow_pos hq.pos j)
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h]
  have e1 : p ^ x = p ^ i * p ^ (x - i) := by
    rw [← pow_add]
    congr 1
    omega
  have e2 : q ^ y = q ^ j * q ^ (y - j) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e1, e2]
  ring

/-- The pair is `{P, Q}`. -/
abbrev FS (P Q : ℕ) (e : ℤ) : Prop := e = (P : ℤ) - (Q : ℤ) ∨ e = -((P : ℤ) - (Q : ℤ))

/-- The pair is `{p^i, p^i' * Q}` with `i, i' ≥ 1` and `i + i' = x`. -/
abbrev NS (p x Q : ℕ) (e : ℤ) : Prop :=
  ∃ i i' : ℕ, 1 ≤ i ∧ 1 ≤ i' ∧ i + i' = x ∧
    (e = ((p ^ i' * Q : ℕ) : ℤ) - ((p ^ i : ℕ) : ℤ) ∨
      e = -(((p ^ i' * Q : ℕ) : ℤ) - ((p ^ i : ℕ) : ℤ)))

theorem FS.symm {P Q : ℕ} {e : ℤ} (h : FS P Q e) : FS Q P e := by
  unfold FS at *
  omega

theorem classify {p q x y a b : ℕ} (hp : p.Prime) (hq : q.Prime) (h : a * b = p ^ x * q ^ y)
    (ha : a ≠ 1) (hb : b ≠ 1) :
    FS (p ^ x) (q ^ y) ((a : ℤ) - b) ∨
      (NS p x (q ^ y) ((a : ℤ) - b) ∧ (p ∣ a ∧ p ∣ b)) ∨
      (NS q y (p ^ x) ((a : ℤ) - b) ∧ (q ∣ a ∧ q ∣ b)) ∨
      ((p ∣ a ∧ p ∣ b) ∧ (q ∣ a ∧ q ∣ b)) := by
  obtain ⟨i, i', j, j', rfl, rfl, rfl, rfl⟩ := pair_shape hp hq h
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp at ha
    · rcases Nat.eq_zero_or_pos j' with rfl | hj0'
      · refine Or.inl (Or.inr ?_)
        push_cast
        ring
      · refine Or.inr (Or.inr (Or.inl ⟨⟨j, j', hj0, hj0', rfl, Or.inr ?_⟩, ?_, ?_⟩))
        · push_cast
          ring
        · exact Dvd.dvd.mul_left (dvd_pow_self q (by omega)) _
        · exact Dvd.dvd.mul_left (dvd_pow_self q (by omega)) _
  · rcases Nat.eq_zero_or_pos i' with rfl | hi0'
    · rcases Nat.eq_zero_or_pos j' with rfl | hj0'
      · simp at hb
      · rcases Nat.eq_zero_or_pos j with rfl | hj0
        · refine Or.inl (Or.inl ?_)
          push_cast
          ring
        · refine Or.inr (Or.inr (Or.inl ⟨⟨j', j, hj0', hj0, by omega, Or.inl ?_⟩, ?_, ?_⟩))
          · push_cast
            ring
          · exact Dvd.dvd.mul_left (dvd_pow_self q (by omega)) _
          · exact Dvd.dvd.mul_left (dvd_pow_self q (by omega)) _
    · have hpa : p ∣ p ^ i * q ^ j := Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
      have hpb : p ∣ p ^ i' * q ^ j' := Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · refine Or.inr (Or.inl ⟨⟨i, i', hi0, hi0', rfl, Or.inr ?_⟩, hpa, hpb⟩)
        push_cast
        ring
      · rcases Nat.eq_zero_or_pos j' with rfl | hj0'
        · refine Or.inr (Or.inl ⟨⟨i', i, hi0', hi0, by omega, Or.inl ?_⟩, hpa, hpb⟩)
          push_cast
          ring
        · exact Or.inr (Or.inr (Or.inr ⟨⟨hpa, hpb⟩,
            Dvd.dvd.mul_left (dvd_pow_self q (by omega)) _,
            Dvd.dvd.mul_left (dvd_pow_self q (by omega)) _⟩))

/-! ### Step 5: the cases with two pairs equal to `{P, Q}` -/

theorem case_fff {P Q : ℕ} (hne : P ≠ Q) {e1 e2 e3 : ℤ} (f1 : FS P Q e1) (f2 : FS P Q e2)
    (f3 : FS P Q e3) (hrel : SumRel e1 e2 e3) : False := by
  unfold FS at *
  unfold SumRel at hrel
  omega

theorem ffx {P Q : ℕ} {e1 e2 e3 : ℤ} (f1 : FS P Q e1) (f2 : FS P Q e2)
    (hrel : SumRel e1 e2 e3) (h30 : e3 ≠ 0) :
    e3 = 2 * ((P : ℤ) - (Q : ℤ)) ∨ e3 = -(2 * ((P : ℤ) - (Q : ℤ))) := by
  unfold FS at *
  unfold SumRel at hrel
  omega

theorem eq_two_of_dvd {p q x y : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hx : 1 ≤ x)
    {e : ℤ} (hd : (p : ℤ) ∣ e)
    (he : e = 2 * (((p ^ x : ℕ) : ℤ) - ((q ^ y : ℕ) : ℤ)) ∨
      e = -(2 * (((p ^ x : ℕ) : ℤ) - ((q ^ y : ℕ) : ℤ)))) : p = 2 := by
  have hP : (p : ℤ) ∣ ((p ^ x : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (dvd_pow_self p (by omega))
  have h2P : (p : ℤ) ∣ 2 * ((p ^ x : ℕ) : ℤ) := Dvd.dvd.mul_left hP 2
  have h2Q : (p : ℤ) ∣ ((2 * q ^ y : ℕ) : ℤ) := by
    rcases he with he | he
    · have h := dvd_sub h2P hd
      rw [he] at h
      have e' : 2 * ((p ^ x : ℕ) : ℤ) - 2 * (((p ^ x : ℕ) : ℤ) - ((q ^ y : ℕ) : ℤ)) =
          ((2 * q ^ y : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [e'] at h
    · have h := dvd_add h2P hd
      rw [he] at h
      have e' : 2 * ((p ^ x : ℕ) : ℤ) + -(2 * (((p ^ x : ℕ) : ℤ) - ((q ^ y : ℕ) : ℤ))) =
          ((2 * q ^ y : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [e'] at h
  have h2Q' : p ∣ 2 * q ^ y := Int.natCast_dvd_natCast.mp h2Q
  rcases hp.dvd_mul.mp h2Q' with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)) hpq

/-- The arithmetic at the end of Step 5: it produces `24` and `40`. -/
theorem two_fs_arith {i i' Q : ℕ} (hi : 1 ≤ i) (hi' : 1 ≤ i') (hQ : Q % 2 = 1)
    (h : Q * (2 ^ i' + 2) = 2 ^ i * (2 * 2 ^ i' + 1)) :
    2 ^ (i + i') * Q = 24 ∨ 2 ^ (i + i') * Q = 40 := by
  rcases Nat.lt_or_ge i' 2 with h1 | h2
  · obtain rfl : i' = 1 := by omega
    have h' : Q * 4 = 2 ^ i * 5 := by
      norm_num at h
      exact h
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · interval_cases i
      · omega
      · right
        have hQ5 : Q = 5 := by omega
        subst hQ5
        norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
      have e : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
      rw [e] at h'
      generalize 2 ^ k = T at h'
      omega
  · obtain ⟨k', rfl⟩ : ∃ k', i' = k' + 2 := ⟨i' - 2, by omega⟩
    have e4 : 2 ^ (k' + 2) = 4 * 2 ^ k' := by ring
    have hT : 0 < 2 ^ k' := by positivity
    rcases Nat.lt_or_ge i 2 with hi1 | hi2
    · obtain rfl : i = 1 := by omega
      rcases Nat.eq_zero_or_pos k' with rfl | hk
      · have h' : Q * 6 = 18 := by
          norm_num at h
          exact h
        left
        have hQ3 : Q = 3 := by omega
        subst hQ3
        norm_num
      · exfalso
        have hT2 : 2 ≤ 2 ^ k' := two_le_pow Nat.prime_two hk
        rw [e4] at h
        generalize 2 ^ k' = T at h hT2
        have h' : Q * (2 * T + 1) = 8 * T + 1 := by
          rw [pow_one] at h
          linarith
        have hQ3 : Q ≤ 3 := by
          by_contra hh
          have hh := not_le.mp hh
          nlinarith [Nat.mul_le_mul_right (2 * T + 1) hh]
        interval_cases Q <;> omega
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
      have e5 : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
      rw [e4, e5] at h
      generalize 2 ^ k' = T at h
      generalize 2 ^ m = W at h
      have heq : Q * (2 * T + 1) = 2 * (W * (8 * T + 1)) := by linarith
      have hodd : Q * (2 * T + 1) % 2 = 1 := by
        rw [Nat.mul_mod, hQ]
        omega
      generalize Q * (2 * T + 1) = Z at heq hodd
      generalize W * (8 * T + 1) = V at heq
      omega

theorem ffn_nat {A B C Q : ℕ} {e : ℤ} (hbig : 2 * Q ≤ A) (hlt : B < C)
    (hX : e = (A : ℤ) - (B : ℤ) ∨ e = -((A : ℤ) - (B : ℤ)))
    (h3 : e = 2 * ((C : ℤ) - (Q : ℤ)) ∨ e = -(2 * ((C : ℤ) - (Q : ℤ)))) :
    A + 2 * Q = 2 * C + B := by
  omega

/-- Two pairs `{P, Q}` and one pair `{p^i, p^i' * Q}`: then `n` is `24` or `40`. -/
theorem case_ffn {p q x y : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {e1 e2 e3 : ℤ}
    (f1 : FS (p ^ x) (q ^ y) e1) (f2 : FS (p ^ x) (q ^ y) e2) (n3 : NS p x (q ^ y) e3)
    (hrel : SumRel e1 e2 e3) (h30 : e3 ≠ 0) : p ^ x * q ^ y = 24 ∨ p ^ x * q ^ y = 40 := by
  have h3 := ffx f1 f2 hrel h30
  obtain ⟨i, i', hi, hi', rfl, hX⟩ := n3
  have hd : (p : ℤ) ∣ ((p ^ i' * q ^ y : ℕ) : ℤ) - ((p ^ i : ℕ) : ℤ) :=
    dvd_sub (Int.natCast_dvd_natCast.mpr (Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _))
      (Int.natCast_dvd_natCast.mpr (dvd_pow_self p (by omega)))
  have hpe : (p : ℤ) ∣ e3 := by
    rcases hX with hX | hX
    · rw [hX]
      exact hd
    · rw [hX]
      exact dvd_neg.mpr hd
  have hp2 : p = 2 := eq_two_of_dvd hp hq hpq (by omega) hpe h3
  subst hp2
  have hQodd : q ^ y % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (q ^ y) with h0 | h1
    · exfalso
      have h2 : 2 ∣ q ^ y := Nat.dvd_of_mod_eq_zero h0
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h2))
    · exact h1
  have hbig : 2 * q ^ y ≤ 2 ^ i' * q ^ y := Nat.mul_le_mul_right _ (two_le_pow hp hi')
  have hlt : 2 ^ i < 2 ^ (i + i') := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hnat := ffn_nat hbig hlt hX h3
  have key : q ^ y * (2 ^ i' + 2) = 2 ^ i * (2 * 2 ^ i' + 1) := by
    rw [pow_add] at hnat
    linarith
  exact two_fs_arith hi hi' hQodd key

theorem case_ffm {p q x y : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {e1 e2 e3 : ℤ}
    (f1 : FS (p ^ x) (q ^ y) e1) (f2 : FS (p ^ x) (q ^ y) e2) (m3 : NS q y (p ^ x) e3)
    (hrel : SumRel e1 e2 e3) (h30 : e3 ≠ 0) : p ^ x * q ^ y = 24 ∨ p ^ x * q ^ y = 40 := by
  rw [mul_comm]
  exact case_ffn hq hp (Ne.symm hpq) f1.symm f2.symm m3 hrel h30

/-- Two pairs `{P, Q}` and a pair with both members divisible by `p` and by `q`: impossible. -/
theorem case_ffb {p q x y a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hx : 1 ≤ x)
    (hy : 1 ≤ y) {e1 e2 : ℤ} (f1 : FS (p ^ x) (q ^ y) e1) (f2 : FS (p ^ x) (q ^ y) e2)
    (hrel : SumRel e1 e2 ((a : ℤ) - b)) (h30 : (a : ℤ) - b ≠ 0) (bp : p ∣ a ∧ p ∣ b)
    (bq : q ∣ a ∧ q ∣ b) : False := by
  have h3 := ffx f1 f2 hrel h30
  have zp : (p : ℤ) ∣ (a : ℤ) - b :=
    dvd_sub (Int.natCast_dvd_natCast.mpr bp.1) (Int.natCast_dvd_natCast.mpr bp.2)
  have zq : (q : ℤ) ∣ (a : ℤ) - b :=
    dvd_sub (Int.natCast_dvd_natCast.mpr bq.1) (Int.natCast_dvd_natCast.mpr bq.2)
  have hp2 : p = 2 := eq_two_of_dvd hp hq hpq hx zp h3
  have hq2 : q = 2 := eq_two_of_dvd (x := y) (y := x) hq hp (Ne.symm hpq) hy zq (by omega)
  exact hpq (hp2.trans hq2.symm)

/-! ### Step 6: the case `{P, Q}`, `{p^i, p^i' * Q}`, `{q^j, q^j' * P}` -/

theorem le_of_mul_eq {a t c : ℤ} (ht : 0 < t) (hc : 0 < c) (h : a * t = c) : t ≤ c := by
  have ha : 0 < a := by
    by_contra hh
    have hh := not_lt.mp hh
    have := mul_nonneg (neg_nonneg.mpr hh) ht.le
    nlinarith
  have := mul_nonneg (by linarith : (0 : ℤ) ≤ a - 1) ht.le
  nlinarith

/-- From the sign patterns to the equation `(*)` of the notes. -/
theorem star_sign {R R' S S' : ℤ} (hR : 2 ≤ R) (hR' : 2 ≤ R') (hS : 2 ≤ S) (hS' : 2 ≤ S')
    (h : SumRel (R * R' - S * S') (R' * (S * S') - R) (S' * (R * R') - S)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      R * (R' * S' + ε * R' + 1) = S * (R' * S' + ε * S' + 1) := by
  have hp1 : 2 * S' ≤ R' * S' := mul_le_mul_of_nonneg_right hR' (by linarith)
  have hp2 : R' * 2 ≤ R' * S' := mul_le_mul_of_nonneg_left hS' (by linarith)
  rcases h with h | h | h | h
  · exfalso
    have h1 : R * (R' - 1 + R' * S') = S * (S' - R' * S' + 1) := by linear_combination h
    have hl : 0 < R * (R' - 1 + R' * S') := mul_pos (by linarith) (by linarith)
    have hr : S * (S' - R' * S' + 1) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  · exact ⟨-1, Or.inr rfl, by linear_combination (-1 : ℤ) * h⟩
  · exact ⟨1, Or.inl rfl, by linear_combination h⟩
  · exfalso
    have h1 : R * (R' * S' - R' - 1) = S * (1 - S' - R' * S') := by linear_combination h
    have hl : 0 < R * (R' * S' - R' - 1) := mul_pos (by linarith) (by linarith)
    have hr : S * (1 - S' - R' * S') < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith

/-- `(*)` and coprimality give the common factor `t`. -/
theorem star_t {R R' S S' ε : ℤ} (hR : 2 ≤ R) (hR' : 2 ≤ R') (hS' : 2 ≤ S')
    (hε : ε = 1 ∨ ε = -1) (hcop : IsCoprime R S)
    (h : R * (R' * S' + ε * R' + 1) = S * (R' * S' + ε * S' + 1)) :
    ∃ t : ℤ, 0 < t ∧ R' * S' + ε * R' + 1 = S * t ∧ R' * S' + ε * S' + 1 = R * t ∧ R ≠ S := by
  have hprod : 2 * S' ≤ R' * S' := mul_le_mul_of_nonneg_right hR' (by linarith)
  have hYpos : 0 < R' * S' + ε * S' + 1 := by
    rcases hε with rfl | rfl <;> linarith
  have hdvd : R ∣ R' * S' + ε * S' + 1 := by
    have hd : R ∣ S * (R' * S' + ε * S' + 1) := Dvd.intro _ h
    exact hcop.dvd_of_dvd_mul_left hd
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_, ?_, ht, ?_⟩
  · by_contra hneg
    have hneg := not_lt.mp hneg
    have := mul_nonneg (by linarith : (0 : ℤ) ≤ R) (neg_nonneg.mpr hneg)
    nlinarith
  · apply mul_left_cancel₀ (by omega : R ≠ 0)
    rw [h, ht]
    ring
  · rintro rfl
    rcases Int.isUnit_iff.mp (isCoprime_self.mp hcop) with h1 | h1 <;> omega

/-- Subcase (d), one half. -/
theorem star_d_half {R R' S S' ε t : ℤ} (hR : 2 ≤ R) (hε : ε = 1 ∨ ε = -1) (ht : 0 < t)
    (hX : R' * S' + ε * R' + 1 = S * t) (hY : R' * S' + ε * S' + 1 = R * t)
    (hRR : 2 * R ≤ R') (hlt : R' < S') : False := by
  have hstar : (R - S) * t = ε * (S' - R') := by linear_combination hX - hY
  have htle : t ≤ S' - R' := by
    rcases hε with rfl | rfl
    · exact le_of_mul_eq ht (by linarith) (by linarith : (R - S) * t = S' - R')
    · exact le_of_mul_eq ht (by linarith) (by linarith : (S - R) * t = S' - R')
  have hYge : R' * S' - S' + 1 ≤ R * t := by
    rcases hε with rfl | rfl <;> linarith
  nlinarith [mul_le_mul_of_nonneg_left htle (by linarith : (0 : ℤ) ≤ R),
    mul_le_mul_of_nonneg_right hRR (by linarith : (0 : ℤ) ≤ S'),
    mul_nonneg (by linarith : (0 : ℤ) ≤ R - 1) (by linarith : (0 : ℤ) ≤ S'),
    mul_nonneg (by linarith : (0 : ℤ) ≤ R) (by linarith : (0 : ℤ) ≤ R')]

/-- Subcase (d): `2R ≤ R'` and `2S ≤ S'`. No solution. -/
theorem star_d {R R' S S' ε t : ℤ} (hR : 2 ≤ R) (hS : 2 ≤ S) (hε : ε = 1 ∨ ε = -1)
    (ht : 0 < t) (hX : R' * S' + ε * R' + 1 = S * t) (hY : R' * S' + ε * S' + 1 = R * t)
    (hne : R ≠ S) (hRR : 2 * R ≤ R') (hSS : 2 * S ≤ S') : False := by
  rcases lt_trichotomy R' S' with hlt | heq | hgt
  · exact star_d_half hR hε ht hX hY hRR hlt
  · subst heq
    exact hne (mul_right_cancel₀ ht.ne' (hY.symm.trans hX))
  · exact star_d_half (R := S) (R' := S') (S := R) (S' := R') hS hε ht
      (by linear_combination hY) (by linear_combination hX) hSS hgt

/-- Subcase (a): `R' ∣ R` and `S' ∣ S`. No solution. -/
theorem star_a {R R' S S' ε t : ℤ} (hR' : 2 ≤ R') (hS' : 2 ≤ S')
    (hε : ε = 1 ∨ ε = -1) (ht : 0 < t) (hX : R' * S' + ε * R' + 1 = S * t)
    (hY : R' * S' + ε * S' + 1 = R * t) (hne : R ≠ S) (hRR : R' ∣ R) (hSS : S' ∣ S)
    (h5R : (5 : ℤ) ∣ R → (5 : ℤ) ∣ R') (h5S : (5 : ℤ) ∣ S → (5 : ℤ) ∣ S') : False := by
  have d1 : R' ∣ ε * S' + 1 := by
    have h1 : R' ∣ R * t := Dvd.dvd.mul_right hRR t
    rw [← hY] at h1
    have h3 := dvd_sub h1 (dvd_mul_right R' S')
    have h4 : R' * S' + ε * S' + 1 - R' * S' = ε * S' + 1 := by ring
    rwa [h4] at h3
  have d2 : S' ∣ ε * R' + 1 := by
    have h1 : S' ∣ S * t := Dvd.dvd.mul_right hSS t
    rw [← hX] at h1
    have h3 := dvd_sub h1 (dvd_mul_left S' R')
    have h4 : R' * S' + ε * R' + 1 - R' * S' = ε * R' + 1 := by ring
    rwa [h4] at h3
  have hRS' : R' ≠ S' := by
    rintro rfl
    exact hne (mul_right_cancel₀ ht.ne' (hY.symm.trans hX))
  rcases hε with rfl | rfl
  · have l1 : R' ≤ 1 * S' + 1 := Int.le_of_dvd (by linarith) d1
    have l2 : S' ≤ 1 * R' + 1 := Int.le_of_dvd (by linarith) d2
    rcases (by omega : S' = R' + 1 ∨ R' = S' + 1) with hs | hs
    · have d3 : R' ∣ 2 := by
        have h := dvd_sub d1 (dvd_refl R')
        have e : 1 * S' + 1 - R' = 2 := by
          rw [hs]
          ring
        rwa [e] at h
      have hR2 : R' = 2 := by
        have := Int.le_of_dvd (by norm_num) d3
        omega
      have hS3 : S' = 3 := by omega
      rw [hR2, hS3] at hX hY
      have h910 : 9 * R = 10 * S := by
        apply mul_right_cancel₀ ht.ne'
        linear_combination 10 * hX - 9 * hY
      have h5 : (5 : ℤ) ∣ R := ⟨2 * (R - S), by linarith⟩
      have h5' := h5R h5
      omega
    · have d3 : S' ∣ 2 := by
        have h := dvd_sub d2 (dvd_refl S')
        have e : 1 * R' + 1 - S' = 2 := by
          rw [hs]
          ring
        rwa [e] at h
      have hS2 : S' = 2 := by
        have := Int.le_of_dvd (by norm_num) d3
        omega
      have hR3 : R' = 3 := by omega
      rw [hS2, hR3] at hX hY
      have h109 : 10 * R = 9 * S := by
        apply mul_right_cancel₀ ht.ne'
        linear_combination 9 * hX - 10 * hY
      have h5 : (5 : ℤ) ∣ S := ⟨2 * (S - R), by linarith⟩
      have h5' := h5S h5
      omega
  · have e1 : -1 * S' + 1 = -(S' - 1) := by ring
    have e2 : -1 * R' + 1 = -(R' - 1) := by ring
    rw [e1, dvd_neg] at d1
    rw [e2, dvd_neg] at d2
    have l1 : R' ≤ S' - 1 := Int.le_of_dvd (by linarith) d1
    have l2 : S' ≤ R' - 1 := Int.le_of_dvd (by linarith) d2
    linarith

/-- Subcase (b): `R' ∣ R`, `S ∣ S'`, `2S ≤ S'`. Exactly one solution. -/
theorem star_b {R R' S S' ε t : ℤ} (hR' : 2 ≤ R') (hS : 2 ≤ S) (hS' : 2 ≤ S')
    (hε : ε = 1 ∨ ε = -1) (ht : 0 < t) (hX : R' * S' + ε * R' + 1 = S * t)
    (hY : R' * S' + ε * S' + 1 = R * t) (hne : R ≠ S) (hRR : R' ∣ R) (hSd : S ∣ S')
    (hSS : 2 * S ≤ S') : R = 4 ∧ R' = 2 ∧ S = 3 ∧ S' = 9 := by
  have d1 : R' ∣ ε * S' + 1 := by
    have h1 : R' ∣ R * t := Dvd.dvd.mul_right hRR t
    rw [← hY] at h1
    have h3 := dvd_sub h1 (dvd_mul_right R' S')
    have h4 : R' * S' + ε * S' + 1 - R' * S' = ε * S' + 1 := by ring
    rwa [h4] at h3
  have d2 : S ∣ ε * R' + 1 := by
    have h1 : S ∣ S * t := dvd_mul_right S t
    rw [← hX] at h1
    have h3 := dvd_sub h1 (Dvd.dvd.mul_left hSd R')
    have h4 : R' * S' + ε * R' + 1 - R' * S' = ε * R' + 1 := by ring
    rwa [h4] at h3
  have hstar : (R - S) * t = ε * (S' - R') := by linear_combination hX - hY
  rcases hε with rfl | rfl
  · have l1 : R' ≤ 1 * S' + 1 := Int.le_of_dvd (by linarith) d1
    have l2 : S ≤ 1 * R' + 1 := Int.le_of_dvd (by linarith) d2
    rcases lt_trichotomy S' R' with hlt | heq | hgt
    · exfalso
      have h1 : (S - R) * t = 1 := by linarith
      have ht1 : t ≤ 1 := le_of_mul_eq ht one_pos h1
      have ht1' : t = 1 := by omega
      subst ht1'
      have hpos : 0 < R' * S' := mul_pos (by linarith) (by linarith)
      linarith
    · exfalso
      subst heq
      exact hne (mul_right_cancel₀ ht.ne' (hY.symm.trans hX))
    · have htle : t ≤ S' - R' :=
        le_of_mul_eq ht (by linarith) (by linarith : (R - S) * t = S' - R')
      have hSgt : R' < S := by
        by_contra hh
        have hh := not_lt.mp hh
        nlinarith [mul_le_mul_of_nonneg_left htle (by linarith : (0 : ℤ) ≤ S),
          mul_le_mul_of_nonneg_right hh (by linarith : (0 : ℤ) ≤ S'),
          mul_nonneg (by linarith : (0 : ℤ) ≤ S) (by linarith : (0 : ℤ) ≤ R')]
      have hS1 : S = R' + 1 := by omega
      obtain ⟨k, hk⟩ := hSd
      have hk2 : 2 ≤ k := by
        by_contra hh
        have hh := not_le.mp hh
        nlinarith [mul_le_mul_of_nonneg_left (by omega : k ≤ 1) (by linarith : (0 : ℤ) ≤ S)]
      have ht' : t = R' * k + 1 := by
        apply mul_left_cancel₀ (by omega : S ≠ 0)
        linear_combination -hX + R' * hk - hS1
      subst hk
      subst ht'
      subst hS1
      have key : (R - R' - 2) * (R' * k + 1) = k - R' - 1 := by
        linear_combination (-1 : ℤ) * hY
      have hk0 : k - R' - 1 = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd (m := R' * k + 1)
        · exact ⟨R - R' - 2, by rw [← key]; ring⟩
        · rw [abs_lt]
          constructor
          · nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1 : ℤ) ≤ k)
              (by linarith : (0 : ℤ) ≤ R')]
          · nlinarith [mul_le_mul_of_nonneg_right (by linarith : (1 : ℤ) ≤ R')
              (by linarith : (0 : ℤ) ≤ k)]
      rw [hk0] at key
      have hRe : R - R' - 2 = 0 := by
        rcases mul_eq_zero.mp key with h | h
        · exact h
        · exfalso
          nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ R') (by linarith : (0 : ℤ) ≤ k)]
      have d3 : R' ∣ 2 := by
        have h := dvd_sub hRR (dvd_refl R')
        have e : R - R' = 2 := by linarith
        rwa [e] at h
      have hR2 : R' = 2 := by
        have := Int.le_of_dvd (by norm_num) d3
        omega
      subst hR2
      have hk3 : k = 3 := by omega
      subst hk3
      refine ⟨by omega, rfl, by norm_num, by norm_num⟩
  · exfalso
    have e1 : -1 * S' + 1 = -(S' - 1) := by ring
    have e2 : -1 * R' + 1 = -(R' - 1) := by ring
    rw [e1, dvd_neg] at d1
    rw [e2, dvd_neg] at d2
    have l1 : R' ≤ S' - 1 := Int.le_of_dvd (by linarith) d1
    have l2 : S ≤ R' - 1 := Int.le_of_dvd (by linarith) d2
    have htle : t ≤ S' - R' :=
      le_of_mul_eq ht (by linarith) (by linarith : (S - R) * t = S' - R')
    nlinarith [mul_le_mul_of_nonneg_left htle (by linarith : (0 : ℤ) ≤ S),
      mul_le_mul_of_nonneg_right l2 (by linarith : (0 : ℤ) ≤ S'),
      mul_le_mul_of_nonneg_right hS (by linarith : (0 : ℤ) ≤ R')]

/-- All solutions of `(*)` under the conditions that prime powers satisfy. -/
theorem star {R R' S S' ε : ℤ} (hR : 2 ≤ R) (hR' : 2 ≤ R') (hS : 2 ≤ S) (hS' : 2 ≤ S')
    (hε : ε = 1 ∨ ε = -1) (hcop : IsCoprime R S)
    (hRR : R' ∣ R ∨ (R ∣ R' ∧ 2 * R ≤ R')) (hSS : S' ∣ S ∨ (S ∣ S' ∧ 2 * S ≤ S'))
    (h5R : (5 : ℤ) ∣ R → (5 : ℤ) ∣ R') (h5S : (5 : ℤ) ∣ S → (5 : ℤ) ∣ S')
    (h : R * (R' * S' + ε * R' + 1) = S * (R' * S' + ε * S' + 1)) :
    (R = 4 ∧ R' = 2 ∧ S = 3 ∧ S' = 9) ∨ (R = 3 ∧ R' = 9 ∧ S = 4 ∧ S' = 2) := by
  obtain ⟨t, ht, hX, hY, hne⟩ := star_t hR hR' hS' hε hcop h
  rcases hRR with hRR | ⟨hRd, hRR⟩ <;> rcases hSS with hSS | ⟨hSd, hSS⟩
  · exact (star_a hR' hS' hε ht hX hY hne hRR hSS h5R h5S).elim
  · exact Or.inl (star_b hR' hS hS' hε ht hX hY hne hRR hSd hSS)
  · obtain ⟨r1, r2, r3, r4⟩ := star_b (R := S) (R' := S') (S := R) (S' := R') hS' hR hR' hε ht
      (by linear_combination hY) (by linear_combination hX) hne.symm hSS hRd hRR
    exact Or.inr ⟨r3, r4, r1, r2⟩
  · exact (star_d hR hS hε ht hX hY hne hRR hSS).elim

theorem pow_dvd_or {p : ℕ} (hp : p.Prime) (i i' : ℕ) :
    ((p : ℤ) ^ i' ∣ (p : ℤ) ^ i) ∨ ((p : ℤ) ^ i ∣ (p : ℤ) ^ i' ∧ 2 * (p : ℤ) ^ i ≤ (p : ℤ) ^ i') := by
  rcases Nat.lt_or_ge i i' with h | h
  swap
  · exact Or.inl (pow_dvd_pow _ h)
  · refine Or.inr ⟨pow_dvd_pow _ h.le, ?_⟩
    have h2 : 2 * p ^ i ≤ p ^ i' :=
      calc 2 * p ^ i ≤ p * p ^ i := Nat.mul_le_mul_right _ hp.two_le
        _ = p ^ (i + 1) := by ring
        _ ≤ p ^ i' := Nat.pow_le_pow_right hp.pos (by omega)
    exact_mod_cast h2

theorem five_dvd {p i i' : ℕ} (hi' : 1 ≤ i') (h : (5 : ℤ) ∣ (p : ℤ) ^ i) :
    (5 : ℤ) ∣ (p : ℤ) ^ i' := by
  have h' : 5 ∣ p ^ i := by exact_mod_cast h
  have h5 : 5 ∣ p := Nat.Prime.dvd_of_dvd_pow (by norm_num) h'
  have h'' : 5 ∣ p ^ i' := dvd_pow h5 (by omega)
  exact_mod_cast h''

/-- One pair of each of the three shapes: then `n = 216`. -/
theorem case_fnm {p q x y : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {e1 e2 e3 : ℤ}
    (f1 : FS (p ^ x) (q ^ y) e1) (n2 : NS p x (q ^ y) e2) (m3 : NS q y (p ^ x) e3)
    (hrel : SumRel e1 e2 e3) : p ^ x * q ^ y = 216 := by
  obtain ⟨i, i', hi, hi', rfl, h2⟩ := n2
  obtain ⟨j, j', hj, hj', rfl, h3⟩ := m3
  have hrel' := hrel.of_signs f1 h2 h3
  have e1' : ((p ^ (i + i') : ℕ) : ℤ) - ((q ^ (j + j') : ℕ) : ℤ) =
      (p : ℤ) ^ i * (p : ℤ) ^ i' - (q : ℤ) ^ j * (q : ℤ) ^ j' := by
    push_cast
    ring
  have e2' : ((p ^ i' * q ^ (j + j') : ℕ) : ℤ) - ((p ^ i : ℕ) : ℤ) =
      (p : ℤ) ^ i' * ((q : ℤ) ^ j * (q : ℤ) ^ j') - (p : ℤ) ^ i := by
    push_cast
    ring
  have e3' : ((q ^ j' * p ^ (i + i') : ℕ) : ℤ) - ((q ^ j : ℕ) : ℤ) =
      (q : ℤ) ^ j' * ((p : ℤ) ^ i * (p : ℤ) ^ i') - (q : ℤ) ^ j := by
    push_cast
    ring
  rw [e1', e2', e3'] at hrel'
  have hR : (2 : ℤ) ≤ (p : ℤ) ^ i := by exact_mod_cast two_le_pow hp hi
  have hR' : (2 : ℤ) ≤ (p : ℤ) ^ i' := by exact_mod_cast two_le_pow hp hi'
  have hS : (2 : ℤ) ≤ (q : ℤ) ^ j := by exact_mod_cast two_le_pow hq hj
  have hS' : (2 : ℤ) ≤ (q : ℤ) ^ j' := by exact_mod_cast two_le_pow hq hj'
  obtain ⟨ε, hε, hstar⟩ := star_sign hR hR' hS hS' hrel'
  have hcop : IsCoprime ((p : ℤ) ^ i) ((q : ℤ) ^ j) :=
    IsCoprime.pow (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq))
  have key := star hR hR' hS hS' hε hcop (pow_dvd_or hp i i') (pow_dvd_or hq j j')
    (five_dvd hi') (five_dvd hj') hstar
  have hprod : ((p ^ (i + i') * q ^ (j + j') : ℕ) : ℤ) =
      (p : ℤ) ^ i * (p : ℤ) ^ i' * ((q : ℤ) ^ j * (q : ℤ) ^ j') := by
    push_cast
    ring
  have h216 : ((p ^ (i + i') * q ^ (j + j') : ℕ) : ℤ) = 216 := by
    rcases key with ⟨r1, r2, r3, r4⟩ | ⟨r1, r2, r3, r4⟩
    · rw [hprod, r1, r2, r3, r4]
      norm_num
    · rw [hprod, r1, r2, r3, r4]
      norm_num
  exact_mod_cast h216

/-! ### Step 7: putting the cases together -/

theorem main {p q x y : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hx : 1 ≤ x)
    (hy : 1 ≤ y) (h : DeltaPrimitive (p ^ x * q ^ y)) :
    p ^ x * q ^ y = 24 ∨ p ^ x * q ^ y = 40 := by
  obtain ⟨hD, hprim⟩ := h
  obtain ⟨a1, b1, a2, b2, a3, b3, h1, h2, h3, he, h20, h30⟩ := exists_triple hD
  have hn : 0 < p ^ x * q ^ y := Nat.mul_pos (pow_pos hp.pos x) (pow_pos hq.pos y)
  obtain ⟨⟨ha1, hb1⟩, ⟨ha2, hb2⟩, ⟨ha3, hb3⟩⟩ := no_one hn h1 h2 h3 he h20 h30
  obtain ⟨hp12, hp13, hp23⟩ := not_two_both hp hn hprim h1 h2 h3 he h20 h30
  obtain ⟨hq12, hq13, hq23⟩ := not_two_both hq hn hprim h1 h2 h3 he h20 h30
  have hrel := sumRel_of_abs he
  have h10 : (a1 : ℤ) - b1 ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at he
    have := abs_pos.mpr h20
    have := abs_nonneg ((a3 : ℤ) - b3)
    linarith
  have hne : p ^ x ≠ q ^ y := by
    intro heq
    have hd : p ∣ q ^ y := by
      rw [← heq]
      exact dvd_pow_self p (by omega)
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd))
  have h216 : p ^ x * q ^ y ≠ 216 := by
    intro heq
    exact hprim ⟨3, 24, by norm_num, by norm_num, heq.trans (by norm_num), hasDelta_24⟩
  have c1 := classify hp hq h1 ha1 hb1
  have c2 := classify hp hq h2 ha2 hb2
  have c3 := classify hp hq h3 ha3 hb3
  rcases c1 with f1 | ⟨n1, bp1⟩ | ⟨m1, bq1⟩ | ⟨bp1, bq1⟩ <;>
  rcases c2 with f2 | ⟨n2, bp2⟩ | ⟨m2, bq2⟩ | ⟨bp2, bq2⟩ <;>
  rcases c3 with f3 | ⟨n3, bp3⟩ | ⟨m3, bq3⟩ | ⟨bp3, bq3⟩ <;>
  first
    | exact (hp12 (And.intro bp1 bp2)).elim
    | exact (hp13 (And.intro bp1 bp3)).elim
    | exact (hp23 (And.intro bp2 bp3)).elim
    | exact (hq12 (And.intro bq1 bq2)).elim
    | exact (hq13 (And.intro bq1 bq3)).elim
    | exact (hq23 (And.intro bq2 bq3)).elim
    | exact (case_fff hne f1 f2 f3 hrel).elim
    | exact case_ffn hp hq hpq f1 f2 n3 hrel h30
    | exact case_ffn hp hq hpq f1 f3 n2 hrel.swap23 h20
    | exact case_ffn hp hq hpq f2 f3 n1 hrel.swap12.swap23 h10
    | exact case_ffm hp hq hpq f1 f2 m3 hrel h30
    | exact case_ffm hp hq hpq f1 f3 m2 hrel.swap23 h20
    | exact case_ffm hp hq hpq f2 f3 m1 hrel.swap12.swap23 h10
    | exact (case_ffb hp hq hpq hx hy f1 f2 hrel h30 bp3 bq3).elim
    | exact (case_ffb hp hq hpq hx hy f1 f3 hrel.swap23 h20 bp2 bq2).elim
    | exact (case_ffb hp hq hpq hx hy f2 f3 hrel.swap12.swap23 h10 bp1 bq1).elim
    | exact absurd (case_fnm hp hq hpq f1 n2 m3 hrel) h216
    | exact absurd (case_fnm hp hq hpq f1 n3 m2 hrel.swap23) h216
    | exact absurd (case_fnm hp hq hpq f2 n1 m3 hrel.swap12) h216
    | exact absurd (case_fnm hp hq hpq f2 n3 m1 hrel.swap12.swap23) h216
    | exact absurd (case_fnm hp hq hpq f3 n1 m2 hrel.swap23.swap12) h216
    | exact absurd (case_fnm hp hq hpq f3 n2 m1 hrel.swap12.swap23.swap12) h216

end DeltaTwoPrimes

theorem result : Claim := fun _ _ _ _ hp hq hpq hx hy h => DeltaTwoPrimes.main hp hq hpq hx hy h
