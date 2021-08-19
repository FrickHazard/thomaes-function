/-
Copyright (c) 2015, 2017 Ender Doe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ender Doe
-/

import data.real.irrational

local notation `|` x `|` := abs x
open_locale classical

/--
  The thomae's function on reals also known as the "Popcorn" function.
-/
noncomputable def thomaes_function (r : ℝ) : ℝ :=
if h : ∃ (q : ℚ), (q : ℝ) = r then (1 : ℝ) / (classical.some h).denom else 0

theorem thomaes_at_irrational_eq_zero {x : ℝ} (h: irrational x) :
  thomaes_function x = 0 :=
dif_neg $ h

/-- The thomae function, restricted to the rationals and taking values in the rationals. -/
def thomae_rat (q : ℚ) : ℚ := 1 / q.denom

@[norm_cast]
lemma coe_thomae_rat (q : ℚ) : thomaes_function q = thomae_rat q :=
begin
  unfold thomaes_function,
  rw dif_pos (⟨q, rfl⟩ : ∃ (q_1 : ℚ), (q_1 : ℝ) = ↑q),
  { generalize_proofs h,
    unfold thomae_rat,
    norm_num,
    congr',
    exact_mod_cast classical.some_spec h },
end

@[norm_cast] lemma coe_thomae_rat' (q : ℚ) : (thomae_rat q : ℝ) = thomaes_function q :=
(coe_thomae_rat q).symm

open rat

-- this should be in data.rat.basic
lemma num_inv_nat {n : ℕ} (hn : 0 < n) : (n : ℚ)⁻¹.num = 1 :=
begin
  rw [rat.inv_def', rat.coe_nat_num, rat.coe_nat_denom],
  suffices : (((1 : ℤ) : ℚ) / (n : ℤ)).num = 1,
    exact_mod_cast this,
  apply num_div_eq_of_coprime,
  { assumption_mod_cast },
  { simp only [nat.coprime_one_left_iff, int.nat_abs_one]}
end

-- so should this
lemma denom_inv_nat {n : ℕ} (hn : 0 < n) : (n : ℚ)⁻¹.denom = n :=
begin
  rw [rat.inv_def', rat.coe_nat_num, rat.coe_nat_denom],
  suffices : ((((1 : ℤ) : ℚ) / (n : ℤ)).denom : ℤ) = n,
    exact_mod_cast this,
  apply denom_div_eq_of_coprime,
  { assumption_mod_cast },
  { simp only [nat.coprime_one_left_iff, int.nat_abs_one]},
end
--@[simp]
lemma thomae_rat_num (q : ℚ) : (thomae_rat q).num = 1 :=
  by simp [thomae_rat, num_inv_nat q.pos ]
--@[simp]
lemma thomae_rat_denom (q : ℚ) : (thomae_rat q).denom = q.denom :=
  by simp [thomae_rat, denom_inv_nat q.pos]

lemma int_not_irrational  (z : ℤ): ¬irrational z :=
  by exact_mod_cast rat.not_irrational (z :ℚ)
--@[simp]
theorem thomae_rat_int_eq_one (z : ℤ) : thomae_rat z = 1 :=
  by simp [thomae_rat]

theorem thomae_rat_pos (q : ℚ) : 0 < (thomae_rat q) := begin
  apply rat.num_pos_iff_pos.mp,
  rw thomae_rat_num,
  exact zero_lt_one,
end
--@[simp]
theorem thomas_int_eq_one (z : ℤ): thomaes_function z = 1 := begin
  suffices : thomaes_function (z : ℚ) = 1,
    convert this using 2, norm_cast,
  exact_mod_cast thomae_rat_int_eq_one z,
end

theorem irrational.add_int (z : ℤ) {x : ℝ} (h : irrational x) :
irrational (x + ↑z) :=
  by exact_mod_cast irrational.add_rat z h

-- add to rat library?
theorem rat.add_int_denom (z: ℤ) (q : ℚ) : (q + z).denom = q.denom :=
begin
  rw rat.add_num_denom,
  simp,
  rw rat.mk_eq_div,
  -- I copied this trick from above
  suffices :(((((q.num + ↑(q.denom) * z) : ℤ) : ℚ) / ((q.denom) : ℤ)).denom : ℤ) = q.denom,
    exact_mod_cast this,
  apply denom_div_eq_of_coprime,
  exact_mod_cast q.pos,
  -- Question here apply a list of things?
  apply int.coprime_iff_nat_coprime.mp,
  apply is_coprime.add_mul_left_left,
  apply int.coprime_iff_nat_coprime.mpr,
  exact_mod_cast q.cop,
end

--@[simp]
theorem thomaes_is_perodic (n : ℤ) (x  : ℝ) : thomaes_function (x + n) = thomaes_function x  :=
begin
  by_cases (irrational x),
  rw [
    thomaes_at_irrational_eq_zero (irrational.add_int n h),
    thomaes_at_irrational_eq_zero h
  ],
  unfold irrational at h,
  push_neg at h,
  cases h with q q_eq_x,
  subst q_eq_x,
  norm_cast,
  apply rat.eq_iff_mul_eq_mul.mpr,
  simp [thomae_rat_num, thomae_rat_denom],
  symmetry,
  exact rat.add_int_denom _ _,
end

/--
 Intermediate def of the delta used in the proof of irrational continouty
-/
noncomputable def delta_f (x : ℝ) : ℕ → ℝ :=
λ (i :ℕ), min (|x - ⌊x * i⌋ / (i :ℝ)|)
  (|x - (⌊x * i⌋ + 1) / (i :ℝ)|)

theorem delta_f_indices_nonempty {n : ℕ} (h: 0 < n) : { i : ℕ | 0 < i ∧ i ≤ n}.nonempty :=
⟨1, zero_lt_one, by linarith⟩

-- theorem

-- should be in mathlib
lemma set.finite_Ico_nat (a b : ℕ) : (set.Ico a b).finite :=
begin
  cases le_or_lt b a with h h,
  { rw ← set.Ico_eq_empty_iff at h,
    rw h,
    exact set.finite_empty },
  { convert set.finite.image (λ x, x + a) (set.finite_lt_nat (b -a)),
    ext c,
    split,
    { rintro ⟨h1, h2⟩,
      rw le_iff_exists_add at h1,
      rcases h1 with ⟨d, rfl⟩,
      exact ⟨d, nat.lt_sub_left_of_add_lt h2, add_comm _ _⟩ },
    { rintro ⟨d, hd1, rfl⟩,
      dsimp at *,
      refine ⟨nat.le_add_left a d, nat.add_lt_of_lt_sub_right hd1⟩ } }
end

-- as should this and the other ones Icc, Ioo (other two proofs are also 3 lines long)
lemma set.finite_Ioc_nat (a b : ℕ) : (set.Ioc a b).finite :=
begin
  convert set.finite_Ico_nat (a + 1) (b + 1),
  ext c,
  exact and_congr nat.lt_iff_add_one_le nat.lt_succ_iff.symm
end

theorem delta_f_indices_finite (n : ℕ) : { i : ℕ | 0 < i ∧ i ≤ n}.finite :=
set.finite_Ioc_nat 0 n

theorem irrational_ne_rat {x: ℝ} (q : ℚ) (h: irrational x) : x ≠ q :=
λ h2, h ⟨q, h2.symm⟩

theorem delta_f_pos {x : ℝ} (n : ℕ) (h : irrational x)
: 0 < delta_f x n :=
begin
  unfold delta_f,
  simp only [abs_pos, gt_iff_lt, lt_min_iff],
  split,
  { suffices : x ≠ ((⌊x * ↑n⌋ / n) : ℚ),
    exact_mod_cast sub_ne_zero.mpr this,
    exact irrational_ne_rat _ h },
  { suffices : x ≠ (((⌊x * ↑n⌋ + 1) / n) : ℚ),
    exact_mod_cast sub_ne_zero.mpr this,
    exact irrational_ne_rat _ h },
end

lemma floor_lt_irrational (x : ℝ) (h : irrational x) : ↑⌊x⌋ < x :=
begin
  cases lt_or_eq_of_le (floor_le x) with h2 h2,
  { exact h2 },
  exact false.elim (irrational_ne_rat (⌊ x ⌋) h (by exact_mod_cast h2.symm)),
end

lemma irrational.floor_mul_div_lt
{x : ℝ} (h: irrational x) {i: ℕ} (hi : 0 < i) :
((⌊x * i⌋ / i) : ℝ) < x :=
begin
  rw div_lt_iff (show 0 < (i : ℝ), by assumption_mod_cast),
  apply floor_lt_irrational,
  convert irrational.mul_rat h (show (i : ℚ) ≠ 0, by exact_mod_cast (ne_of_lt hi).symm) using 2,
  norm_cast,
end

lemma irrational.floor_mul_add_one_div_lt
{i: ℕ} (x : ℝ) (hi : 0 < i) :
x < ((⌊x * i⌋ + 1) : ℝ) / (i : ℝ)
:=
begin
  rw lt_div_iff (show 0 < (i : ℝ), by assumption_mod_cast),
  exact lt_floor_add_one _,
end

theorem delta_f_between {x: ℝ} {r : ℝ}  {n : ℕ}
(hx0 : irrational x) (hn0 : 0 < n) (h : |r - x| < delta_f x n) :
(⌊x * n⌋ / n : ℝ) < r ∧ r < ((⌊x * n⌋ + 1) / n : ℝ)
:=
begin
  unfold delta_f at h,
  simp only [lt_min_iff] at h,
  rw abs_of_pos (sub_pos_of_lt (irrational.floor_mul_div_lt hx0 hn0)) at h,
  rw abs_of_neg (sub_neg_of_lt (irrational.floor_mul_add_one_div_lt x hn0)) at h,
  split,
  linarith [(abs_lt.mp h.left).left],
  linarith [(abs_lt.mp h.right).right],
end

theorem no_rat_between  (A : ℤ) (q : ℚ) (l: (A / q.denom : ℚ) < q) (r: q < ((A +1) / q.denom : ℚ))
: false :=
begin
  nth_rewrite 1 ←rat.num_div_denom q at l,
  nth_rewrite 0 ←rat.num_div_denom q at r,
  have h : (0 : ℚ) < q.denom := by exact_mod_cast q.pos,
  have l' := (mul_lt_mul_right h).mp ((div_lt_div_iff h h).mp l),
  norm_cast at l',
  have r' := (mul_lt_mul_right h).mp ((div_lt_div_iff h h).mp r),
  norm_cast at r',
  linarith,
end

theorem thomaes_continous_at_irrational {x} (h : irrational x)
: continuous_at thomaes_function x :=
begin
  apply metric.continuous_at_iff.mpr,
  simp_rw [real.dist_eq, thomaes_at_irrational_eq_zero h, sub_zero],
  intros ε ε_pos,

  cases (exists_nat_one_div_lt ε_pos) with r hr,

  have r_add_one_pos : 0 < r + 1 := nat.succ_pos r,

  rcases set.exists_min_image _
    (delta_f x)
    (delta_f_indices_finite _)
    (delta_f_indices_nonempty r_add_one_pos)
    with ⟨n, ⟨n_pos, n_le_r_plus_1⟩, n_min_indice⟩,

  refine ⟨delta_f x n, delta_f_pos n h, λ x₁ hx₁, _⟩,

  by_cases H : ∃ q : ℚ, (q : ℝ) = x₁,
  { rcases H with ⟨q, rfl⟩,
    norm_cast,

    rw abs_of_pos (thomae_rat_pos q),

    have r_add_one_le_q_denom : (r + 1) ≤ q.denom,
    { by_contradiction H,
      push_neg at H,
      have lt_delta_of_q := lt_of_lt_of_le hx₁ (n_min_indice q.denom ⟨q.pos, le_of_lt H⟩),
      rcases delta_f_between h q.pos lt_delta_of_q with ⟨l, r⟩,
      apply no_rat_between (⌊ x * q.denom⌋) q,
      { exact_mod_cast l },
      { exact_mod_cast r } },

   suffices : ((thomae_rat q) :ℝ) ≤ (((1 / (r + 1)) :ℚ) :ℝ),
      calc ((thomae_rat q) :ℝ) ≤ (((1 / (r + 1)) :ℚ) :ℝ) : this
      ... < ε : by { push_cast, exact hr },
    norm_cast,
    apply rat.le_def'.mpr,
    simp only [thomae_rat_num, thomae_rat_denom, one_div, one_mul, nat.cast_add, nat.cast_one],
    norm_cast,
    rw [num_inv_nat r_add_one_pos, denom_inv_nat r_add_one_pos, one_mul],
    exact_mod_cast r_add_one_le_q_denom,
  },
  { rw thomaes_at_irrational_eq_zero H,
    simpa using ε_pos },
end

-- TODO math Lib
lemma one_lt_sqrt_two : 1 < real.sqrt 2 :=
begin
  refine (real.lt_sqrt zero_le_one (zero_le_bit0.mpr zero_le_one)).mpr _,
  rw [one_pow],
  exact one_lt_two,
end

lemma exists_irrational_btwn_rats {x y :ℚ} (h : (x :ℝ) < y) :
∃ (r : ℝ), irrational r ∧ (x : ℝ) < r ∧ r < y:=
begin
  use x + ((y - x) : ℚ) * (real.sqrt 2)⁻¹,
  split, {
    refine irrational.rat_add _
      (irrational.rat_mul
        (irrational_inv_iff.mpr irrational_sqrt_two) _),
    exact_mod_cast (ne_of_gt (sub_pos_of_lt h)) },
  split, {
    suffices : 0 < ↑(y - x) * (real.sqrt 2)⁻¹,
      linarith,
    refine (zero_lt_mul_right _).mpr _,
    apply inv_pos.mpr,
    norm_num,
    exact_mod_cast (sub_pos_of_lt h)},
  { apply (sub_lt_sub_iff_right (x :ℝ)).mp,
    rw [add_sub_cancel', ←cast_sub],
    refine (mul_lt_iff_lt_one_right _).mpr
      (inv_lt_one one_lt_sqrt_two),
    exact_mod_cast  (sub_pos_of_lt h) }
end
-- TODO Mathlib
theorem exists_irrational_btwn {x y :ℝ} (h : x < y) :
∃ (r : ℝ), irrational r ∧ x < r ∧ r < y:=
begin
  rcases exists_rat_btwn h with ⟨q₁, ⟨x_lt_q₁,  q₁_lt_y⟩⟩,
  rcases exists_rat_btwn q₁_lt_y with ⟨q₂, ⟨q₁_lt_q₂, q₂_lt_y⟩⟩,
  rcases exists_irrational_btwn_rats q₁_lt_q₂ with ⟨r, ⟨irrational_r, q₁_lt_r, r_lt_q₂⟩⟩,
  use r,
  refine ⟨irrational_r, lt_trans x_lt_q₁ q₁_lt_r, lt_trans r_lt_q₂ q₂_lt_y⟩,
end

theorem thomaes_discontinous_at_rational (q :ℚ)
: ¬continuous_at thomaes_function q :=
begin
  intro h,
  simp only [metric.continuous_at_iff] at h,
  norm_cast at h,
  specialize h
    (thomae_rat q)
    (by exact_mod_cast (thomae_rat_pos q)),
  rcases h with ⟨δ, δ_pos, hδ⟩,
  simp_rw real.dist_eq at hδ,

  rcases exists_irrational_btwn δ_pos with ⟨r, ⟨r_irrat, r_pos, r_lt_δ⟩⟩ ,

  specialize hδ (show |(r + q) - q| < δ, by simpa [abs_of_pos r_pos]),

  rw [
    thomaes_at_irrational_eq_zero (irrational.add_rat q r_irrat)
  ] at hδ,
  simp only [zero_sub, abs_neg] at hδ,
  rw abs_of_pos _ at hδ,
  linarith,
  exact_mod_cast (thomae_rat_pos q),
end
