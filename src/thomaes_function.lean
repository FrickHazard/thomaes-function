/-
Copyright (c) 2015, 2017 Ender Doe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ender Doe, Kevin Buzzard
-/

import data.real.irrational

local notation `|` x `|` := abs x
open_locale classical

/--
  The thomae's function on reals also known as the "Popcorn" function.
-/
noncomputable def thomaes_function (r : ℝ) : ℝ :=
if h : ∃ (q : ℚ), (q : ℝ) = r then (classical.some h).denom⁻¹ else 0

theorem thomaes_at_irrational_eq_zero {x : ℝ} (h: irrational x) :
  thomaes_function x = 0 :=
dif_neg $ h

/-- The thomae function, restricted to the rationals and taking values in the rationals. -/
def thomae_rat (q : ℚ) : ℚ := q.denom⁻¹

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

--@[simp]
lemma thomae_rat_num (q : ℚ) : (thomae_rat q).num = 1 :=
  by simp [thomae_rat, rat.inv_coe_nat_num q.pos ]
--@[simp]
lemma thomae_rat_denom (q : ℚ) : (thomae_rat q).denom = q.denom :=
  by simp [thomae_rat, rat.inv_coe_nat_denom q.pos]

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
  apply rat.denom_div_eq_of_coprime,
  exact_mod_cast q.pos,
  exact int.coprime_iff_nat_coprime.mp
    (is_coprime.add_mul_left_left
      (int.coprime_iff_nat_coprime.mpr (by exact_mod_cast q.cop)) _),
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


theorem irrational_ne_rat {x: ℝ} (q : ℚ) (h: irrational x) : x ≠ q :=
λ h2, h ⟨q, h2.symm⟩

theorem δᵢ_pos {x : ℝ} (i : ℕ) (h : irrational x)
: 0 < min (|x - ⌊x * i⌋ / (i :ℝ)|)  (|x - (⌊x * i⌋ + 1) / (i :ℝ)|) :=
begin
  simp only [abs_pos, gt_iff_lt, lt_min_iff],
  split,
  { suffices : x ≠ ((⌊x * ↑i⌋ / i) : ℚ),
    exact_mod_cast sub_ne_zero.mpr this,
    exact irrational_ne_rat _ h },
  { suffices : x ≠ (((⌊x * ↑i⌋ + 1) / i) : ℚ),
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

theorem δᵢ_between {x: ℝ} {r : ℝ}  {i : ℕ}
(hx0 : irrational x) (hn0 : 0 < i)
(h : |r - x| < min (|x - ⌊x * i⌋ / (i :ℝ)|)  (|x - (⌊x * i⌋ + 1) / (i :ℝ)|)) :
(⌊x * i⌋ / i : ℝ) < r ∧ r < ((⌊x * i⌋ + 1) / i : ℝ)
:=
begin
  simp only [lt_min_iff] at h,
  rw abs_of_pos (sub_pos_of_lt (irrational.floor_mul_div_lt hx0 hn0)) at h,
  rw abs_of_neg (sub_neg_of_lt (irrational.floor_mul_add_one_div_lt x hn0)) at h,
  split,
  linarith [(abs_lt.mp h.left).left],
  linarith [(abs_lt.mp h.right).right],
end

theorem no_rat_between  (n : ℤ) (q : ℚ) (l: (n / q.denom : ℚ) < q) (r: q < ((n + 1) / q.denom : ℚ))
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
#check set.Icc_ℕ_finite

theorem thomaes_continous_at_irrational {x} (h : irrational x)
: continuous_at thomaes_function x :=
begin
  apply metric.continuous_at_iff.mpr,
  simp_rw [real.dist_eq, thomaes_at_irrational_eq_zero h, sub_zero],
  intros ε ε_pos,

  obtain ⟨r, hr⟩ := exists_nat_one_div_lt ε_pos,
  have r_add_one_pos : 0 < r + 1 := nat.succ_pos r,
  rw one_div at hr,

  let δᵢ : ℝ → ℕ → ℝ  := λ x i, min
    (|x - ⌊x * i⌋ / (i :ℝ)|)
    (|x - (⌊x * i⌋ + 1) / (i :ℝ)|),

  obtain ⟨i_min, ⟨i_pos, i_le_r⟩, i_min_indice⟩ :=
    set.exists_min_image _
    (δᵢ x)
    -- δ indices are finite and nonempty
    (set.Ioc_ℕ_finite 0 _)
    (⟨1, zero_lt_one, nat.one_le_of_lt r_add_one_pos⟩),

  refine ⟨δᵢ x i_min, δᵢ_pos i_min h, λ x₁ hδ, _⟩,

  by_cases H : ∃ q : ℚ, (q : ℝ) = x₁,
  { obtain ⟨q, rfl⟩ := H,
    norm_cast,
    rw abs_of_pos (thomae_rat_pos q),

    have r_add_one_le_q_denom : (r + 1) ≤ q.denom,
    { by_contradiction H,
      push_neg at H,
      have lt_delta_of_q := lt_of_lt_of_le hδ (i_min_indice q.denom ⟨q.pos, le_of_lt H⟩),
      obtain ⟨l, r⟩ := δᵢ_between h q.pos lt_delta_of_q,
      exact no_rat_between (⌊ x * q.denom⌋) q (by exact_mod_cast l) (by exact_mod_cast r) },

      rw thomae_rat,
      exact_mod_cast (lt_of_le_of_lt (
        (inv_le_inv
          (show 0 < ((q.denom : ℚ) : ℝ), by exact_mod_cast q.pos)
            (show 0 < (r + 1 :ℝ ), by exact_mod_cast r_add_one_pos)).mpr
              (by exact_mod_cast r_add_one_le_q_denom)) hr),
  },
  { rw thomaes_at_irrational_eq_zero H,
    simpa using ε_pos },
end

theorem thomaes_discontinous_at_rational (q : ℚ)
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

  rcases exists_irrational_btwn δ_pos with ⟨r, ⟨r_irrat, r_pos, r_lt_δ⟩⟩,

  specialize hδ (show |(r + q) - q| < δ, by simpa [abs_of_pos r_pos]),

  rw [
    thomaes_at_irrational_eq_zero (irrational.add_rat q r_irrat)
  ] at hδ,
  simp only [zero_sub, abs_neg] at hδ,
  rw abs_of_pos (show ((thomae_rat q) : ℝ) > 0, by exact_mod_cast (thomae_rat_pos q)) at hδ,
  exact (lt_self_iff_false _).mp hδ,
end
