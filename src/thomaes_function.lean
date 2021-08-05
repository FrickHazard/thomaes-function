/-
Copyright (c) 2015, 2017 Ender Doe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ender Doe
-/

import data.real.irrational


local notation `|` x `|` := abs x
open_locale classical

theorem not_irrational_is_rat (x: ℝ) : ¬ (irrational x) →  x ∈ set.range (coe : ℚ → ℝ) :=
not_not.1

noncomputable def thomaes_function (r : ℝ) : ℝ :=
if h : ∃ (q : ℚ), (q : ℝ) = r then (1 : ℝ) / (classical.some h).denom else 0

theorem thomaes_at_irrational_eq_zero {x : ℝ} (h: irrational x) :
  thomaes_function x = 0 :=
dif_neg $ h

/-- The thomae function, restricted to the rationals and taking values in the rationals. -/
def thomae_rat (q : ℚ) : ℚ := 1 / q.denom

--@[norm_cast]
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

@[norm_cast] lemma coe_rhomae_rat' (q : ℚ) : (thomae_rat q : ℝ) = thomaes_function q :=
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
  { simp }
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

lemma thomae_rat_num (q : ℚ) : (thomae_rat q).num = 1 :=
  by simp [thomae_rat, num_inv_nat q.pos ]

lemma thomae_rat_denom (q : ℚ) : (thomae_rat q).denom = q.denom :=
  by simp [thomae_rat, denom_inv_nat q.pos]

lemma int_not_irrational  (z : ℤ): ¬irrational z :=
  by exact_mod_cast rat.not_irrational (z :ℚ)

theorem thomae_rat_int_eq_one (z : ℤ) : thomae_rat z = 1 :=
  by simp [thomae_rat]

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

noncomputable def delta_f (x : ℝ) (h : irrational x) : ℕ → ℝ :=
λ (i :ℕ), min (|x - ⌊x * i⌋ / (i :ℝ)|)
  (|x - (⌊x * i⌋ + 1) / (i :ℝ)|)

theorem delta_f_indices_nonempty (n : ℕ) (h: n > 0) : { i : ℕ | 0 < i ∧ i ≤ n}.nonempty :=
begin
  use 1,
  constructor,
  exact zero_lt_one,
  linarith,
end

theorem delta_f_indices_finite (n : ℕ) (h: n > 0) : { i : ℕ | 0 < i ∧ i ≤ n}.finite :=
begin
  have succ_fin := set.finite.image nat.succ (set.finite_lt_nat n),
  suffices : (nat.succ '' {i : ℕ | i < n}) = { i : ℕ | 0 < i ∧ i ≤ n},
  rw this at succ_fin,
  assumption,
  ext x,
  split,
  {
    intro h,
    cases h with h1 h2,
    rw ←h2.2,
    constructor,
    exact nat.zero_lt_succ h1,
    exact  nat.succ_le_of_lt  h2.1,
  },
  {
    intro h,
    use x.pred,
    constructor, {
      rw set.mem_set_of_eq,
      linarith [h.2,  @nat.pred_lt x (by linarith [h.1])],
    },
    exact nat.succ_pred_eq_of_pos h.1,
  }
end

theorem irrational_ne_rat {x: ℝ} (q : ℚ) (h: irrational x) : x ≠ q :=
begin
  unfold irrational at h,
  intro x_eq_q,
  apply h,
  use q,
  exact eq.symm x_eq_q,
end

theorem delta_f_pos {x : ℝ} (h : irrational x) {n : ℕ} (n_pos : n > 0)
: delta_f x h n > 0 :=
begin
  unfold delta_f,
  norm_num,
  constructor,
  suffices : x ≠ ((⌊x * ↑n⌋ / n) : ℚ),
    exact_mod_cast sub_ne_zero.mpr this,
    exact irrational_ne_rat _ h,
  suffices : x ≠ (((⌊x * ↑n⌋ + 1) / n) : ℚ),
    exact_mod_cast sub_ne_zero.mpr this,
    exact irrational_ne_rat _ h,
end



theorem no_rat_between  (A : ℤ) (q : ℚ) (l: (A / q.denom : ℚ) < q) (r: q < ((A +1) / q.denom : ℚ))
: false  :=
begin
  nth_rewrite 1 ←rat.num_div_denom q at l,
  nth_rewrite 0 ←rat.num_div_denom q at r,
  have l' := (mul_lt_mul_right _).mp ((div_lt_div_iff _ _).mp l),
  have r' := (mul_lt_mul_right _).mp ((div_lt_div_iff _ _).mp r),
  repeat { norm_cast, exact q.pos },
  norm_cast at l',
  norm_cast at r',
  linarith,
end

theorem thomaes_fact : ∀ x, irrational x → continuous_at thomaes_function x :=
begin
  intros x h,
  apply metric.continuous_at_iff.mpr,
  simp_rw [real.dist_eq , thomaes_at_irrational_eq_zero h, sub_zero],
  intros ε ε_pos,
  -- There exists a rational number 1/(r+1) between epsilon and 0
  -- by the archmedian property.
  cases (exists_nat_one_div_lt ε_pos) with r hr,

  have r_add_one_pos : 0 < r + 1 := nat.succ_pos r,

  rcases set.exists_min_image _
    (delta_f x h)
    (delta_f_indices_finite _ r_add_one_pos)
    (delta_f_indices_nonempty _ r_add_one_pos)
    with ⟨n, ⟨hn₁, hn₂⟩ ⟩,

  use delta_f x h n,

  constructor,
  {
    exact delta_f_pos h hn₁.1,
  },
  {
    intros x₁ hx₁,

    by_cases H : irrational x₁,
    {
      rw thomaes_at_irrational_eq_zero H,
      norm_num,
      assumption,
    },
    {
      unfold irrational at H,
      push_neg at H,
      set q₁  := classical.some H with q₁_def,
      have hq₁ := classical.some_spec H,
      rw ←q₁_def at hq₁,
      rw ←hq₁,
      rcases thomaes_pos_input_num_eq_one q₁ with ⟨a₁, a₂, a₃⟩,
      rw ←a₂,
      unfold irrational at h,

      have a₁_pos : (↑a₁ :ℝ) > 0, {
        norm_cast,
        apply rat.num_pos_iff_pos.mp,
        linarith,
      },

      rw abs_of_pos a₁_pos,

      have : (r + 1) ≤ a₁.denom,
      {
        rw a₃.2,
        rw ←hq₁ at hx₁,
        by_contradiction H,
        push_neg at H,

        have k_of_i_fact := k_of_i_fact x h q₁.denom q₁.pos,

        have lt_delta_of_q := lt_of_lt_of_le hx₁ (hn₂ q₁.denom ⟨q₁.pos, le_of_lt H⟩),
        unfold delta_f at lt_delta_of_q,
        norm_num at lt_delta_of_q,
        rcases lt_delta_of_q with ⟨ldelta, rdelta⟩,

        have AA : x - ↑(k_of_i x h q₁.denom) / ↑(q₁.denom) > 0, {
          linarith [k_of_i_fact.1],
        },
        have BB : x - (↑(k_of_i x h q₁.denom) + 1) / ↑(q₁.denom) < 0, {
          linarith [k_of_i_fact.2],
        },

        nth_rewrite 0 abs_of_pos AA at ldelta,
        nth_rewrite 0 abs_of_neg BB at rdelta,
        have l := abs_lt.mp ldelta,
        have r := abs_lt.mp rdelta,
        simp at r,
        simp at l,
        apply no_rat_between (k_of_i x h q₁.denom) q₁,
        {
          norm_cast,
          have := l.1,
          norm_cast at this,
          exact this,
        },
        {
          norm_cast,
          have := r.2,
          norm_cast at this,
          exact this,
        },
      },
      have : a₁ ≤ 1 / (r + 1),
      {
        apply rat.le_def'.mpr,
        rw a₃.1,
        norm_cast,

        rw very_useful_thing _ r_add_one_pos,
        rw very_useful_thing_2 _ r_add_one_pos,
        simp,
        linarith,
      },
      have : (a₁ :ℝ) ≤ (((1 / (r + 1)) :ℚ) :ℝ) , {
        norm_cast,
        exact this,
      },
      calc (a₁ :ℝ) ≤ (((1 / (r + 1)) :ℚ) :ℝ) : this
      ... < ε : by { push_cast, exact hr },
    },
  },
end
