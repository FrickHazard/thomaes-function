/-
Copyright (c) 2015, 2017 Ender Doe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ender Doe
-/

import data.real.irrational


local notation `|` x `|` := abs x
open_locale classical

lemma very_useful_thing (n: ℕ) (h: n > 0) : ((1 / n) :ℚ).denom = n :=
begin
  have : (1: ℤ).nat_abs.coprime (n :ℤ).nat_abs,
  {
    -- TODO remove this simp
    simp,
  },
  have := rat.denom_div_eq_of_coprime (by linarith [h]) this,
  norm_cast at this,
  rw rat.mk_eq_div at this,
  simp at this,
  simp,
  exact this,
end
lemma very_useful_thing_2  (n: ℕ) (h: n > 0) : ((1 / n) :ℚ).num = 1 :=
begin
  have : (1: ℤ).nat_abs.coprime (n :ℤ).nat_abs, {
   simp,
  },
  have := rat.num_div_eq_of_coprime (by linarith [h]) this,
  simp at this,
  simp,
  exact this,
end

lemma real_of_rat_eq_imp_rat_eq (q₁ q₂ : ℚ)  (h: (↑q₁ :ℝ) = ↑q₂): q₁=q₂ :=
begin
  rw ←real.of_rat_eq_cast q₁ at h,
  rw ←real.of_rat_eq_cast q₂ at h,
  by_contradiction H,
  cases ne_iff_lt_or_gt.mp H with A B,
  linarith [real.of_rat_lt.mpr A],
  linarith [real.of_rat_lt.mpr B],
end

lemma mk_pnat_num_one_denom_eq  (n : ℕ+): (rat.mk_pnat 1 n).denom = n :=
begin
 rw rat.mk_pnat_denom,
 rw int.nat_abs_one,
 simp,
end

lemma mk_pnat_num_one_num_eq_one  (n : ℕ+): (rat.mk_pnat 1 n).num = 1 :=
begin
 rw rat.mk_pnat_num,
 rw int.nat_abs_one,
 simp,
end

theorem not_irrational_is_rat (x: ℝ) : ¬ (irrational x) →  x ∈ set.range (coe : ℚ → ℝ) :=
begin
  intro h,
  unfold irrational at h,
  push_neg at h,
  assumption,
end

noncomputable def one_over_denom_rat_of_real (r : ℝ) (h : ¬irrational r) : ℚ :=
rat.mk_pnat 1 ⟨(classical.some  (not_irrational_is_rat r h)).denom, (classical.some (not_irrational_is_rat r h)).pos⟩

lemma one_over_rat_of_real_denom_eq (q: ℚ) : (one_over_denom_rat_of_real q (rat.not_irrational q)).denom = q.denom ∧ (one_over_denom_rat_of_real q (rat.not_irrational q)).num = 1:=
begin
  unfold one_over_denom_rat_of_real,
  generalize_proofs H,
  constructor,
  {
    -- TODO why doesn't norm_cast work here?
    simp_rw (real_of_rat_eq_imp_rat_eq _ _ (classical.some_spec H)),
    exact mk_pnat_num_one_denom_eq _,
  },
  {
    exact mk_pnat_num_one_num_eq_one _,
  }
end

noncomputable def thomaes_function (r : ℝ) : ℝ :=
if h : irrational r
  then 0
  else
    if r = 0
      then 1
      else one_over_denom_rat_of_real r h

theorem thomaes_at_irrational_eq_zero {x : ℝ} (h: irrational x) : thomaes_function x = 0 :=
begin
  unfold thomaes_function,
  simp [h],
end

theorem thomaes_pos_input_num_eq_one (q : ℚ) : ∃ (q₂ : ℚ), ↑q₂ = thomaes_function q ∧ q₂.num = 1 ∧ q₂.denom = q.denom :=
begin
  unfold thomaes_function,
  use rat.mk_pnat 1 ⟨q.2, q.3⟩,
  simp [rat.not_irrational q],
  generalize_proofs D a,
  by_cases q = 0,
  constructor, {
    simp_rw [h],
    norm_cast,
    -- TODO simp ite
    simp,
    apply rat.eq_iff_mul_eq_mul.mpr,
    rw rat.mk_pnat_num,
    rw rat.mk_pnat_denom,
    -- TODO simp gcd
    simp,
  },
  {
    exact ⟨
      mk_pnat_num_one_num_eq_one ⟨q.denom, D⟩,
      mk_pnat_num_one_denom_eq ⟨ q.denom, D⟩
    ⟩
  },
  simp [h],
  constructor,
  {
    apply rat.eq_iff_mul_eq_mul.mpr,
    simp_rw [mk_pnat_num_one_denom_eq, mk_pnat_num_one_num_eq_one, one_over_rat_of_real_denom_eq q],
    simp,
  },
  {
     exact ⟨
      mk_pnat_num_one_num_eq_one ⟨q.denom, D⟩,
      mk_pnat_num_one_denom_eq ⟨ q.denom, D⟩
    ⟩
  },
end

lemma int_not_irrational  (z : ℤ): ¬irrational z := begin
  rw  ←rat.cast_coe_int,
  exact rat.not_irrational ↑z,
end

theorem thomas_int_eq_one (z : ℤ): thomaes_function z = 1 := begin
  unfold thomaes_function,
  -- TODO simp ite with z not irrational
  simp [int_not_irrational],
  generalize_proofs A B,
  intro h,
  rw ←rat.cast_one,
  apply congr_arg,
  have : (↑z :ℝ)  = (↑(↑z :ℚ): ℝ),
  norm_cast,
  simp_rw this,
  apply rat.eq_iff_mul_eq_mul.mpr,
  simp_rw [
    (one_over_rat_of_real_denom_eq z)
  ],
  -- TODO simp with integer denom and basic algebra
  simp,
end

theorem thomaes_rat_ne_zero_eq_one_over (q : ℚ) (h: q ≠ 0) : thomaes_function q = (rat.mk_pnat 1 ⟨q.denom, q.3⟩) :=
begin
  unfold thomaes_function,
  simp [rat.not_irrational, h],
  generalize_proofs A B,
  apply rat.eq_iff_mul_eq_mul.mpr,
  simp_rw [one_over_rat_of_real_denom_eq q, mk_pnat_num_one_num_eq_one ,mk_pnat_num_one_denom_eq],
  simp,
end

theorem irrational.int_add (z : ℤ) {x : ℝ} (h : irrational x) :
irrational (x + ↑z) :=
begin
 rw ←rat.cast_coe_int,
 rw add_comm,
 exact irrational.rat_add z h,
end

theorem rat_add_nat_denom_eq (z: ℤ) (q : ℚ) : (q + z).denom = q.denom :=
begin
  have := q.4,
  rw ←int.nat_abs_of_nat q.denom at this,
  rw ←int.coprime_iff_nat_coprime at this,
  have := is_coprime.add_mul_left_left this z,

  rw int.coprime_iff_nat_coprime at this,
  rw int.nat_abs_of_nat q.denom at this,

  have := @rat.num_denom' (q.num + ↑(q.denom) * z) q.denom q.3 this,
  simp_rw int.mul_comm ↑(q.denom) z at this,

  rw rat.coe_int_eq_mk z,
-- TODO surely this exists
  have AA : q = rat.mk q.num q.denom , {
    apply rat.eq_iff_mul_eq_mul.mpr,
    simp,
  },
  rw AA,
  rw rat.add_def,
  simp,
  simp_rw ←this,
  norm_cast,
  linarith [q.3],
  linarith,
end

theorem thomaes_is_perodic (n : ℤ) (x  : ℝ) : thomaes_function x = thomaes_function (x + n) :=
begin
  by_cases (irrational x), {
    rw thomaes_at_irrational_eq_zero (irrational.int_add n h),
    rw thomaes_at_irrational_eq_zero h,
  }, {
    unfold irrational at h,
    push_neg at h,
    cases h with q q_eq_x,
    subst q_eq_x,
    by_cases q = 0,
    subst h,
    simp,
    rw [←int.cast_zero, thomas_int_eq_one 0, thomas_int_eq_one n],
    rw thomaes_rat_ne_zero_eq_one_over,
    rotate,
    assumption,
    cases thomaes_pos_input_num_eq_one (q + n) with q₁ hq₁,
    norm_cast,
    rw ←hq₁.1,
    apply congr_arg,
    apply rat.eq_iff_mul_eq_mul.mpr,
    rw hq₁.2.2,
    rw hq₁.2.1,
    rw mk_pnat_num_one_denom_eq,
    rw mk_pnat_num_one_num_eq_one,
    simp,
    exact rat_add_nat_denom_eq n q,
  }
end

lemma irrational_btwn_int (x : ℝ) (h : irrational x) : ↑⌊x⌋ < x ∧ x < ↑⌊x⌋ + 1 :=
begin
  have := (irrational_iff_ne_rational x).mp h (floor x) 1,
  simp at this,
  constructor,
  cases ne.lt_or_lt this,
  linarith [floor_le x],
  assumption,
  cases ne.lt_or_lt this,
  linarith,
  linarith [lt_floor_add_one x],
end

noncomputable def k_of_i (x : ℝ) (h: irrational x) : ℕ → ℤ := λ i, ⌊x * i⌋

lemma asdfasdf (z : ℤ) (h: z ≠ 0): rat.mk z z = 1 := begin
  rw rat.mk_eq_div z z,
  rw ←rat.coe_int_div_self z,
  rw int.div_self,
  norm_cast,
  assumption,
end
lemma here1124 (a: ℝ) (b: ℤ) (h: b ≠ 0): (a  * b) / b = a :=
begin
  rw mul_div_right_comm,
  rw mul_comm_div',
  norm_cast,
  rw asdfasdf b h,
  simp,
end

theorem k_of_i_fact (x : ℝ) (h: irrational x) :
∀ (i : ℕ), 0 < i → ((↑ (k_of_i x h i) / (i : ℝ) < x) ∧ (x <  (↑(k_of_i x h i) + 1) / (i :ℝ)))
:=
begin
   intros i i_pos,
   unfold k_of_i,
   have : ↑i ≠ (0 : ℚ), {
     norm_cast,
     linarith [i_pos],
   },
   have := irrational.mul_rat h this,
   have btwn_h:= irrational_btwn_int _ this,
   clear this,

   have fact: (x * (i : ℤ)) / (i :ℤ) = x, {
    apply here1124,
    have : ↑i ≠ (0 : ℤ), {
     norm_cast,
     linarith [i_pos],
    },
    assumption,
  },

   simp at fact,

   norm_cast at btwn_h,
   have i_pos_real: (0 : ℝ ) < i,
   { norm_cast, assumption },
   constructor,

   have := div_lt_div_of_lt i_pos_real btwn_h.1,
   rw fact at this,
   assumption,
   clear this,
   have := div_lt_div_of_lt i_pos_real btwn_h.2,
   rw fact at this,
   simp at this,
   assumption,
end

noncomputable def delta_f (x : ℝ) (h : irrational x) : ℕ → ℝ :=
(λ (i :ℕ), min (|x - ((k_of_i x h i) / (i :ℝ))|) (|x - (((k_of_i x h i) + 1) / (i :ℝ))|))

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


theorem irrational_ne_rat (x: ℝ) (q : ℚ) (h: irrational x) : x ≠ q :=
begin
  unfold irrational at h,
  intro x_eq_q,
  apply h,
  use q,
  exact eq.symm x_eq_q,
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
    unfold delta_f,
    unfold k_of_i,
    apply lt_min, {
      suffices H: ↑⌊x * ↑n⌋ / ↑n ≠ x,
      norm_num,
      intro h₁,
      apply H,
      linarith,
      symmetry,
      norm_cast,
      apply irrational_ne_rat,
      exact h,
    },
    {
      suffices H: (↑⌊x * ↑n⌋ + 1) / ↑n ≠ x,
      norm_num,
      intro h₁,
      apply H,
      linarith,
      symmetry,
      norm_cast,
      apply irrational_ne_rat,
      exact h,
    }
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
