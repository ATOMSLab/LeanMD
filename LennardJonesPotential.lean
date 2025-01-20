/-
Authors: Ejike Ugwuanyi
-/

import Mathlib

lemma differentiable_at_zpow_neg12 (r : ℝ) (h : r ≠ 0) : DifferentiableAt ℝ (fun r ↦ r ^ (-12:ℤ )) r := by
  apply DifferentiableAt.zpow
  · apply differentiable_id
  · apply Or.inl
    exact h

lemma differentiable_at_zpow_neg6 (r : ℝ) (h : r ≠ 0) : DifferentiableAt ℝ (fun r ↦ r ^ (-6:ℤ )) r := by
  apply DifferentiableAt.zpow
  · apply differentiable_id
  · apply Or.inl
    exact h

lemma pow_12: deriv (fun r => r ^ (- 12:ℤ) ) r = (-12:ℤ)  *  r ^ (-13 : ℤ) := by
 rw [show (-13 : ℤ ) = -12 - 1 by ring]
 apply deriv_zpow

lemma pow_6: deriv (fun r => r ^ (- 6:ℤ) ) r = (-6:ℤ)  *  r ^ (-7 : ℤ) := by
 rw [show (-7 : ℤ ) = - 6 - 1 by ring]
 apply deriv_zpow

lemma lj_pow_12 (σ r : ℝ) (h : r ≠ 0): deriv (fun r => σ^12 * r ^ (- 12:ℤ) ) r = σ^12 * (-12:ℤ) * r ^ (-13 : ℤ) := by
  rw [deriv_const_mul]
  rw [pow_12]
  ring
  apply differentiable_at_zpow_neg12
  exact h

lemma lj_pow_6 (σ r : ℝ) (h : r ≠ 0): deriv (fun r => σ^6 * r ^ (- 6:ℤ) ) r = σ^6 * (-6:ℤ) * r ^ (-7 : ℤ) := by
  rw [deriv_const_mul]
  rw [pow_6]
  ring
  apply differentiable_at_zpow_neg6
  exact h

lemma lj_pow_12' (σ r : ℝ) (h : r ≠ 0): deriv (fun r => σ^12 * r ^ (- 12:ℤ) ) r =  σ^12 * (-12:ℤ)  *  r ^ (-13 : ℤ) := by
   rw [deriv_const_mul]
   rw [deriv_zpow]
   rw [show (-12 - 1) = (- 13: ℤ ) by ring]
   ring
   apply differentiable_at_zpow_neg12
   exact h

lemma lj_pow_6' (σ r : ℝ) (h : r ≠ 0): deriv (fun r => σ^6 * r ^ (- 6:ℤ) ) r =  σ^6 * (-6:ℤ)  *  r ^ (-7 : ℤ) := by
   rw [deriv_const_mul]
   rw [deriv_zpow]
   rw [show (-6 - 1) = (- 7: ℤ ) by ring]
   ring
   apply differentiable_at_zpow_neg6
   exact h

lemma div_continuous (σ : ℝ) :
  ContinuousOn (fun r => σ / r) {r | r > 0} := by
  apply ContinuousOn.div
  · exact continuous_const.continuousOn
  · exact continuous_id.continuousOn
  · intro r hr
    exact ne_of_gt hr

lemma pow_continuous (σ : ℝ) (n : ℕ) :
  ContinuousOn (fun r => (σ / r) ^ n) {r | r > 0} := by
  apply ContinuousOn.pow
  exact div_continuous σ

lemma sub_continuous (σ : ℝ) :
  ContinuousOn (fun r => (σ / r) ^ 12 - (σ / r) ^ 6) {r | r > 0} := by
  apply ContinuousOn.sub
  · exact pow_continuous σ 12
  · exact pow_continuous σ 6

lemma scale_continuous (ε σ : ℝ) :
  ContinuousOn (fun r => 4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)) {r | r > 0} := by
  apply ContinuousOn.mul
  · exact continuous_const.continuousOn
  · exact sub_continuous σ


lemma differentiable_on_const (σ : ℝ) :
  DifferentiableOn ℝ (fun r : ℝ => σ) {r | r > 0} := by
  exact (differentiable_const σ).differentiableOn

lemma differentiable_on_square_pow (σ : ℝ) :
  DifferentiableOn ℝ (fun y => ((σ / y) ^ 6) ^ 2) {r | r > 0} := by
  apply DifferentiableOn.pow
  · apply DifferentiableOn.pow
    · apply DifferentiableOn.div
      · apply differentiable_on_const
      · exact differentiable_id.differentiableOn
      · intro x hx
        exact ne_of_gt hx

lemma differentiable_on_pow_div (σ : ℝ) :
  DifferentiableOn ℝ (fun x => (σ / x) ^ 6) {r | r > 0} := by
  apply DifferentiableOn.pow
  apply DifferentiableOn.div
  · exact (differentiable_const σ).differentiableOn
  · exact differentiable_id.differentiableOn
  · intro x hx
    exact ne_of_gt hx


lemma differentiable_at_zpow_neg14 (r : ℝ) (h : r ≠ 0) :
  DifferentiableAt ℝ (fun r ↦ r ^ (-14:ℤ)) r := by
  apply DifferentiableAt.zpow
  · apply differentiable_id
  · apply Or.inl
    exact h


lemma differentiable_at_zpow_neg8 (r : ℝ) (h : r ≠ 0) :
  DifferentiableAt ℝ (fun r ↦ r ^ (-8:ℤ)) r := by
  apply DifferentiableAt.zpow
  · apply differentiable_id
  · apply Or.inl
    exact h


lemma differentiable_on_zpow_neg14 (r_c : ℝ) :
  DifferentiableOn ℝ (fun r ↦ r ^ (-14 : ℤ)) {r | 0 < r ∧ r ≤ r_c} := by
  apply DifferentiableOn.zpow
  · exact differentiable_id.differentiableOn
  · apply Or.inl
    intro x hx
    exact ne_of_gt hx.1

lemma differentiable_on_zpow_neg8 (r_c : ℝ) :
  DifferentiableOn ℝ (fun r ↦ r ^ (-8 : ℤ)) {r | 0 < r ∧ r ≤ r_c} := by
  apply DifferentiableOn.zpow
  · exact differentiable_id.differentiableOn
  · apply Or.inl
    intro x hx
    exact ne_of_gt hx.1


lemma differentiable_on_pow_div' (σ : ℝ) :
  DifferentiableOn ℝ (fun x => (σ / x) ^ 6) {r | r > 0} := by
  apply DifferentiableOn.pow
  apply DifferentiableOn.div
  · exact (differentiable_const σ).differentiableOn
  · exact differentiable_id.differentiableOn
  · intro x hx
    exact ne_of_gt hx


lemma differentiable_pow12_div (σ : ℝ) (hr : ∀ x : ℝ, x > 0) :
  Differentiable ℝ (fun x ↦ (σ / x) ^ 12) := by
  apply Differentiable.pow
  apply Differentiable.div
  · simp only [differentiable_const]
  · simp only [differentiable_id']
  · intro x hx
    have h_pos : x > 0 := hr x
    exact absurd hx (ne_of_gt h_pos)


lemma differentiable_pow6_div (σ : ℝ) (hr : ∀ x : ℝ, x > 0) :
  Differentiable ℝ (fun x ↦ (σ / x) ^ 6) := by
  apply Differentiable.pow
  apply Differentiable.div
  · simp only [differentiable_const]
  · simp only [differentiable_id']
  · intro x hx
    have h_pos : x > 0 := hr x
    exact absurd hx (ne_of_gt h_pos)


noncomputable def Ljp  (r r_c ε σ  : ℝ) : ℝ :=
  if r ≤ r_c then
    let r6 := (σ / r) ^ 6
    let r12 := r6 ^ 2
    4 * ε * (r12 - r6)
  else
    0

theorem cutoff_behavior (r r_c ε σ : ℝ)
    (h : r > r_c) : Ljp r r_c ε σ = 0 := by
  unfold Ljp
  simp [if_neg (not_le_of_gt h)]


theorem ljp_zero_on_tail (r_c ε σ : ℝ) :
  ∀ r, r > r_c → Ljp r r_c ε σ = 0 := by
  intro r h
  unfold Ljp
  simp only [if_neg (not_le_of_gt h)]


theorem ljp_eq_le {r_c ε σ : ℝ} :
  ∀ r ∈ {r | r > 0 ∧ r ≤ r_c }, Ljp r r_c ε σ = 4 * ε * ((σ / r)^12 - (σ / r)^6) := by
  intro r hr
  have h_r_le_rc : r ≤ r_c := hr.2
  unfold Ljp
  rw [if_pos h_r_le_rc]
  ring

theorem ljp_eq_gt : ∀ r ∈ {r | r > r_c ∧ r > 0}, Ljp r r_c ε σ = 0 := by
  intro r hr
  have h_r_gt_rc : r > r_c := hr.1
  have h_r_pos : r > 0 := hr.2
  unfold Ljp
  rw [if_neg (not_le_of_gt h_r_gt_rc)]


theorem ljp_continuous_closed_domain (r_c ε σ : ℝ) :
  ContinuousOn (fun r => if r ≤ r_c then 4 * ε * (((σ / r) ^ 6) ^ 2 - (σ / r) ^ 6) else 0)
    {r | 0 < r ∧ r ≤ r_c} := by
  have subset_pos : {r | 0 < r ∧ r ≤ r_c} ⊆ {r | r > 0} := by
    intro r hr
    exact hr.1
  have base := (scale_continuous ε σ).mono subset_pos
  apply ContinuousOn.congr base
  intro r hr
  simp [if_pos hr.2]
  left
  ring


theorem ljp_continuous_piecewise (r_c ε σ : ℝ) :
  ContinuousOn (fun r => if r ≤ r_c then 4 * ε * (((σ / r) ^ 6) ^ 2 - (σ / r) ^ 6) else 0)
    {r | 0 < r ∧ r < r_c} := by
  have subset_pos : {r | 0 < r ∧ r < r_c} ⊆ {r | r > 0} := by
    intro r hr
    exact hr.1
  have base := (scale_continuous ε σ).mono subset_pos
  apply ContinuousOn.congr base
  intro r hr
  simp [if_pos (le_of_lt hr.2)]
  left
  ring


theorem ljp_differentiable (r_c ε σ : ℝ) :
  DifferentiableOn ℝ (fun r => if r ≤ r_c then 4 * ε * (((σ / r) ^ 6) ^ 2 - (σ / r) ^ 6) else 0)
    {r | 0 < r ∧ r ≤ r_c} := by
  have subset_pos : {r | 0 < r ∧ r ≤ r_c} ⊆ {r | r > 0} := by
    intro r hr
    exact hr.1
  have base : DifferentiableOn ℝ (fun r => 4 * ε * (((σ / r) ^ 6) ^ 2 - (σ / r) ^ 6)) {r | r > 0} := by
    apply DifferentiableOn.mul
    · intro r hr
      simp only [gt_iff_lt]
      apply differentiableOn_const
      exact hr
    · apply DifferentiableOn.sub
      · apply differentiable_on_square_pow
      · apply differentiable_on_pow_div
  apply DifferentiableOn.congr (base.mono subset_pos)
  · intro r hr
    simp [if_pos hr.2]


theorem ljp_second_derivative (r_c ε σ : ℝ) :
  DifferentiableOn ℝ (fun r => 4 * ε * (156 * σ^12 * r^(-14:ℤ ) - 42 * σ^6 * r^(-8:ℤ))) {r | 0 < r ∧ r ≤ r_c} := by
  apply DifferentiableOn.mul
  · exact (differentiable_const (4 * ε)).differentiableOn
  · apply DifferentiableOn.sub
    · apply DifferentiableOn.const_mul
      apply differentiable_on_zpow_neg14
    · apply DifferentiableOn.const_mul
      apply differentiable_on_zpow_neg8


