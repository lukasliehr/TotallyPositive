import LeanCode.Vendor.E1.IntegralEstimates
import LeanCode.Vendor.E1.Reflection
import LeanCode.Vendor.E1.GeometricDecay

noncomputable section

namespace ExpDecay

theorem exists_right_decay_point {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g)
    (hunbounded : ∀ B : ℝ, ∃ p ∈ positivitySet g, B < p)
    {u : ℝ} (hu : u ∈ positivitySet g) :
    ∃ v : ℝ, u < v ∧ 0 < g v ∧ g v < g u := by
  have hu_pos : 0 < g u := by simpa [positivitySet] using hu
  by_contra hnone
  rcases hunbounded (u + totalMass g / g u + 1) with ⟨q, hq_set, hBq⟩
  have hq_pos : 0 < g q := by simpa [positivitySet] using hq_set
  have hmass_nonneg : 0 ≤ totalMass g := totalMass_nonneg hg
  have hdiv_nonneg : 0 ≤ totalMass g / g u := div_nonneg hmass_nonneg hu_pos.le
  have huq : u < q := by linarith
  have hq_ge : g u ≤ g q := by
    exact le_of_not_gt (fun hq_lt => hnone ⟨q, huq, hq_pos, hq_lt⟩)
  have hprod_nonneg : 0 ≤ g u * g q := mul_nonneg hu_pos.le hq_pos.le
  have hsq_le : (g u) ^ 2 ≤ g u * g q := by
    have h := mul_le_mul_of_nonneg_left hq_ge hu_pos.le
    nlinarith
  have hsqrt_ge : g u ≤ Real.sqrt (g u * g q) :=
    (Real.le_sqrt hu_pos.le hprod_nonneg).2 hsq_le
  have hdiff_pos : 0 < q - u := sub_pos.mpr huq
  have hmass_lower : (q - u) * g u ≤ totalMass g := by
    calc
      (q - u) * g u ≤ (q - u) * Real.sqrt (g u * g q) :=
        mul_le_mul_of_nonneg_left hsqrt_ge hdiff_pos.le
      _ ≤ ∫ x in Set.Icc u q, g x := intervalIntegral_lower hg huq
      _ ≤ totalMass g := intervalIntegral_le_totalMass hg huq.le
  have hq_far : totalMass g / g u + 1 < q - u := by linarith
  have hfar_mul : (totalMass g / g u + 1) * g u < (q - u) * g u :=
    mul_lt_mul_of_pos_right hq_far hu_pos
  have hleft_eq : (totalMass g / g u + 1) * g u = totalMass g + g u := by
    field_simp [hu_pos.ne']
  have hmass_lt_interval : totalMass g < (q - u) * g u := by
    have hmass_lt_left : totalMass g < (totalMass g / g u + 1) * g u := by
      rw [hleft_eq]
      linarith
    exact hmass_lt_left.trans hfar_mul
  linarith

theorem right_tail_decay {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) :
    ∃ A C α : ℝ, 0 ≤ A ∧ 0 < C ∧ 0 < α ∧
      ∀ x : ℝ, A ≤ x → g x ≤ C * Real.exp (-α * x) := by
  classical
  by_cases hunbounded : ∀ B : ℝ, ∃ p ∈ positivitySet g, B < p
  · rcases hunbounded 0 with ⟨u, hu, _h0u⟩
    have hu_pos : 0 < g u := by simpa [positivitySet] using hu
    rcases exists_right_decay_point hg hunbounded hu with ⟨v, huv, hv_pos, hv_lt_gu⟩
    let L : ℝ := v - u
    let ρ : ℝ := g v / g u
    have hL : 0 < L := by dsimp [L]; linarith
    have hρ0 : 0 < ρ := by dsimp [ρ]; exact div_pos hv_pos hu_pos
    have hρ1 : ρ < 1 := by
      dsimp [ρ]
      exact (div_lt_one hu_pos).2 hv_lt_gu
    rcases hunbounded (v + L) with ⟨q, hq_set, hq_gt⟩
    have hq_pos : 0 < g q := by simpa [positivitySet] using hq_set
    have hvq : v < q := by linarith
    have hmass_pos : 0 < totalMass g := totalMass_pos_of_two_pos hg hvq hv_pos hq_pos
    let M' : ℝ := (totalMass g) ^ 2 / (g q * (q - (v + L)) ^ 2)
    have hq_base : 0 < q - (v + L) := sub_pos.mpr hq_gt
    have hM' : 0 < M' := by
      dsimp [M']
      exact div_pos (sq_pos_of_pos hmass_pos) (mul_pos hq_pos (sq_pos_of_pos hq_base))
    have hbound : ∀ z : ℝ, z ≤ v + L → g z ≤ M' := by
      intro z hz
      have hzq : z < q := by linarith
      have hleft := endpointLeft_bound hg hzq hq_pos
      have hbase_le : q - (v + L) ≤ q - z := by linarith
      have hqz_nonneg : 0 ≤ q - z := sub_nonneg.mpr hzq.le
      have hsq_le : (q - (v + L)) ^ 2 ≤ (q - z) ^ 2 :=
        (sq_le_sq₀ hq_base.le hqz_nonneg).2 hbase_le
      have hden_pos : 0 < g q * (q - (v + L)) ^ 2 :=
        mul_pos hq_pos (sq_pos_of_pos hq_base)
      have hden_le : g q * (q - (v + L)) ^ 2 ≤ g q * (q - z) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq_le hq_pos.le
      have hquot :
          (totalMass g) ^ 2 / (g q * (q - z) ^ 2) ≤ M' := by
        dsimp [M']
        exact div_le_div_of_nonneg_left (sq_nonneg (totalMass g)) hden_pos hden_le
      exact hleft.trans hquot
    have hstep : ∀ x : ℝ, v < x → g x ≤ ρ * g (x - L) := by
      intro x hxv
      have hk : 0 < x - v := sub_pos.mpr hxv
      have hineq := isTotallyPositive_fourPoint hg.1 u L (x - v) hL hk
      have hineq' : g u * g x ≤ g v * g (x - L) := by
        have htmp : g v * g (x - L) ≥ g u * g x := by
          convert hineq using 2 <;> dsimp [L] <;> ring_nf
        linarith
      have hdiv : g x ≤ (g v * g (x - L)) / g u := by
        rw [le_div_iff₀ hu_pos]
        nlinarith
      calc
        g x ≤ (g v * g (x - L)) / g u := hdiv
        _ = ρ * g (x - L) := by
          dsimp [ρ]
          field_simp [hu_pos.ne']
    rcases geometric_decay g hL hρ0 hρ1 hM' hstep hbound with
      ⟨C, α, hC, hα, htail⟩
    refine ⟨max 0 v, C, α, le_max_left 0 v, hC, hα, ?_⟩
    intro x hx
    exact htail x ((le_max_right 0 v).trans hx)
  · push Not at hunbounded
    rcases hunbounded with ⟨B, hB⟩
    refine ⟨max 0 (B + 1), 1, 1, le_max_left 0 (B + 1), zero_lt_one,
      zero_lt_one, ?_⟩
    intro x hx
    have hBx : B < x := by
      have hB1x : B + 1 ≤ x := (le_max_right 0 (B + 1)).trans hx
      linarith
    have hx_not_pos : ¬ x ∈ positivitySet g := by
      intro hxpos
      have hxleB := hB x hxpos
      linarith
    have hx_le_zero : g x ≤ 0 := by
      dsimp [positivitySet] at hx_not_pos
      exact le_of_not_gt hx_not_pos
    have hrhs_nonneg : 0 ≤ (1 : ℝ) * Real.exp (-(1 : ℝ) * x) := by positivity
    exact hx_le_zero.trans hrhs_nonneg

theorem left_tail_decay {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) :
    ∃ A C α : ℝ, 0 ≤ A ∧ 0 < C ∧ 0 < α ∧
      ∀ x : ℝ, x ≤ -A → g x ≤ C * Real.exp (α * x) := by
  rcases right_tail_decay (reflection_preserves_totallyPositiveIntegrable hg) with
    ⟨A, C, α, hA, hC, hα, htail⟩
  refine ⟨A, C, α, hA, hC, hα, ?_⟩
  intro x hx
  have hAx : A ≤ -x := by linarith
  have h := htail (-x) hAx
  simpa [reflected] using h

end ExpDecay
