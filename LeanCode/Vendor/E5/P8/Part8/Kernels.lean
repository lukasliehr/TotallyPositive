import LeanCode.Vendor.E5.P8.Part8.Lattice
import Mathlib.Analysis.SumIntegralExpDecay
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open scoped BigOperators

namespace Part8

noncomputable section


theorem p_formula (a : ℝ) (ha : a ≠ 0) :
  ((0 < a →
      (∀ t : ℝ, 0 ≤ t → expKernel a t = a * Real.exp (-a * t)) ∧
      (∀ t : ℝ, t < 0 → expKernel a t = 0)) ∧
    (a < 0 →
      (∀ t : ℝ, t ≤ 0 → expKernel a t = (-a) * Real.exp ((-a) * t)) ∧
      (∀ t : ℝ, 0 < t → expKernel a t = 0)) ∧
    Measurable (expKernel a) ∧
    (∀ t : ℝ, 0 ≤ expKernel a t ∧ expKernel a t ≤ |a|) ∧
    (∀ t : ℝ, expKernel a t ≤ |a| * Real.exp (-|a| * |t|))) := by
  have _ha : a ≠ 0 := ha
  constructor
  · intro ha_pos
    constructor
    · intro t ht
      have hcond : 0 ≤ a * t := mul_nonneg ha_pos.le ht
      simp [expKernel, hcond, abs_of_pos ha_pos]
    · intro t ht
      have hcond : ¬ 0 ≤ a * t := by
        have hlt : a * t < 0 := mul_neg_of_pos_of_neg ha_pos ht
        exact not_le.mpr hlt
      simp [expKernel, hcond]
  constructor
  · intro ha_neg
    constructor
    · intro t ht
      have hcond : 0 ≤ a * t := mul_nonneg_of_nonpos_of_nonpos ha_neg.le ht
      have habs : |a| = -a := abs_of_neg ha_neg
      simp [expKernel, hcond, habs]
    · intro t ht
      have hcond : ¬ 0 ≤ a * t := by
        have hlt : a * t < 0 := mul_neg_of_neg_of_pos ha_neg ht
        exact not_le.mpr hlt
      simp [expKernel, hcond]
  constructor
  · unfold expKernel
    have hmul : Measurable fun t : ℝ => a * t := by fun_prop
    have hset : MeasurableSet {t : ℝ | 0 ≤ a * t} := by
      exact measurableSet_le measurable_const hmul
    exact Measurable.ite hset (by fun_prop) measurable_const
  constructor
  · intro t
    constructor
    · by_cases hcond : 0 ≤ a * t
      · simp [expKernel, hcond, mul_nonneg (abs_nonneg a) (Real.exp_pos _).le]
      · simp [expKernel, hcond]
    · by_cases hcond : 0 ≤ a * t
      · simp only [expKernel, hcond, ↓reduceIte]
        have hexp : Real.exp (-(a * t)) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by linarith)
        exact mul_le_of_le_one_right (abs_nonneg a) hexp
      · simp [expKernel, hcond, abs_nonneg]
  · intro t
    by_cases hcond : 0 ≤ a * t
    · simp only [expKernel, hcond, ↓reduceIte]
      have hprod : a * t = |a| * |t| := by
        rw [← abs_of_nonneg hcond, abs_mul]
      rw [hprod]
      ring_nf
      exact le_rfl
    · simp only [expKernel, hcond, ↓reduceIte]
      exact mul_nonneg (abs_nonneg a) (Real.exp_pos _).le


theorem p_int (a : ℝ) (ha : a ≠ 0) :
  Integrable (expKernel a) ∧ ∫ t : ℝ, expKernel a t = 1 := by
  rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
  · have h_eq : (fun t : ℝ => expKernel a t) =
        fun t : ℝ => (Set.Iic (0 : ℝ)).indicator
          (fun t => (-a) * Real.exp ((-a) * t)) t := by
      funext t
      have hp := p_formula a ha
      have hneg_branch := hp.2.1 ha_neg
      by_cases ht : t ≤ 0
      · have htmem : t ∈ Set.Iic (0 : ℝ) := ht
        rw [Set.indicator_of_mem htmem]
        exact hneg_branch.1 t ht
      · have htpos : 0 < t := lt_of_not_ge ht
        have hnotmem : t ∉ Set.Iic (0 : ℝ) := ht
        rw [Set.indicator_of_notMem hnotmem]
        exact hneg_branch.2 t htpos
    have hgOn : IntegrableOn (fun t : ℝ => (-a) * Real.exp ((-a) * t))
        (Set.Iic (0 : ℝ)) := by
      have hbase : IntegrableOn (fun t : ℝ => Real.exp ((-a) * t))
          (Set.Iic (0 : ℝ)) := by
        exact integrableOn_exp_mul_Iic (a := -a) (by linarith) 0
      change Integrable (fun t : ℝ => (-a) * Real.exp ((-a) * t))
        (volume.restrict (Set.Iic (0 : ℝ)))
      exact hbase.const_mul (-a)
    have hg : Integrable (fun t : ℝ => (Set.Iic (0 : ℝ)).indicator
        (fun t => (-a) * Real.exp ((-a) * t)) t) :=
      hgOn.integrable_indicator measurableSet_Iic
    constructor
    · change Integrable (fun t : ℝ => expKernel a t)
      rw [h_eq]
      exact hg
    · rw [h_eq]
      calc
        ∫ t : ℝ, (Set.Iic (0 : ℝ)).indicator
            (fun t => (-a) * Real.exp ((-a) * t)) t =
            ∫ t : ℝ in Set.Iic (0 : ℝ), (-a) * Real.exp ((-a) * t) := by
          rw [integral_indicator measurableSet_Iic]
        _ = 1 := by
          rw [integral_const_mul]
          rw [integral_exp_mul_Iic (a := -a) (by linarith) 0]
          field_simp [neg_ne_zero.mpr ha]
          norm_num
  · have h_ae : (fun t : ℝ => expKernel a t) =ᵐ[volume]
        fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator
          (fun t => a * Real.exp ((-a) * t)) t := by
      have hp := p_formula a ha
      have hpos_branch := hp.1 ha_pos
      have hne0_ae : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
        rw [ae_iff]
        simp [MeasureTheory.NoAtoms.measure_singleton (μ := volume) (0 : ℝ)]
      filter_upwards [hne0_ae] with t ht0
      by_cases htpos : 0 < t
      · have htmem : t ∈ Set.Ioi (0 : ℝ) := htpos
        rw [Set.indicator_of_mem htmem]
        have hnonneg : 0 ≤ t := le_of_lt htpos
        rw [hpos_branch.1 t hnonneg]
      · have htneg : t < 0 := by
          have hle : t ≤ 0 := le_of_not_gt htpos
          exact lt_of_le_of_ne hle ht0
        have hnotmem : t ∉ Set.Ioi (0 : ℝ) := by exact fun h => htpos h
        rw [Set.indicator_of_notMem hnotmem]
        exact hpos_branch.2 t htneg
    have hgOn : IntegrableOn (fun t : ℝ => a * Real.exp ((-a) * t))
        (Set.Ioi (0 : ℝ)) := by
      have hbase : IntegrableOn (fun t : ℝ => Real.exp ((-a) * t))
          (Set.Ioi (0 : ℝ)) := by
        exact integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
      change Integrable (fun t : ℝ => a * Real.exp ((-a) * t))
        (volume.restrict (Set.Ioi (0 : ℝ)))
      exact hbase.const_mul a
    have hg : Integrable (fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator
        (fun t => a * Real.exp ((-a) * t)) t) :=
      hgOn.integrable_indicator measurableSet_Ioi
    constructor
    · exact (integrable_congr h_ae).mpr hg
    · calc
        ∫ t : ℝ, expKernel a t =
            ∫ t : ℝ, (Set.Ioi (0 : ℝ)).indicator
              (fun t => a * Real.exp ((-a) * t)) t :=
          integral_congr_ae h_ae
        _ = ∫ t : ℝ in Set.Ioi (0 : ℝ), a * Real.exp ((-a) * t) := by
          rw [integral_indicator measurableSet_Ioi]
        _ = 1 := by
          rw [integral_const_mul]
          rw [integral_exp_mul_Ioi (a := -a) (by linarith) 0]
          field_simp [ha_pos.ne']
          norm_num


theorem p_FT (a : ℝ) (ha : a ≠ 0) :
  ∀ ξ : ℝ,
    FT (expKernel a) ξ =
      (a : ℂ) / ((a : ℂ) + 2 * Real.pi * Complex.I * ξ) ∧
    ((a : ℂ) + 2 * Real.pi * Complex.I * ξ) ≠ 0 ∧
    (1 + 2 * Real.pi * Complex.I * ξ / (a : ℂ)) ≠ 0 := by
  intro ξ
  have hden : ((a : ℂ) + 2 * Real.pi * Complex.I * ξ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at hre
    exact ha hre
  have hden2 : (1 + 2 * Real.pi * Complex.I * ξ / (a : ℂ)) ≠ 0 := by
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hrewrite : 1 + 2 * Real.pi * Complex.I * ξ / (a : ℂ) =
        ((a : ℂ) + 2 * Real.pi * Complex.I * ξ) / (a : ℂ) := by
      field_simp [haC]
    rw [hrewrite]
    exact div_ne_zero hden haC
  have hft : FT (expKernel a) ξ =
      (a : ℂ) / ((a : ℂ) + 2 * Real.pi * Complex.I * ξ) := by
    rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
    · let z : ℂ := (((-a : ℝ) : ℂ) - 2 * Real.pi * Complex.I * ξ)
      have hp := p_formula a ha
      have hneg_branch := hp.2.1 ha_neg
      have h_ae :
          (fun t : ℝ => Complex.exp (-2 * Real.pi * Complex.I * ξ * t) *
            expKernel a t) =ᵐ[volume]
          fun t : ℝ => (Set.Iic (0 : ℝ)).indicator
            (fun t => ((-a : ℝ) : ℂ) * Complex.exp (z * t)) t := by
        filter_upwards with t
        by_cases ht : t ≤ 0
        · have htmem : t ∈ Set.Iic (0 : ℝ) := ht
          rw [Set.indicator_of_mem htmem]
          rw [hneg_branch.1 t ht]
          rw [Complex.ofReal_mul, Complex.ofReal_exp]
          dsimp [z]
          calc
            Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑t) *
                (↑(-a) * Complex.exp ↑((-a) * t)) =
                ((-a : ℝ) : ℂ) *
                  (Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑t) *
                    Complex.exp ↑((-a) * t)) := by
              ring_nf
            _ = ((-a : ℝ) : ℂ) *
                Complex.exp ((-2 * Real.pi * Complex.I * ↑ξ * ↑t) +
                  ↑((-a) * t)) := by
              rw [Complex.exp_add]
            _ = ((-a : ℝ) : ℂ) *
                Complex.exp ((((-a : ℝ) : ℂ) - 2 * Real.pi * Complex.I * ξ) *
                  t) := by
              congr 1
              norm_num
              ring_nf
        · have htpos : 0 < t := lt_of_not_ge ht
          have hnotmem : t ∉ Set.Iic (0 : ℝ) := ht
          rw [Set.indicator_of_notMem hnotmem]
          rw [hneg_branch.2 t htpos]
          simp
      have hz_re : 0 < z.re := by
        dsimp [z]
        simp [Complex.mul_re]
        linarith
      calc
        FT (expKernel a) ξ = ∫ t : ℝ, (Set.Iic (0 : ℝ)).indicator
            (fun t => ((-a : ℝ) : ℂ) * Complex.exp (z * t)) t := by
          unfold FT
          exact integral_congr_ae h_ae
        _ = ∫ t : ℝ in Set.Iic (0 : ℝ),
            ((-a : ℝ) : ℂ) * Complex.exp (z * t) := by
          rw [integral_indicator measurableSet_Iic]
        _ = ((-a : ℝ) : ℂ) *
            ∫ t : ℝ in Set.Iic (0 : ℝ), Complex.exp (z * t) := by
          rw [integral_const_mul]
        _ = (a : ℂ) / ((a : ℂ) + 2 * Real.pi * Complex.I * ξ) := by
          rw [integral_exp_mul_complex_Iic (a := z) hz_re 0]
          have hz_eq : z = -((a : ℂ) + 2 * Real.pi * Complex.I * ξ) := by
            dsimp [z]
            norm_num
            ring_nf
          rw [hz_eq]
          norm_num
          have hD : (-(2 * Real.pi * Complex.I * ξ) + -(a : ℂ)) =
              -((a : ℂ) + 2 * Real.pi * Complex.I * ξ) := by
            norm_num
          rw [hD, inv_neg]
          rw [mul_neg, neg_neg, div_eq_mul_inv]
    · let z : ℂ := -((a : ℂ) + 2 * Real.pi * Complex.I * ξ)
      have hp := p_formula a ha
      have hpos_branch := hp.1 ha_pos
      have h_ae :
          (fun t : ℝ => Complex.exp (-2 * Real.pi * Complex.I * ξ * t) *
            expKernel a t) =ᵐ[volume]
          fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator
            (fun t => (a : ℂ) * Complex.exp (z * t)) t := by
        have hne0_ae : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
          rw [ae_iff]
          simp [MeasureTheory.NoAtoms.measure_singleton (μ := volume) (0 : ℝ)]
        filter_upwards [hne0_ae] with t ht0
        by_cases htpos : 0 < t
        · have htmem : t ∈ Set.Ioi (0 : ℝ) := htpos
          rw [Set.indicator_of_mem htmem]
          have hnonneg : 0 ≤ t := le_of_lt htpos
          rw [hpos_branch.1 t hnonneg]
          rw [Complex.ofReal_mul, Complex.ofReal_exp]
          dsimp [z]
          calc
            Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑t) *
                (↑a * Complex.exp ↑(-a * t)) =
                (a : ℂ) * (Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑t) *
                  Complex.exp ↑(-a * t)) := by
              ring_nf
            _ = (a : ℂ) * Complex.exp ((-2 * Real.pi * Complex.I * ↑ξ * ↑t) +
                ↑(-a * t)) := by
              rw [Complex.exp_add]
            _ = (a : ℂ) *
                Complex.exp (-((a : ℂ) + 2 * Real.pi * Complex.I * ξ) * t) := by
              congr 1
              norm_num
              ring_nf
        · have htneg : t < 0 := by
            have hle : t ≤ 0 := le_of_not_gt htpos
            exact lt_of_le_of_ne hle ht0
          have hnotmem : t ∉ Set.Ioi (0 : ℝ) := by exact fun h => htpos h
          rw [Set.indicator_of_notMem hnotmem]
          rw [hpos_branch.2 t htneg]
          simp
      have hz_re : z.re < 0 := by
        dsimp [z]
        simp [Complex.mul_re]
        linarith
      calc
        FT (expKernel a) ξ = ∫ t : ℝ, (Set.Ioi (0 : ℝ)).indicator
            (fun t => (a : ℂ) * Complex.exp (z * t)) t := by
          unfold FT
          exact integral_congr_ae h_ae
        _ = ∫ t : ℝ in Set.Ioi (0 : ℝ), (a : ℂ) * Complex.exp (z * t) := by
          rw [integral_indicator measurableSet_Ioi]
        _ = (a : ℂ) * ∫ t : ℝ in Set.Ioi (0 : ℝ), Complex.exp (z * t) := by
          rw [integral_const_mul]
        _ = (a : ℂ) / ((a : ℂ) + 2 * Real.pi * Complex.I * ξ) := by
          rw [integral_exp_mul_complex_Ioi (a := z) hz_re 0]
          dsimp [z]
          field_simp [hden]
          norm_num
  exact ⟨hft, hden, hden2⟩


theorem q_formula (α : ℝ) (hα : α ≠ 0) :
  ((0 < α →
      (∀ t : ℝ, -α ≤ t → centeredExp α t = (1 / α) * Real.exp (-(t + α) / α)) ∧
      (∀ t : ℝ, t < -α → centeredExp α t = 0)) ∧
    (α < 0 →
      (∀ t : ℝ, t ≤ -α → centeredExp α t = (1 / (-α)) * Real.exp ((t + α) / (-α))) ∧
      (∀ t : ℝ, -α < t → centeredExp α t = 0)) ∧
    Measurable (centeredExp α) ∧
    (∀ t : ℝ, 0 ≤ centeredExp α t ∧ centeredExp α t ≤ 1 / |α|) ∧
    Integrable (centeredExp α) ∧
    (∫ t : ℝ, centeredExp α t) = 1) := by
  have ha_ne : (1 / α : ℝ) ≠ 0 := one_div_ne_zero hα
  have hp := p_formula (1 / α) ha_ne
  have hi := p_int (1 / α) ha_ne
  constructor
  · intro hα_pos
    have ha_pos : 0 < (1 / α : ℝ) := one_div_pos.mpr hα_pos
    have hbranch := hp.1 ha_pos
    constructor
    · intro t ht
      have hs : 0 ≤ t + α := by linarith
      rw [centeredExp, hbranch.1 (t + α) hs]
      ring_nf
    · intro t ht
      have hs : t + α < 0 := by linarith
      rw [centeredExp, hbranch.2 (t + α) hs]
  constructor
  · intro hα_neg
    have ha_neg : (1 / α : ℝ) < 0 := one_div_neg.mpr hα_neg
    have hbranch := hp.2.1 ha_neg
    constructor
    · intro t ht
      have hs : t + α ≤ 0 := by linarith
      rw [centeredExp, hbranch.1 (t + α) hs]
      field_simp [hα]
    · intro t ht
      have hs : 0 < t + α := by linarith
      rw [centeredExp, hbranch.2 (t + α) hs]
  constructor
  · change Measurable (fun t : ℝ => expKernel (1 / α) (t + α))
    exact hp.2.2.1.comp (by fun_prop : Measurable fun t : ℝ => t + α)
  constructor
  · intro t
    have hb := hp.2.2.2.1 (t + α)
    simpa [centeredExp, abs_one_div] using hb
  constructor
  · change Integrable (fun t : ℝ => expKernel (1 / α) (t + α))
    exact hi.1.comp_add_right α
  · calc
      ∫ t : ℝ, centeredExp α t = ∫ t : ℝ, expKernel (1 / α) (t + α) := by rfl
      _ = ∫ t : ℝ, expKernel (1 / α) t := by
        exact MeasureTheory.integral_add_right_eq_self (fun t : ℝ => expKernel (1 / α) t) α
      _ = 1 := hi.2


theorem q_window (α : ℝ) (hα : α ≠ 0) :
  ∃ w ε : ℝ, 0 < ε ∧
    (∀ t ∈ Set.Icc w (w + 1), ε ≤ centeredExp α t) ∧
    ((0 < α →
      (∀ s t : ℝ, -α ≤ s → s ≤ t → centeredExp α t ≤ centeredExp α s) ∧
      ∀ t : ℝ, -α ≤ t → 0 < centeredExp α t) ∧
    (α < 0 →
      (∀ s t : ℝ, s ≤ t → t ≤ -α → centeredExp α s ≤ centeredExp α t) ∧
      ∀ t : ℝ, t ≤ -α → 0 < centeredExp α t)) := by
  rcases lt_or_gt_of_ne hα with hα_neg | hα_pos
  · let β : ℝ := -α
    have hβ_pos : 0 < β := by dsimp [β]; linarith
    let ε : ℝ := (1 / β) * Real.exp (-(1 / β))
    refine ⟨β - 1, ε, ?_, ?_, ?_⟩
    · dsimp [ε]
      positivity
    · intro t ht
      have hq := q_formula α hα
      have hneg := hq.2.1 hα_neg
      have ht_support : t ≤ -α := by
        dsimp [β] at ht
        linarith [ht.2]
      rw [hneg.1 t ht_support]
      dsimp [ε, β]
      have hcoef_nonneg : 0 ≤ 1 / (-α) := by positivity
      apply mul_le_mul_of_nonneg_left ?_ hcoef_nonneg
      apply Real.exp_le_exp.mpr
      have ht_lower : -1 ≤ t + α := by
        dsimp [β] at ht
        linarith [ht.1]
      have hden_nonneg : 0 ≤ (-α)⁻¹ := by positivity
      have hmul := mul_le_mul_of_nonneg_right ht_lower hden_nonneg
      simpa [div_eq_mul_inv, one_div, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
    · constructor
      · intro hpos
        exfalso
        linarith
      · intro _
        have hq := q_formula α hα
        have hneg := hq.2.1 hα_neg
        constructor
        · intro s t hst ht_support
          have hs_support : s ≤ -α := by linarith
          rw [hneg.1 s hs_support, hneg.1 t ht_support]
          have hcoef_nonneg : 0 ≤ 1 / (-α) := by positivity
          apply mul_le_mul_of_nonneg_left ?_ hcoef_nonneg
          apply Real.exp_le_exp.mpr
          have hst_add : s + α ≤ t + α := by linarith
          have hden_nonneg : 0 ≤ (-α)⁻¹ := by positivity
          have hmul := mul_le_mul_of_nonneg_right hst_add hden_nonneg
          simpa [div_eq_mul_inv, one_div, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
        · intro t ht
          rw [hneg.1 t ht]
          positivity
  · let ε : ℝ := (1 / α) * Real.exp (-(1 / α))
    refine ⟨-α, ε, ?_, ?_, ?_⟩
    · dsimp [ε]
      positivity
    · intro t ht
      have hq := q_formula α hα
      have hpos := hq.1 hα_pos
      have ht_support : -α ≤ t := ht.1
      rw [hpos.1 t ht_support]
      dsimp [ε]
      have hcoef_nonneg : 0 ≤ 1 / α := by positivity
      apply mul_le_mul_of_nonneg_left ?_ hcoef_nonneg
      apply Real.exp_le_exp.mpr
      have ht_upper : t + α ≤ 1 := by linarith [ht.2]
      field_simp [hα_pos.ne']
      nlinarith
    · constructor
      · intro _
        have hq := q_formula α hα
        have hpos := hq.1 hα_pos
        constructor
        · intro s t hs_support hst
          have ht_support : -α ≤ t := by linarith
          rw [hpos.1 t ht_support, hpos.1 s hs_support]
          have hcoef_nonneg : 0 ≤ 1 / α := by positivity
          apply mul_le_mul_of_nonneg_left ?_ hcoef_nonneg
          apply Real.exp_le_exp.mpr
          field_simp [hα_pos.ne']
          nlinarith
        · intro t ht
          rw [hpos.1 t ht]
          positivity
      · intro hneg
        exfalso
        linarith


theorem FT_translate (u : ℝ → ℝ) (c : ℝ) (hu : Integrable u) :
  ∀ ξ : ℝ,
    FT (translate c u) ξ =
      Complex.exp (-2 * Real.pi * Complex.I * c * ξ) * FT u ξ := by
  have _hu : Integrable u := hu
  intro ξ
  let f : ℝ → ℂ := fun y =>
    Complex.exp (-2 * Real.pi * Complex.I * ξ * (y + c)) * u y
  calc
    FT (translate c u) ξ = ∫ x : ℝ,
        Complex.exp (-2 * Real.pi * Complex.I * ξ * x) * u (x - c) := by
      rfl
    _ = ∫ x : ℝ, f (x + (-c)) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [f]
      congr 2
      norm_num
    _ = ∫ y : ℝ, f y := by
      exact MeasureTheory.integral_add_right_eq_self f (-c)
    _ = ∫ y : ℝ,
        Complex.exp (-2 * Real.pi * Complex.I * c * ξ) *
          (Complex.exp (-2 * Real.pi * Complex.I * ξ * y) * u y) := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp [f]
      rw [← mul_assoc]
      congr 1
      rw [← Complex.exp_add]
      congr 1
      norm_num
      ring
    _ = Complex.exp (-2 * Real.pi * Complex.I * c * ξ) *
        ∫ y : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ξ * y) * u y := by
      rw [integral_const_mul]
    _ = Complex.exp (-2 * Real.pi * Complex.I * c * ξ) * FT u ξ := by
      rfl


theorem q_FT (α : ℝ) (hα : α ≠ 0) :
  (∀ ξ : ℝ, FT (centeredExp α) ξ = expFactor α ξ) ∧
    centeredExp α = translate (-α) (expKernel (1 / α)) := by
  have ha_ne : (1 / α : ℝ) ≠ 0 := one_div_ne_zero hα
  have hi : Integrable (expKernel (1 / α)) := (p_int (1 / α) ha_ne).1
  have htrans : centeredExp α = translate (-α) (expKernel (1 / α)) := by
    funext t
    unfold centeredExp translate
    congr 1
    ring
  constructor
  · intro ξ
    have ht := FT_translate (expKernel (1 / α)) (-α) hi ξ
    have hp := p_FT (1 / α) ha_ne ξ
    calc
      FT (centeredExp α) ξ = FT (translate (-α) (expKernel (1 / α))) ξ := by
        rw [htrans]
      _ = Complex.exp (-2 * Real.pi * Complex.I * ((-α : ℝ) : ℂ) * ξ) *
          FT (expKernel (1 / α)) ξ := ht
      _ = Complex.exp (-2 * Real.pi * Complex.I * ((-α : ℝ) : ℂ) * ξ) *
          (((1 / α : ℝ) : ℂ) /
          (((1 / α : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ξ)) := by
        rw [hp.1]
      _ = expFactor α ξ := by
        unfold expFactor
        have hexp :
            Complex.exp (-2 * Real.pi * Complex.I * ((-α : ℝ) : ℂ) * ξ) =
              Complex.exp (2 * Real.pi * Complex.I * α * ξ) := by
          congr 1
          norm_num
        rw [hexp]
        have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα
        have hden_target : (1 + 2 * Real.pi * Complex.I * ξ * α : ℂ) ≠ 0 := by
          convert hp.2.2 using 1
          rw [one_div, Complex.ofReal_inv]
          field_simp [hαC]
        have hden_target_norm :
            (1 + (α : ℂ) * Real.pi * Complex.I * ξ * 2 : ℂ) ≠ 0 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hden_target
        rw [one_div, Complex.ofReal_inv] at hp ⊢
        field_simp [hαC, hp.2.1, hden_target_norm]
  · exact htrans

private theorem expKernel_pos_ae_one (a : ℝ) (ha : 0 < a) :
    (fun t : ℝ => t * expKernel a t) =ᵐ[volume]
      fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator
        (fun t => t * (a * Real.exp (-(a * t)))) t := by
  have hp := p_formula a ha.ne'
  have hbranch := hp.1 ha
  filter_upwards with t
  by_cases htpos : 0 < t
  · have htmem : t ∈ Set.Ioi (0 : ℝ) := htpos
    rw [Set.indicator_of_mem htmem]
    have hnonneg : 0 ≤ t := le_of_lt htpos
    rw [hbranch.1 t hnonneg]
    ring_nf
  · have hle : t ≤ 0 := le_of_not_gt htpos
    have hnotmem : t ∉ Set.Ioi (0 : ℝ) := fun h => htpos h
    rw [Set.indicator_of_notMem hnotmem]
    by_cases ht0 : t = 0
    · simp [ht0]
    · have htneg : t < 0 := lt_of_le_of_ne hle ht0
      rw [hbranch.2 t htneg]
      simp

private theorem expKernel_pos_ae_two (a : ℝ) (ha : 0 < a) :
    (fun t : ℝ => t ^ 2 * expKernel a t) =ᵐ[volume]
      fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator
        (fun t => t ^ 2 * (a * Real.exp (-(a * t)))) t := by
  have hp := p_formula a ha.ne'
  have hbranch := hp.1 ha
  filter_upwards with t
  by_cases htpos : 0 < t
  · have htmem : t ∈ Set.Ioi (0 : ℝ) := htpos
    rw [Set.indicator_of_mem htmem]
    have hnonneg : 0 ≤ t := le_of_lt htpos
    rw [hbranch.1 t hnonneg]
    ring_nf
  · have hle : t ≤ 0 := le_of_not_gt htpos
    have hnotmem : t ∉ Set.Ioi (0 : ℝ) := fun h => htpos h
    rw [Set.indicator_of_notMem hnotmem]
    by_cases ht0 : t = 0
    · simp [ht0]
    · have htneg : t < 0 := lt_of_le_of_ne hle ht0
      rw [hbranch.2 t htneg]
      simp

private theorem exp_pos_moment_one_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(a * t))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := a)
    (by norm_num : (-1 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1) ha
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _ht
  simp [Real.rpow_one]

private theorem exp_pos_moment_two_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-(a * t))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2) (b := a)
    (by norm_num : (-1 : ℝ) < 2) (by norm_num : (1 : ℝ) ≤ 1) ha
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _ht
  simp [Real.rpow_one]

private theorem exp_pos_moment_one_value {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), t * Real.exp (-(a * t))) = 1 / a ^ 2 := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a)
    (by norm_num : (0 : ℝ) < 2) ha
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at key
  have hG : Real.Gamma (2 : ℝ) = 1 := by
    norm_num [← Real.Gamma_nat_eq_factorial 1]
  rw [hG] at key
  simpa [Real.rpow_one, sq, one_div, mul_assoc, mul_comm, mul_left_comm] using key

private theorem exp_pos_moment_two_value {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), t ^ 2 * Real.exp (-(a * t))) = 2 / a ^ 3 := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := a)
    (by norm_num : (0 : ℝ) < 3) ha
  rw [show (3 : ℝ) - 1 = 2 by norm_num] at key
  have hG : Real.Gamma (3 : ℝ) = 2 := by
    norm_num [← Real.Gamma_nat_eq_factorial 2]
  rw [hG] at key
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ), t ^ 2 * Real.exp (-(a * t))) =
        (1 / a) ^ (3 : ℝ) * 2 := by
      simpa [Real.rpow_two] using key
    _ = 2 / a ^ 3 := by
      norm_num [Real.rpow_natCast]
      field_simp [ha.ne']

private theorem expKernel_moments_pos (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => t * expKernel a t) ∧
      Integrable (fun t : ℝ => t ^ 2 * expKernel a t) ∧
      (∫ t : ℝ, t * expKernel a t) = 1 / a ∧
      (∫ t : ℝ, t ^ 2 * expKernel a t) = 2 / a ^ 2 := by
  have hOn1 : IntegrableOn (fun t : ℝ => t * (a * Real.exp (-(a * t)))) (Set.Ioi 0) := by
    change Integrable (fun t : ℝ => t * (a * Real.exp (-(a * t))))
      (volume.restrict (Set.Ioi 0))
    have hbase : Integrable (fun t : ℝ => t * Real.exp (-(a * t)))
        (volume.restrict (Set.Ioi 0)) :=
      exp_pos_moment_one_integrable ha
    convert hbase.const_mul a using 1
    ext t
    ring_nf
  have hOn2 : IntegrableOn (fun t : ℝ => t ^ 2 * (a * Real.exp (-(a * t)))) (Set.Ioi 0) := by
    change Integrable (fun t : ℝ => t ^ 2 * (a * Real.exp (-(a * t))))
      (volume.restrict (Set.Ioi 0))
    have hbase : Integrable (fun t : ℝ => t ^ 2 * Real.exp (-(a * t)))
        (volume.restrict (Set.Ioi 0)) :=
      exp_pos_moment_two_integrable ha
    convert hbase.const_mul a using 1
    ext t
    ring_nf
  have hint1 : Integrable (fun t : ℝ => t * expKernel a t) := by
    have hInd : Integrable (fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator
          (fun t => t * (a * Real.exp (-(a * t)))) t) :=
      hOn1.integrable_indicator measurableSet_Ioi
    exact (integrable_congr (expKernel_pos_ae_one a ha)).mpr hInd
  have hint2 : Integrable (fun t : ℝ => t ^ 2 * expKernel a t) := by
    have hInd : Integrable (fun t : ℝ => (Set.Ioi (0 : ℝ)).indicator
          (fun t => t ^ 2 * (a * Real.exp (-(a * t)))) t) :=
      hOn2.integrable_indicator measurableSet_Ioi
    exact (integrable_congr (expKernel_pos_ae_two a ha)).mpr hInd
  refine ⟨hint1, hint2, ?_, ?_⟩
  · calc
      ∫ t : ℝ, t * expKernel a t =
          ∫ t : ℝ, (Set.Ioi (0 : ℝ)).indicator
            (fun t => t * (a * Real.exp (-(a * t)))) t := by
        exact integral_congr_ae (expKernel_pos_ae_one a ha)
      _ = ∫ t : ℝ in Set.Ioi (0 : ℝ), t * (a * Real.exp (-(a * t))) := by
        rw [integral_indicator measurableSet_Ioi]
      _ = a * ∫ t : ℝ in Set.Ioi (0 : ℝ), t * Real.exp (-(a * t)) := by
        simp_rw [show ∀ t : ℝ, t * (a * Real.exp (-(a * t))) =
            a * (t * Real.exp (-(a * t))) by intro t; ring]
        rw [integral_const_mul]
      _ = a * (1 / a ^ 2) := by
        rw [exp_pos_moment_one_value ha]
      _ = 1 / a := by
        field_simp [ha.ne']
  · calc
      ∫ t : ℝ, t ^ 2 * expKernel a t =
          ∫ t : ℝ, (Set.Ioi (0 : ℝ)).indicator
            (fun t => t ^ 2 * (a * Real.exp (-(a * t)))) t := by
        exact integral_congr_ae (expKernel_pos_ae_two a ha)
      _ = ∫ t : ℝ in Set.Ioi (0 : ℝ), t ^ 2 * (a * Real.exp (-(a * t))) := by
        rw [integral_indicator measurableSet_Ioi]
      _ = a * ∫ t : ℝ in Set.Ioi (0 : ℝ), t ^ 2 * Real.exp (-(a * t)) := by
        simp_rw [show ∀ t : ℝ, t ^ 2 * (a * Real.exp (-(a * t))) =
            a * (t ^ 2 * Real.exp (-(a * t))) by intro t; ring]
        rw [integral_const_mul]
      _ = a * (2 / a ^ 3) := by
        rw [exp_pos_moment_two_value ha]
      _ = 2 / a ^ 2 := by
        field_simp [ha.ne']

private theorem integral_comp_neg_univ (f : ℝ → ℝ) :
    (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
  have h := MeasureTheory.integral_map_equiv (MeasurableEquiv.neg ℝ) f (μ := volume)
  have hmap : Measure.map (⇑(MeasurableEquiv.neg ℝ)) (volume : Measure ℝ) = volume := by
    simp [Measure.map_neg_eq_self (volume : Measure ℝ)]
  simpa [hmap] using h.symm

private theorem expKernel_neg_reflect (a t : ℝ) (ha : a < 0) :
    expKernel a t = expKernel (-a) (-t) := by
  unfold expKernel
  have habs1 : |a| = -a := abs_of_neg ha
  have habs2 : |-a| = -a := abs_of_pos (neg_pos.mpr ha)
  rw [habs1, habs2]
  have hprod : (-a) * (-t) = a * t := by ring
  rw [hprod]

private theorem expKernel_moments_neg (a : ℝ) (ha : a < 0) :
    Integrable (fun t : ℝ => t * expKernel a t) ∧
      Integrable (fun t : ℝ => t ^ 2 * expKernel a t) ∧
      (∫ t : ℝ, t * expKernel a t) = 1 / a ∧
      (∫ t : ℝ, t ^ 2 * expKernel a t) = 2 / a ^ 2 := by
  let b : ℝ := -a
  have hb : 0 < b := by dsimp [b]; linarith
  rcases expKernel_moments_pos b hb with ⟨hb_int1, hb_int2, hb_m1, hb_m2⟩
  have hrel1 : (fun t : ℝ => t * expKernel a t) =
      fun t : ℝ => - ((-t) * expKernel b (-t)) := by
    funext t
    rw [expKernel_neg_reflect a t ha]
    dsimp [b]
    ring
  have hrel2 : (fun t : ℝ => t ^ 2 * expKernel a t) =
      fun t : ℝ => ((-t) ^ 2 * expKernel b (-t)) := by
    funext t
    rw [expKernel_neg_reflect a t ha]
    dsimp [b]
    ring
  have hcomp1 : Integrable (fun t : ℝ => (-t) * expKernel b (-t)) := by
    let g : ℝ → ℝ := fun u => u * expKernel b u
    have hg : Integrable g := hb_int1
    have hgsm : AEStronglyMeasurable g (volume : Measure ℝ) := hg.aestronglyMeasurable
    have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp hgsm).2 hg
    simpa [g, Function.comp_def] using h
  have hcomp2 : Integrable (fun t : ℝ => (-t) ^ 2 * expKernel b (-t)) := by
    let g : ℝ → ℝ := fun u => u ^ 2 * expKernel b u
    have hg : Integrable g := hb_int2
    have hgsm : AEStronglyMeasurable g (volume : Measure ℝ) := hg.aestronglyMeasurable
    have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp hgsm).2 hg
    simpa [g, Function.comp_def] using h
  have hint1 : Integrable (fun t : ℝ => t * expKernel a t) := by
    rw [hrel1]
    exact hcomp1.neg
  have hint2 : Integrable (fun t : ℝ => t ^ 2 * expKernel a t) := by
    rw [hrel2]
    exact hcomp2
  have hnegint1 : (∫ t : ℝ, (-t) * expKernel b (-t)) =
      ∫ u : ℝ, u * expKernel b u := by
    simpa [Function.comp_def] using integral_comp_neg_univ (fun u : ℝ => u * expKernel b u)
  have hnegint2 : (∫ t : ℝ, (-t) ^ 2 * expKernel b (-t)) =
      ∫ u : ℝ, u ^ 2 * expKernel b u :=
    integral_comp_neg_univ (fun u : ℝ => u ^ 2 * expKernel b u)
  refine ⟨hint1, hint2, ?_, ?_⟩
  · calc
      ∫ t : ℝ, t * expKernel a t = ∫ t : ℝ, - ((-t) * expKernel b (-t)) := by
        rw [hrel1]
      _ = - ∫ t : ℝ, (-t) * expKernel b (-t) := by
        rw [integral_neg]
      _ = - ∫ u : ℝ, u * expKernel b u := by
        rw [hnegint1]
      _ = 1 / a := by
        rw [hb_m1]
        dsimp [b]
        field_simp [ha.ne]
  · calc
      ∫ t : ℝ, t ^ 2 * expKernel a t = ∫ t : ℝ, (-t) ^ 2 * expKernel b (-t) := by
        rw [hrel2]
      _ = ∫ u : ℝ, u ^ 2 * expKernel b u := by
        rw [hnegint2]
      _ = 2 / a ^ 2 := by
        rw [hb_m2]
        dsimp [b]
        ring_nf

private theorem expKernel_moments (a : ℝ) (ha : a ≠ 0) :
    Integrable (fun t : ℝ => t * expKernel a t) ∧
      Integrable (fun t : ℝ => t ^ 2 * expKernel a t) ∧
      (∫ t : ℝ, t * expKernel a t) = 1 / a ∧
      (∫ t : ℝ, t ^ 2 * expKernel a t) = 2 / a ^ 2 := by
  rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
  · exact expKernel_moments_neg a ha_neg
  · exact expKernel_moments_pos a ha_pos


theorem q_moments (α : ℝ) (hα : α ≠ 0) :
  Integrable (fun t : ℝ => t * centeredExp α t) ∧
    Integrable (fun t : ℝ => t ^ 2 * centeredExp α t) ∧
    (∫ t : ℝ, t * centeredExp α t) = 0 ∧
    (∫ t : ℝ, t ^ 2 * centeredExp α t) = α ^ 2 := by
  let a : ℝ := 1 / α
  have ha : a ≠ 0 := by dsimp [a]; exact one_div_ne_zero hα
  rcases expKernel_moments a ha with ⟨hp_int1, hp_int2, hp_m1, hp_m2⟩
  have hp0 := p_int a ha
  let f1 : ℝ → ℝ := fun u => (u - α) * expKernel a u
  let f2 : ℝ → ℝ := fun u => (u - α) ^ 2 * expKernel a u
  have hf1_eq : f1 = fun u : ℝ => u * expKernel a u - α * expKernel a u := by
    funext u
    dsimp [f1]
    ring
  have hf2_eq : f2 =
      fun u : ℝ => u ^ 2 * expKernel a u - (2 * α) * (u * expKernel a u) +
        α ^ 2 * expKernel a u := by
    funext u
    dsimp [f2]
    ring
  have hf1_int : Integrable f1 := by
    rw [hf1_eq]
    exact hp_int1.sub (hp0.1.const_mul α)
  have hf2_int : Integrable f2 := by
    rw [hf2_eq]
    exact (hp_int2.sub (hp_int1.const_mul (2 * α))).add (hp0.1.const_mul (α ^ 2))
  have hcenter1 : (fun t : ℝ => t * centeredExp α t) = fun t : ℝ => f1 (t + α) := by
    funext t
    dsimp [f1, centeredExp, a]
    ring
  have hcenter2 :
      (fun t : ℝ => t ^ 2 * centeredExp α t) = fun t : ℝ => f2 (t + α) := by
    funext t
    dsimp [f2, centeredExp, a]
    ring
  have hint1 : Integrable (fun t : ℝ => t * centeredExp α t) := by
    rw [hcenter1]
    exact hf1_int.comp_add_right α
  have hint2 : Integrable (fun t : ℝ => t ^ 2 * centeredExp α t) := by
    rw [hcenter2]
    exact hf2_int.comp_add_right α
  refine ⟨hint1, hint2, ?_, ?_⟩
  · calc
      ∫ t : ℝ, t * centeredExp α t = ∫ t : ℝ, f1 (t + α) := by
        rw [hcenter1]
      _ = ∫ u : ℝ, f1 u := by
        exact MeasureTheory.integral_add_right_eq_self f1 α
      _ = ∫ u : ℝ, (u * expKernel a u - α * expKernel a u) := by
        rw [hf1_eq]
      _ = (∫ u : ℝ, u * expKernel a u) - ∫ u : ℝ, α * expKernel a u := by
        rw [integral_sub hp_int1 (hp0.1.const_mul α)]
      _ = (1 / a) - α * 1 := by
        rw [hp_m1, integral_const_mul, hp0.2]
      _ = 0 := by
        dsimp [a]
        field_simp [hα]
        ring
  · calc
      ∫ t : ℝ, t ^ 2 * centeredExp α t = ∫ t : ℝ, f2 (t + α) := by
        rw [hcenter2]
      _ = ∫ u : ℝ, f2 u := by
        exact MeasureTheory.integral_add_right_eq_self f2 α
      _ = ∫ u : ℝ,
          (u ^ 2 * expKernel a u - (2 * α) * (u * expKernel a u) +
            α ^ 2 * expKernel a u) := by
        rw [hf2_eq]
      _ = ∫ u : ℝ, (u ^ 2 * expKernel a u - (2 * α) * (u * expKernel a u)) +
          α ^ 2 * expKernel a u := by
        congr
      _ = (∫ u : ℝ, u ^ 2 * expKernel a u - (2 * α) * (u * expKernel a u)) +
          ∫ u : ℝ, α ^ 2 * expKernel a u := by
        exact integral_add (hp_int2.sub (hp_int1.const_mul (2 * α)))
          (hp0.1.const_mul (α ^ 2))
      _ = ((∫ u : ℝ, u ^ 2 * expKernel a u) -
            ∫ u : ℝ, (2 * α) * (u * expKernel a u)) +
          ∫ u : ℝ, α ^ 2 * expKernel a u := by
        rw [integral_sub hp_int2 (hp_int1.const_mul (2 * α))]
      _ = ((∫ u : ℝ, u ^ 2 * expKernel a u) -
            ((2 * α) * ∫ u : ℝ, u * expKernel a u)) +
          (α ^ 2 * ∫ u : ℝ, expKernel a u) := by
        rw [integral_const_mul, integral_const_mul]
      _ = (2 / a ^ 2 - (2 * α) * (1 / a)) + α ^ 2 * 1 := by
        rw [hp_m2, hp_m1, hp0.2]
      _ = α ^ 2 := by
        dsimp [a]
        field_simp [hα]
        ring


theorem phi_basic (α ξ : ℝ) :
  expFactor 0 ξ = 1 ∧
    expFactor α ξ ≠ 0 ∧
    ‖expFactor α ξ‖ =
      (Real.sqrt (1 + (2 * Real.pi * α * ξ) ^ 2))⁻¹ ∧
    ‖expFactor α ξ‖ ≤ 1 := by
  constructor
  · simp [expFactor]
  constructor
  · unfold expFactor
    apply div_ne_zero
    · exact Complex.exp_ne_zero _
    · intro h
      have hre := congrArg Complex.re h
      norm_num at hre
  have hnorm : ‖expFactor α ξ‖ =
      (Real.sqrt (1 + (2 * Real.pi * α * ξ) ^ 2))⁻¹ := by
    unfold expFactor
    rw [norm_div]
    have hnum : ‖Complex.exp (2 * Real.pi * Complex.I * α * ξ)‖ = 1 := by
      have harg : 2 * Real.pi * Complex.I * α * ξ =
          Complex.I * (2 * Real.pi * α * ξ) := by
        ring_nf
      simpa [harg] using (Complex.norm_exp_I_mul_ofReal (2 * Real.pi * α * ξ))
    have hden : ‖(1 : ℂ) + 2 * Real.pi * Complex.I * α * ξ‖ =
        Real.sqrt (1 + (2 * Real.pi * α * ξ) ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg ((1 : ℂ) + 2 * Real.pi * Complex.I * α * ξ))]
      congr 1
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      ring
    rw [hnum, hden]
    simp
  constructor
  · exact hnorm
  · rw [hnorm]
    exact inv_le_one_of_one_le₀
      (Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg (2 * Real.pi * α * ξ)]))


theorem exp_lip (s t : ℝ) :
  ‖Complex.exp (Complex.I * s) - Complex.exp (Complex.I * t)‖ ≤ |s - t| := by
  calc
    ‖Complex.exp (Complex.I * s) - Complex.exp (Complex.I * t)‖
        = ‖Complex.exp (Complex.I * t) * (Complex.exp (Complex.I * (s - t)) - 1)‖ := by
          congr 1
          rw [mul_sub, mul_one, ← Complex.exp_add]
          ring_nf
    _ = ‖Complex.exp (Complex.I * (s - t)) - 1‖ := by
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal]
      norm_num
    _ ≤ |s - t| := by
      simpa [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s - t))

end

end Part8
