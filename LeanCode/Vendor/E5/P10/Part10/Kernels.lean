import LeanCode.Vendor.E5.P10.Part10.HaltBasics
import LeanCode.Vendor.E5.Defs

open MeasureTheory


theorem expker_cases (a : ℝ) :
  ((0 < a →
      (∀ t : ℝ, 0 ≤ t → expKernel a t = a * Real.exp (-a * t)) ∧
      (∀ t : ℝ, t < 0 → expKernel a t = 0)) ∧
    (a < 0 →
      (∀ t : ℝ, t ≤ 0 → expKernel a t = (-a) * Real.exp (-a * t)) ∧
      (∀ t : ℝ, 0 < t → expKernel a t = 0)) ∧
    ∀ t : ℝ, 0 ≤ expKernel a t) := by
  constructor
  · intro ha
    constructor
    · intro t ht
      have hat : 0 ≤ a * t := mul_nonneg (le_of_lt ha) ht
      simp [expKernel, hat, abs_of_pos ha]
    · intro t ht
      have hat : ¬ 0 ≤ a * t := not_le_of_gt (mul_neg_of_pos_of_neg ha ht)
      simp [expKernel, hat]
  constructor
  · intro ha
    constructor
    · intro t ht
      have hat : 0 ≤ a * t := mul_nonneg_of_nonpos_of_nonpos (le_of_lt ha) ht
      simp [expKernel, hat, abs_of_neg ha]
    · intro t ht
      have hat : ¬ 0 ≤ a * t := not_le_of_gt (mul_neg_of_neg_of_pos ha ht)
      simp [expKernel, hat]
  · intro t
    unfold expKernel
    by_cases hat : 0 ≤ a * t
    · simp [hat, mul_nonneg (abs_nonneg a) (le_of_lt (Real.exp_pos (-(a * t))))]
    · simp [hat]


theorem expker_meas (a : ℝ) : Measurable (expKernel a) := by
  unfold expKernel
  refine Measurable.ite ?hset ?hthen ?helse
  · exact measurableSet_le measurable_const (measurable_const.mul measurable_id)
  · exact measurable_const.mul (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
  · exact measurable_const


theorem expker_int (a : ℝ) (ha : a ≠ 0) :
    MeasureTheory.Integrable (expKernel a) ∧
      (∀ t : ℝ, 0 ≤ expKernel a t) ∧
      (∫ t : ℝ, expKernel a t) = 1 ∧
      (∫ t : ℝ, |expKernel a t|) = 1 := by
  have hnonneg : ∀ t : ℝ, 0 ≤ expKernel a t := (expker_cases a).2.2
  rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
  · have hkernel_eq : expKernel a = (Set.Iic (0 : ℝ)).indicator
        (fun t : ℝ => (-a) * Real.exp (-a * t)) := by
      funext t
      by_cases ht : t ≤ 0
      · have hat : 0 ≤ a * t := mul_nonneg_of_nonpos_of_nonpos (le_of_lt ha_neg) ht
        simp [expKernel, hat, ht, abs_of_neg ha_neg]
      · have htpos : 0 < t := lt_of_not_ge ht
        have hat : ¬ 0 ≤ a * t := not_le_of_gt (mul_neg_of_neg_of_pos ha_neg htpos)
        simp [expKernel, hat, ht]
    have hbase : IntegrableOn (fun t : ℝ => Real.exp ((-a) * t)) (Set.Iic (0 : ℝ)) :=
      integrableOn_exp_mul_Iic (a := -a) (by linarith) (0 : ℝ)
    have hbranch : IntegrableOn
        (fun t : ℝ => (-a) * Real.exp (-a * t)) (Set.Iic (0 : ℝ)) := by
      change Integrable
        (fun t : ℝ => (-a) * Real.exp (-a * t)) (volume.restrict (Set.Iic (0 : ℝ)))
      simpa using hbase.const_mul (-a)
    have hint : Integrable (expKernel a) := by
      rw [hkernel_eq]
      exact hbranch.integrable_indicator measurableSet_Iic
    have hmass : (∫ t : ℝ, expKernel a t) = 1 := by
      rw [hkernel_eq, MeasureTheory.integral_indicator measurableSet_Iic]
      calc
        (∫ t in Set.Iic (0 : ℝ), (-a) * Real.exp (-a * t)) =
            (-a) * (∫ t in Set.Iic (0 : ℝ), Real.exp ((-a) * t)) := by
          rw [integral_const_mul]
        _ = (-a) * (Real.exp ((-a) * 0) / (-a)) := by
          rw [integral_exp_mul_Iic (a := -a) (by linarith) (0 : ℝ)]
        _ = 1 := by
          have hane : -a ≠ 0 := by linarith
          field_simp [hane]
          simp
    have habs : (∫ t : ℝ, |expKernel a t|) = 1 := by
      have habs_eq : (fun t : ℝ => |expKernel a t|) = expKernel a := by
        funext t
        exact abs_of_nonneg (hnonneg t)
      rw [habs_eq, hmass]
    exact ⟨hint, hnonneg, hmass, habs⟩
  · have hkernel_eq : expKernel a = (Set.Ici (0 : ℝ)).indicator
        (fun t : ℝ => a * Real.exp (-a * t)) := by
      funext t
      by_cases ht : 0 ≤ t
      · have hat : 0 ≤ a * t := mul_nonneg (le_of_lt ha_pos) ht
        simp [expKernel, hat, ht, abs_of_pos ha_pos]
      · have htneg : t < 0 := lt_of_not_ge ht
        have hat : ¬ 0 ≤ a * t := not_le_of_gt (mul_neg_of_pos_of_neg ha_pos htneg)
        simp [expKernel, hat, ht]
    have hbase : IntegrableOn (fun t : ℝ => Real.exp ((-a) * t)) (Set.Ici (0 : ℝ)) := by
      have hopen : IntegrableOn (fun t : ℝ => Real.exp ((-a) * t)) (Set.Ioi (0 : ℝ)) :=
        integrableOn_exp_mul_Ioi (a := -a) (by linarith) (0 : ℝ)
      rw [← Set.Ioi_union_left, MeasureTheory.integrableOn_union]
      exact ⟨hopen, MeasureTheory.integrableOn_singleton (hx := by simp)⟩
    have hbranch : IntegrableOn
        (fun t : ℝ => a * Real.exp (-a * t)) (Set.Ici (0 : ℝ)) := by
      change Integrable
        (fun t : ℝ => a * Real.exp (-a * t)) (volume.restrict (Set.Ici (0 : ℝ)))
      simpa using hbase.const_mul a
    have hint : Integrable (expKernel a) := by
      rw [hkernel_eq]
      exact hbranch.integrable_indicator measurableSet_Ici
    have hmass : (∫ t : ℝ, expKernel a t) = 1 := by
      rw [hkernel_eq, MeasureTheory.integral_indicator measurableSet_Ici,
        MeasureTheory.integral_Ici_eq_integral_Ioi]
      calc
        (∫ t in Set.Ioi (0 : ℝ), a * Real.exp (-a * t)) =
            a * (∫ t in Set.Ioi (0 : ℝ), Real.exp ((-a) * t)) := by
          rw [integral_const_mul]
        _ = a * (-Real.exp ((-a) * 0) / (-a)) := by
          rw [integral_exp_mul_Ioi (a := -a) (by linarith) (0 : ℝ)]
        _ = 1 := by
          have hane : a ≠ 0 := ne_of_gt ha_pos
          field_simp [hane]
          simp
    have habs : (∫ t : ℝ, |expKernel a t|) = 1 := by
      have habs_eq : (fun t : ℝ => |expKernel a t|) = expKernel a := by
        funext t
        exact abs_of_nonneg (hnonneg t)
      rw [habs_eq, hmass]
    exact ⟨hint, hnonneg, hmass, habs⟩


theorem conv_bounded (a : ℝ) (ha : a ≠ 0) (F : ℝ → ℝ) (M : ℝ)
    (hF_meas : Measurable F) (hF_bound : ∀ y : ℝ, |F y| ≤ M) :
    ∀ x : ℝ,
      MeasureTheory.Integrable (fun t : ℝ => expKernel a t * F (x - t)) ∧
        |conv (expKernel a) F x| ≤ M := by
  intro x
  have hk := expker_int a ha
  have hFcomp : Measurable (fun t : ℝ => F (x - t)) :=
    hF_meas.comp (measurable_const.sub measurable_id)
  have hFbound_ae : ∀ᵐ t : ℝ, ‖F (x - t)‖ ≤ M :=
    Filter.Eventually.of_forall fun t => by
      simpa [Real.norm_eq_abs] using hF_bound (x - t)
  have hint : Integrable (fun t : ℝ => expKernel a t * F (x - t)) :=
    hk.1.mul_bdd hFcomp.aestronglyMeasurable hFbound_ae
  constructor
  · exact hint
  · have hleft_int : Integrable (fun t : ℝ => |expKernel a t * F (x - t)|) := by
      simpa [Real.norm_eq_abs] using hint.norm
    have hright_int : Integrable (fun t : ℝ => M * expKernel a t) := hk.1.const_mul M
    have hpoint : (fun t : ℝ => |expKernel a t * F (x - t)|) ≤
        fun t : ℝ => M * expKernel a t := by
      intro t
      calc
        |expKernel a t * F (x - t)| = expKernel a t * |F (x - t)| := by
          rw [abs_mul, abs_of_nonneg (hk.2.1 t)]
        _ ≤ expKernel a t * M :=
          mul_le_mul_of_nonneg_left (hF_bound (x - t)) (hk.2.1 t)
        _ = M * expKernel a t := by ring
    unfold conv
    calc
      |∫ t : ℝ, expKernel a t * F (x - t)| =
          ‖∫ t : ℝ, expKernel a t * F (x - t)‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ∫ t : ℝ, ‖expKernel a t * F (x - t)‖ :=
        MeasureTheory.norm_integral_le_integral_norm
          (fun t : ℝ => expKernel a t * F (x - t))
      _ = ∫ t : ℝ, |expKernel a t * F (x - t)| := by
        simp [Real.norm_eq_abs]
      _ ≤ ∫ t : ℝ, M * expKernel a t :=
        MeasureTheory.integral_mono hleft_int hright_int hpoint
      _ = M := by
        rw [MeasureTheory.integral_const_mul, hk.2.2.1]
        ring


theorem conv_shift (σ : ℝ) (hσ : σ ≠ 0) (F : ℝ → ℝ) :
    ∀ x : ℝ,
      conv (centeredExp σ) F x = conv (expKernel (1 / σ)) F (x + σ) := by
  have _ : σ ≠ 0 := hσ
  intro x
  unfold conv centeredExp
  rw [← MeasureTheory.integral_add_right_eq_self
    (fun u : ℝ => expKernel (1 / σ) u * F (x + σ - u)) σ]
  apply integral_congr_ae
  filter_upwards with t
  congr 2
  ring


theorem qq_translate (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    ∀ x : ℝ,
    conv (centeredExp a₁) (centeredExp a₂) x =
      conv (expKernel (1 / a₁)) (expKernel (1 / a₂)) (x + a₁ + a₂) ∧
    conv (centeredExp a₁) (centeredExp a₂) x =
      finiteType 1 (fun i : Fin (1 + 1) => if i = 0 then 1 / a₁ else 1 / a₂)
        (x + a₁ + a₂) := by
  have _ : a₂ ≠ 0 := ha₂
  intro x
  have hfirst : conv (centeredExp a₁) (centeredExp a₂) x =
      conv (expKernel (1 / a₁)) (expKernel (1 / a₂)) (x + a₁ + a₂) := by
    rw [conv_shift a₁ ha₁ (centeredExp a₂) x]
    unfold conv centeredExp
    apply integral_congr_ae
    filter_upwards with t
    congr 2
    ring
  constructor
  · exact hfirst
  · rw [hfirst]
    simp [finiteType]


theorem exp_halfline (a y : ℝ) (ha : a ≠ 0) :
    (0 < a → IntegrableOn (fun s : ℝ => Real.exp (a * s)) (Set.Iic y)) ∧
      (a < 0 → IntegrableOn (fun s : ℝ => Real.exp (a * s)) (Set.Ici y)) := by
  have _ : a ≠ 0 := ha
  constructor
  · intro ha_pos
    have hopen : IntegrableOn (fun u : ℝ => Real.exp (-a * u)) (Set.Ioi (-y)) :=
      exp_neg_integrableOn_Ioi (-y) ha_pos
    have hclosed : IntegrableOn (fun u : ℝ => Real.exp (-a * u)) (Set.Ici (-y)) := by
      rw [← Set.Ioi_union_left, MeasureTheory.integrableOn_union]
      exact ⟨hopen, MeasureTheory.integrableOn_singleton (hx := by simp)⟩
    simpa using hclosed.comp_neg_Iic
  · intro ha_neg
    have hpos : 0 < -a := neg_pos.mpr ha_neg
    have hopen : IntegrableOn (fun s : ℝ => Real.exp (-(-a) * s)) (Set.Ioi y) :=
      exp_neg_integrableOn_Ioi y hpos
    have hclosed : IntegrableOn (fun s : ℝ => Real.exp (-(-a) * s)) (Set.Ici y) := by
      rw [← Set.Ioi_union_left, MeasureTheory.integrableOn_union]
      exact ⟨hopen, MeasureTheory.integrableOn_singleton (hx := by simp)⟩
    simpa using hclosed
