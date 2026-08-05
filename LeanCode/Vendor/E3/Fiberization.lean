import LeanCode.Vendor.E3.Defs

open MeasureTheory
open scoped NNReal ENNReal

namespace VendorE3
noncomputable section







instance intAddActionReal : AddAction ℤ ℝ where
  vadd n x := (n : ℝ) + x
  zero_vadd := by
    intro x
    change (((0 : ℤ) : ℝ) + x = x)
    simp
  add_vadd := by
    intro m n x
    change ((((m + n : ℤ) : ℝ) + x) = (m : ℝ) + ((n : ℝ) + x))
    norm_num
    ring

instance intMeasurableConstVAddReal : MeasurableConstVAdd ℤ ℝ where
  measurable_const_vadd := by
    intro c
    change Measurable (fun x : ℝ => (c : ℝ) + x)
    fun_prop

instance intVAddInvariantVolumeReal :
    VAddInvariantMeasure ℤ ℝ (volume : Measure ℝ) where
  measure_preimage_vadd := by
    intro c s hs
    change volume ((fun x : ℝ => (c : ℝ) + x) ⁻¹' s) = volume s
    exact (measurePreserving_add_left (volume : Measure ℝ) (c : ℝ)).measure_preimage
      hs.nullMeasurableSet



lemma existsUnique_int_vadd_mem_Ioc (x : ℝ) :
    ∃! g : ℤ, g +ᵥ x ∈ Set.Ioc (0 : ℝ) 1 := by
  let g : ℤ := Int.floor (1 - x)
  refine ⟨g, ?_, ?_⟩
  · constructor
    · have hlt : (1 - x : ℝ) < g + 1 := Int.lt_floor_add_one (1 - x)
      change 0 < (g : ℝ) + x
      linarith
    · have hle : (g : ℝ) ≤ 1 - x := Int.floor_le (1 - x)
      change (g : ℝ) + x ≤ 1
      linarith
  · intro y hy
    change (y : ℝ) + x ∈ Set.Ioc (0 : ℝ) 1 at hy
    have hy0 : 0 < (y : ℝ) + x := hy.1
    have hy1 : (y : ℝ) + x ≤ 1 := hy.2
    have hle_y : (y : ℝ) ≤ 1 - x := by linarith
    have hlt_y : 1 - x < (y : ℝ) + 1 := by linarith
    have hy_le_g : y ≤ g := Int.le_floor.mpr hle_y
    have hg_lt_y1 : g < y + 1 := by
      rw [Int.floor_lt]
      simpa [Int.cast_add, Int.cast_one] using hlt_y
    have hg_le_y : g ≤ y := Int.lt_add_one_iff.mp hg_lt_y1
    exact le_antisymm hy_le_g hg_le_y


lemma int_Ioc_fundamentalDomain :
    IsAddFundamentalDomain ℤ (Set.Ioc (0 : ℝ) 1) (volume : Measure ℝ) := by
  refine IsAddFundamentalDomain.mk' measurableSet_Ioc.nullMeasurableSet ?_
  exact existsUnique_int_vadd_mem_Ioc




theorem lintegral_eq_tsum_lintegral_Ioc_sub_int_noMeas
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ t : ℝ, F t ∂volume) =
      ∑' l : ℤ,
        ∫⁻ x : ℝ, F (x - (l : ℝ)) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have h := int_Ioc_fundamentalDomain.lintegral_eq_tsum'' F
  rw [h]
  have hcomm :
      (∑' g : ℤ,
        ∫⁻ x : ℝ, F (g +ᵥ x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) =
      ∑' g : ℤ,
        ∫⁻ x : ℝ, F (x + (g : ℝ)) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply tsum_congr
    intro g
    congr 1
    ext x
    change F ((g : ℝ) + x) = F (x + (g : ℝ))
    rw [add_comm]
  have hneg :
      (∑' l : ℤ,
        ∫⁻ x : ℝ, F (x - (l : ℝ)) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) =
      ∑' g : ℤ,
        ∫⁻ x : ℝ, F (x + (g : ℝ)) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    simpa [Int.cast_neg, sub_eq_add_neg] using
      ((Equiv.neg ℤ).tsum_eq
        (fun l : ℤ =>
          ∫⁻ x : ℝ, F (x - (l : ℝ))
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))).symm
  exact hcomm.trans hneg.symm


def fiberCoordinate (f : ℝ → ℂ) (x : ℝ) (l : ℤ) : ℂ :=
  star (f (x - (l : ℝ)))


def fiberNormSq (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ∑' l : ℤ, ‖fiberCoordinate f x l‖ ^ 2



theorem lintegral_eq_tsum_lintegral_Ioc_sub_int
    (F : ℝ → ℝ≥0∞) (_hF : Measurable F) :
    (∫⁻ t : ℝ, F t ∂volume) =
      ∑' l : ℤ,
        ∫⁻ x : ℝ, F (x - (l : ℝ)) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  exact lintegral_eq_tsum_lintegral_Ioc_sub_int_noMeas F


theorem measurable_fiber_norm_tsum
    {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (fun x : ℝ => fiberNormSq f x) := by
  unfold fiberNormSq fiberCoordinate
  apply Measurable.tsum
  intro l
  fun_prop

private lemma memLp_lintegral_sq_lt_top (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    (∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume) < ∞ := by
  have hint : Integrable (fun t : ℝ => ‖f t‖ ^ 2) (volume : Measure ℝ) := by
    exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  exact Integrable.lintegral_lt_top hint

private lemma shifted_sq_aemeasurable (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (l : ℤ) :
    AEMeasurable (fun x : ℝ => ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hqmp :
      Measure.QuasiMeasurePreserving (fun x : ℝ => x - (l : ℝ)) μI volume := by
    exact (measurePreserving_sub_right (volume : Measure ℝ) (l : ℝ)).quasiMeasurePreserving.mono_left
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hstrong : AEStronglyMeasurable (fun x : ℝ => f (x - (l : ℝ))) μI := by
    simpa [Function.comp_def] using
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp)
  exact ((hstrong.norm.aemeasurable.pow_const (2 : ℕ)).ennreal_ofReal)

private lemma ae_fiber_square_sum_ne_top (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      (∑' l : ℤ, ENNReal.ofReal (‖fiberCoordinate f x l‖ ^ 2)) ≠ ∞ := by
  let μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hterm_ae : ∀ l : ℤ,
      AEMeasurable (fun x : ℝ => ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2)) μI := by
    intro l
    exact shifted_sq_aemeasurable f hf l
  have hlintegral_tsum :
      (∫⁻ x : ℝ, (∑' l : ℤ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2)) ∂μI) =
        ∑' l : ℤ, ∫⁻ x : ℝ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2) ∂μI := by
    exact lintegral_tsum hterm_ae
  have htiling := lintegral_eq_tsum_lintegral_Ioc_sub_int_noMeas
    (fun t : ℝ => ENNReal.ofReal (‖f t‖ ^ 2))
  have hglobal_lt :
      (∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume) < ∞ :=
    memLp_lintegral_sq_lt_top f hf
  have hsum_integral_ne_top :
      (∑' l : ℤ, ∫⁻ x : ℝ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2) ∂μI) ≠ ∞ := by
    rw [← htiling]
    exact ne_of_lt hglobal_lt
  have hsum_fun_ne_top :
      (∫⁻ x : ℝ, (∑' l : ℤ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2)) ∂μI) ≠ ∞ := by
    rw [hlintegral_tsum]
    exact hsum_integral_ne_top
  have hsum_ae_meas :
      AEMeasurable
        (fun x : ℝ => ∑' l : ℤ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2)) μI :=
    AEMeasurable.tsum hterm_ae
  filter_upwards [ae_lt_top' hsum_ae_meas hsum_fun_ne_top] with x hx
  have hne : (∑' l : ℤ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2)) ≠ ∞ :=
    ne_of_lt hx
  simpa [fiberCoordinate] using hne

private lemma summable_sq_of_tsum_ofReal_ne_top (f : ℝ → ℂ) (x : ℝ)
    (h : (∑' l : ℤ, ENNReal.ofReal (‖fiberCoordinate f x l‖ ^ 2)) ≠ ∞) :
    Summable (fun l : ℤ => ‖fiberCoordinate f x l‖ ^ 2) := by
  let a : ℤ → ℝ≥0 := fun l => Real.toNNReal (‖fiberCoordinate f x l‖ ^ 2)
  have hcoe : (∑' l : ℤ, (a l : ℝ≥0∞)) ≠ ∞ := by
    simpa [a, ENNReal.ofReal] using h
  have hnn : Summable a := ENNReal.tsum_coe_ne_top_iff_summable.mp hcoe
  have hr : Summable (fun l : ℤ => (a l : ℝ)) := NNReal.summable_coe.mpr hnn
  convert hr using 1
  ext l
  simp [a, Real.toNNReal_of_nonneg (sq_nonneg _)]

private def fiberOfSummable (f : ℝ → ℂ) (x : ℝ)
    (h : Summable (fun l : ℤ => ‖fiberCoordinate f x l‖ ^ 2)) :
    ellp (2 : ℝ≥0∞) := by
  refine ⟨fun l : ℤ => fiberCoordinate f x l, ?_⟩
  exact memℓp_gen (by simpa using h)

private lemma fiberOfSummable_norm_sq (f : ℝ → ℂ) (x : ℝ)
    (h : Summable (fun l : ℤ => ‖fiberCoordinate f x l‖ ^ 2)) :
    ‖fiberOfSummable f x h‖ ^ 2 =
      ∑' l : ℤ, ‖fiberCoordinate f x l‖ ^ 2 := by
  have hnorm : ‖fiberOfSummable f x h‖ ^ 2 =
      ∑' l : ℤ, ‖(fiberOfSummable f x h) l‖ ^ 2 := by
    simpa using
      (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ)
        (by norm_num) (fiberOfSummable f x h))
  calc
    ‖fiberOfSummable f x h‖ ^ 2 =
        ∑' l : ℤ, ‖(fiberOfSummable f x h) l‖ ^ 2 := hnorm
    _ = ∑' l : ℤ, ‖fiberCoordinate f x l‖ ^ 2 := by
      apply tsum_congr
      intro l
      rfl

private def fiberFromSummablePredicate (f : ℝ → ℂ) (x : ℝ) :
    ellp (2 : ℝ≥0∞) := by
  classical
  exact if h : Summable (fun l : ℤ => ‖fiberCoordinate f x l‖ ^ 2) then
    fiberOfSummable f x h
  else 0

private lemma fiberFromSummablePredicate_apply_of_summable (f : ℝ → ℂ) (x : ℝ)
    (h : Summable (fun l : ℤ => ‖fiberCoordinate f x l‖ ^ 2)) (l : ℤ) :
    fiberFromSummablePredicate f x l = fiberCoordinate f x l := by
  classical
  simp [fiberFromSummablePredicate, h, fiberOfSummable]

private lemma fiberFromSummablePredicate_norm_integrand_eq_tsum_of_summable
    (f : ℝ → ℂ) (x : ℝ)
    (h : Summable (fun l : ℤ => ‖fiberCoordinate f x l‖ ^ 2)) :
    ENNReal.ofReal (‖fiberFromSummablePredicate f x‖ ^ 2) =
      ∑' l : ℤ, ENNReal.ofReal (‖fiberCoordinate f x l‖ ^ 2) := by
  classical
  calc
    ENNReal.ofReal (‖fiberFromSummablePredicate f x‖ ^ 2) =
        ENNReal.ofReal (∑' l : ℤ, ‖fiberCoordinate f x l‖ ^ 2) := by
          congr 1
          simp [fiberFromSummablePredicate, h, fiberOfSummable_norm_sq]
    _ = ∑' l : ℤ, ENNReal.ofReal (‖fiberCoordinate f x l‖ ^ 2) := by
      exact ENNReal.ofReal_tsum_of_nonneg (fun l => sq_nonneg _) h


theorem fiberization_L2
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    ∃ fiber : ℝ → ellp (2 : ℝ≥0∞),
      (∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        ∀ l : ℤ, fiber x l = fiberCoordinate f x l) ∧
      (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) =
        ∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume := by
  let μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let fiber : ℝ → ellp (2 : ℝ≥0∞) := fiberFromSummablePredicate f
  refine ⟨fiber, ?_, ?_⟩
  · filter_upwards [ae_fiber_square_sum_ne_top f hf] with x hx l
    exact fiberFromSummablePredicate_apply_of_summable f x
      (summable_sq_of_tsum_ofReal_ne_top f x hx) l
  · have hnorm_ae :
        ∀ᵐ x ∂μI,
          ENNReal.ofReal (‖fiber x‖ ^ 2) =
            ∑' l : ℤ, ENNReal.ofReal (‖fiberCoordinate f x l‖ ^ 2) := by
      filter_upwards [ae_fiber_square_sum_ne_top f hf] with x hx
      exact fiberFromSummablePredicate_norm_integrand_eq_tsum_of_summable f x
        (summable_sq_of_tsum_ofReal_ne_top f x hx)
    have hterm_ae : ∀ l : ℤ,
        AEMeasurable (fun x : ℝ => ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2)) μI := by
      intro l
      exact shifted_sq_aemeasurable f hf l
    have hlintegral_tsum :
        (∫⁻ x : ℝ, (∑' l : ℤ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2)) ∂μI) =
          ∑' l : ℤ, ∫⁻ x : ℝ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2) ∂μI := by
      exact lintegral_tsum hterm_ae
    have hcoord_tsum :
        (fun x : ℝ => ∑' l : ℤ, ENNReal.ofReal (‖fiberCoordinate f x l‖ ^ 2)) =
          (fun x : ℝ => ∑' l : ℤ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2)) := by
      funext x
      apply tsum_congr
      intro l
      simp [fiberCoordinate]
    have htiling := lintegral_eq_tsum_lintegral_Ioc_sub_int_noMeas
      (fun t : ℝ => ENNReal.ofReal (‖f t‖ ^ 2))
    calc
      (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) =
          ∫⁻ x : ℝ, (∑' l : ℤ, ENNReal.ofReal (‖fiberCoordinate f x l‖ ^ 2)) ∂μI :=
            lintegral_congr_ae hnorm_ae
      _ = ∫⁻ x : ℝ, (∑' l : ℤ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2)) ∂μI := by
            rw [hcoord_tsum]
      _ = ∑' l : ℤ, ∫⁻ x : ℝ, ENNReal.ofReal (‖f (x - (l : ℝ))‖ ^ 2) ∂μI :=
            hlintegral_tsum
      _ = ∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume :=
            htiling.symm

end

end VendorE3
