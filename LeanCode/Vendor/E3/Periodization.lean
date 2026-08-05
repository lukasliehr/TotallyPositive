import LeanCode.Vendor.E3.Fiberization

open MeasureTheory
open scoped ENNReal Interval

namespace VendorE3
noncomputable section




def fourierKernel (m : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ))


def periodization (H : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' l : ℤ, H (x - (l : ℝ))

private lemma summable_of_tsum_enorm_lt_top {f : ℤ → ℂ}
    (h : (∑' l : ℤ, ‖f l‖ₑ) < ∞) : Summable f := by
  have hne : (∑' l : ℤ, (‖f l‖₊ : ℝ≥0∞)) ≠ ∞ := by
    exact ne_of_lt (by simpa [enorm_eq_nnnorm] using h)
  have hnn : Summable (fun l : ℤ => ‖f l‖₊) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hne
  have hr : Summable (fun l : ℤ => (‖f l‖₊ : ℝ)) :=
    NNReal.summable_coe.mpr hnn
  exact Summable.of_norm (by simpa using hr)



theorem periodization_integrable
    {H : ℝ → ℂ} (hH : Integrable H (volume : Measure ℝ)) :
    Integrable (fun x : ℝ => periodization H x)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hterm_strong : ∀ l : ℤ,
      AEStronglyMeasurable (fun x : ℝ => H (x - (l : ℝ))) μI := by
    intro l
    have hqmp :
        Measure.QuasiMeasurePreserving (fun x : ℝ => x - (l : ℝ)) μI volume := by
      exact (measurePreserving_sub_right (volume : Measure ℝ) (l : ℝ)).quasiMeasurePreserving.mono_left
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    simpa [Function.comp_def] using
      (hH.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp)
  have hper_meas : AEStronglyMeasurable (fun x : ℝ => periodization H x) μI := by
    unfold periodization
    exact AEStronglyMeasurable.tsum hterm_strong
  have hfinite_total : (∫⁻ t : ℝ, ‖H t‖ₑ ∂volume) < ∞ := by
    exact hasFiniteIntegral_iff_enorm.mp hH.hasFiniteIntegral
  have hterm_ae : ∀ l : ℤ,
      AEMeasurable (fun x : ℝ => ‖H (x - (l : ℝ))‖ₑ) μI := by
    intro l
    exact (hterm_strong l).enorm
  have hlintegral_tsum :
      (∫⁻ x : ℝ, (∑' l : ℤ, ‖H (x - (l : ℝ))‖ₑ) ∂μI) =
        ∑' l : ℤ, ∫⁻ x : ℝ, ‖H (x - (l : ℝ))‖ₑ ∂μI := by
    exact lintegral_tsum hterm_ae
  have htiling := lintegral_eq_tsum_lintegral_Ioc_sub_int_noMeas
    (fun t : ℝ => ‖H t‖ₑ)
  have hsum_integral_ne_top :
      (∑' l : ℤ, ∫⁻ x : ℝ, ‖H (x - (l : ℝ))‖ₑ ∂μI) ≠ ∞ := by
    rw [← htiling]
    exact ne_of_lt hfinite_total
  have hsum_fun_lt_top :
      (∫⁻ x : ℝ, (∑' l : ℤ, ‖H (x - (l : ℝ))‖ₑ) ∂μI) < ∞ := by
    rw [hlintegral_tsum]
    exact lt_top_iff_ne_top.mpr hsum_integral_ne_top
  have hnorm_le : ∀ᵐ x ∂μI,
      ‖periodization H x‖ₑ ≤ ∑' l : ℤ, ‖H (x - (l : ℝ))‖ₑ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    unfold periodization
    exact enorm_tsum_le_tsum_enorm
  have hfinite_periodization : HasFiniteIntegral (fun x : ℝ => periodization H x) μI := by
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt (lintegral_mono_ae hnorm_le) hsum_fun_lt_top
  exact ⟨hper_meas, hfinite_periodization⟩


theorem periodization_ae_summable
    {H : ℝ → ℂ} (hH : Integrable H (volume : Measure ℝ)) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      Summable (fun l : ℤ => H (x - (l : ℝ))) := by
  let μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hfinite_total : (∫⁻ t : ℝ, ‖H t‖ₑ ∂volume) < ∞ := by
    exact hasFiniteIntegral_iff_enorm.mp hH.hasFiniteIntegral
  have hterm_ae : ∀ l : ℤ,
      AEMeasurable (fun x : ℝ => ‖H (x - (l : ℝ))‖ₑ) μI := by
    intro l
    have hqmp :
        Measure.QuasiMeasurePreserving (fun x : ℝ => x - (l : ℝ)) μI volume := by
      exact (measurePreserving_sub_right (volume : Measure ℝ) (l : ℝ)).quasiMeasurePreserving.mono_left
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    simpa [Function.comp_def] using
      (hH.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving hqmp)
  have hlintegral_tsum :
      (∫⁻ x : ℝ, (∑' l : ℤ, ‖H (x - (l : ℝ))‖ₑ) ∂μI) =
        ∑' l : ℤ, ∫⁻ x : ℝ, ‖H (x - (l : ℝ))‖ₑ ∂μI := by
    exact lintegral_tsum hterm_ae
  have htiling := lintegral_eq_tsum_lintegral_Ioc_sub_int_noMeas
    (fun t : ℝ => ‖H t‖ₑ)
  have hsum_integral_ne_top :
      (∑' l : ℤ, ∫⁻ x : ℝ, ‖H (x - (l : ℝ))‖ₑ ∂μI) ≠ ∞ := by
    rw [← htiling]
    exact ne_of_lt hfinite_total
  have hsum_fun_ne_top :
      (∫⁻ x : ℝ, (∑' l : ℤ, ‖H (x - (l : ℝ))‖ₑ) ∂μI) ≠ ∞ := by
    rw [hlintegral_tsum]
    exact hsum_integral_ne_top
  have hsum_ae_meas :
      AEMeasurable (fun x : ℝ => ∑' l : ℤ, ‖H (x - (l : ℝ))‖ₑ) μI :=
    AEMeasurable.tsum hterm_ae
  filter_upwards [ae_lt_top' hsum_ae_meas hsum_fun_ne_top] with x hx
  exact summable_of_tsum_enorm_lt_top (f := fun l : ℤ => H (x - (l : ℝ))) hx

private theorem integral_eq_integral_periodization
    {F : ℝ → ℂ} (hF : Integrable F (volume : Measure ℝ)) :
    (∫ t : ℝ, F t ∂volume) =
      ∫ x : ℝ, periodization F x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hglobal :
      (∫ t : ℝ, F t ∂volume) =
        ∑' l : ℤ, ∫ x : ℝ, F (x - (l : ℝ)) ∂μI := by
    have hfd :=
      int_Ioc_fundamentalDomain.integral_eq_tsum'' F hF
    calc
      (∫ t : ℝ, F t ∂volume)
          = ∑' g : ℤ, ∫ x : ℝ, F (g +ᵥ x)
              ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
            simpa using hfd
      _ = ∑' g : ℤ, ∫ x : ℝ, F (x + (g : ℝ)) ∂μI := by
            apply tsum_congr
            intro g
            congr 1
            ext x
            change F ((g : ℝ) + x) = F (x + (g : ℝ))
            rw [add_comm]
      _ = ∑' l : ℤ, ∫ x : ℝ, F (x - (l : ℝ)) ∂μI := by
            have hneg :
                (∑' l : ℤ, ∫ x : ℝ, F (x - (l : ℝ)) ∂μI) =
                  ∑' g : ℤ, ∫ x : ℝ, F (x + (g : ℝ)) ∂μI := by
              simpa [Int.cast_neg, sub_eq_add_neg] using
                ((Equiv.neg ℤ).tsum_eq
                  (fun l : ℤ => ∫ x : ℝ, F (x - (l : ℝ)) ∂μI)).symm
            exact hneg.symm
  have hterm_strong : ∀ l : ℤ,
      AEStronglyMeasurable (fun x : ℝ => F (x - (l : ℝ))) μI := by
    intro l
    have hqmp :
        Measure.QuasiMeasurePreserving (fun x : ℝ => x - (l : ℝ)) μI volume := by
      exact (measurePreserving_sub_right (volume : Measure ℝ) (l : ℝ)).quasiMeasurePreserving.mono_left
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    simpa [Function.comp_def] using
      (hF.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp)
  have hfinite_total : (∫⁻ t : ℝ, ‖F t‖ₑ ∂volume) < ∞ := by
    exact hasFiniteIntegral_iff_enorm.mp hF.hasFiniteIntegral
  have hsum_integral_ne_top :
      (∑' l : ℤ, ∫⁻ x : ℝ, ‖F (x - (l : ℝ))‖ₑ ∂μI) ≠ ∞ := by
    rw [← lintegral_eq_tsum_lintegral_Ioc_sub_int_noMeas (fun t : ℝ => ‖F t‖ₑ)]
    exact ne_of_lt hfinite_total
  have hfold :
      (∫ x : ℝ, periodization F x ∂μI) =
        ∑' l : ℤ, ∫ x : ℝ, F (x - (l : ℝ)) ∂μI := by
    unfold periodization
    exact integral_tsum hterm_strong hsum_integral_ne_top
  exact hglobal.trans hfold.symm

private lemma fourierKernel_periodic_int (m l : ℤ) (x : ℝ) :
    fourierKernel m (x - (l : ℝ)) = fourierKernel m x := by
  unfold fourierKernel
  rw [show (-2 * Real.pi * Complex.I * (m : ℂ) * ((x - (l : ℝ) : ℝ) : ℂ)) =
      (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) +
        ((m * l : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
    norm_num
    ring]
  rw [Complex.exp_add]
  have hfactor : Complex.exp (((m * l : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    simpa using Complex.exp_int_mul_two_pi_mul_I (m * l)
  simpa [Int.cast_mul] using hfactor

private lemma norm_fourierKernel (m : ℤ) (x : ℝ) :
    ‖fourierKernel m x‖ = 1 := by
  unfold fourierKernel
  rw [show (-2 * Real.pi * Complex.I * (m : ℂ) * (x : ℂ)) =
      Complex.I * ((-2 * Real.pi * (m : ℝ) * x : ℝ) : ℂ) by
    norm_num
    ring]
  simpa using Complex.norm_exp_I_mul_ofReal (-2 * Real.pi * (m : ℝ) * x)



theorem integral_periodization_fourierKernel
    {H : ℝ → ℂ} (hH : Integrable H (volume : Measure ℝ)) (m : ℤ) :
    (∫ t : ℝ, H t * fourierKernel m t ∂volume) =
      ∫ x : ℝ, periodization H x * fourierKernel m x
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hK_meas :
      AEStronglyMeasurable (fun t : ℝ => fourierKernel m t) (volume : Measure ℝ) := by
    unfold fourierKernel
    fun_prop
  have hK_bound : ∀ᵐ t ∂(volume : Measure ℝ), ‖fourierKernel m t‖ ≤ (1 : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro t
    rw [norm_fourierKernel]
  have hF : Integrable (fun t : ℝ => H t * fourierKernel m t) (volume : Measure ℝ) :=
    hH.mul_bdd hK_meas hK_bound
  calc
    (∫ t : ℝ, H t * fourierKernel m t ∂volume)
        = ∫ x : ℝ, periodization (fun t : ℝ => H t * fourierKernel m t) x
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
          integral_eq_integral_periodization hF
    _ = ∫ x : ℝ, periodization H x * fourierKernel m x
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall ?_
          intro x
          unfold periodization
          calc
            (∑' l : ℤ, H (x - (l : ℝ)) * fourierKernel m (x - (l : ℝ))) =
                ∑' l : ℤ, H (x - (l : ℝ)) * fourierKernel m x := by
                  apply tsum_congr
                  intro l
                  rw [fourierKernel_periodic_int]
            _ = (∑' l : ℤ, H (x - (l : ℝ))) * fourierKernel m x := by
                  rw [tsum_mul_right]

private lemma fourierCoeffOn_zero_one_eq_fourierKernel
    {u : ℝ → ℂ} (m : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u m =
      ∫ x : ℝ, u x * fourierKernel m x
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hab : (0 : ℝ) < 1 := by norm_num
  rw [fourierCoeffOn_eq_integral (f := u) (n := m) hab]
  rw [intervalIntegral.integral_of_le hab.le]
  simp only [sub_zero, div_one, one_smul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  simp [fourierKernel, smul_eq_mul]
  rw [← Complex.exp_conj]
  have hconj :
      (starRingEnd ℂ) (2 * ↑Real.pi * Complex.I * ↑m * ↑x) =
        -(2 * ↑Real.pi * Complex.I * ↑m * ↑x) := by
    rw [map_mul, map_mul, map_mul, map_mul]
    rw [map_ofNat]
    simp [Complex.conj_ofReal, Complex.conj_I]
  rw [hconj]
  ring



theorem parseval_Ioc_zero_one
    {u : ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    Summable (fun m : ℤ =>
      ‖∫ x : ℝ, u x * fourierKernel m x
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))‖ ^ 2) ∧
    (∑' m : ℤ,
      ‖∫ x : ℝ, u x * fourierKernel m x
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))‖ ^ 2) =
      ∫ x : ℝ, ‖u x‖ ^ 2 ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hab : (0 : ℝ) < 1 := by norm_num
  have hparseval :=
    hasSum_sq_fourierCoeffOn (a := (0 : ℝ)) (b := 1) (f := u) hab hu
  constructor
  · simpa [fourierCoeffOn_zero_one_eq_fourierKernel] using hparseval.summable
  · calc
      (∑' m : ℤ,
        ‖∫ x : ℝ, u x * fourierKernel m x
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))‖ ^ 2)
          = ∑' m : ℤ, ‖fourierCoeffOn hab u m‖ ^ 2 := by
              apply tsum_congr
              intro m
              rw [fourierCoeffOn_zero_one_eq_fourierKernel]
      _ = (1 - 0 : ℝ)⁻¹ • ∫ x : ℝ in (0 : ℝ)..1, ‖u x‖ ^ 2 :=
              hparseval.tsum_eq
      _ = ∫ x : ℝ, ‖u x‖ ^ 2 ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
              rw [intervalIntegral.integral_of_le hab.le]
              simp

end

end VendorE3
