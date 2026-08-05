import LeanCode.Vocab
import LeanCode.Scaling















open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace Assembly.Hard_ScalingFrame




def dilFun (c : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => (Real.sqrt c : ℂ) * f (c * t)

theorem dilFun_eq_smul_comp (c : ℝ) (f : ℝ → ℂ) :
    dilFun c f = (Real.sqrt c : ℂ) • (fun t => f (c * t)) := by
  funext t; simp [dilFun, smul_eq_mul]



theorem qmp_mul {c : ℝ} (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => c * t) (volume : Measure ℝ) volume := by
  refine ⟨measurable_const_mul c, ?_⟩
  rw [Real.map_volume_mul_left hc]
  exact Measure.smul_absolutelyContinuous


theorem dilFun_congr {c : ℝ} (hc : c ≠ 0) {f₁ f₂ : ℝ → ℂ} (h : f₁ =ᵐ[(volume : Measure ℝ)] f₂) :
    dilFun c f₁ =ᵐ[(volume : Measure ℝ)] dilFun c f₂ := by
  have hcomp : (fun t => f₁ (c * t)) =ᵐ[(volume : Measure ℝ)] (fun t => f₂ (c * t)) :=
    (qmp_mul hc).ae_eq h
  filter_upwards [hcomp] with t ht
  simp only [dilFun, ht]



private theorem dil_coeff_one {c : ℝ} (hc : 0 < c) :
    (‖(Real.sqrt c : ℂ)‖ₑ) * ENNReal.ofReal |c⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal = 1 := by
  have hsc : ‖(Real.sqrt c : ℂ)‖ₑ = ENNReal.ofReal (Real.sqrt c) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg c)]
  have hhalf : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by
    rw [one_div, ENNReal.toReal_inv]; norm_num
  have habs : |c⁻¹| = c⁻¹ := abs_of_pos (inv_pos.mpr hc)
  rw [hsc, hhalf, habs,
      ENNReal.ofReal_rpow_of_nonneg (le_of_lt (inv_pos.mpr hc)) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  have hreal : Real.sqrt c * c⁻¹ ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_inv, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hc))]
  rw [hreal, ENNReal.ofReal_one]


theorem eLpNorm_dilFun {c : ℝ} (hc : 0 < c) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (dilFun c f) 2 (volume : Measure ℝ) = eLpNorm f 2 volume := by
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [dilFun_eq_smul_comp, eLpNorm_const_smul]
  have hae : AEStronglyMeasurable f (Measure.map (fun x => c * x) volume) := by
    rw [Real.map_volume_mul_left hcne]; exact hf.smul_measure _
  have hcomp : eLpNorm (fun t => f (c * t)) 2 volume
      = eLpNorm f 2 (Measure.map (fun x => c * x) volume) := by
    rw [eLpNorm_map_measure hae (measurable_const_mul c).aemeasurable]; rfl
  rw [hcomp, Real.map_volume_mul_left hcne,
      eLpNorm_smul_measure_of_ne_top (by norm_num) f _, smul_eq_mul, ← mul_assoc,
      dil_coeff_one hc, one_mul]


theorem memLp_dilFun {c : ℝ} (hc : 0 < c) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (dilFun c f) 2 volume := by
  refine ⟨?_, ?_⟩
  · rw [dilFun_eq_smul_comp]
    exact AEStronglyMeasurable.const_smul
      (hf.1.comp_quasiMeasurePreserving (qmp_mul (ne_of_gt hc))) _
  · rw [eLpNorm_dilFun hc f hf.1]; exact hf.2



theorem dilFun_dilFun_inv {c : ℝ} (hc : 0 < c) (f : ℝ → ℂ) :
    dilFun (1 / c) (dilFun c f) = f := by
  funext t
  simp only [dilFun]
  have harg : c * (1 / c * t) = t := by field_simp
  rw [harg]
  have hsqrt : (Real.sqrt (1 / c) : ℂ) * (Real.sqrt c : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have : Real.sqrt (1 / c) * Real.sqrt c = 1 := by
      rw [one_div, Real.sqrt_inv, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hc))]
    rw [this, Complex.ofReal_one]
  rw [← mul_assoc, hsqrt, one_mul]





def dilLp (c : ℝ) (hc : 0 < c) (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_dilFun hc (Lp.memLp f)).toLp (dilFun c (f : ℝ → ℂ))

theorem dilLp_coeFn {c : ℝ} (hc : 0 < c) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    dilLp c hc f =ᵐ[(volume : Measure ℝ)] dilFun c (f : ℝ → ℂ) :=
  MemLp.coeFn_toLp _


theorem dilLp_add {c : ℝ} (hc : 0 < c) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    dilLp c hc (f + g) = dilLp c hc f + dilLp c hc g := by
  apply Lp.ext_iff.mpr
  have h1 : dilLp c hc (f + g) =ᵐ[(volume : Measure ℝ)] dilFun c ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    dilLp_coeFn hc _
  have h2 : dilFun c ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)] dilFun c ((f : ℝ → ℂ) + (g : ℝ → ℂ)) :=
    dilFun_congr (ne_of_gt hc) (Lp.coeFn_add f g)
  have h3 : dilFun c ((f : ℝ → ℂ) + (g : ℝ → ℂ))
      =ᵐ[(volume : Measure ℝ)] dilFun c (f : ℝ → ℂ) + dilFun c (g : ℝ → ℂ) := by
    filter_upwards with t
    simp only [dilFun, Pi.add_apply, mul_add]
  have h4 : dilFun c (f : ℝ → ℂ) + dilFun c (g : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)] (dilLp c hc f + dilLp c hc g : Lp ℂ 2 (volume : Measure ℝ)) := by
    have hf := (dilLp_coeFn hc f).symm
    have hg := (dilLp_coeFn hc g).symm
    filter_upwards [hf, hg, Lp.coeFn_add (dilLp c hc f) (dilLp c hc g)]
      with t htf htg htadd
    rw [Pi.add_apply, htf, htg, htadd, Pi.add_apply]
  exact h1.trans (h2.trans (h3.trans h4))


theorem dilLp_smul {c : ℝ} (hc : 0 < c) (r : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    dilLp c hc (r • f) = r • dilLp c hc f := by
  apply Lp.ext_iff.mpr
  have h1 : dilLp c hc (r • f) =ᵐ[(volume : Measure ℝ)] dilFun c ((r • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    dilLp_coeFn hc _
  have h2 : dilFun c ((r • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)] dilFun c (r • (f : ℝ → ℂ)) :=
    dilFun_congr (ne_of_gt hc) (Lp.coeFn_smul r f)
  have h3 : dilFun c (r • (f : ℝ → ℂ)) =ᵐ[(volume : Measure ℝ)] r • dilFun c (f : ℝ → ℂ) := by
    filter_upwards with t
    simp only [dilFun, Pi.smul_apply, smul_eq_mul]; ring
  have h4 : r • dilFun c (f : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] (r • dilLp c hc f : Lp ℂ 2 (volume : Measure ℝ)) := by
    filter_upwards [(dilLp_coeFn hc f).symm, Lp.coeFn_smul r (dilLp c hc f)]
      with t htf htsmul
    rw [Pi.smul_apply, smul_eq_mul, htf, htsmul, Pi.smul_apply, smul_eq_mul]
  exact h1.trans (h2.trans (h3.trans h4))

theorem dilLp_norm {c : ℝ} (hc : 0 < c) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖dilLp c hc f‖ = ‖f‖ := by
  rw [dilLp, Lp.norm_toLp, eLpNorm_dilFun hc _ (Lp.memLp f).1, ← Lp.norm_def]


def dilLpₗ (c : ℝ) (hc : 0 < c) : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun := dilLp c hc
  map_add' := dilLp_add hc
  map_smul' r f := dilLp_smul hc r f


def dilLpₗᵢ (c : ℝ) (hc : 0 < c) : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toLinearMap := dilLpₗ c hc
  norm_map' := dilLp_norm hc




theorem dilLp_comp_eq {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hid : ∀ f : ℝ → ℂ, dilFun d (dilFun c f) = f) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    dilLp d hd (dilLp c hc f) = f := by
  apply Lp.ext_iff.mpr
  have h1 : dilLp d hd (dilLp c hc f)
      =ᵐ[(volume : Measure ℝ)] dilFun d ((dilLp c hc f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    dilLp_coeFn _ _
  have h2 : dilFun d ((dilLp c hc f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)] dilFun d (dilFun c (f : ℝ → ℂ)) :=
    dilFun_congr (ne_of_gt hd) (dilLp_coeFn hc f)
  refine h1.trans (h2.trans ?_)
  rw [hid]



def dilation (c : ℝ) (hc : 0 < c) : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  refine LinearIsometryEquiv.ofSurjective (dilLpₗᵢ c hc) ?_
  intro y
  have hc' : 0 < 1 / c := by positivity
  refine ⟨dilLp (1 / c) hc' y, ?_⟩

  show dilLp c hc (dilLp (1 / c) hc' y) = y

  refine dilLp_comp_eq hc' hc (fun f => ?_) y
  have h := dilFun_dilFun_inv hc' f
  have hcc : (1 : ℝ) / (1 / c) = c := by field_simp
  rwa [hcc] at h

@[simp] theorem dilation_apply (c : ℝ) (hc : 0 < c) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    dilation c hc f = dilLp c hc f := rfl



open Assembly in



theorem dilFun_gaborAtom {g : ℝ → ℝ} {α β : ℝ} (hβ : 0 < β) (m n : ℤ) :
    dilFun β (Assembly.GaborAtom (Assembly.Scaling.scaleWindow β g) (α * β) 1 m n)
      = Assembly.GaborAtom g α β m n := by
  funext t
  simp only [dilFun, Assembly.GaborAtom, Assembly.Scaling.scaleWindow]
  have hβne : β ≠ 0 := ne_of_gt hβ
  have harg : (β * t - α * β * (m : ℝ)) / β = t - α * (m : ℝ) := by field_simp
  rw [harg]
  have hexp : (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) * (n : ℂ) * ((β * t : ℝ) : ℂ))
      = (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (n : ℂ) * (t : ℂ)) := by push_cast; ring
  rw [hexp]
  have hsb : (Real.sqrt β : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hβ))
  push_cast
  field_simp

open Assembly in


theorem dilation_gaborAtom_L2 {g : ℝ → ℝ} {α β : ℝ} (hβ : 0 < β)
    (hg : Continuous g) (hpd : Assembly.HasPolynomialDecay g) (m n : ℤ) :
    dilation β hβ (Assembly.GaborAtom_L2 (Assembly.Scaling.scaleWindow β g)
        (Assembly.Scaling.continuous_scaleWindow hg)
        (Assembly.Scaling.hasPolynomialDecay_scaleWindow hβ hpd) (α * β) 1 m n)
      = Assembly.GaborAtom_L2 g hg hpd α β m n := by
  rw [dilation_apply]
  apply Lp.ext_iff.mpr


  have h1 := dilLp_coeFn hβ (Assembly.GaborAtom_L2 (Assembly.Scaling.scaleWindow β g)
      (Assembly.Scaling.continuous_scaleWindow hg)
      (Assembly.Scaling.hasPolynomialDecay_scaleWindow hβ hpd) (α * β) 1 m n)
  have hcoe : (Assembly.GaborAtom_L2 (Assembly.Scaling.scaleWindow β g)
      (Assembly.Scaling.continuous_scaleWindow hg)
      (Assembly.Scaling.hasPolynomialDecay_scaleWindow hβ hpd) (α * β) 1 m n : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)]
      Assembly.GaborAtom (Assembly.Scaling.scaleWindow β g) (α * β) 1 m n :=
    MemLp.coeFn_toLp _
  have h2 : dilFun β ((Assembly.GaborAtom_L2 (Assembly.Scaling.scaleWindow β g)
      (Assembly.Scaling.continuous_scaleWindow hg)
      (Assembly.Scaling.hasPolynomialDecay_scaleWindow hβ hpd) (α * β) 1 m n : ℝ → ℂ))
      =ᵐ[(volume : Measure ℝ)]
      dilFun β (Assembly.GaborAtom (Assembly.Scaling.scaleWindow β g) (α * β) 1 m n) :=
    dilFun_congr (ne_of_gt hβ) hcoe
  have h3 : dilFun β (Assembly.GaborAtom (Assembly.Scaling.scaleWindow β g) (α * β) 1 m n)
      = Assembly.GaborAtom g α β m n := dilFun_gaborAtom hβ m n
  have h4 : Assembly.GaborAtom g α β m n
      =ᵐ[(volume : Measure ℝ)] (Assembly.GaborAtom_L2 g hg hpd α β m n : ℝ → ℂ) :=
    (MemLp.coeFn_toLp _).symm
  calc (dilLp β hβ _ : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)] dilFun β _ := h1
    _ =ᵐ[(volume : Measure ℝ)] dilFun β (Assembly.GaborAtom (Assembly.Scaling.scaleWindow β g) (α * β) 1 m n) := h2
    _ = Assembly.GaborAtom g α β m n := h3
    _ =ᵐ[(volume : Measure ℝ)] (Assembly.GaborAtom_L2 g hg hpd α β m n : ℝ → ℂ) := h4



open Assembly in



theorem scaling_frame_transfer_proof
    (g : ℝ → ℝ) (α β : ℝ) (hβ : 0 < β)
    (hg : Continuous g) (hpd : Assembly.HasPolynomialDecay g)
    (hfr : Assembly.IsGaborFrame (Assembly.Scaling.scaleWindow β g)
      (Assembly.Scaling.continuous_scaleWindow hg)
      (Assembly.Scaling.hasPolynomialDecay_scaleWindow hβ hpd) (α * β) 1) :
    Assembly.IsGaborFrame g hg hpd α β := by
  obtain ⟨A, B, hA, hAB, hbound⟩ := hfr
  refine ⟨A, B, hA, hAB, ?_⟩
  intro x
  set U := dilation β hβ with hU

  set y : Lp ℂ 2 (volume : Measure ℝ) := U.symm x with hy
  have hnorm : ‖y‖ = ‖x‖ := by rw [hy]; exact U.symm.norm_map x

  have hinner : ∀ m n : ℤ,
      inner ℂ x (Assembly.GaborAtom_L2 g hg hpd α β m n)
        = inner ℂ y (Assembly.GaborAtom_L2 (Assembly.Scaling.scaleWindow β g)
            (Assembly.Scaling.continuous_scaleWindow hg)
            (Assembly.Scaling.hasPolynomialDecay_scaleWindow hβ hpd) (α * β) 1 m n) := by
    intro m n

    rw [← dilation_gaborAtom_L2 hβ hg hpd m n, ← hU]
    conv_lhs => rw [show x = U y by rw [hy, LinearIsometryEquiv.apply_symm_apply]]
    rw [U.inner_map_map]

  have hsum_eq : (∑' (m : ℤ) (n : ℤ),
        ‖inner ℂ x (Assembly.GaborAtom_L2 g hg hpd α β m n)‖ ^ 2)
      = ∑' (m : ℤ) (n : ℤ),
        ‖inner ℂ y (Assembly.GaborAtom_L2 (Assembly.Scaling.scaleWindow β g)
          (Assembly.Scaling.continuous_scaleWindow hg)
          (Assembly.Scaling.hasPolynomialDecay_scaleWindow hβ hpd) (α * β) 1 m n)‖ ^ 2 := by
    congr 1; funext m; congr 1; funext n; rw [hinner m n]
  rw [hsum_eq, ← hnorm]
  exact hbound y

end Assembly.Hard_ScalingFrame
