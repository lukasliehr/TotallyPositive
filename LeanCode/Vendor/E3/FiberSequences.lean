import LeanCode.Vendor.E3.FiberLowerBound
import LeanCode.Vendor.E3.Fiberization
import LeanCode.Vendor.E3.Periodization

open MeasureTheory
open scoped ENNReal

namespace VendorE3
noncomputable section







def fiberProduct (f : ℝ → ℂ) (g : ℝ → ℝ) (α : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  f t * star ((g (t - α * (n : ℝ)) : ℂ))


def fiberSequence (f : ℝ → ℂ) (g : ℝ → ℝ) (α : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  ∑' l : ℤ, f (x - (l : ℝ)) *
    star ((g (x - (l : ℝ) - α * (n : ℝ)) : ℂ))



def gaborCoefficient (f : ℝ → ℂ) (g : ℝ → ℝ) (α : ℝ) (m n : ℤ) : ℂ :=
  ∫ t : ℝ, f t * star (GaborAtom g α 1 n m t) ∂volume

private lemma modulation_star (m : ℤ) (t : ℝ) :
    star (Complex.exp (2 * Real.pi * Complex.I * (1 : ℂ) * (m : ℂ) * (t : ℂ))) =
      Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (t : ℂ)) := by
  calc
    star (Complex.exp (2 * Real.pi * Complex.I * (1 : ℂ) * (m : ℂ) * (t : ℂ)))
        = Complex.exp (star (2 * Real.pi * Complex.I * (1 : ℂ) * (m : ℂ) * (t : ℂ))) :=
          (Complex.exp_conj _).symm
    _ = Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (t : ℂ)) := by
      congr 1
      simp

private lemma star_GaborAtom_eq_kernel
    (g : ℝ → ℝ) (α t : ℝ) (m n : ℤ) :
    star (GaborAtom g α 1 n m t) =
      star ((g (t - α * (n : ℝ)) : ℂ)) * fourierKernel m t := by
  unfold GaborAtom fourierKernel
  rw [star_mul]
  rw [show star (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(1 : ℝ) * ↑m * ↑t)) =
      Complex.exp (-2 * ↑Real.pi * Complex.I * ↑m * ↑t) by
    simpa using modulation_star m t]

private lemma gabor_integrand_eq_fiberProduct_kernel
    (f : ℝ → ℂ) (g : ℝ → ℝ) (α t : ℝ) (m n : ℤ) :
    f t * star (GaborAtom g α 1 n m t) =
      fiberProduct f g α n t * fourierKernel m t := by
  unfold fiberProduct
  rw [star_GaborAtom_eq_kernel]
  ring


theorem memL2_of_polynomialDecay
    (g : ℝ → ℝ) (hg : Continuous g) (hgd : HasPolynomialDecay g) :
    MemLp (fun t : ℝ => (g t : ℂ)) 2 (volume : Measure ℝ) := by
  convert (memL2_GaborAtom g hg hgd 0 0 0 0) using 1
  funext t
  simp [GaborAtom]


theorem fiberSequence_measurable
    {f : ℝ → ℂ} {g : ℝ → ℝ} {α : ℝ} (n : ℤ)
    (hf : Measurable f) (hg : Continuous g) :
    Measurable (fun x : ℝ => fiberSequence f g α n x) := by
  unfold fiberSequence
  apply Measurable.tsum
  intro l
  fun_prop


theorem fiberProduct_integrable_periodization_eq
    {f : ℝ → ℂ} {g : ℝ → ℝ} {α : ℝ} (n : ℤ)
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : Continuous g) (hgd : HasPolynomialDecay g) :
    Integrable (fiberProduct f g α n) (volume : Measure ℝ) ∧
      ∀ x : ℝ, periodization (fiberProduct f g α n) x =
        fiberSequence f g α n x := by
  have hwin : MemLp (fun t : ℝ => (g (t - α * (n : ℝ)) : ℂ)) 2
      (volume : Measure ℝ) := by
    convert (memL2_GaborAtom g hg hgd α 0 n 0) using 1
    funext t
    simp [GaborAtom]
  have hint : Integrable (fun t : ℝ => f t * (g (t - α * (n : ℝ)) : ℂ))
      (volume : Measure ℝ) := by
    change Integrable (f * fun t : ℝ => (g (t - α * (n : ℝ)) : ℂ))
      (volume : Measure ℝ)
    exact hf.integrable_mul hwin
  constructor
  · unfold fiberProduct
    simpa using hint
  · intro x
    rfl


theorem fiberSequence_eq_preGramian_apply
    (f : ℝ → ℂ) (g : ℝ → ℝ) (α C σ : ℝ)
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ)
    (fiber : ℝ → ellp (2 : ℝ≥0∞))
    {x : ℝ} (hcoord : ∀ l : ℤ, fiber x l = fiberCoordinate f x l)
    (n : ℤ) :
    fiberSequence f g α n x =
      star ((preGramianOperator g α C σ hα hdec x (fiber x)) (-n)) := by
  have hP :=
    preGramianOperator_isMatrixOperator g α C σ hα hdec x (fiber x) (-n)
  rw [hP.2]
  rw [tsum_star]
  unfold fiberSequence
  apply tsum_congr
  intro l
  dsimp [preGramianMatrix, fiberCoordinate]
  rw [hcoord l]
  have harg :
      x + α * ((-n : ℤ) : ℝ) - (l : ℝ) =
        x - (l : ℝ) - α * (n : ℝ) := by
    norm_num
    ring
  rw [harg]
  simp [fiberCoordinate, mul_comm]


theorem fiberSequence_norm_tsum_eq_preGramian_norm
    (f : ℝ → ℂ) (g : ℝ → ℝ) (α C σ : ℝ)
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ)
    (fiber : ℝ → ellp (2 : ℝ≥0∞))
    {x : ℝ} (hcoord : ∀ l : ℤ, fiber x l = fiberCoordinate f x l) :
    (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2) =
      ‖preGramianOperator g α C σ hα hdec x (fiber x)‖ ^ 2 := by
  let v := preGramianOperator g α C σ hα hdec x (fiber x)
  have hpoint : ∀ n : ℤ,
      ‖fiberSequence f g α n x‖ ^ 2 = ‖v (-n)‖ ^ 2 := by
    intro n
    have hseq :=
      fiberSequence_eq_preGramian_apply f g α C σ hα hdec fiber hcoord n
    rw [hseq]
    simp [v]
  have hsum1 :
      (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2) =
        ∑' n : ℤ, ‖v (-n)‖ ^ 2 := by
    exact tsum_congr hpoint
  have hsum2 :
      (∑' n : ℤ, ‖v (-n)‖ ^ 2) =
        ∑' n : ℤ, ‖v n‖ ^ 2 := by
    exact (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ‖v n‖ ^ 2)
  have hnorm : ‖v‖ ^ 2 = ∑' n : ℤ, ‖v n‖ ^ 2 := by
    simpa using
      (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ)
        (by norm_num) v)
  calc
    (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2) =
        ∑' n : ℤ, ‖v (-n)‖ ^ 2 := hsum1
    _ = ∑' n : ℤ, ‖v n‖ ^ 2 := hsum2
    _ = ‖v‖ ^ 2 := hnorm.symm
    _ = ‖preGramianOperator g α C σ hα hdec x (fiber x)‖ ^ 2 := rfl


theorem fiberSequence_two_sided_estimates
    (f : ℝ → ℂ) (g : ℝ → ℝ) (α C σ : ℝ)
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : Continuous g) (hα : 0 < α)
    (hdec : HasDecayWithConstants g C σ)
    (hsub : SubmatrixCondition g α) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧
      A * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) ≤
        ∫ x : ℝ, (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
      (∫ x : ℝ, (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤
        B * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) := by
  let μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let S : ℝ → ℝ := fun x => ∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2
  obtain ⟨fiber, hcoord_ae, hfiber_norm⟩ := fiberization_L2 f hf
  obtain ⟨a, ha_pos, ha_le, hbounds⟩ :=
    preGramian_two_sided_bound_Icc g α C σ hg hα hdec hsub
  let A : ℝ := a ^ 2
  let B : ℝ := preGramianBesselBound C σ α
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, preGramianBesselBound]
    exact sq_nonneg _
  have hA_le_B : A ≤ B := by
    dsimp [A, B, preGramianBesselBound]
    have hM_pos : 0 < preGramianNormBound C σ α := lt_of_lt_of_le ha_pos ha_le
    nlinarith
  have hIoc : ∀ᵐ x ∂μI, x ∈ Set.Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  have hpoint_ae : ∀ᵐ x ∂μI,
      A * (‖fiber x‖ ^ 2) ≤ S x ∧ S x ≤ B * (‖fiber x‖ ^ 2) := by
    filter_upwards [hcoord_ae, hIoc] with x hcoord hxIoc
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hsum :=
      fiberSequence_norm_tsum_eq_preGramian_norm f g α C σ hα hdec fiber hcoord
    have hb := hbounds x hxIcc (fiber x)
    constructor
    · calc
        A * (‖fiber x‖ ^ 2) = a ^ 2 * ‖fiber x‖ ^ 2 := rfl
        _ ≤ ‖preGramianOperator g α C σ hα hdec x (fiber x)‖ ^ 2 := hb.1
        _ = S x := by
          dsimp [S]
          exact hsum.symm
    · calc
        S x = ‖preGramianOperator g α C σ hα hdec x (fiber x)‖ ^ 2 := by
          dsimp [S]
          exact hsum
        _ ≤ B * (‖fiber x‖ ^ 2) := by
          simpa [B] using hb.2
  have hS_nonneg : 0 ≤ S := by
    intro x
    dsimp [S]
    exact tsum_nonneg (fun n => sq_nonneg _)
  have hS_nonneg_ae : 0 ≤ᵐ[μI] S := Filter.Eventually.of_forall hS_nonneg
  have hS_ae : AEMeasurable S μI := by
    dsimp [S]
    apply AEMeasurable.tsum
    intro n
    have hprod :=
      fiberProduct_integrable_periodization_eq (f := f) (g := g) (α := α) n hf hg
        ⟨C, σ, hdec⟩
    have hper_int : Integrable (fun x : ℝ => periodization (fiberProduct f g α n) x) μI :=
      periodization_integrable hprod.1
    have hseq_int : Integrable (fun x : ℝ => fiberSequence f g α n x) μI := by
      convert hper_int using 1
      ext x
      exact hprod.2 x
    exact (hseq_int.aestronglyMeasurable.norm.aemeasurable.pow_const (2 : ℕ))
  have hF_int : Integrable (fun t : ℝ => ‖f t‖ ^ 2) (volume : Measure ℝ) := by
    exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hF_nonneg : 0 ≤ᵐ[(volume : Measure ℝ)] fun t : ℝ => ‖f t‖ ^ 2 :=
    Filter.Eventually.of_forall (fun t => sq_nonneg _)
  have hF_lintegral_eq :
      ENNReal.ofReal (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) =
        ∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF_int hF_nonneg
  have hF_lintegral_lt :
      (∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume) < ∞ := by
    exact Integrable.lintegral_lt_top hF_int
  have hfiber_lintegral_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) < ∞ := by
    rw [hfiber_norm]
    exact hF_lintegral_lt
  have hmajor_lintegral_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) ∂μI) < ∞ := by
    calc
      (∫⁻ x : ℝ, ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) ∂μI) =
          ∫⁻ x : ℝ, ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI := by
            apply lintegral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro x
            change ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) =
              ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2)
            exact ENNReal.ofReal_mul hB_nonneg
      _ = ENNReal.ofReal B *
          (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := by
            exact lintegral_const_mul' (ENNReal.ofReal B)
              (fun x : ℝ => ENNReal.ofReal (‖fiber x‖ ^ 2)) ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfiber_lintegral_lt
  have hS_lintegral_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI) < ∞ := by
    refine lt_of_le_of_lt ?_ hmajor_lintegral_lt
    apply lintegral_mono_ae
    filter_upwards [hpoint_ae] with x hx
    exact ENNReal.ofReal_le_ofReal hx.2
  have hS_int : Integrable S μI :=
    (lintegral_ofReal_ne_top_iff_integrable hS_ae.aestronglyMeasurable
      hS_nonneg_ae).mp (ne_of_lt hS_lintegral_lt)
  have hS_lintegral_eq :
      ENNReal.ofReal (∫ x : ℝ, S x ∂μI) =
        ∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hS_int hS_nonneg_ae
  have hS_integral_nonneg : 0 ≤ ∫ x : ℝ, S x ∂μI :=
    integral_nonneg hS_nonneg
  have hF_integral_nonneg : 0 ≤ ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume :=
    integral_nonneg (fun t => sq_nonneg _)
  have hlower_lintegral :
      ENNReal.ofReal A * (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) ≤
        ∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI := by
    calc
      ENNReal.ofReal A * (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) =
          ∫⁻ x : ℝ, ENNReal.ofReal A * ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI := by
            exact (lintegral_const_mul' (ENNReal.ofReal A)
              (fun x : ℝ => ENNReal.ofReal (‖fiber x‖ ^ 2)) ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ x : ℝ, ENNReal.ofReal (A * (‖fiber x‖ ^ 2)) ∂μI := by
            apply lintegral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro x
            change ENNReal.ofReal A * ENNReal.ofReal (‖fiber x‖ ^ 2) =
              ENNReal.ofReal (A * (‖fiber x‖ ^ 2))
            exact (ENNReal.ofReal_mul hA_nonneg).symm
      _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI := by
            apply lintegral_mono_ae
            filter_upwards [hpoint_ae] with x hx
            exact ENNReal.ofReal_le_ofReal hx.1
  have hupper_lintegral :
      (∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI) ≤
        ENNReal.ofReal B * (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := by
    calc
      (∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI) ≤
          ∫⁻ x : ℝ, ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) ∂μI := by
            apply lintegral_mono_ae
            filter_upwards [hpoint_ae] with x hx
            exact ENNReal.ofReal_le_ofReal hx.2
      _ = ∫⁻ x : ℝ, ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI := by
            apply lintegral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro x
            change ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) =
              ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2)
            exact ENNReal.ofReal_mul hB_nonneg
      _ = ENNReal.ofReal B *
          (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := by
            exact lintegral_const_mul' (ENNReal.ofReal B)
              (fun x : ℝ => ENNReal.ofReal (‖fiber x‖ ^ 2)) ENNReal.ofReal_ne_top
  have hlower_ofReal :
      ENNReal.ofReal (A * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume)) ≤
        ENNReal.ofReal (∫ x : ℝ, S x ∂μI) := by
    calc
      ENNReal.ofReal (A * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume)) =
          ENNReal.ofReal A * ENNReal.ofReal (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) := by
            exact ENNReal.ofReal_mul hA_nonneg
      _ = ENNReal.ofReal A *
          (∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume) := by
            rw [hF_lintegral_eq]
      _ = ENNReal.ofReal A *
          (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := by
            rw [hfiber_norm]
      _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI := hlower_lintegral
      _ = ENNReal.ofReal (∫ x : ℝ, S x ∂μI) := hS_lintegral_eq.symm
  have hupper_ofReal :
      ENNReal.ofReal (∫ x : ℝ, S x ∂μI) ≤
        ENNReal.ofReal (B * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume)) := by
    calc
      ENNReal.ofReal (∫ x : ℝ, S x ∂μI) =
          ∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI := hS_lintegral_eq
      _ ≤ ENNReal.ofReal B *
          (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := hupper_lintegral
      _ = ENNReal.ofReal B *
          (∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume) := by
            rw [hfiber_norm]
      _ = ENNReal.ofReal B * ENNReal.ofReal (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) := by
            rw [hF_lintegral_eq]
      _ = ENNReal.ofReal (B * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume)) := by
            exact (ENNReal.ofReal_mul hB_nonneg).symm
  refine ⟨A, B, hA_pos, hA_le_B, ?_, ?_⟩
  · dsimp [S] at hlower_ofReal ⊢
    exact (ENNReal.ofReal_le_ofReal_iff hS_integral_nonneg).mp hlower_ofReal
  · dsimp [S] at hupper_ofReal ⊢
    have hright_nonneg : 0 ≤ B * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) :=
      mul_nonneg hB_nonneg hF_integral_nonneg
    exact (ENNReal.ofReal_le_ofReal_iff hright_nonneg).mp hupper_ofReal


theorem fiberSequence_memLp
    (f : ℝ → ℂ) (g : ℝ → ℝ) (α C σ : ℝ)
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : Continuous g) (hα : 0 < α)
    (hdec : HasDecayWithConstants g C σ)
    (hsub : SubmatrixCondition g α) (n : ℤ) :
    MemLp (fun x : ℝ => fiberSequence f g α n x) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hprod :=
    fiberProduct_integrable_periodization_eq (f := f) (g := g) (α := α) n hf hg
      ⟨C, σ, hdec⟩
  have hper_int : Integrable (fun x : ℝ => periodization (fiberProduct f g α n) x) μI :=
    periodization_integrable hprod.1
  have hseq_int : Integrable (fun x : ℝ => fiberSequence f g α n x) μI := by
    convert hper_int using 1
    ext x
    exact hprod.2 x
  obtain ⟨fiber, hcoord_ae, hfiber_norm⟩ := fiberization_L2 f hf
  obtain ⟨a, _ha_pos, _ha_le, hbounds⟩ :=
    preGramian_two_sided_bound_Icc g α C σ hg hα hdec hsub
  let B : ℝ := preGramianBesselBound C σ α
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, preGramianBesselBound]
    exact sq_nonneg _
  have hIoc : ∀ᵐ x ∂μI, x ∈ Set.Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  have hseq_le_ae :
      ∀ᵐ x ∂μI,
        ENNReal.ofReal (‖fiberSequence f g α n x‖ ^ 2) ≤
          ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) := by
    filter_upwards [hcoord_ae, hIoc] with x hcoord hxIoc
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    let P := preGramianOperator g α C σ hα hdec x
    have hseq :=
      fiberSequence_eq_preGramian_apply f g α C σ hα hdec fiber hcoord n
    have hseqnorm :
        ‖fiberSequence f g α n x‖ ^ 2 = ‖(P (fiber x)) (-n)‖ ^ 2 := by
      rw [hseq]
      simp [P]
    have hcoord_sq_le : ‖(P (fiber x)) (-n)‖ ^ 2 ≤ ‖P (fiber x)‖ ^ 2 := by
      have hcoord_le := lp_norm_apply_le_norm_int (P (fiber x)) (-n)
      nlinarith [norm_nonneg ((P (fiber x)) (-n)), norm_nonneg (P (fiber x))]
    have hP_le : ‖P (fiber x)‖ ^ 2 ≤ B * (‖fiber x‖ ^ 2) := by
      simpa [P, B] using (hbounds x hxIcc (fiber x)).2
    have hreal : ‖fiberSequence f g α n x‖ ^ 2 ≤ B * (‖fiber x‖ ^ 2) := by
      calc
        ‖fiberSequence f g α n x‖ ^ 2 = ‖(P (fiber x)) (-n)‖ ^ 2 := hseqnorm
        _ ≤ ‖P (fiber x)‖ ^ 2 := hcoord_sq_le
        _ ≤ B * (‖fiber x‖ ^ 2) := hP_le
    exact ENNReal.ofReal_le_ofReal hreal
  have hglobal_sq_lt :
      (∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume) < ∞ := by
    have hint : Integrable (fun t : ℝ => ‖f t‖ ^ 2) (volume : Measure ℝ) := by
      exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    exact Integrable.lintegral_lt_top hint
  have hfiber_sq_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) < ∞ := by
    rw [hfiber_norm]
    exact hglobal_sq_lt
  have hmajor_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) ∂μI) < ∞ := by
    calc
      (∫⁻ x : ℝ, ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) ∂μI) =
          ∫⁻ x : ℝ, ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI := by
            apply lintegral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro x
            change ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) =
              ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2)
            exact ENNReal.ofReal_mul hB_nonneg
      _ = ENNReal.ofReal B *
          (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := by
            exact lintegral_const_mul' (ENNReal.ofReal B)
              (fun x : ℝ => ENNReal.ofReal (‖fiber x‖ ^ 2)) ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfiber_sq_lt
  have hseq_sq_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (‖fiberSequence f g α n x‖ ^ 2) ∂μI) < ∞ :=
    lt_of_le_of_lt (lintegral_mono_ae hseq_le_ae) hmajor_lt
  refine ⟨hseq_int.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (p := (2 : ℝ≥0∞)) two_ne_zero ENNReal.ofNat_ne_top]
  simpa [ofReal_norm] using hseq_sq_lt


theorem gabor_inner_eq_fiber_fourierCoeff
    (f : ℝ → ℂ) (g : ℝ → ℝ) (α : ℝ) (m n : ℤ)
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : Continuous g) (hgd : HasPolynomialDecay g) :
    gaborCoefficient f g α m n =
      ∫ x : ℝ, fiberSequence f g α n x * fourierKernel m x
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hprod :=
    fiberProduct_integrable_periodization_eq (f := f) (g := g) (α := α) n hf hg hgd
  have hunfold := integral_periodization_fourierKernel (H := fiberProduct f g α n) hprod.1 m
  unfold gaborCoefficient
  calc
    (∫ t : ℝ, f t * star (GaborAtom g α 1 n m t) ∂volume)
        = ∫ t : ℝ, fiberProduct f g α n t * fourierKernel m t ∂volume := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall ?_
          intro t
          exact gabor_integrand_eq_fiberProduct_kernel f g α t m n
    _ = ∫ x : ℝ, periodization (fiberProduct f g α n) x * fourierKernel m x
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := hunfold
    _ = ∫ x : ℝ, fiberSequence f g α n x * fourierKernel m x
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall ?_
          intro x
          exact congrArg (fun z => z * fourierKernel m x) (hprod.2 x)


theorem gabor_coefficients_parseval_per_fiber
    (f : ℝ → ℂ) (g : ℝ → ℝ) (α C σ : ℝ)
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : Continuous g) (hα : 0 < α)
    (hdec : HasDecayWithConstants g C σ)
    (hsub : SubmatrixCondition g α) (n : ℤ) :
    Summable (fun m : ℤ => ‖gaborCoefficient f g α m n‖ ^ 2) ∧
      (∑' m : ℤ, ‖gaborCoefficient f g α m n‖ ^ 2) =
        ∫ x : ℝ, ‖fiberSequence f g α n x‖ ^ 2
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hmem := fiberSequence_memLp f g α C σ hf hg hα hdec hsub n
  obtain ⟨hsum, hparseval⟩ :=
    parseval_Ioc_zero_one (u := fun x : ℝ => fiberSequence f g α n x) hmem
  have hcoeff : ∀ m : ℤ,
      gaborCoefficient f g α m n =
        ∫ x : ℝ, fiberSequence f g α n x * fourierKernel m x
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro m
    exact gabor_inner_eq_fiber_fourierCoeff f g α m n hf hg
      ⟨C, σ, hdec⟩
  constructor
  · convert hsum using 1
    ext m
    rw [hcoeff m]
  · calc
      (∑' m : ℤ, ‖gaborCoefficient f g α m n‖ ^ 2)
          = ∑' m : ℤ,
              ‖∫ x : ℝ, fiberSequence f g α n x * fourierKernel m x
                ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))‖ ^ 2 := by
            apply tsum_congr
            intro m
            rw [hcoeff m]
      _ = ∫ x : ℝ, ‖fiberSequence f g α n x‖ ^ 2
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := hparseval


theorem gabor_coefficient_congr_ae
    {f₁ f₂ : ℝ → ℂ} (hfeq : f₁ =ᵐ[volume] f₂)
    (g : ℝ → ℝ) (α : ℝ) (m n : ℤ) :
    gaborCoefficient f₁ g α m n = gaborCoefficient f₂ g α m n := by
  unfold gaborCoefficient
  apply integral_congr_ae
  filter_upwards [hfeq] with x hx
  rw [hx]

private theorem fiberSequence_ofReal_tsum_sq_eq
    (f : ℝ → ℂ) (g : ℝ → ℝ) (α C σ : ℝ)
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ)
    (fiber : ℝ → ellp (2 : ℝ≥0∞)) {x : ℝ}
    (hcoord : ∀ l : ℤ, fiber x l = fiberCoordinate f x l) :
    ENNReal.ofReal (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2) =
      ∑' n : ℤ, ENNReal.ofReal (‖fiberSequence f g α n x‖ ^ 2) := by
  let v := preGramianOperator g α C σ hα hdec x (fiber x)
  have hvsum : Summable (fun j : ℤ => ‖v j‖ ^ 2) := by
    simpa using (lp.memℓp v).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hnegsum : Summable (fun n : ℤ => ‖v (-n)‖ ^ 2) := by
    simpa [Function.comp_def] using
      ((Equiv.neg ℤ).summable_iff (f := fun j : ℤ => ‖v j‖ ^ 2)).mpr hvsum
  have hpoint : ∀ n : ℤ,
      ‖v (-n)‖ ^ 2 = ‖fiberSequence f g α n x‖ ^ 2 := by
    intro n
    have hseq :=
      fiberSequence_eq_preGramian_apply f g α C σ hα hdec fiber hcoord n
    rw [hseq]
    simp [v]
  have hsum : Summable (fun n : ℤ => ‖fiberSequence f g α n x‖ ^ 2) :=
    hnegsum.congr hpoint
  exact ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsum

private theorem fiberSequence_integral_tsum_eq_tsum_integral
    (f : ℝ → ℂ) (g : ℝ → ℝ) (α C σ : ℝ)
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : Continuous g) (hα : 0 < α)
    (hdec : HasDecayWithConstants g C σ)
    (hsub : SubmatrixCondition g α) :
    (∫ x : ℝ, (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) =
      ∑' n : ℤ,
        ∫ x : ℝ, ‖fiberSequence f g α n x‖ ^ 2
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let S : ℝ → ℝ := fun x => ∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2
  obtain ⟨fiber, hcoord_ae, hfiber_norm⟩ := fiberization_L2 f hf
  obtain ⟨_a, _ha_pos, _ha_le, hbounds⟩ :=
    preGramian_two_sided_bound_Icc g α C σ hg hα hdec hsub
  let B : ℝ := preGramianBesselBound C σ α
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, preGramianBesselBound]
    exact sq_nonneg _
  have hIoc : ∀ᵐ x ∂μI, x ∈ Set.Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  have hS_ae : AEMeasurable S μI := by
    dsimp [S]
    apply AEMeasurable.tsum
    intro n
    have hprod :=
      fiberProduct_integrable_periodization_eq (f := f) (g := g) (α := α) n hf hg
        ⟨C, σ, hdec⟩
    have hper_int :
        Integrable (fun x : ℝ => periodization (fiberProduct f g α n) x) μI :=
      periodization_integrable hprod.1
    have hseq_int : Integrable (fun x : ℝ => fiberSequence f g α n x) μI := by
      convert hper_int using 1
      ext x
      exact hprod.2 x
    exact (hseq_int.aestronglyMeasurable.norm.aemeasurable.pow_const (2 : ℕ))
  have hS_nonneg : 0 ≤ᵐ[μI] S := by
    refine Filter.Eventually.of_forall ?_
    intro x
    dsimp [S]
    exact tsum_nonneg (fun n => sq_nonneg _)
  have hpoint_upper : ∀ᵐ x ∂μI, S x ≤ B * (‖fiber x‖ ^ 2) := by
    filter_upwards [hcoord_ae, hIoc] with x hcoord hxIoc
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hsum :=
      fiberSequence_norm_tsum_eq_preGramian_norm f g α C σ hα hdec fiber hcoord
    have hb := hbounds x hxIcc (fiber x)
    calc
      S x = ‖preGramianOperator g α C σ hα hdec x (fiber x)‖ ^ 2 := by
        dsimp [S]
        exact hsum
      _ ≤ B * (‖fiber x‖ ^ 2) := by
        simpa [B] using hb.2
  have hglobal_sq_lt :
      (∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume) < ∞ := by
    have hint : Integrable (fun t : ℝ => ‖f t‖ ^ 2) (volume : Measure ℝ) := by
      exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    exact Integrable.lintegral_lt_top hint
  have hfiber_sq_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) < ∞ := by
    rw [hfiber_norm]
    exact hglobal_sq_lt
  have hmajor_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) ∂μI) < ∞ := by
    calc
      (∫⁻ x : ℝ, ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) ∂μI) =
          ∫⁻ x : ℝ, ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI := by
            apply lintegral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro x
            exact ENNReal.ofReal_mul hB_nonneg
      _ = ENNReal.ofReal B *
          (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := by
            exact lintegral_const_mul' (ENNReal.ofReal B)
              (fun x : ℝ => ENNReal.ofReal (‖fiber x‖ ^ 2)) ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfiber_sq_lt
  have hS_lintegral_lt : (∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI) < ∞ := by
    refine lt_of_le_of_lt ?_ hmajor_lt
    apply lintegral_mono_ae
    filter_upwards [hpoint_upper] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  have hS_int : Integrable S μI :=
    (lintegral_ofReal_ne_top_iff_integrable hS_ae.aestronglyMeasurable hS_nonneg).mp
      (ne_of_lt hS_lintegral_lt)
  have hterm_ae : ∀ n : ℤ,
      AEMeasurable (fun x : ℝ => ENNReal.ofReal (‖fiberSequence f g α n x‖ ^ 2))
        μI := by
    intro n
    have hmem := fiberSequence_memLp f g α C σ hf hg hα hdec hsub n
    exact ((hmem.aestronglyMeasurable.norm.aemeasurable.pow_const (2 : ℕ)).ennreal_ofReal)
  have hlin_tsum := lintegral_tsum hterm_ae
  have hlin_eq :
      (∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI) =
        ∑' n : ℤ, ∫⁻ x : ℝ,
          ENNReal.ofReal (‖fiberSequence f g α n x‖ ^ 2) ∂μI := by
    rw [← hlin_tsum]
    apply lintegral_congr_ae
    filter_upwards [hcoord_ae] with x hcoord
    dsimp [S]
    exact fiberSequence_ofReal_tsum_sq_eq f g α C σ hα hdec fiber hcoord
  have hlin_ne_top_ofReal :
      (∑' n : ℤ, ∫⁻ x : ℝ,
          ENNReal.ofReal (‖fiberSequence f g α n x‖ ^ 2) ∂μI) ≠ ∞ := by
    rw [← hlin_eq]
    exact ne_of_lt hS_lintegral_lt
  have hlin_ne_top :
      (∑' n : ℤ, ∫⁻ x : ℝ,
          ‖(‖fiberSequence f g α n x‖ ^ 2 : ℝ)‖ₑ ∂μI) ≠ ∞ := by
    simpa [ofReal_norm] using hlin_ne_top_ofReal
  have hbochner := integral_tsum
    (μ := μI)
    (f := fun n : ℤ => fun x : ℝ => ‖fiberSequence f g α n x‖ ^ 2)
    ?hstrong hlin_ne_top
  · simpa [S, μI] using hbochner
  · intro n
    have hmem := fiberSequence_memLp f g α C σ hf hg hα hdec hsub n
    have hsq_int : Integrable (fun x : ℝ => ‖fiberSequence f g α n x‖ ^ 2) μI := by
      exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
    exact hsq_int.aestronglyMeasurable

private theorem gabor_coefficient_sum_eq_fiber_integral
    (f : ℝ → ℂ) (g : ℝ → ℝ) (α C σ : ℝ)
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : Continuous g) (hα : 0 < α)
    (hdec : HasDecayWithConstants g C σ)
    (hsub : SubmatrixCondition g α) :
    (∑' n : ℤ, ∑' m : ℤ, ‖gaborCoefficient f g α m n‖ ^ 2) =
      ∫ x : ℝ, (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  calc
    (∑' n : ℤ, ∑' m : ℤ, ‖gaborCoefficient f g α m n‖ ^ 2)
        = ∑' n : ℤ,
            ∫ x : ℝ, ‖fiberSequence f g α n x‖ ^ 2
              ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          apply tsum_congr
          intro n
          exact (gabor_coefficients_parseval_per_fiber f g α C σ hf hg hα hdec hsub n).2
    _ = ∫ x : ℝ, (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          exact (fiberSequence_integral_tsum_eq_tsum_integral
            f g α C σ hf hg hα hdec hsub).symm

private theorem fiberSequence_two_sided_estimates_uniform
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hg : Continuous g) (hα : 0 < α)
    (hdec : HasDecayWithConstants g C σ)
    (hsub : SubmatrixCondition g α) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧
      ∀ f : ℝ → ℂ, MemLp f 2 (volume : Measure ℝ) →
        A * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) ≤
          ∫ x : ℝ, (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2)
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
        (∫ x : ℝ, (∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2)
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤
          B * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) := by
  obtain ⟨a, ha_pos, ha_le, hbounds⟩ :=
    preGramian_two_sided_bound_Icc g α C σ hg hα hdec hsub
  let A : ℝ := a ^ 2
  let B : ℝ := preGramianBesselBound C σ α
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, preGramianBesselBound]
    exact sq_nonneg _
  have hA_le_B : A ≤ B := by
    dsimp [A, B, preGramianBesselBound]
    have hM_pos : 0 < preGramianNormBound C σ α := lt_of_lt_of_le ha_pos ha_le
    nlinarith
  refine ⟨A, B, hA_pos, hA_le_B, ?_⟩
  intro f hf
  let μI : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let S : ℝ → ℝ := fun x => ∑' n : ℤ, ‖fiberSequence f g α n x‖ ^ 2
  obtain ⟨fiber, hcoord_ae, hfiber_norm⟩ := fiberization_L2 f hf
  have hIoc : ∀ᵐ x ∂μI, x ∈ Set.Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  have hpoint_ae : ∀ᵐ x ∂μI,
      A * (‖fiber x‖ ^ 2) ≤ S x ∧ S x ≤ B * (‖fiber x‖ ^ 2) := by
    filter_upwards [hcoord_ae, hIoc] with x hcoord hxIoc
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hsum :=
      fiberSequence_norm_tsum_eq_preGramian_norm f g α C σ hα hdec fiber hcoord
    have hb := hbounds x hxIcc (fiber x)
    constructor
    · calc
        A * (‖fiber x‖ ^ 2) = a ^ 2 * ‖fiber x‖ ^ 2 := rfl
        _ ≤ ‖preGramianOperator g α C σ hα hdec x (fiber x)‖ ^ 2 := hb.1
        _ = S x := by
          dsimp [S]
          exact hsum.symm
    · calc
        S x = ‖preGramianOperator g α C σ hα hdec x (fiber x)‖ ^ 2 := by
          dsimp [S]
          exact hsum
        _ ≤ B * (‖fiber x‖ ^ 2) := by
          simpa [B] using hb.2
  have hS_nonneg : 0 ≤ S := by
    intro x
    dsimp [S]
    exact tsum_nonneg (fun n => sq_nonneg _)
  have hS_nonneg_ae : 0 ≤ᵐ[μI] S := Filter.Eventually.of_forall hS_nonneg
  have hS_ae : AEMeasurable S μI := by
    dsimp [S]
    apply AEMeasurable.tsum
    intro n
    have hprod :=
      fiberProduct_integrable_periodization_eq (f := f) (g := g) (α := α) n hf hg
        ⟨C, σ, hdec⟩
    have hper_int :
        Integrable (fun x : ℝ => periodization (fiberProduct f g α n) x) μI :=
      periodization_integrable hprod.1
    have hseq_int : Integrable (fun x : ℝ => fiberSequence f g α n x) μI := by
      convert hper_int using 1
      ext x
      exact hprod.2 x
    exact (hseq_int.aestronglyMeasurable.norm.aemeasurable.pow_const (2 : ℕ))
  have hF_int : Integrable (fun t : ℝ => ‖f t‖ ^ 2) (volume : Measure ℝ) := by
    exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hF_nonneg : 0 ≤ᵐ[(volume : Measure ℝ)] fun t : ℝ => ‖f t‖ ^ 2 :=
    Filter.Eventually.of_forall (fun t => sq_nonneg _)
  have hF_lintegral_eq :
      ENNReal.ofReal (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) =
        ∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF_int hF_nonneg
  have hF_lintegral_lt :
      (∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume) < ∞ := by
    exact Integrable.lintegral_lt_top hF_int
  have hfiber_lintegral_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) < ∞ := by
    rw [hfiber_norm]
    exact hF_lintegral_lt
  have hmajor_lintegral_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) ∂μI) < ∞ := by
    calc
      (∫⁻ x : ℝ, ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) ∂μI) =
          ∫⁻ x : ℝ, ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI := by
            apply lintegral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro x
            change ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) =
              ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2)
            exact ENNReal.ofReal_mul hB_nonneg
      _ = ENNReal.ofReal B *
          (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := by
            exact lintegral_const_mul' (ENNReal.ofReal B)
              (fun x : ℝ => ENNReal.ofReal (‖fiber x‖ ^ 2)) ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfiber_lintegral_lt
  have hS_lintegral_lt :
      (∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI) < ∞ := by
    refine lt_of_le_of_lt ?_ hmajor_lintegral_lt
    apply lintegral_mono_ae
    filter_upwards [hpoint_ae] with x hx
    exact ENNReal.ofReal_le_ofReal hx.2
  have hS_int : Integrable S μI :=
    (lintegral_ofReal_ne_top_iff_integrable hS_ae.aestronglyMeasurable
      hS_nonneg_ae).mp (ne_of_lt hS_lintegral_lt)
  have hS_lintegral_eq :
      ENNReal.ofReal (∫ x : ℝ, S x ∂μI) =
        ∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hS_int hS_nonneg_ae
  have hS_integral_nonneg : 0 ≤ ∫ x : ℝ, S x ∂μI :=
    integral_nonneg hS_nonneg
  have hF_integral_nonneg : 0 ≤ ∫ t : ℝ, ‖f t‖ ^ 2 ∂volume :=
    integral_nonneg (fun t => sq_nonneg _)
  have hlower_lintegral :
      ENNReal.ofReal A * (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) ≤
        ∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI := by
    calc
      ENNReal.ofReal A * (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) =
          ∫⁻ x : ℝ, ENNReal.ofReal A * ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI := by
            exact (lintegral_const_mul' (ENNReal.ofReal A)
              (fun x : ℝ => ENNReal.ofReal (‖fiber x‖ ^ 2)) ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ x : ℝ, ENNReal.ofReal (A * (‖fiber x‖ ^ 2)) ∂μI := by
            apply lintegral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro x
            change ENNReal.ofReal A * ENNReal.ofReal (‖fiber x‖ ^ 2) =
              ENNReal.ofReal (A * (‖fiber x‖ ^ 2))
            exact (ENNReal.ofReal_mul hA_nonneg).symm
      _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI := by
            apply lintegral_mono_ae
            filter_upwards [hpoint_ae] with x hx
            exact ENNReal.ofReal_le_ofReal hx.1
  have hupper_lintegral :
      (∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI) ≤
        ENNReal.ofReal B * (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := by
    calc
      (∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI) ≤
          ∫⁻ x : ℝ, ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) ∂μI := by
            apply lintegral_mono_ae
            filter_upwards [hpoint_ae] with x hx
            exact ENNReal.ofReal_le_ofReal hx.2
      _ = ∫⁻ x : ℝ, ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI := by
            apply lintegral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro x
            change ENNReal.ofReal (B * (‖fiber x‖ ^ 2)) =
              ENNReal.ofReal B * ENNReal.ofReal (‖fiber x‖ ^ 2)
            exact ENNReal.ofReal_mul hB_nonneg
      _ = ENNReal.ofReal B *
          (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := by
            exact lintegral_const_mul' (ENNReal.ofReal B)
              (fun x : ℝ => ENNReal.ofReal (‖fiber x‖ ^ 2)) ENNReal.ofReal_ne_top
  have hlower_ofReal :
      ENNReal.ofReal (A * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume)) ≤
        ENNReal.ofReal (∫ x : ℝ, S x ∂μI) := by
    calc
      ENNReal.ofReal (A * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume)) =
          ENNReal.ofReal A * ENNReal.ofReal (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) := by
            exact ENNReal.ofReal_mul hA_nonneg
      _ = ENNReal.ofReal A *
          (∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume) := by
            rw [hF_lintegral_eq]
      _ = ENNReal.ofReal A *
          (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := by
            rw [hfiber_norm]
      _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI := hlower_lintegral
      _ = ENNReal.ofReal (∫ x : ℝ, S x ∂μI) := hS_lintegral_eq.symm
  have hupper_ofReal :
      ENNReal.ofReal (∫ x : ℝ, S x ∂μI) ≤
        ENNReal.ofReal (B * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume)) := by
    calc
      ENNReal.ofReal (∫ x : ℝ, S x ∂μI) =
          ∫⁻ x : ℝ, ENNReal.ofReal (S x) ∂μI := hS_lintegral_eq
      _ ≤ ENNReal.ofReal B *
          (∫⁻ x : ℝ, ENNReal.ofReal (‖fiber x‖ ^ 2) ∂μI) := hupper_lintegral
      _ = ENNReal.ofReal B *
          (∫⁻ t : ℝ, ENNReal.ofReal (‖f t‖ ^ 2) ∂volume) := by
            rw [hfiber_norm]
      _ = ENNReal.ofReal B * ENNReal.ofReal (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) := by
            rw [hF_lintegral_eq]
      _ = ENNReal.ofReal (B * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume)) := by
            exact (ENNReal.ofReal_mul hB_nonneg).symm
  constructor
  · dsimp [S] at hlower_ofReal ⊢
    exact (ENNReal.ofReal_le_ofReal_iff hS_integral_nonneg).mp hlower_ofReal
  · dsimp [S] at hupper_ofReal ⊢
    have hright_nonneg : 0 ≤ B * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) :=
      mul_nonneg hB_nonneg hF_integral_nonneg
    exact (ENNReal.ofReal_le_ofReal_iff hright_nonneg).mp hupper_ofReal

theorem gabor_coefficient_two_sided_estimates_uniform
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hg : Continuous g) (hα : 0 < α)
    (hdec : HasDecayWithConstants g C σ)
    (hsub : SubmatrixCondition g α) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧
      ∀ f : ℝ → ℂ, MemLp f 2 (volume : Measure ℝ) →
        A * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) ≤
          (∑' n : ℤ, ∑' m : ℤ, ‖gaborCoefficient f g α m n‖ ^ 2) ∧
        (∑' n : ℤ, ∑' m : ℤ, ‖gaborCoefficient f g α m n‖ ^ 2) ≤
          B * (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) := by
  obtain ⟨A, B, hA_pos, hA_le_B, hfiber⟩ :=
    fiberSequence_two_sided_estimates_uniform g α C σ hg hα hdec hsub
  refine ⟨A, B, hA_pos, hA_le_B, ?_⟩
  intro f hf
  have hcoeff := gabor_coefficient_sum_eq_fiber_integral f g α C σ hf hg hα hdec hsub
  have hest := hfiber f hf
  constructor
  · rw [hcoeff]
    exact hest.1
  · rw [hcoeff]
    exact hest.2

end

end VendorE3
