import LeanCode.Vendor.E3.FiberLowerBound
import LeanCode.Vendor.E3.FiberSequences

open MeasureTheory
open scoped ENNReal

namespace VendorE3
noncomputable section






private theorem l2_integral_norm_sq_eq_norm_sq
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ t : ℝ, ‖x t‖ ^ 2 ∂volume) = ‖x‖ ^ 2 := by
  have hnorm := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x
  rw [L2.inner_def] at hnorm
  have hcomplex :
      (∫ t : ℝ, inner ℂ (x t) (x t) ∂volume) =
        ((∫ t : ℝ, ‖x t‖ ^ 2 ∂volume : ℝ) : ℂ) := by
    calc
      (∫ t : ℝ, inner ℂ (x t) (x t) ∂volume)
          = ∫ t : ℝ, ((‖x t‖ ^ 2 : ℝ) : ℂ) ∂volume := by
              apply integral_congr_ae
              refine Filter.Eventually.of_forall ?_
              intro t
              calc
                inner ℂ (x t) (x t) = (↑‖x t‖ : ℂ) ^ 2 := by
                  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x t)
                _ = ((‖x t‖ ^ 2 : ℝ) : ℂ) := by
                  norm_num [pow_two]
      _ = ((∫ t : ℝ, ‖x t‖ ^ 2 ∂volume : ℝ) : ℂ) := by
              exact integral_ofReal (μ := (volume : Measure ℝ)) (𝕜 := ℂ)
                (f := fun t : ℝ => ‖x t‖ ^ 2)
  rw [hcomplex] at hnorm
  simpa using hnorm.symm

private theorem norm_inner_GaborAtom_L2_eq_gaborCoefficient
    {α : ℝ} (g : ℝ → ℝ) (hg : Continuous g) (h2 : HasPolynomialDecay g)
    (x : Lp ℂ 2 (volume : Measure ℝ)) (m n : ℤ) :
    ‖inner ℂ x (GaborAtom_L2 g hg h2 α 1 m n)‖ =
      ‖gaborCoefficient (fun t : ℝ => x t) g α n m‖ := by
  let atom : Lp ℂ 2 (volume : Measure ℝ) := GaborAtom_L2 g hg h2 α 1 m n
  have hsymm : (starRingEnd ℂ) (inner ℂ atom x) = inner ℂ x atom :=
    inner_conj_symm x atom
  have hcoeff : inner ℂ atom x = gaborCoefficient (fun t : ℝ => x t) g α n m := by
    rw [L2.inner_def]
    unfold gaborCoefficient
    apply integral_congr_ae
    have hatom : (fun t : ℝ => atom t) =ᵐ[volume] GaborAtom g α 1 m n := by
      unfold atom GaborAtom_L2
      exact (memL2_GaborAtom g hg h2 α 1 m n).coeFn_toLp
    filter_upwards [hatom] with t ht
    rw [ht]
    simp [RCLike.inner_apply]
  calc
    ‖inner ℂ x atom‖ = ‖(starRingEnd ℂ) (inner ℂ atom x)‖ := by rw [← hsymm]
    _ = ‖inner ℂ atom x‖ := by rw [RCLike.norm_conj]
    _ = ‖gaborCoefficient (fun t : ℝ => x t) g α n m‖ := by rw [hcoeff]

private theorem frame_sum_eq_gabor_coefficient_sum
    {α : ℝ} (g : ℝ → ℝ) (hg : Continuous g) (h2 : HasPolynomialDecay g)
    (x : Lp ℂ 2 (volume : Measure ℝ)) :
    (∑' m : ℤ, ∑' n : ℤ,
        ‖inner ℂ x (GaborAtom_L2 g hg h2 α 1 m n)‖ ^ 2) =
      ∑' m : ℤ, ∑' n : ℤ,
        ‖gaborCoefficient (fun t : ℝ => x t) g α n m‖ ^ 2 := by
  apply tsum_congr
  intro m
  apply tsum_congr
  intro n
  rw [norm_inner_GaborAtom_L2_eq_gaborCoefficient g hg h2 x m n]


theorem SubmatrixCriterion
    {α : ℝ} (hα : 0 < α) (h1 : α < 1)
    (g : ℝ → ℝ) (hg : Continuous g) (h2 : HasPolynomialDecay g)
    (h3 : SubmatrixCondition g α) :
    IsGaborFrame g hg h2 α 1 := by
  have _hα_lt_one : α < 1 := h1
  rcases h2 with ⟨C, σ, hC, hσ, hbound⟩
  have hdec : HasDecayWithConstants g C σ := ⟨hC, hσ, hbound⟩
  obtain ⟨A, B, hA_pos, hA_le_B, hcoeff⟩ :=
    gabor_coefficient_two_sided_estimates_uniform g α C σ hg hα hdec h3
  refine ⟨A, B, hA_pos, hA_le_B, ?_⟩
  intro x
  let f : ℝ → ℂ := fun t => x t
  have hf : MemLp f 2 (volume : Measure ℝ) := by
    simpa [f] using (Lp.memLp x)
  have hest := hcoeff f hf
  have hnorm : (∫ t : ℝ, ‖f t‖ ^ 2 ∂volume) = ‖x‖ ^ 2 := by
    simpa [f] using l2_integral_norm_sq_eq_norm_sq x
  have hsum := frame_sum_eq_gabor_coefficient_sum (α := α) g hg
    (show HasPolynomialDecay g from ⟨C, σ, hC, hσ, hbound⟩) x
  constructor
  · rw [hsum, ← hnorm]
    exact hest.1
  · rw [hsum, ← hnorm]
    exact hest.2

end

end VendorE3
