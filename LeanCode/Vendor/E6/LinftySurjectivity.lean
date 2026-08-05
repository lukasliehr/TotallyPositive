import LeanCode.Vendor.E6.External
import LeanCode.Vendor.E6.GaborMatrix

noncomputable section

namespace E6

theorem gaborSubmatrix_surjective_linf_real (g : ℝ → ℝ)
    (hg₀ : g ≠ 0) (hg : IsTotallyPositiveIntegrableContinuous g)
    (hdecay : HasExponentialDecay g)
    {x₀ ε : ℝ}
    (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hx₀zero : Z g hdecay (x₀, 1 / 2) = 0)
    (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2)
    (δ : ℤ → ℝ)
    (hδ : ∀ k : ℤ, δ k ∈ PerturbationInterval x₀ ε) :
    ∀ x : ℤ → ℝ, IsBoundedSequence x →
      ∃ y : ℤ → ℝ, IsBoundedSequence y ∧
        MatVec (GaborSubmatrix g δ) y = x := by
  have hTP := gaborSubmatrix_totallyPositiveMatrix g hg.1 hx₀ hε₀ hε₁ δ hδ
  have hpoly := gaborSubmatrix_hasPolynomialOffDiagonalDecay
    g hdecay hx₀ hε₀ hε₁ δ hδ
  rcases gaborSubmatrix_image_alternatingVector_uniform
      g hg₀ hg hdecay hx₀ hx₀zero hε₀ hε₁ δ hδ with
    ⟨halt, hlower⟩
  exact DFP_Groechnig_Version (GaborSubmatrix g δ) hTP hpoly alternatingVector
    alternatingVector_bounded halt hlower

end E6
