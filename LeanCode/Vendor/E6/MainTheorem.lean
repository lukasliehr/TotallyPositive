import LeanCode.Vendor.E6.OperatorBridge

noncomputable section

namespace E6

theorem gaborSubmatrix_surjective_l1_real
    (g : ℝ → ℝ) (hg₀ : g ≠ 0)
    (hg : IsTotallyPositiveIntegrableContinuous g)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1 ∧
      Z g (ExponentialDecay g ⟨hg.1, hg.2.1⟩) (x₀, 1 / 2) = 0)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2)
    (δ : ℤ → ℝ)
    (hδ : ∀ k : ℤ, δ k ∈ PerturbationInterval x₀ ε) :
    ∀ v : ℤ → ℝ, IsSummableSequence v →
      ∃ y : ℤ → ℝ, IsSummableSequence y ∧
        MatVec (GaborSubmatrix g δ) y = v := by
  let hdecay : HasExponentialDecay g := ExponentialDecay g ⟨hg.1, hg.2.1⟩
  have hlinfReal : ∀ x : ℤ → ℝ, IsBoundedSequence x →
      ∃ y : ℤ → ℝ, IsBoundedSequence y ∧
        MatVec (GaborSubmatrix g δ) y = x :=
    gaborSubmatrix_surjective_linf_real
      g hg₀ hg hdecay hx₀.1 hx₀.2 hε₀ hε₁ δ hδ
  have hpolyReal : HasPolynomialOffDiagonalDecay (GaborSubmatrix g δ) :=
    gaborSubmatrix_hasPolynomialOffDiagonalDecay
      g hdecay hx₀.1 hε₀ hε₁ δ hδ
  have hlinfComplex :
      MatrixSurjectiveOn (ComplexifyMatrix (GaborSubmatrix g δ)) SequenceSpace.infinity :=
    realSequenceSurjectivity_complexifies (GaborSubmatrix g δ) hpolyReal hlinfReal
  have hpolyComplex :
      HasPolynomialOffDiagonalDecay (ComplexifyMatrix (GaborSubmatrix g δ)) :=
    gaborSubmatrix_complex_hasPolynomialOffDiagonalDecay
      g hdecay hx₀.1 hε₀ hε₁ δ hδ
  have hl1Complex :
      MatrixSurjectiveOn (ComplexifyMatrix (GaborSubmatrix g δ)) SequenceSpace.one :=
    SurjSpectralInvariance
      (ComplexifyMatrix (GaborSubmatrix g δ)) hpolyComplex hlinfComplex
  exact real_l1_preimage_of_complex_l1_surjective
    (GaborSubmatrix g δ) hpolyReal hl1Complex

end E6
