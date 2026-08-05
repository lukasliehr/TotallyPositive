import LeanCode.Vendor.E6
import LeanCode.Vocab
import LeanCode.Base
import LeanCode.Bridge_E5

































noncomputable section













theorem Assembly.Ext.E6_GroechenigSurjectivity_thm
    (g : ℝ → ℝ) (hg : g ≠ 0) (h : Assembly.IsTotallyPositiveIntegrableContinuous g)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ico (0:ℝ) 1 ∧
      Assembly.Z g (Assembly.Ext.E5_test_thm g h) (x₀, 1/2) = 0)
    {ε : ℝ} (hε₁ : 0 < ε) (hε₂ : ε < 1/2)
    (δ : ℤ → ℝ) (hδ : ∀ k : ℤ, δ k ∈ Set.Icc (x₀ - 1 + ε) (x₀ - ε)) :
    ∀ v : ℤ → ℝ, Assembly.IsSummableSequence v →
      ∃ y : ℤ → ℝ, Assembly.IsSummableSequence y ∧
        Assembly.MatVec (Assembly.GaborSubmatrixR g δ) y = v := by

  have hE6 : E6.IsTotallyPositiveIntegrableContinuous g :=
    ⟨fun n a b ha hb => h.1 n a b ha hb, h.2.1, h.2.2⟩


  have hx₀E6 : x₀ ∈ Set.Ico (0:ℝ) 1 ∧
      E6.Z g (E6.ExponentialDecay g ⟨hE6.1, hE6.2.1⟩) (x₀, 1/2) = 0 :=
    ⟨hx₀.1, hx₀.2⟩

  have hδE6 : ∀ k : ℤ, δ k ∈ E6.PerturbationInterval x₀ ε := hδ


  exact E6.gaborSubmatrix_surjective_l1_real g hg hE6 hx₀E6 hε₁ hε₂ δ hδE6

end
