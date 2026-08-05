import LeanCode.Vocab
import LeanCode.Bridge_E1
import LeanCode.Bridge_E2
import LeanCode.Bridge_E3
import LeanCode.Bridge_E5
import LeanCode.Bridge_E6




















open Matrix
open MeasureTheory
open scoped ENNReal
open lp

namespace Assembly.Ext






theorem E1_ExponentialDecay (g : ℝ → ℝ) (h : Assembly.IsTotallyPositiveIntegrable g) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|) :=
  Assembly.Ext.E1_ExponentialDecay_thm g h












theorem E2_SpectralInvariance
    (A : ℤ → ℤ → ℂ)
    (hA : Assembly.HasPolynomialOffDiagonalDecayC A)
    (p₀ : ℝ≥0∞) [Fact (1 ≤ p₀)]
    (h_inv : Assembly.MatrixInvertibleOn p₀ A) :
    ∀ q : ℝ≥0∞, [Fact (1 ≤ q)] → Assembly.MatrixInvertibleOn q A :=
  Assembly.Ext.E2_SpectralInvariance_thm A hA p₀ h_inv








theorem E5_test (g : ℝ → ℝ) (h : Assembly.IsTotallyPositiveIntegrableContinuous g) :
    Assembly.HasExponentialDecay g :=
  Assembly.Ext.E5_test_thm g h


theorem E5_VinogradovUlitskaya (g : ℝ → ℝ) (hg : g ≠ 0)
    (h : Assembly.IsTotallyPositiveIntegrableContinuous g) :
    ∃! x : ℝ, x ∈ Set.Ico (0:ℝ) 1 ∧ Assembly.Z g (E5_test g h) (x, 1/2) = 0 :=
  Assembly.Ext.E5_VinogradovUlitskaya_thm g hg h






theorem E3_SubmatrixCriterion
    {α : ℝ} (hα : 0 < α) (h1 : α < 1)
    (g : ℝ → ℝ) (hg : Continuous g) (h2 : Assembly.HasPolynomialDecay g)
    (h3 : Assembly.SubmatrixCondition g α) :
    Assembly.IsGaborFrame g hg h2 α 1 :=
  Assembly.Ext.E3_SubmatrixCriterion_thm hα h1 g hg h2 h3













theorem E6_GroechenigSurjectivity
    (g : ℝ → ℝ) (hg : g ≠ 0) (h : Assembly.IsTotallyPositiveIntegrableContinuous g)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ico (0:ℝ) 1 ∧ Assembly.Z g (E5_test g h) (x₀, 1/2) = 0)
    {ε : ℝ} (hε₁ : 0 < ε) (hε₂ : ε < 1/2)
    (δ : ℤ → ℝ) (hδ : ∀ k : ℤ, δ k ∈ Set.Icc (x₀ - 1 + ε) (x₀ - ε)) :
    ∀ v : ℤ → ℝ, Assembly.IsSummableSequence v →
      ∃ y : ℤ → ℝ, Assembly.IsSummableSequence y ∧
        Assembly.MatVec (Assembly.GaborSubmatrixR g δ) y = v :=
  Assembly.Ext.E6_GroechenigSurjectivity_thm g hg h hx₀ hε₁ hε₂ δ hδ

end Assembly.Ext
