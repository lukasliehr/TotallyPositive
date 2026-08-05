import LeanCode.Conventions
import LeanCode.Scaling
import LeanCode.Construction
import LeanCode.OperatorConventions
import LeanCode.E7Vocab
import LeanCode.SelfSimilarPrereqs
import LeanCode.Hard_OpnormL1
import LeanCode.Hard_ScalingFrame
import LeanCode.Hard_RealComplex
import LeanCode.Hard_FredholmBridge
import LeanCode.Hard_SelfSimilar




































open MeasureTheory
open scoped ENNReal

namespace Assembly.Endgame

















theorem winG_e7_decay
    (g : ℝ → ℝ) (δ : ℤ → ℝ)
    (hg : Assembly.HasPolynomialDecay g) (hδ : ∃ R : ℝ, ∀ k : ℤ, |δ k| ≤ R) :
    Assembly.E7.HasPolynomialOffDiagonalDecay (Assembly.GaborSubmatrixC g δ) := by

  obtain ⟨C, η, hC, hη, hbound⟩ :=
    Assembly.Construction.gaborSubmatrix_offDiagonalDecay g δ hg hδ
  refine ⟨C, η, hC, hη, ?_⟩
  intro k l

  have hnorm : ‖Assembly.GaborSubmatrixC g δ k l‖ = ‖Assembly.GaborSubmatrixR g δ k l‖ := by
    simp only [Assembly.GaborSubmatrixC, Assembly.GaborSubmatrixR, Complex.norm_real]
  rw [hnorm]

  have hden : (0 : ℝ) < (1 + |(k : ℝ) - (l : ℝ)|) ^ η :=
    Real.rpow_pos_of_pos (by positivity) η
  have hb := hbound k l
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv]
  exact hb













theorem prop_fibre
    (g : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (htpic : Assembly.IsTotallyPositiveIntegrableContinuous g) (hg0 : g ≠ 0)
    (x : ℝ) :
    ∃ (δ : ℤ → ℝ) (ν : ℤ → ℤ),
      Function.Injective ν ∧
      (∀ k : ℤ, x + α * (ν k : ℝ) = (k : ℝ) + δ k) ∧
      Assembly.MatrixInvertibleOn (2 : ℝ≥0∞) (Assembly.GaborSubmatrixC g δ) := by

  obtain ⟨hTP, hInt, hCont⟩ := htpic
  have htpic : Assembly.IsTotallyPositiveIntegrableContinuous g := ⟨hTP, hInt, hCont⟩
  have hpd : Assembly.HasPolynomialDecay g := Assembly.TotallyPositiveHasDecay g htpic

  obtain ⟨x₀, ⟨hx₀_mem, hx₀_zero⟩, _⟩ := Assembly.Ext.E5_VinogradovUlitskaya g hg0 htpic

  set ε : ℝ := (1 - α) / 4 with hε_def
  have hε₁ : 0 < ε := by rw [hε_def]; linarith
  have hε₂ : ε < 1 / 2 := by rw [hε_def]; linarith
  have hsum : 2 * ε + α < 1 := by rw [hε_def]; linarith

  obtain ⟨a, ha_mem, ha_bad⟩ :=
    Assembly.Construction.choose_a x₀ ε x α hα hε₁ hsum

  have hsub : Set.Ico a (a + α) ⊆ Assembly.Construction.I x₀ ε := by
    obtain ⟨ha_lo, ha_hi⟩ := ha_mem
    intro t ht
    obtain ⟨ht_lo, ht_hi⟩ := ht
    refine ⟨?_, ?_⟩
    · exact le_trans ha_lo ht_lo
    · linarith

  set δ : ℤ → ℝ := Assembly.Construction.deltaSeq x α a with hδ_def
  set ν : ℤ → ℤ := Assembly.Construction.nu x α a with hν_def
  refine ⟨δ, ν, ?_, ?_, ?_⟩
  ·
    exact Assembly.Construction.nu_injective x α a hα hα1 ha_bad
  ·
    intro k
    have := Assembly.Construction.deltaSeq_lattice x α a hα k
    rw [hδ_def, hν_def]; linarith [this]
  ·

    have hδ_mem : ∀ k : ℤ, δ k ∈ Assembly.Construction.I x₀ ε := by
      rw [hδ_def]
      exact Assembly.Construction.deltaSeq_mem_I x₀ ε x α a hα ha_bad hsub

    have hδ_Icc : ∀ k : ℤ, δ k ∈ Set.Icc (x₀ - 1 + ε) (x₀ - ε) := hδ_mem

    have hδ_bdd : ∃ R : ℝ, ∀ k : ℤ, |δ k| ≤ R := by
      refine ⟨max |x₀ - 1 + ε| |x₀ - ε|, fun k => ?_⟩
      obtain ⟨hlo, hhi⟩ := hδ_Icc k
      rw [abs_le]
      constructor
      · have : -(|x₀ - 1 + ε|) ≤ x₀ - 1 + ε := neg_abs_le _
        exact le_trans (neg_le_neg (le_max_left _ _)) (le_trans this hlo)
      · have : x₀ - ε ≤ |x₀ - ε| := le_abs_self _
        exact le_trans hhi (le_trans this (le_max_right _ _))

    have hsurjR : ∀ v : ℤ → ℝ, Assembly.IsSummableSequence v →
        ∃ y : ℤ → ℝ, Assembly.IsSummableSequence y ∧
          Assembly.MatVec (Assembly.GaborSubmatrixR g δ) y = v := by

      have hx₀' : x₀ ∈ Set.Ico (0:ℝ) 1 ∧ Assembly.Z g (Assembly.Ext.E5_test g htpic) (x₀, 1/2) = 0 :=
        ⟨hx₀_mem, hx₀_zero⟩
      exact Assembly.Ext.E6_GroechenigSurjectivity g hg0 htpic hx₀' hε₁ hε₂ δ hδ_Icc

    have hsurjC : Assembly.E7.MatrixSurjectiveOnEllOne (Assembly.GaborSubmatrixC g δ) :=
      Assembly.Hard.real_to_complex_surjOnEllOne_proof g δ hpd hsurjR

    have hdecay : Assembly.E7.HasPolynomialOffDiagonalDecay (Assembly.GaborSubmatrixC g δ) :=
      winG_e7_decay g δ hpd hδ_bdd

    have hself : Assembly.E7.opOfMatrix (Assembly.GaborSubmatrixC g δ)
        ∈ Assembly.E7.operatorSpectrum (Assembly.E7.opOfMatrix (Assembly.GaborSubmatrixC g δ)) := by
      have := Assembly.Hard.selfSimilar_proof g α a x hCont hpd hα hα1 ha_bad
      rw [hδ_def]; exact this

    exact Assembly.Hard.fredholm_inj_surj_to_invertible2_proof g δ hdecay hsurjC hself




theorem prop_submatcond
    (g : ℝ → ℝ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (htpic : Assembly.IsTotallyPositiveIntegrableContinuous g) (hg0 : g ≠ 0) :
    Assembly.SubmatrixCondition g α := by
  intro x
  obtain ⟨δ, ν, hν, hlat, hinv⟩ := prop_fibre g α hα hα1 htpic hg0 x
  exact ⟨δ, ν, hν, hlat, hinv⟩





theorem main_equiv
    (g : ℝ → ℝ) (htpic : Assembly.IsTotallyPositiveIntegrableContinuous g)
    (hg0 : g ≠ 0) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Assembly.IsGaborFrame g htpic.2.2 (Assembly.TotallyPositiveHasDecay g htpic) α 1 := by
  have hsub : Assembly.SubmatrixCondition g α :=
    prop_submatcond g α hα hα1 htpic hg0
  exact Assembly.Ext.E3_SubmatrixCriterion hα hα1 g htpic.2.2
    (Assembly.TotallyPositiveHasDecay g htpic) hsub







theorem frameSetConjecture_proof
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (h1 : α * β < 1)
    (g : ℝ → ℝ)
    (htpic : Assembly.IsTotallyPositiveIntegrableContinuous g)
    (hg0 : g ≠ 0) :
    Assembly.IsGaborFrame g htpic.2.2 (Assembly.TotallyPositiveHasDecay g htpic) α β := by

  have hα' : 0 < α * β := mul_pos hα hβ

  set gβ : ℝ → ℝ := Assembly.Scaling.scaleWindow β g with hgβ_def

  obtain ⟨hTP, hInt, hCont⟩ := htpic
  have hTPβ : Assembly.IsTotallyPositive gβ :=
    Assembly.Scaling.isTotallyPositive_scaleWindow hβ hTP
  have hContβ : Continuous gβ := Assembly.Scaling.continuous_scaleWindow hCont

  have hIntβ : MeasureTheory.Integrable gβ := by

    have hdiv : MeasureTheory.Integrable (fun t : ℝ => g (t / β)) :=
      hInt.comp_div (ne_of_gt hβ)
    have hconst : MeasureTheory.Integrable (fun t : ℝ => (Real.sqrt β)⁻¹ * g (t / β)) :=
      hdiv.const_mul _
    rw [hgβ_def]
    exact hconst
  have htpicβ : Assembly.IsTotallyPositiveIntegrableContinuous gβ := ⟨hTPβ, hIntβ, hContβ⟩

  have hg0β : gβ ≠ 0 := by
    intro hzero
    apply hg0
    funext t
    have hround := Assembly.Scaling.scaleWindow_scaleWindow_inv hβ g t
    rw [hgβ_def] at hzero

    have : Assembly.Scaling.scaleWindow (1 / β) (Assembly.Scaling.scaleWindow β g) t
        = Assembly.Scaling.scaleWindow (1 / β) 0 t := by rw [hzero]
    rw [hround] at this
    rw [this]
    simp [Assembly.Scaling.scaleWindow]

  have hframeβ : Assembly.IsGaborFrame gβ htpicβ.2.2
      (Assembly.TotallyPositiveHasDecay gβ htpicβ) (α * β) 1 :=
    main_equiv gβ htpicβ hg0β hα' h1

  have hpd : Assembly.HasPolynomialDecay g :=
    Assembly.TotallyPositiveHasDecay g ⟨hTP, hInt, hCont⟩





  have hframeβ' : Assembly.IsGaborFrame gβ
      (Assembly.Scaling.continuous_scaleWindow hCont)
      (Assembly.Scaling.hasPolynomialDecay_scaleWindow hβ hpd) (α * β) 1 := hframeβ
  have := Assembly.Hard_ScalingFrame.scaling_frame_transfer_proof g α β hβ hCont hpd hframeβ'

  exact this

end Assembly.Endgame
