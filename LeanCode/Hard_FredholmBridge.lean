import LeanCode.E7Vocab
import LeanCode.Bridge_E7
import LeanCode.OperatorConventions
import LeanCode.ExternalInputs
import LeanCode.Hard_OpnormL1







open scoped ENNReal
open Classical
noncomputable section
namespace Assembly.Hard







theorem summable_one_add_abs_rpow {η : ℝ} (hη : 1 < η) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-η)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hkey : ∀ x : ℝ, 0 ≤ x → 1 / |x + 1| ^ η = (1 + x) ^ (-η) := by
    intro x hx
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ x + 1),
      add_comm x 1, Real.rpow_neg (by positivity), one_div]
  constructor
  · have h := (Real.summable_one_div_nat_add_rpow 1 η).mpr hη
    refine h.congr (fun n => ?_)
    rw [hkey (n : ℝ) n.cast_nonneg]
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  · have h := (Real.summable_one_div_nat_add_rpow 1 η).mpr hη
    refine h.congr (fun n => ?_)
    rw [hkey (n : ℝ) n.cast_nonneg]
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]


theorem summable_col {A : ℤ → ℤ → ℂ} (h : Assembly.E7.HasPolynomialOffDiagonalDecay A) (l : ℤ) :
    Summable (fun k : ℤ => ‖A k l‖) := by
  obtain ⟨C, η, hC, hη, hbound⟩ := h
  have hdom : Summable (fun k : ℤ => C * (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)) := by
    have hbase := (summable_one_add_abs_rpow hη)
    have hre := (Equiv.subRight l).summable_iff.mpr hbase
    have heq : (fun k : ℤ => (1 + |((k - l : ℤ) : ℝ)|) ^ (-η))
        = ((fun n : ℤ => (1 + |(n : ℝ)|) ^ (-η)) ∘ ⇑(Equiv.subRight l)) := by
      funext k; simp [Equiv.subRight_apply]
    rw [← heq] at hre
    have hre' : Summable (fun k : ℤ => (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)) := by
      refine hre.congr (fun k => ?_)
      push_cast; ring_nf
    exact hre'.mul_left C
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hbound k l) hdom


theorem summable_row_decay {A : ℤ → ℤ → ℂ} (h : Assembly.E7.HasPolynomialOffDiagonalDecay A) (k : ℤ) :
    Summable (fun l : ℤ => ‖A k l‖) := by
  obtain ⟨C, η, hC, hη, hbound⟩ := h
  have hdom : Summable (fun l : ℤ => C * (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)) := by
    have hbase := (summable_one_add_abs_rpow hη)
    have hre := (Equiv.subLeft k).summable_iff.mpr hbase
    have heq : (fun l : ℤ => (1 + |((k - l : ℤ) : ℝ)|) ^ (-η))
        = ((fun n : ℤ => (1 + |(n : ℝ)|) ^ (-η)) ∘ ⇑(Equiv.subLeft k)) := by
      funext l; simp [Equiv.subLeft_apply]
    rw [← heq] at hre
    have hre' : Summable (fun l : ℤ => (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)) := by
      refine hre.congr (fun l => ?_)
      push_cast; ring_nf
    exact hre'.mul_left C
  refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => hbound k l) hdom


theorem exists_col_sum_bound {A : ℤ → ℤ → ℂ} (h : Assembly.E7.HasPolynomialOffDiagonalDecay A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℤ, Summable (fun k : ℤ => ‖A k l‖) ∧ ∑' k : ℤ, ‖A k l‖ ≤ M := by
  obtain ⟨C, η, hC, hη, hbound⟩ := h
  have hbase := summable_one_add_abs_rpow hη
  refine ⟨C * ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-η), ?_, ?_⟩
  · exact mul_nonneg hC.le (tsum_nonneg (fun n => Real.rpow_nonneg (by positivity) _))
  · intro l
    refine ⟨summable_col ⟨C, η, hC, hη, hbound⟩ l, ?_⟩
    have hdom : Summable (fun k : ℤ => C * (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)) := by
      have hre := (Equiv.subRight l).summable_iff.mpr hbase
      have heq : (fun k : ℤ => (1 + |((k - l : ℤ) : ℝ)|) ^ (-η))
          = ((fun n : ℤ => (1 + |(n : ℝ)|) ^ (-η)) ∘ ⇑(Equiv.subRight l)) := by
        funext k; simp [Equiv.subRight_apply]
      rw [← heq] at hre
      have hre' : Summable (fun k : ℤ => (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)) := by
        refine hre.congr (fun k => ?_)
        push_cast; ring_nf
      exact hre'.mul_left C
    have hsum_row : Summable (fun k : ℤ => ‖A k l‖) :=
      summable_col ⟨C, η, hC, hη, hbound⟩ l
    calc ∑' k : ℤ, ‖A k l‖
        ≤ ∑' k : ℤ, C * (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η) :=
          hsum_row.tsum_le_tsum (fun k => hbound k l) hdom
      _ = C * ∑' k : ℤ, (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η) := tsum_mul_left
      _ = C * ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-η) := by
          congr 1
          have := (Equiv.subRight l).tsum_eq (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-η))
          rw [← this]
          refine tsum_congr (fun k => ?_)
          simp only [Equiv.subRight_apply]
          push_cast; ring_nf







theorem exists_bounded_realizing {A : ℤ → ℤ → ℂ}
    (h : Assembly.E7.HasPolynomialOffDiagonalDecay A) :
    ∃ T : Assembly.E7.ℓ1 →L[ℂ] Assembly.E7.ℓ1, ∀ (c : Assembly.E7.ℓ1) (k : ℤ),
      (T c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l := by
  obtain ⟨M, hM0, hcol⟩ := exists_col_sum_bound h
  obtain ⟨T, hT, _⟩ := Assembly.Endgame.opnorm_l1_col_sup_proof A M hM0 hcol
  exact ⟨T, hT⟩


theorem opOfMatrix_apply {A : ℤ → ℤ → ℂ}
    (h : Assembly.E7.HasPolynomialOffDiagonalDecay A)
    (c : Assembly.E7.ℓ1) (k : ℤ) :
    (Assembly.E7.opOfMatrix A c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l := by
  have hex := exists_bounded_realizing h
  rw [Assembly.E7.opOfMatrix, dif_pos hex]
  exact hex.choose_spec c k


theorem summable_row_matVec {A : ℤ → ℤ → ℂ}
    (h : Assembly.E7.HasPolynomialOffDiagonalDecay A) (c : Assembly.E7.ℓ1) (k : ℤ) :
    Summable (fun l : ℤ => A k l * (c : ℤ → ℂ) l) := by
  refine Summable.of_norm ?_
  have hrow : Summable (fun l : ℤ => ‖A k l‖ * ‖c‖) := (summable_row_decay h k).mul_right ‖c‖
  refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) hrow
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm one_ne_zero c l) (norm_nonneg _)




theorem surjective_opOfMatrix {A : ℤ → ℤ → ℂ}
    (hdecay : Assembly.E7.HasPolynomialOffDiagonalDecay A)
    (hsurj : Assembly.E7.MatrixSurjectiveOnEllOne A) :
    Function.Surjective (Assembly.E7.opOfMatrix A) := by
  intro v
  obtain ⟨y, hy_mem, hy_eq⟩ := hsurj (v : ℤ → ℂ)
    (Assembly.E7.memℓp_one_iff.mp (lp.memℓp v))
  refine ⟨⟨y, Assembly.E7.memℓp_one_iff.mpr hy_mem⟩, ?_⟩
  apply lp.ext
  funext k
  rw [opOfMatrix_apply hdecay]
  exact congrFun hy_eq k




theorem fredholm_inj_surj_to_invertible2_proof
    (g : ℝ → ℝ) (δ : ℤ → ℝ)
    (hdecay : Assembly.E7.HasPolynomialOffDiagonalDecay (Assembly.GaborSubmatrixC g δ))
    (hsurjC : Assembly.E7.MatrixSurjectiveOnEllOne (Assembly.GaborSubmatrixC g δ))
    (hself : Assembly.E7.opOfMatrix (Assembly.GaborSubmatrixC g δ)
      ∈ Assembly.E7.operatorSpectrum (Assembly.E7.opOfMatrix (Assembly.GaborSubmatrixC g δ))) :
    Assembly.MatrixInvertibleOn (2 : ℝ≥0∞) (Assembly.GaborSubmatrixC g δ) := by
  set A : ℤ → ℤ → ℂ := Assembly.GaborSubmatrixC g δ with hA

  have hFred : Assembly.E7.Fredholm (Assembly.E7.opOfMatrix A) :=
    Assembly.E7.E7_surjectivity_implies_Fredholm_thm A hdecay hsurjC

  have hInj : Function.Injective (Assembly.E7.opOfMatrix A) :=
    Assembly.E7.E7_limitOperators_injective_thm (Assembly.E7.opOfMatrix A) hFred
      (Assembly.E7.opOfMatrix A) hself

  have hSurj : Function.Surjective (Assembly.E7.opOfMatrix A) :=
    surjective_opOfMatrix hdecay hsurjC

  haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_refl _⟩
  have hUnit : IsUnit (Assembly.E7.opOfMatrix A) :=
    Assembly.OpConv.isUnit_of_bijective (Assembly.E7.opOfMatrix A) ⟨hInj, hSurj⟩

  have hIsMat : Assembly.IsMatrixOperator (1 : ℝ≥0∞) A (Assembly.E7.opOfMatrix A) := by
    intro x n
    refine ⟨summable_row_matVec hdecay x n, ?_⟩
    exact opOfMatrix_apply hdecay x n
  have hInv1 : Assembly.MatrixInvertibleOn (1 : ℝ≥0∞) A :=
    ⟨Assembly.E7.opOfMatrix A, hIsMat, hUnit⟩

  have hdecayC : Assembly.HasPolynomialOffDiagonalDecayC A := by
    obtain ⟨C, η, hC, hη, hbound⟩ := hdecay
    refine ⟨C, η, hC, hη, ?_⟩
    intro n m
    have hb := hbound n m
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv] at hb
    exact hb

  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  exact Assembly.Ext.E2_SpectralInvariance A hdecayC (1 : ℝ≥0∞) hInv1 (2 : ℝ≥0∞)

end Assembly.Hard

end
