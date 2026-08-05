import LeanCode.Vendor.E7.Operators
import LeanCode.Vendor.E7.Decay
import Mathlib.Analysis.Normed.Operator.Basic







open scoped ENNReal
noncomputable section
namespace LimitOps




theorem summable_row_mul {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) (c : ℓ1) (k : ℤ) :
    Summable (fun l : ℤ => ‖A k l‖ * ‖(c : ℤ → ℂ) l‖) := by
  have hrow : Summable (fun l : ℤ => ‖A k l‖ * ‖c‖) := (summable_row h k).mul_right ‖c‖
  refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) hrow
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm one_ne_zero c l) (norm_nonneg _)


theorem summable_row_matVec {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) (c : ℓ1)
    (k : ℤ) : Summable (fun l : ℤ => A k l * (c : ℤ → ℂ) l) := by
  refine Summable.of_norm ?_
  refine (summable_row_mul h c k).congr (fun l => ?_)
  rw [norm_mul]





theorem tsum_ofReal_norm_matVec_le {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A)
    {M : ℝ} (hMbound : ∀ l : ℤ, ∑' k : ℤ, ‖A k l‖ ≤ M) (c : ℓ1) :
    (∑' k : ℤ, ENNReal.ofReal ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖)
      ≤ ENNReal.ofReal (M * ‖c‖) := by

  have hrowbound : ∀ k : ℤ,
      ENNReal.ofReal ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖
        ≤ ∑' l : ℤ, ENNReal.ofReal (‖A k l‖ * ‖(c : ℤ → ℂ) l‖) := by
    intro k
    have hnorm : ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖
        ≤ ∑' l : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖ := by
      have := norm_tsum_le_tsum_norm
        (f := fun l : ℤ => A k l * (c : ℤ → ℂ) l)
        (by
          refine (summable_row_mul h c k).congr (fun l => ?_)
          rw [norm_mul])
      refine this.trans_eq ?_
      exact tsum_congr (fun l => by rw [norm_mul])
    calc ENNReal.ofReal ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖
        ≤ ENNReal.ofReal (∑' l : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖) :=
          ENNReal.ofReal_le_ofReal hnorm
      _ = ∑' l : ℤ, ENNReal.ofReal (‖A k l‖ * ‖(c : ℤ → ℂ) l‖) :=
          ENNReal.ofReal_tsum_of_nonneg (fun l => by positivity) (summable_row_mul h c k)

  calc (∑' k : ℤ, ENNReal.ofReal ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖)
      ≤ ∑' k : ℤ, ∑' l : ℤ, ENNReal.ofReal (‖A k l‖ * ‖(c : ℤ → ℂ) l‖) :=
        ENNReal.tsum_le_tsum hrowbound
    _ = ∑' l : ℤ, ∑' k : ℤ, ENNReal.ofReal (‖A k l‖ * ‖(c : ℤ → ℂ) l‖) := ENNReal.tsum_comm
    _ = ∑' l : ℤ, (∑' k : ℤ, ENNReal.ofReal ‖A k l‖) * ENNReal.ofReal ‖(c : ℤ → ℂ) l‖ := by
        refine tsum_congr (fun l => ?_)
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr (fun k => ?_)
        rw [ENNReal.ofReal_mul (norm_nonneg _)]
    _ = ∑' l : ℤ, ENNReal.ofReal (∑' k : ℤ, ‖A k l‖) * ENNReal.ofReal ‖(c : ℤ → ℂ) l‖ := by
        refine tsum_congr (fun l => ?_)
        congr 1
        exact (ENNReal.ofReal_tsum_of_nonneg (fun k => norm_nonneg _) (summable_col h l)).symm
    _ ≤ ∑' l : ℤ, ENNReal.ofReal M * ENNReal.ofReal ‖(c : ℤ → ℂ) l‖ := by
        refine ENNReal.tsum_le_tsum (fun l => ?_)
        gcongr
        exact hMbound l
    _ = ENNReal.ofReal M * ∑' l : ℤ, ENNReal.ofReal ‖(c : ℤ → ℂ) l‖ := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal M * ENNReal.ofReal (∑' l : ℤ, ‖(c : ℤ → ℂ) l‖) := by
        congr 1
        exact (ENNReal.ofReal_tsum_of_nonneg (fun l => norm_nonneg _)
          (memℓp_one_iff.mp (lp.memℓp c))).symm
    _ = ENNReal.ofReal (M * ‖c‖) := by
        have hM0 : 0 ≤ M :=
          le_trans (tsum_nonneg (fun k => norm_nonneg _)) (hMbound 0)
        rw [← ENNReal.ofReal_mul hM0, norm_eq_tsum]


theorem memℓp_matVec {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) (c : ℓ1) :
    Memℓp (fun k : ℤ => ∑' l : ℤ, A k l * (c : ℤ → ℂ) l) 1 := by
  refine memℓp_one_iff.mpr ?_
  obtain ⟨M, _hM0, hMbound⟩ := exists_col_sum_bound h
  have hfin : (∑' k : ℤ, ENNReal.ofReal ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tsum_ofReal_norm_matVec_le h hMbound c)
  have hsum := ENNReal.summable_toReal hfin
  refine hsum.congr (fun k => ?_)
  exact ENNReal.toReal_ofReal (norm_nonneg _)


theorem exists_bound_matVec {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℓ1,
      (∑' k : ℤ, ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖) ≤ M * ‖c‖ := by
  obtain ⟨M, hM0, hMbound⟩ := exists_col_sum_bound h
  refine ⟨M, hM0, fun c => ?_⟩
  have hsummable : Summable (fun k : ℤ => ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖) :=
    memℓp_one_iff.mp (memℓp_matVec h c)
  have hkey : ENNReal.ofReal (∑' k : ℤ, ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖)
      ≤ ENNReal.ofReal (M * ‖c‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => norm_nonneg _) hsummable]
    exact tsum_ofReal_norm_matVec_le h hMbound c
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM0 (norm_nonneg _))).mp hkey


def matVecLM {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) : ℓ1 →ₗ[ℂ] ℓ1 where
  toFun c := ⟨fun k => ∑' l : ℤ, A k l * (c : ℤ → ℂ) l, memℓp_matVec h c⟩
  map_add' c d := by
    apply lp.ext
    funext k
    show (∑' l : ℤ, A k l * ((c + d : ℓ1) : ℤ → ℂ) l)
        = (∑' l : ℤ, A k l * (c : ℤ → ℂ) l) + ∑' l : ℤ, A k l * (d : ℤ → ℂ) l
    rw [← (summable_row_matVec h c k).tsum_add (summable_row_matVec h d k)]
    refine tsum_congr (fun l => ?_)
    rw [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' r c := by
    apply lp.ext
    funext k
    show (∑' l : ℤ, A k l * ((r • c : ℓ1) : ℤ → ℂ) l)
        = r • ∑' l : ℤ, A k l * (c : ℤ → ℂ) l
    rw [smul_eq_mul, ← tsum_mul_left]
    refine tsum_congr (fun l => ?_)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

theorem norm_matVecLM_le {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A)
    {M : ℝ} (hbound : ∀ c : ℓ1, (∑' k : ℤ, ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖) ≤ M * ‖c‖)
    (c : ℓ1) : ‖matVecLM h c‖ ≤ M * ‖c‖ := by
  rw [norm_eq_tsum]
  exact hbound c


theorem exists_bounded_realizing {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) :
    ∃ T : ℓ1 →L[ℂ] ℓ1, ∀ (c : ℓ1) (k : ℤ),
      (T c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l := by
  obtain ⟨M, _hM0, hbound⟩ := exists_bound_matVec h
  refine ⟨(matVecLM h).mkContinuous M (norm_matVecLM_le h hbound), fun c k => ?_⟩
  rfl

end LimitOps
