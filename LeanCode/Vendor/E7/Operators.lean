import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Operator.Basic







open scoped ENNReal
noncomputable section
namespace LimitOps


abbrev ℓ1 : Type := lp (fun _ : ℤ => ℂ) 1



theorem memℓp_one_iff {f : ℤ → ℂ} : Memℓp f 1 ↔ Summable (fun k : ℤ => ‖f k‖) := by
  have hp : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp]
  simp only [ENNReal.toReal_one, Real.rpow_one]


theorem norm_eq_tsum (c : ℓ1) : ‖c‖ = ∑' k : ℤ, ‖(c : ℤ → ℂ) k‖ := by
  have hp : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp c]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]



theorem memℓp_shift (c : ℓ1) (m : ℤ) :
    Memℓp (fun k : ℤ => (c : ℤ → ℂ) (k - m)) 1 := by
  refine memℓp_one_iff.mpr ?_
  have hc : Summable (fun k : ℤ => ‖(c : ℤ → ℂ) k‖) := memℓp_one_iff.mp (lp.memℓp c)
  exact (Equiv.subRight m).summable_iff.mpr hc

def shiftLM (m : ℤ) : ℓ1 →ₗ[ℂ] ℓ1 where
  toFun c := ⟨fun k => (c : ℤ → ℂ) (k - m), memℓp_shift c m⟩
  map_add' c d := by
    apply lp.ext
    funext k
    simp only [lp.coeFn_add, Pi.add_apply]
  map_smul' r c := by
    apply lp.ext
    funext k
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]

theorem norm_shiftLM_le (m : ℤ) (c : ℓ1) : ‖shiftLM m c‖ ≤ 1 * ‖c‖ := by
  rw [one_mul, norm_eq_tsum, norm_eq_tsum]
  have h : ∑' k : ℤ, ‖(shiftLM m c : ℤ → ℂ) k‖ = ∑' k : ℤ, ‖(c : ℤ → ℂ) k‖ := by
    show ∑' k : ℤ, ‖(c : ℤ → ℂ) (k - m)‖ = ∑' k : ℤ, ‖(c : ℤ → ℂ) k‖
    have := (Equiv.subRight m).tsum_eq (fun k => ‖(c : ℤ → ℂ) k‖)
    simpa using this
  rw [h]


def shiftCLM (m : ℤ) : ℓ1 →L[ℂ] ℓ1 := (shiftLM m).mkContinuous 1 (norm_shiftLM_le m)

theorem shiftCLM_apply (m : ℤ) (c : ℓ1) (k : ℤ) :
    (shiftCLM m c : ℤ → ℂ) k = (c : ℤ → ℂ) (k - m) := rfl




theorem norm_proj_le (c : ℓ1) (n : ℕ) (k : ℤ) :
    ‖(if |k| ≤ (n : ℤ) then (c : ℤ → ℂ) k else 0)‖ ≤ ‖(c : ℤ → ℂ) k‖ := by
  by_cases hk : |k| ≤ (n : ℤ)
  · rw [if_pos hk]
  · rw [if_neg hk, norm_zero]
    positivity

theorem memℓp_proj (c : ℓ1) (n : ℕ) :
    Memℓp (fun k : ℤ => if |k| ≤ (n : ℤ) then (c : ℤ → ℂ) k else 0) 1 := by
  refine memℓp_one_iff.mpr ?_
  have hc : Summable (fun k : ℤ => ‖(c : ℤ → ℂ) k‖) := memℓp_one_iff.mp (lp.memℓp c)
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_proj_le c n k) hc

def projLM (n : ℕ) : ℓ1 →ₗ[ℂ] ℓ1 where
  toFun c := ⟨fun k => if |k| ≤ (n : ℤ) then (c : ℤ → ℂ) k else 0, memℓp_proj c n⟩
  map_add' c d := by
    apply lp.ext
    funext k
    simp only [lp.coeFn_add, Pi.add_apply]
    split <;> simp
  map_smul' r c := by
    apply lp.ext
    funext k
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    split <;> simp

theorem norm_projLM_le (n : ℕ) (c : ℓ1) : ‖projLM n c‖ ≤ 1 * ‖c‖ := by
  rw [one_mul, norm_eq_tsum, norm_eq_tsum]
  have hsum_lhs : Summable (fun k : ℤ => ‖(projLM n c : ℤ → ℂ) k‖) :=
    memℓp_one_iff.mp (lp.memℓp (projLM n c))
  have hsum_rhs : Summable (fun k : ℤ => ‖(c : ℤ → ℂ) k‖) :=
    memℓp_one_iff.mp (lp.memℓp c)
  exact hsum_lhs.tsum_le_tsum (fun k => norm_proj_le c n k) hsum_rhs


def projCLM (n : ℕ) : ℓ1 →L[ℂ] ℓ1 := (projLM n).mkContinuous 1 (norm_projLM_le n)

theorem projCLM_apply (n : ℕ) (c : ℓ1) (k : ℤ) :
    (projCLM n c : ℤ → ℂ) k = if |k| ≤ (n : ℤ) then (c : ℤ → ℂ) k else 0 := rfl

end LimitOps
