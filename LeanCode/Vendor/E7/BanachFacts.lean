import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient







noncomputable section
namespace LimitOps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]



theorem isUnit_one_sub_of_norm_lt_one (x : E →L[ℂ] E) (hx : ‖x‖ < 1) :
    IsUnit (1 - x) :=
  (Units.oneSub x hx).isUnit


theorem norm_inverse_one_sub_le (x : E →L[ℂ] E) (hx : ‖x‖ < 1)
    (u : (E →L[ℂ] E)ˣ) (hu : (u : E →L[ℂ] E) = 1 - x) :
    ‖(↑u⁻¹ : E →L[ℂ] E)‖ ≤ (1 - ‖x‖)⁻¹ := by


  have hval : (u : E →L[ℂ] E) = (Units.oneSub x hx : E →L[ℂ] E) := by
    rw [hu, Units.val_oneSub]
  have huv : u = Units.oneSub x hx := Units.ext hval
  have hinv : (↑u⁻¹ : E →L[ℂ] E) = ∑' n : ℕ, x ^ n := by
    rw [huv]; rfl
  rw [hinv]

  have hsummable : Summable fun n : ℕ => ‖x ^ n‖ :=
    summable_norm_geometric_of_norm_lt_one hx


  have hterm : ∀ n : ℕ, ‖x ^ n‖ ≤ ‖x‖ ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa only [pow_zero, ContinuousLinearMap.one_def] using ContinuousLinearMap.norm_id_le
    · exact norm_pow_le' x hn
  have hsummable' : Summable fun n : ℕ => ‖x‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg x) hx
  calc ‖∑' n : ℕ, x ^ n‖ ≤ ∑' n : ℕ, ‖x ^ n‖ := norm_tsum_le_tsum_norm hsummable
    _ ≤ ∑' n : ℕ, ‖x‖ ^ n := hsummable.tsum_le_tsum hterm hsummable'
    _ = (1 - ‖x‖)⁻¹ := tsum_geometric_of_lt_one (norm_nonneg x) hx




theorem exists_lower_bound_of_isClosed_range (T : E →L[ℂ] E)
    (hT : IsClosed (Set.range T)) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : E,
      c * Metric.infDist z (LinearMap.ker T.toLinearMap : Set E) ≤ ‖T z‖ := by
  set K : Submodule ℂ E := LinearMap.ker T.toLinearMap with hK

  haveI hKclosed : IsClosed (K : Set E) := T.isClosed_ker
  haveI : CompleteSpace (E ⧸ K) := Submodule.Quotient.completeSpace K

  set Tbar : (E ⧸ K) →L[ℂ] E := K.liftQL T (le_of_eq hK) with hTbar

  have hker_bot : LinearMap.ker (Tbar : (E ⧸ K) →ₗ[ℂ] E) = ⊥ :=
    Submodule.ker_liftQ_eq_bot' K T.toLinearMap hK
  have hTbar_inj : Function.Injective Tbar := by
    have : Function.Injective (Tbar : (E ⧸ K) →ₗ[ℂ] E) := LinearMap.ker_eq_bot.mp hker_bot
    simpa only [ContinuousLinearMap.coe_coe] using this

  have hrange : LinearMap.range (Tbar : (E ⧸ K) →ₗ[ℂ] E) = LinearMap.range T.toLinearMap :=
    Submodule.range_liftQ K T.toLinearMap (le_of_eq hK)
  have hTbar_range : Set.range Tbar = Set.range T := by
    have h1 := congrArg (fun (s : Submodule ℂ E) => (s : Set E)) hrange
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.range_toLinearMap] using h1
  have hTbar_closed : IsClosed (Set.range Tbar) := by rw [hTbar_range]; exact hT

  obtain ⟨Kc, hKc⟩ :=
    Tbar.antilipschitz_of_injective_of_isClosed_range hTbar_inj hTbar_closed
  refine ⟨((Kc : ℝ) + 1)⁻¹, by positivity, fun z => ?_⟩

  have happ : Tbar (Submodule.Quotient.mk z) = T z := by
    rw [hTbar, Submodule.liftQL_apply, Submodule.liftQ_apply]; rfl

  have hdist := hKc.le_mul_dist (Submodule.Quotient.mk z) 0
  rw [dist_zero_right, map_zero, dist_zero_right, happ] at hdist

  have hnorm : ‖(Submodule.Quotient.mk z : E ⧸ K)‖ = Metric.infDist z (K : Set E) := by
    rw [show (Submodule.Quotient.mk z : E ⧸ K) = ((z : E) : E ⧸ K.toAddSubgroup) from rfl]
    exact QuotientAddGroup.norm_mk z
  rw [hnorm] at hdist
  have hle : Metric.infDist z (K : Set E) ≤ ((Kc : ℝ) + 1) * ‖T z‖ := by
    refine hdist.trans ?_
    gcongr
    exact le_add_of_nonneg_right zero_le_one
  calc ((Kc : ℝ) + 1)⁻¹ * Metric.infDist z (K : Set E)
      ≤ ((Kc : ℝ) + 1)⁻¹ * (((Kc : ℝ) + 1) * ‖T z‖) := by
        gcongr
    _ = ‖T z‖ := by
        rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end LimitOps
