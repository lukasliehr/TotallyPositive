import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic







open scoped ENNReal
noncomputable section
namespace LimitOps



def HasPolynomialOffDiagonalDecay (A : ℤ → ℤ → ℂ) : Prop :=
  ∃ C η : ℝ, 0 < C ∧ 1 < η ∧
    ∀ k l : ℤ, ‖A k l‖ ≤ C * (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)


theorem summable_one_add_abs_rpow {η : ℝ} (hη : 1 < η) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-η)) := by

  rw [summable_int_iff_summable_nat_and_neg]
  have hkey : ∀ x : ℝ, 0 ≤ x → 1 / |x + 1| ^ η = (1 + x) ^ (-η) := by
    intro x hx
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ x + 1),
      add_comm x 1, Real.rpow_neg (by positivity), one_div]
  constructor
  ·
    have h := (Real.summable_one_div_nat_add_rpow 1 η).mpr hη
    refine h.congr (fun n => ?_)
    rw [hkey (n : ℝ) n.cast_nonneg]
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  ·
    have h := (Real.summable_one_div_nat_add_rpow 1 η).mpr hη
    refine h.congr (fun n => ?_)
    rw [hkey (n : ℝ) n.cast_nonneg]
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]


theorem summable_row {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) (k : ℤ) :
    Summable (fun l : ℤ => ‖A k l‖) := by
  obtain ⟨C, η, hC, hη, hbound⟩ := h


  have hdom : Summable (fun l : ℤ => C * (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)) := by
    have hbase := (summable_one_add_abs_rpow hη)
    have hre := (Equiv.subLeft k).summable_iff.mpr hbase
    have : (fun l : ℤ => (1 + |((k - l : ℤ) : ℝ)|) ^ (-η))
        = ((fun n : ℤ => (1 + |(n : ℝ)|) ^ (-η)) ∘ ⇑(Equiv.subLeft k)) := by
      funext l; simp [Equiv.subLeft_apply]
    rw [← this] at hre
    have hre' : Summable (fun l : ℤ => (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)) := by
      refine hre.congr (fun l => ?_)
      push_cast; ring_nf
    exact hre'.mul_left C
  refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => hbound k l) hdom


theorem summable_col {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) (l : ℤ) :
    Summable (fun k : ℤ => ‖A k l‖) := by
  obtain ⟨C, η, hC, hη, hbound⟩ := h
  have hdom : Summable (fun k : ℤ => C * (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)) := by
    have hbase := (summable_one_add_abs_rpow hη)
    have hre := (Equiv.subRight l).summable_iff.mpr hbase
    have : (fun k : ℤ => (1 + |((k - l : ℤ) : ℝ)|) ^ (-η))
        = ((fun n : ℤ => (1 + |(n : ℝ)|) ^ (-η)) ∘ ⇑(Equiv.subRight l)) := by
      funext k; simp [Equiv.subRight_apply]
    rw [← this] at hre
    have hre' : Summable (fun k : ℤ => (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η)) := by
      refine hre.congr (fun k => ?_)
      push_cast; ring_nf
    exact hre'.mul_left C
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hbound k l) hdom


theorem exists_col_sum_bound {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℤ, ∑' k : ℤ, ‖A k l‖ ≤ M := by
  obtain ⟨C, η, hC, hη, hbound⟩ := h
  have hbase := summable_one_add_abs_rpow hη
  refine ⟨C * ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-η), ?_, ?_⟩
  ·
    exact mul_nonneg hC.le (tsum_nonneg (fun n => Real.rpow_nonneg (by positivity) _))
  · intro l

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

end LimitOps
