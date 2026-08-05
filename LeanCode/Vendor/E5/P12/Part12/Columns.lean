import LeanCode.Vendor.E5.P12.Part12.Defs
import LeanCode.Vendor.E5.P12.Part12.Envelope
import LeanCode.Vendor.E5.P12.Part12.ParitySplit
import LeanCode.Vendor.E5.Defs
open VendorE5

open MeasureTheory












namespace Part12



theorem split (g : ℝ → ℝ) (hdec : HasExponentialDecay g) :
    ∀ x : ℝ, Halt g x = Acol g x - Bcol g x := by
  obtain ⟨C, c, hC, hc, hbound⟩ := hdec
  intro x
  have habs : Summable (fun k : ℤ => |(-1 : ℝ) ^ k * g (x + k)|) :=
    (summable_halt g C c hC hc hbound x).2.2
  obtain ⟨_, hsplit⟩ := parity_split (fun k : ℤ => (-1 : ℝ) ^ k * g (x + k)) habs
  have hHalt : Halt g x = ∑' k : ℤ, (-1 : ℝ) ^ k * g (x + k) := rfl
  rw [hHalt, hsplit]
  have hEven : (∑' n : ℤ, (-1 : ℝ) ^ (2 * n) * g (x + ((2 * n : ℤ) : ℝ))) = Acol g x := by
    unfold Acol
    refine tsum_congr (fun n => ?_)
    rw [Even.neg_one_zpow (even_two_mul n), one_mul]
    congr 1
    push_cast; ring
  have hOdd : (∑' n : ℤ, (-1 : ℝ) ^ (2 * n + 1) * g (x + ((2 * n + 1 : ℤ) : ℝ)))
      = -Bcol g x := by
    have h1 : (∑' n : ℤ, (-1 : ℝ) ^ (2 * n + 1) * g (x + ((2 * n + 1 : ℤ) : ℝ)))
        = -∑' n : ℤ, g (x + ((2 * n + 1 : ℤ) : ℝ)) := by
      rw [← tsum_neg]
      refine tsum_congr (fun n => ?_)
      rw [Odd.neg_one_zpow (odd_two_mul_add_one n), neg_one_mul]
    rw [h1]
    congr 1
    have h2 : (∑' n : ℤ, g (x + ((2 * n + 1 : ℤ) : ℝ)))
        = ∑' n : ℤ, (fun m : ℤ => g (x - 1 + 2 * m)) (n + 1) := by
      refine tsum_congr (fun n => ?_)
      show g (x + ((2 * n + 1 : ℤ) : ℝ)) = g (x - 1 + 2 * ((n + 1 : ℤ) : ℝ))
      congr 1
      push_cast; ring
    unfold Bcol
    rw [h2, reindex_shift (fun m : ℤ => g (x - 1 + 2 * m))]
  rw [hEven, hOdd]
  ring



theorem shift (g : ℝ → ℝ) :
    ∀ x : ℝ, Acol g (x + 1) = Bcol g x ∧ Bcol g (x + 1) = Acol g x := by
  intro x
  refine ⟨?_, ?_⟩
  ·
    unfold Acol Bcol
    refine (tsum_congr (fun n => ?_)).trans (reindex_shift (fun m : ℤ => g (x - 1 + 2 * m)))
    show g (x + 1 + 2 * (n : ℝ)) = g (x - 1 + 2 * ((n + 1 : ℤ) : ℝ))
    congr 1
    push_cast; ring
  ·
    unfold Acol Bcol
    refine tsum_congr (fun n => ?_)
    show g (x + 1 - 1 + 2 * (n : ℝ)) = g (x + 2 * (n : ℝ))
    congr 1
    ring



theorem cont (g : ℝ → ℝ) (hg : Continuous g) (hdec : HasExponentialDecay g) :
    Continuous (Acol g) ∧ Continuous (Bcol g) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := hdec
  have h2c : (0 : ℝ) < 2 * c := by linarith
  constructor
  ·
    rw [continuous_iff_continuousAt]
    intro x0
    set R := |x0| + 1 with hR
    have hMsum : Summable
        (fun n : ℤ => C * Real.exp (c * (R + 1)) * Real.exp (-(2 * c) * |(n : ℝ)|)) :=
      (exp_summable (2 * c) h2c).mul_left _
    have hcontOn : ContinuousOn (fun x => ∑' n : ℤ, g (x + 2 * n))
        (Set.Icc (x0 - 1) (x0 + 1)) := by
      apply continuousOn_tsum
      · intro n; apply Continuous.continuousOn; fun_prop
      · exact hMsum
      · intro n x hx
        rw [Set.mem_Icc] at hx
        have hxR : |x| ≤ R := by
          rw [hR, abs_le]
          exact ⟨by linarith [neg_abs_le x0, hx.1], by linarith [le_abs_self x0, hx.2]⟩
        rw [Real.norm_eq_abs]
        refine ((summable_cols g C c hC hc hbound x).1.1 n).trans ?_
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hc.le
        linarith [hxR]
    exact hcontOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  ·
    rw [continuous_iff_continuousAt]
    intro x0
    set R := |x0| + 1 with hR
    have hMsum : Summable
        (fun n : ℤ => C * Real.exp (c * (R + 1)) * Real.exp (-(2 * c) * |(n : ℝ)|)) :=
      (exp_summable (2 * c) h2c).mul_left _
    have hcontOn : ContinuousOn (fun x => ∑' n : ℤ, g (x - 1 + 2 * n))
        (Set.Icc (x0 - 1) (x0 + 1)) := by
      apply continuousOn_tsum
      · intro n; apply Continuous.continuousOn; fun_prop
      · exact hMsum
      · intro n x hx
        rw [Set.mem_Icc] at hx
        have hxR : |x| ≤ R := by
          rw [hR, abs_le]
          exact ⟨by linarith [neg_abs_le x0, hx.1], by linarith [le_abs_self x0, hx.2]⟩
        rw [Real.norm_eq_abs]
        refine ((summable_cols g C c hC hc hbound x).2.1 n).trans ?_
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hc.le
        linarith [hxR]
    exact hcontOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

end Part12
