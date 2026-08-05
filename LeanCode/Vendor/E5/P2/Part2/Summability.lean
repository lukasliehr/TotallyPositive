import LeanCode.Vendor.E5.P2.Part2.Basic
import LeanCode.Vendor.E5.Defs

open MeasureTheory











namespace Part2


theorem exp_ratio (c : ℝ) (hc : 0 < c) :
    0 ≤ Real.exp (-c) ∧ Real.exp (-c) < 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_lt_one_iff.mpr (by linarith)⟩



theorem geom_nat (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c * n)) := by
  have hfun : (fun n : ℕ => Real.exp (-c * n)) = (fun n : ℕ => Real.exp (-c) ^ n) := by
    funext n
    rw [show (-c * (n : ℝ)) = ((n : ℝ) * (-c)) from by ring, Real.exp_nat_mul]
  rw [hfun]
  exact summable_geometric_of_lt_one (exp_ratio c hc).1 (exp_ratio c hc).2



theorem exp_int_summable (c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℤ => Real.exp (-c * |(k : ℝ)|)) := by
  apply Summable.of_nat_of_neg_add_one (f := fun k : ℤ => Real.exp (-c * |(k : ℝ)|))
  ·
    refine (geom_nat c hc).congr (fun n => ?_)
    congr 1
    rw [Int.cast_natCast, abs_of_nonneg (by positivity)]
  ·
    refine ((geom_nat c hc).mul_left (Real.exp (-c))).congr (fun n => ?_)
    rw [← Real.exp_add]
    congr 1
    rw [show (((-((n : ℤ) + 1)) : ℤ) : ℝ) = -((n : ℝ) + 1) from by push_cast; ring,
        abs_neg, abs_of_nonneg (by positivity)]
    ring



theorem rev_triangle (x y : ℝ) : |y| - |x| ≤ |x + y| := by
  have h := abs_add_le (x + y) (-x)
  rw [show (x + y) + (-x) = y from by ring, abs_neg] at h
  linarith



theorem envelope (f : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hb : ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|)) (R : ℝ) (_hR : 0 ≤ R)
    (k : ℤ) (x : ℝ) (hx : |x| ≤ R) :
    |(-1 : ℝ) ^ k * f (x + k)| ≤ C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|) := by
  have hsign : |(-1 : ℝ) ^ k| = 1 := by rw [abs_zpow]; norm_num
  rw [abs_mul, hsign, one_mul]
  calc |f (x + k)|
      ≤ C * Real.exp (-c * |x + k|) := hb (x + k)
    _ ≤ C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|) := by
        rw [mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        refine Real.exp_le_exp.mpr ?_
        have hk : |(k : ℝ)| - R ≤ |x + (k : ℝ)| := by
          have hrev := rev_triangle x (k : ℝ); linarith
        nlinarith [mul_le_mul_of_nonneg_left hk hc.le]



theorem envelope_summable (C c R : ℝ) (hc : 0 < c) :
    Summable (fun k : ℤ => C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|)) :=
  (exp_int_summable c hc).mul_left (C * Real.exp (c * R))




theorem abs_summable (f : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hb : ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|)) (x : ℝ) :
    Summable (fun k : ℤ => |(-1 : ℝ) ^ k * f (x + k)|) ∧
    Summable (fun k : ℤ => (-1 : ℝ) ^ k * f (x + k)) := by
  have habs : Summable (fun k : ℤ => |(-1 : ℝ) ^ k * f (x + k)|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _)
      (fun k => envelope f C c hC hc hb |x| (abs_nonneg x) k x (le_refl _))
      (envelope_summable C c |x| hc)
  exact ⟨habs, summable_abs_iff.mp habs⟩

end Part2
