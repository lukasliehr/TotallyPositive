import LeanCode.Vendor.E5.P2.Part2.Basic
import LeanCode.Vendor.E5.Defs

open MeasureTheory











namespace Part2



theorem sign_succ (k : ℤ) :
    (-1 : ℝ) ^ (k + 1) = -(-1 : ℝ) ^ k ∧ (-1 : ℝ) ^ (k - 1) = -(-1 : ℝ) ^ k := by
  constructor
  · rw [zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]; ring
  · rw [zpow_sub_one₀ (by norm_num : (-1 : ℝ) ≠ 0), inv_neg_one]; ring


theorem sign_neg (k : ℤ) : (-1 : ℝ) ^ (-k) = (-1 : ℝ) ^ k := by
  rw [zpow_neg, ← inv_zpow, inv_neg_one]



theorem exp_zpow (z : ℂ) (k : ℤ) :
    Complex.exp ((k : ℂ) * z) = Complex.exp z ^ k :=
  Complex.exp_int_mul z k



theorem exp_half (k : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((1 / 2 : ℝ) : ℂ))
      = (-1 : ℂ) ^ k := by
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((1 / 2 : ℝ) : ℂ))
        = (k : ℂ) * ((Real.pi : ℂ) * Complex.I) from by push_cast; ring,
    exp_zpow, Complex.exp_pi_mul_I]



theorem coe_bridge (k : ℤ) (t : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((1 / 2 : ℝ) : ℂ)) * (t : ℂ)
      = (((-1 : ℝ) ^ k * t : ℝ) : ℂ) := by
  rw [exp_half]
  push_cast
  ring

end Part2
