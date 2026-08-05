import Mathlib
import LeanCode.Vendor.E5.Defs

open MeasureTheory














namespace Part4



def PointwiseOneCrossing (F : ℝ → ℝ) (r ε : ℝ) : Prop :=
  (∀ x : ℝ, r - 1 < x → x < r → ε * F x < 0) ∧
  (∀ x : ℝ, r < x → x < r + 1 → 0 < ε * F x)

end Part4
