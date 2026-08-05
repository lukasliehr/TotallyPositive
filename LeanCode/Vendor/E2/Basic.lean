import Mathlib

open Matrix
open MeasureTheory
open scoped ENNReal
open lp

namespace VendorE2.Lean_Code


abbrev ellp (p : ℝ≥0∞) : Type := lp (fun _ : ℤ => ℂ) p


def OperatorBoundedBelow {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : ellp p →L[ℂ] ellp p) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : ellp p, c * ‖x‖ ≤ ‖T x‖

end VendorE2.Lean_Code
