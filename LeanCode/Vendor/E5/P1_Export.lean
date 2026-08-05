import Mathlib
import LeanCode.Vendor.E5.P1.MainTheorem
import LeanCode.Vendor.E5.Defs

open MeasureTheory














theorem Part_1_main : Statement_Part_1 := by
  intro g hg
  have htp : VendorE5ExpDecay.IsTotallyPositive g := by
    intro n a b ha hb
    exact hg.1 n a b ha hb
  exact VendorE5ExpDecay.ExponentialDecay g ⟨htp, hg.2.1⟩

#print axioms Part_1_main
