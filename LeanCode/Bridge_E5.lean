import LeanCode.Vendor.E5
import LeanCode.Vocab
import LeanCode.Base




















noncomputable section




theorem Assembly.Ext.E5_test_thm
    (g : ℝ → ℝ) (h : Assembly.IsTotallyPositiveIntegrableContinuous g) :
    Assembly.HasExponentialDecay g :=
  VendorE5.test g h







theorem Assembly.Ext.E5_VinogradovUlitskaya_thm
    (g : ℝ → ℝ) (hg : g ≠ 0)
    (h : Assembly.IsTotallyPositiveIntegrableContinuous g) :
    ∃! x : ℝ, x ∈ Set.Ico (0:ℝ) 1 ∧
      Assembly.Z g (Assembly.Ext.E5_test_thm g h) (x, 1/2) = 0 :=
  VendorE5.VinogradovUlitskaya g hg h

end
