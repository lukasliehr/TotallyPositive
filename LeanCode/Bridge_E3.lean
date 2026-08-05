import LeanCode.Vendor.E3
import LeanCode.Vocab
import LeanCode.Base




















noncomputable section




theorem Assembly.Ext.E3_SubmatrixCriterion_thm
    {α : ℝ} (hα : 0 < α) (h1 : α < 1)
    (g : ℝ → ℝ) (hg : Continuous g) (h2 : Assembly.HasPolynomialDecay g)
    (h3 : Assembly.SubmatrixCondition g α) :
    Assembly.IsGaborFrame g hg h2 α 1 :=
  VendorE3.SubmatrixCriterion hα h1 g hg h2 h3

end
