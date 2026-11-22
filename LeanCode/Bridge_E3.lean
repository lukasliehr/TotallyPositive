module

public import LeanCode.Vendor.E3
public import LeanCode.Vocab
public import LeanCode.Base

@[expose] public section

noncomputable section




theorem Assembly.Ext.E3_SubmatrixCriterion_thm
    {α : ℝ} (hα : 0 < α) (h1 : α < 1)
    (g : ℝ → ℝ) (hg : Continuous g) (h2 : Assembly.HasPolynomialDecay g)
    (h3 : Assembly.SubmatrixCondition g α) :
    Assembly.IsGaborFrame g hg h2 α 1 :=
  VendorE3.SubmatrixCriterion hα h1 g hg h2 h3

theorem Assembly.Ext.E3_SubmatrixCriterion_summable_thm
    {α : ℝ} (hα : 0 < α)
    (g : ℝ → ℝ) (hg : Continuous g) (h2 : Assembly.HasPolynomialDecay g)
    (h3 : Assembly.SubmatrixCondition g α)
    (x : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    Summable (fun p : ℤ × ℤ =>
      ‖inner ℂ x (Assembly.GaborAtom_L2 g hg h2 α 1 p.1 p.2)‖ ^ 2) :=
  VendorE3.SubmatrixCriterion_summable hα g hg h2 h3 x

end
