import LeanCode.Vendor.E5.P4.Part4.Main
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open Part4









theorem Part_4_main : Statement_Part_4 := by
  intro m hm a ha
  exact ⟨(regularity m a ha).2.2.2.2 hm,
    (regularity m a ha).2.2.2.1.1,
    (regularity m a ha).2.2.1,
    ((main_induction m a ha).2.2 hm).2⟩
