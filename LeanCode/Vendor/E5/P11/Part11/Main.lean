import LeanCode.Vendor.E5.P11.Part11.Core
import LeanCode.Vendor.E5.Defs
















theorem Part_11_main : Statement_Part_11 := by
  intro R _hcont hpos hfe hcyc hne r s hr hs hRr hRs
  rw [Set.mem_Ico] at hr hs
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hs0, hs1⟩ := hs
  rcases lt_trichotomy r s with hlt | heq | hgt
  · exact absurd ⟨r, s, hr0, hlt, hs1, hRr, hRs⟩ (core R hpos hfe hcyc hne)
  · exact heq
  · exact absurd ⟨s, r, hs0, hgt, hr1, hRs, hRr⟩ (core R hpos hfe hcyc hne)
