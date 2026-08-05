import LeanCode.Vendor.E5.P8.Main
import LeanCode.Vendor.E5.Defs

open MeasureTheory









theorem Part_8_main : Statement_Part_8 := by
  intro g hH1 hH2 hH3 hS
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact Part8.acol_pos g hH1 hH2 hH3 hS x
  · intro x
    exact Part8.bcol_pos g hH1 hH2 hH3 hS x
  · rcases hS with ⟨Cst, γ, δ, α, hCst, hγ_nonneg, hsum, hmul, hFT, hFT_ne, hbound⟩
    have hdata : Part8.SchoenbergData g Cst γ δ α :=
      ⟨hCst, hγ_nonneg, hsum, hmul, hFT, hFT_ne, hbound⟩
    by_cases hγpos : 0 < γ
    · exact Or.inr (Or.inl (Part8.caseG g Cst γ δ α hH1 hH2 hH3 hdata hγpos))
    · have hγzero : γ = 0 := le_antisymm (le_of_not_gt hγpos) hγ_nonneg
      by_cases hfin : (Part8.nonzeroFactorSet α).Finite
      · exact Or.inl (Part8.caseF g Cst γ δ α hH1 hH2 hH3 hdata hγzero hfin)
      · have hinf : (Part8.nonzeroFactorSet α).Infinite := (Set.not_finite).1 hfin
        exact Or.inr
          (Or.inr (Part8.caseI g Cst γ δ α hH1 hH2 hH3 hdata hγzero hinf))
