import LeanCode.Vendor.E4.DFP.Decay
import LeanCode.Vendor.E4.DFP.Reduction

noncomputable section

namespace VendorE4



theorem DFP_Groechnig_Version
  (G : Int -> Int -> Real)
  (h0 : IsTotallyPositive G)
  (h1 : HasPolynomialOffDiagonalDecay G)
  {c : Int -> Real}
  (h4 : IsBoundedSequence c)
  (h2 : IsUniformlyAlternating (MatVec G c))
  (h3 : IsUniformlyBoundedFromBelow (MatVec G c)) :
  forall x : Int -> Real, IsBoundedSequence x ->
    exists y : Int -> Real, IsBoundedSequence y /\ MatVec G y = x := by
  exact
    dfp_surjective_of_uniformly_summable_rows G h0
      (uniformlySummableRows_of_polynomialOffDiagonalDecay h1) h4 h2 h3

end VendorE4
