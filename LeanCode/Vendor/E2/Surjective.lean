import LeanCode.Vendor.E2.Decay

open scoped ENNReal

namespace VendorE2.Lean_Code


theorem SurjSpectralInvariance
    (A : ℤ → ℤ → ℂ)
    (hA : HasPolynomialOffDiagonalDecay A)
    (h_surj : MatrixSurjectiveOn (∞ : ℝ≥0∞) A) :
    MatrixSurjectiveOn (1 : ℝ≥0∞) A := by
  rcases polynomialDecay_to_even_ellOne_domination A hA with
    ⟨a, _ha_even, hdomA, hdomAt⟩
  have hconj_top_one :
      (1 : ℝ≥0∞) = conjugateExponent (∞ : ℝ≥0∞) := by
    exact (ENNReal.HolderConjugate.top_one.conjExponent_eq).symm
  have hAt_below_one : MatrixBoundedBelowOn (1 : ℝ≥0∞) (transposeMatrix A) :=
    transpose_lower_bound_of_surjective A a hdomA hdomAt
      (∞ : ℝ≥0∞) (1 : ℝ≥0∞) hconj_top_one h_surj
  have hAt_below_top : MatrixBoundedBelowOn (∞ : ℝ≥0∞) (transposeMatrix A) :=
    propagate_lower_bound (transposeMatrix A) a hdomAt (1 : ℝ≥0∞) hAt_below_one
      (∞ : ℝ≥0∞)
  have hconj_one_top :
      (∞ : ℝ≥0∞) = conjugateExponent (1 : ℝ≥0∞) := by
    exact (ENNReal.HolderConjugate.one_top.conjExponent_eq).symm
  exact surjective_of_transpose_lower_bound A a hdomA hdomAt
    (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (by simp) hconj_one_top hAt_below_top

end VendorE2.Lean_Code
