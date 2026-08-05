import LeanCode.Vendor.E2.Basic

open scoped ENNReal

namespace VendorE2.Lean_Code


def IsMatrixOperator (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ)
    (T : ellp p →L[ℂ] ellp p) : Prop :=
  ∀ x : ellp p, ∀ n : ℤ,
    Summable (fun m : ℤ => A n m * x m) ∧
      (T x) n = ∑' m : ℤ, A n m * x m


def HasPolynomialOffDiagonalDecay (A : ℤ → ℤ → ℂ) : Prop :=
  ∃ C η : ℝ, 0 < C ∧ 1 < η ∧
    ∀ n m : ℤ, ‖A n m‖ ≤ C / (1 + |(n - m : ℝ)|)^η


def MatrixInvertibleOn (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) : Prop :=
  ∃ T : ellp p →L[ℂ] ellp p, IsMatrixOperator p A T ∧ IsUnit T


def MatrixSurjectiveOn (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) : Prop :=
  ∃ T : ellp p →L[ℂ] ellp p, IsMatrixOperator p A T ∧ Function.Surjective T


def MatrixBoundedBelowOn (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) : Prop :=
  ∃ T : ellp p →L[ℂ] ellp p, IsMatrixOperator p A T ∧ OperatorBoundedBelow T

end VendorE2.Lean_Code
