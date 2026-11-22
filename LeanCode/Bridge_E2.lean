module

public import LeanCode.Vendor.E2
public import LeanCode.Vocab
public import LeanCode.Base

@[expose] public section

open scoped ENNReal





theorem Assembly.Ext.E2_SpectralInvariance_thm
    (A : ℤ → ℤ → ℂ) (hA : Assembly.HasPolynomialOffDiagonalDecayC A)
    (p₀ : ℝ≥0∞) [Fact (1 ≤ p₀)] (h_inv : Assembly.MatrixInvertibleOn p₀ A) :
    ∀ q : ℝ≥0∞, [Fact (1 ≤ q)] → Assembly.MatrixInvertibleOn q A :=
  VendorE2.Lean_Code.SpectralInvariance A hA p₀ h_inv
