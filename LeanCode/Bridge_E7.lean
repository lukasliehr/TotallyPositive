import LeanCode.Vendor.E7
import LeanCode.E7Vocab






















noncomputable section




theorem Assembly.E7.E7_surjectivity_implies_Fredholm_thm
    (A : ℤ → ℤ → ℂ) (hdecay : Assembly.E7.HasPolynomialOffDiagonalDecay A)
    (hsurj : Assembly.E7.MatrixSurjectiveOnEllOne A) :
    Assembly.E7.Fredholm (Assembly.E7.opOfMatrix A) := by
  have h : LimitOps.Fredholm (LimitOps.opOfMatrix A) :=
    LimitOps.thm_surjectivity_implies_Fredholm A hdecay hsurj
  exact ⟨h.isClosed_range, h.finiteDimensional_ker, h.finiteDimensional_coker⟩




theorem Assembly.E7.E7_limitOperators_injective_thm
    (A : Assembly.E7.ℓ1 →L[ℂ] Assembly.E7.ℓ1) (hA : Assembly.E7.Fredholm A) :
    ∀ B ∈ Assembly.E7.operatorSpectrum A, Function.Injective B := by
  have hA' : LimitOps.Fredholm A :=
    ⟨hA.isClosed_range, hA.finiteDimensional_ker, hA.finiteDimensional_coker⟩
  exact LimitOps.thm_limitOperators_injective A hA'

end
