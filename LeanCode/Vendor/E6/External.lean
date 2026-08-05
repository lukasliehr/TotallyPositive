import LeanCode.Vendor.E6.Defs
import LeanCode.Vendor.E1
import LeanCode.Vendor.E2
import LeanCode.Vendor.E4
import LeanCode.Vendor.E5
import LeanCode.Hard_E6Surj_A














noncomputable section

namespace E6





theorem ExponentialDecay (g : ℝ → ℝ)
    (hg : IsTotallyPositiveIntegrable g) :
    HasExponentialDecay g := by

  have hg1 : ExpDecay.IsTotallyPositiveIntegrable g := by
    refine ⟨?_, hg.2⟩
    intro n a b ha hb
    exact hg.1 n a b ha hb
  exact ExpDecay.ExponentialDecay g hg1




theorem VinogradovUlitskaya (g : ℝ → ℝ) (hg0 : g ≠ 0)
    (hg : IsTotallyPositiveIntegrableContinuous g) :
    ∃! x : ℝ,
      x ∈ Set.Ico (0 : ℝ) 1 ∧
        Z g (ExponentialDecay g ⟨hg.1, hg.2.1⟩) (x, 1 / 2) = 0 := by

  have hg5 : VendorE5.IsTotallyPositiveIntegrableContinuous g := by
    refine ⟨?_, hg.2.1, hg.2.2⟩
    intro n a b ha hb
    exact hg.1 n a b ha hb

  have h5 := VendorE5.VinogradovUlitskaya g hg0 hg5


  exact h5




theorem DFP_Groechnig_Version (A : ℤ → ℤ → ℝ)
    (hTP : IsTotallyPositiveMatrix A)
    (hdecay : HasPolynomialOffDiagonalDecay A)
    (c : ℤ → ℝ)
    (hc : IsBoundedSequence c)
    (halt : IsUniformlyAlternating (MatVec A c))
    (hlower : IsUniformlyBoundedFromBelow (MatVec A c)) :
    ∀ x : ℤ → ℝ, IsBoundedSequence x →
      ∃ y : ℤ → ℝ, IsBoundedSequence y ∧ MatVec A y = x := by

  have hTP4 : VendorE4.IsTotallyPositive A := by
    intro r i j hi hj; exact hTP r i j hi hj
  have hdecay4 : VendorE4.HasPolynomialOffDiagonalDecay A := by
    obtain ⟨C, n, hC, hn, hbd⟩ := hdecay
    refine ⟨C, (n : ℝ), hC, by exact_mod_cast hn, ?_⟩
    intro p q
    have h := hbd p q
    rw [Real.rpow_natCast]
    rwa [Int.norm_eq_abs] at h

  have boundE6toE4 : ∀ u : ℤ → ℝ, IsBoundedSequence u → VendorE4.IsBoundedSequence u := by
    intro u hu
    obtain ⟨M, hM⟩ := hu
    refine ⟨M + 1, by linarith [norm_nonneg (u 0), hM 0], ?_⟩
    intro k
    have := hM k; rw [Real.norm_eq_abs] at this; linarith

  have boundE4toE6 : ∀ u : ℤ → ℝ, VendorE4.IsBoundedSequence u → IsBoundedSequence u := by
    intro u hu
    obtain ⟨M, _, hM⟩ := hu
    exact ⟨M, fun k => by rw [Real.norm_eq_abs]; exact hM k⟩
  have hc4 : VendorE4.IsBoundedSequence c := boundE6toE4 c hc


  have halt4 : VendorE4.IsUniformlyAlternating (VendorE4.MatVec A c) := halt
  have hlower4 : VendorE4.IsUniformlyBoundedFromBelow (VendorE4.MatVec A c) := hlower
  have hE4 := VendorE4.DFP_Groechnig_Version A hTP4 hdecay4 hc4 halt4 hlower4
  intro x hx
  obtain ⟨y, hy4, heq⟩ := hE4 x (boundE6toE4 x hx)
  exact ⟨y, boundE4toE6 y hy4, heq⟩





theorem SurjSpectralInvariance (A : ℤ → ℤ → ℂ)
    (hdecay : HasPolynomialOffDiagonalDecay A) :
    MatrixSurjectiveOn A SequenceSpace.infinity →
      MatrixSurjectiveOn A SequenceSpace.one :=
  Assembly.HardE6SurjA.surjSpectralInvariance_proof A hdecay

end E6
