import LeanCode.Vendor.E5.P7.Part7.Basic
import LeanCode.Vendor.E5.P7.Part7.ProdHelpers
import LeanCode.Vendor.E5.P7.Part7.Laplace
import LeanCode.Vendor.E5.P7.Part7.Psi
import LeanCode.Vendor.E5.P7.Part7.ImaginaryAxis
import LeanCode.Vendor.E5.Defs

open Part7
















theorem Part_7_main (h5 : Statement_Part_5) (h6 : Statement_Part_6) :
    Statement_Part_7 := by
  intro g hTPIC hg0 hdecay
  obtain ⟨C, c, hC, hc, hbound⟩ := hdecay
  have hgcont : Continuous g := hTPIC.2.2
  obtain ⟨β, hβmr, hβ0, hβreal⟩ := h5 g hTPIC hg0 ⟨C, c, hC, hc, hbound⟩
  obtain ⟨γ₀, δ₀, α, hγ₀nn, hαsq, hprod6⟩ := h6 β hβ0 hβreal
  have hconv : ∀ s : ℂ, Summable (fun m : ℕ => ((β m / m.factorial : ℝ) : ℂ) * s ^ m) :=
    fun s => (hprod6 s).2.summable

  have hkey : ∀ ξ : ℝ, ∃ L : ℂ,
      HasProd (fun ν => Efac (α ν) (2 * Real.pi * Complex.I * ξ)) L ∧ L ≠ 0 ∧
      FT g ξ = F g (2 * Real.pi * Complex.I * ξ) ∧
      F g (2 * Real.pi * Complex.I * ξ) = (Psi β (2 * Real.pi * Complex.I * ξ))⁻¹ ∧
      Psi β (2 * Real.pi * Complex.I * ξ)
        = (β 0 : ℂ) * Complex.exp (-(γ₀ : ℂ) * (2 * Real.pi * Complex.I * ξ) ^ 2
            + (δ₀ : ℂ) * (2 * Real.pi * Complex.I * ξ)) * L ∧
      Multipliable (fun ν : ℕ => expFactor (α ν) ξ) ∧
      (∏' ν : ℕ, expFactor (α ν) ξ) = L⁻¹ ∧ (1 : ℝ) ≤ ‖L‖ := by
    intro ξ
    have hFTF := FT_eq_F g C c hC hc hgcont hbound ξ
    have hsS : (2 * Real.pi * Complex.I * ξ) ∈ strip c := hFTF.1
    have hFnz := F_nonzero g C c hC hc hgcont hbound β hβmr hconv _ hsS
    have hmult : Multipliable (fun ν => Efac (α ν) (2 * Real.pi * Complex.I * ξ)) := (hprod6 _).1
    have hLprod := hmult.hasProd
    have hΨval : Psi β (2 * Real.pi * Complex.I * ξ)
        = (β 0 : ℂ) * Complex.exp (-(γ₀ : ℂ) * (2 * Real.pi * Complex.I * ξ) ^ 2
            + (δ₀ : ℂ) * (2 * Real.pi * Complex.I * ξ)) * ∏' ν, Efac (α ν) (2 * Real.pi * Complex.I * ξ) :=
      (hprod6 _).2.tsum_eq
    have hLne := L_nonzero ξ _ rfl (β 0) γ₀ δ₀ hβ0 α _ _ hLprod hΨval hFnz.2.1
    have hphi := phi_multipliable ξ _ rfl α _ hLne hLprod
    have hLge := L_ge_one ξ _ rfl α _ hLprod
    exact ⟨_, hLprod, hLne, hFTF.2, hFnz.2.2, hΨval, hphi.1, hphi.2, hLge⟩
  refine ⟨1 / β 0, 4 * Real.pi ^ 2 * γ₀, -δ₀, α, by positivity, by positivity, hαsq,
    ?_, ?_, ?_, ?_⟩
  ·
    intro ξ
    obtain ⟨L, _, _, _, _, _, hMult, _, _⟩ := hkey ξ
    exact hMult
  ·
    intro ξ
    obtain ⟨L, hLprod, hLne, hFTF, hFeq, hΨval, _, hphival, _⟩ := hkey ξ
    have hs2 : (2 * Real.pi * Complex.I * ξ) ^ 2 = ((-(4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ) :=
      (modulus 0 ξ 0 0 _ rfl).2.2.2.2.1
    have hexp : -(-(γ₀ : ℂ) * (2 * Real.pi * Complex.I * ξ) ^ 2
          + (δ₀ : ℂ) * (2 * Real.pi * Complex.I * ξ))
        = -((4 * Real.pi ^ 2 * γ₀ : ℝ) : ℂ) * (ξ : ℂ) ^ 2
          + 2 * Real.pi * Complex.I * ((-δ₀ : ℝ) : ℂ) * (ξ : ℂ) := by
      rw [hs2]; push_cast; ring
    rw [hFTF, hFeq, hΨval, hphival, mul_inv, mul_inv, ← Complex.exp_neg, hexp,
      show ((β 0 : ℂ))⁻¹ = ((1 / β 0 : ℝ) : ℂ) from by push_cast; ring]
  ·
    intro ξ
    obtain ⟨L, _, _, hFTF, hFeq, _, _, _, _⟩ := hkey ξ
    rw [hFTF, hFeq]
    exact inv_ne_zero (by
      have := F_nonzero g C c hC hc hgcont hbound β hβmr hconv _ (FT_eq_F g C c hC hc hgcont hbound ξ).1
      rw [hFeq] at this; exact this.2.1)
  ·
    intro ξ
    obtain ⟨L, hLprod, hLne, hFTF, hFeq, hΨval, _, _, hLge⟩ := hkey ξ
    have hnβ : ‖(β 0 : ℂ)‖ = β 0 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
    have hnexp : ‖Complex.exp (-(γ₀ : ℂ) * (2 * Real.pi * Complex.I * ξ) ^ 2
        + (δ₀ : ℂ) * (2 * Real.pi * Complex.I * ξ))‖ = Real.exp (4 * Real.pi ^ 2 * γ₀ * ξ ^ 2) :=
      (modulus 0 ξ γ₀ δ₀ _ rfl).2.2.2.2.2.1
    have hE : (0 : ℝ) < Real.exp (4 * Real.pi ^ 2 * γ₀ * ξ ^ 2) := Real.exp_pos _
    have hnorm : ‖FT g ξ‖ = 1 / (β 0 * Real.exp (4 * Real.pi ^ 2 * γ₀ * ξ ^ 2) * ‖L‖) := by
      rw [hFTF, hFeq, norm_inv, hΨval, norm_mul, norm_mul, hnβ, hnexp, inv_eq_one_div]
    have hrhs : (1 / β 0) * Real.exp (-(4 * Real.pi ^ 2 * γ₀) * ξ ^ 2)
        = 1 / (β 0 * Real.exp (4 * Real.pi ^ 2 * γ₀ * ξ ^ 2)) := by
      rw [show -(4 * Real.pi ^ 2 * γ₀) * ξ ^ 2 = -(4 * Real.pi ^ 2 * γ₀ * ξ ^ 2) from by ring,
        Real.exp_neg]
      field_simp
    rw [hnorm, hrhs]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [hLge, mul_pos hβ0 hE]
