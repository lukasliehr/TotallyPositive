import LeanCode.Vendor.E5.P7.Part7.Basic
import LeanCode.Vendor.E5.P7.Part7.ProdHelpers
import LeanCode.Vendor.E5.P7.Part7.Psi
import LeanCode.Vendor.E5.Defs



namespace Part7


theorem modulus (α ξ γ₀ δ₀ : ℝ) (s : ℂ) (hs : s = 2 * Real.pi * Complex.I * ξ) :
    ‖Complex.exp (-(α : ℂ) * s)‖ = 1 ∧
    ‖Complex.exp ((α : ℂ) * s)‖ = 1 ∧
    (1 + (α : ℂ) * s = 1 + 2 * Real.pi * Complex.I * α * ξ) ∧
    (1 : ℝ) ≤ ‖1 + (α : ℂ) * s‖ ∧
    s ^ 2 = ((-(4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ) ∧
    ‖Complex.exp (-(γ₀ : ℂ) * s ^ 2 + (δ₀ : ℂ) * s)‖
      = Real.exp (4 * Real.pi ^ 2 * γ₀ * ξ ^ 2) ∧
    ‖Complex.exp ((γ₀ : ℂ) * s ^ 2 - (δ₀ : ℂ) * s)‖
      = Real.exp (-(4 * Real.pi ^ 2 * γ₀ * ξ ^ 2)) := by
  subst hs

  have key : (2 * Real.pi * Complex.I * (ξ : ℂ)) = ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hsq : (2 * Real.pi * Complex.I * (ξ : ℂ)) ^ 2 = ((-(4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ) := by
    rw [key, mul_pow, Complex.I_sq]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, hsq, ?_, ?_⟩
  · rw [Complex.norm_exp]
    have : (-(α : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ))).re = 0 := by
      rw [key]; simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  · rw [Complex.norm_exp]
    have : ((α : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ))).re = 0 := by
      rw [key]; simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  · ring
  · have hre1 : (1 + (α : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ))).re = 1 := by
      rw [key]; simp [Complex.mul_re, Complex.mul_im]
    calc (1 : ℝ) = (1 + (α : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ))).re := hre1.symm
      _ ≤ ‖1 + (α : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ))‖ := Complex.re_le_norm _
  · rw [Complex.norm_exp]
    have hA : (-(γ₀ : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ)) ^ 2
        + (δ₀ : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ))).re
        = 4 * Real.pi ^ 2 * γ₀ * ξ ^ 2 := by
      rw [hsq, key]
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [hA]
  · rw [Complex.norm_exp]
    have hB : ((γ₀ : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ)) ^ 2
        - (δ₀ : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ))).re
        = -(4 * Real.pi ^ 2 * γ₀ * ξ ^ 2) := by
      rw [hsq, key]
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [hB]


theorem factor_inverse (α ξ : ℝ) (s : ℂ) (hs : s = 2 * Real.pi * Complex.I * ξ) :
    Efac α s ≠ 0 ∧ (Efac α s)⁻¹ = expFactor α ξ := by
  subst hs
  have hm := modulus α ξ 0 0 (2 * Real.pi * Complex.I * (ξ : ℂ)) rfl
  have hden : (1 : ℂ) + (α : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ)) ≠ 0 := by
    intro h
    have h1 := hm.2.2.2.1
    rw [h, norm_zero] at h1
    linarith
  have hexp : Complex.exp (-(α : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ))) ≠ 0 :=
    Complex.exp_ne_zero _
  refine ⟨?_, ?_⟩
  · unfold Efac; exact mul_ne_zero hden hexp
  · unfold Efac expFactor
    rw [mul_inv, neg_mul, Complex.exp_neg, inv_inv, div_eq_mul_inv]
    have e2 : (1 : ℂ) + (α : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ))
        = 1 + 2 * Real.pi * Complex.I * (α : ℂ) * (ξ : ℂ) := by ring
    have e1 : (α : ℂ) * (2 * Real.pi * Complex.I * (ξ : ℂ))
        = 2 * Real.pi * Complex.I * (α : ℂ) * (ξ : ℂ) := by ring
    rw [e2, e1]
    exact mul_comm _ _


theorem L_nonzero (ξ : ℝ) (s : ℂ) (hs : s = 2 * Real.pi * Complex.I * ξ)
    (β₀ γ₀ δ₀ : ℝ) (hβ₀ : 0 < β₀) (α : ℕ → ℝ) (L P : ℂ)
    (hprod : HasProd (fun ν : ℕ => Efac (α ν) s) L)
    (hP : P = (β₀ : ℂ) * Complex.exp (-(γ₀ : ℂ) * s ^ 2 + (δ₀ : ℂ) * s) * L)
    (hP0 : P ≠ 0) :
    L ≠ 0 := by
  intro hL
  apply hP0
  rw [hP, hL, mul_zero]


theorem phi_multipliable (ξ : ℝ) (s : ℂ) (hs : s = 2 * Real.pi * Complex.I * ξ)
    (α : ℕ → ℝ) (L : ℂ) (hL : L ≠ 0)
    (hprod : HasProd (fun ν : ℕ => Efac (α ν) s) L) :
    Multipliable (fun ν : ℕ => expFactor (α ν) ξ) ∧
    (∏' ν : ℕ, expFactor (α ν) ξ) = L⁻¹ := by
  have hne : ∀ ν, Efac (α ν) s ≠ 0 := fun ν => (factor_inverse (α ν) ξ s hs).1
  have hinv : ∀ ν, (Efac (α ν) s)⁻¹ = expFactor (α ν) ξ := fun ν => (factor_inverse (α ν) ξ s hs).2
  have hp := prod_inv (fun ν : ℕ => Efac (α ν) s) L hne hprod hL
  have hp' : HasProd (fun ν : ℕ => expFactor (α ν) ξ) L⁻¹ := by
    have hfun : (fun ν : ℕ => (Efac (α ν) s)⁻¹) = (fun ν : ℕ => expFactor (α ν) ξ) := funext hinv
    rwa [hfun] at hp
  exact ⟨⟨L⁻¹, hp'⟩, hp'.tprod_eq⟩


theorem L_ge_one (ξ : ℝ) (s : ℂ) (hs : s = 2 * Real.pi * Complex.I * ξ)
    (α : ℕ → ℝ) (L : ℂ)
    (hprod : HasProd (fun ν : ℕ => Efac (α ν) s) L) :
    (1 : ℝ) ≤ ‖L‖ := by
  have hnorm := prod_norm (fun ν : ℕ => Efac (α ν) s) L hprod
  have hge : ∀ ν, 1 ≤ ‖Efac (α ν) s‖ := by
    intro ν
    have hm := modulus (α ν) ξ 0 0 s hs
    unfold Efac
    rw [norm_mul, hm.1, mul_one]
    exact hm.2.2.2.1
  exact prod_ge_one (fun ν : ℕ => ‖Efac (α ν) s‖) ‖L‖ hge hnorm

end Part7
