import LeanCode.Vendor.E5.P1.GlobalBound
import LeanCode.Vendor.E5.P1.OneSidedDecay
import LeanCode.Vendor.E5.Defs

noncomputable section

namespace VendorE5ExpDecay

theorem eventual_twoSided_decay {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) :
    ∃ R α C₀ : ℝ, 0 ≤ R ∧ 0 < α ∧ 0 < C₀ ∧
      ∀ x : ℝ, R ≤ |x| → g x ≤ C₀ * Real.exp (-α * |x|) := by
  rcases right_tail_decay hg with ⟨AR, CR, αR, hAR, hCR, hαR, hright⟩
  rcases left_tail_decay hg with ⟨AL, CL, αL, hAL, hCL, hαL, hleft⟩
  let R := max AR AL
  let α := min αR αL
  let C₀ := max CR CL
  have hR : 0 ≤ R := le_max_of_le_left hAR
  have hα : 0 < α := lt_min hαR hαL
  have hC₀ : 0 < C₀ := hCR.trans_le (le_max_left CR CL)
  refine ⟨R, α, C₀, hR, hα, hC₀, ?_⟩
  intro x hx
  rcases le_total 0 x with hx_nonneg | hx_nonpos
  · have hx_abs : |x| = x := abs_of_nonneg hx_nonneg
    have hARx : AR ≤ x := by
      have hRx : R ≤ x := by simpa [hx_abs] using hx
      exact (le_max_left AR AL).trans hRx
    have hαle : α ≤ αR := min_le_left αR αL
    have hCRle : CR ≤ C₀ := le_max_left CR CL
    have hexp : Real.exp (-αR * x) ≤ Real.exp (-α * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc
      g x ≤ CR * Real.exp (-αR * x) := hright x hARx
      _ ≤ C₀ * Real.exp (-α * x) :=
        mul_le_mul hCRle hexp (Real.exp_pos _).le hC₀.le
      _ = C₀ * Real.exp (-α * |x|) := by rw [hx_abs]
  · have hx_abs : |x| = -x := abs_of_nonpos hx_nonpos
    have hxAL : x ≤ -AL := by
      have hRx : R ≤ -x := by simpa [hx_abs] using hx
      have hALx : AL ≤ -x := (le_max_right AR AL).trans hRx
      linarith
    have hαle : α ≤ αL := min_le_right αR αL
    have hCLle : CL ≤ C₀ := le_max_right CR CL
    have hexp : Real.exp (αL * x) ≤ Real.exp (α * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc
      g x ≤ CL * Real.exp (αL * x) := hleft x hxAL
      _ ≤ C₀ * Real.exp (α * x) :=
        mul_le_mul hCLle hexp (Real.exp_pos _).le hC₀.le
      _ = C₀ * Real.exp (-α * |x|) := by rw [hx_abs]; ring_nf

theorem exponentialDecay_scaffold {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|) := by
  rcases eventual_twoSided_decay hg with ⟨R, α, C₀, hR, hα, hC₀, htail⟩
  rcases global_bound hg with ⟨M, hM, hglobal⟩
  let C : ℝ := max C₀ (M * Real.exp (α * R))
  have hC : 0 < C := hC₀.trans_le (le_max_left C₀ (M * Real.exp (α * R)))
  refine ⟨C, α, hC, hα, ?_⟩
  intro x
  have hx_nonneg : 0 ≤ g x := isTotallyPositive_nonneg hg.1 x
  rw [abs_of_nonneg hx_nonneg]
  by_cases hlarge : R ≤ |x|
  · have htail_x := htail x hlarge
    have hC₀le : C₀ ≤ C := le_max_left C₀ (M * Real.exp (α * R))
    exact htail_x.trans
      (mul_le_mul_of_nonneg_right hC₀le (Real.exp_pos (-α * |x|)).le)
  · have hxR : |x| ≤ R := le_of_not_ge hlarge
    have hRminus : 0 ≤ R - |x| := sub_nonneg.mpr hxR
    have hexp_one : 1 ≤ Real.exp (α * (R - |x|)) :=
      Real.one_le_exp (mul_nonneg hα.le hRminus)
    have hM_to_base : M ≤ M * Real.exp (α * (R - |x|)) := by
      calc
        M = M * 1 := by ring_nf
        _ ≤ M * Real.exp (α * (R - |x|)) :=
          mul_le_mul_of_nonneg_left hexp_one hM.le
    have hbase_eq :
        M * Real.exp (α * (R - |x|)) =
          (M * Real.exp (α * R)) * Real.exp (-α * |x|) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    have hbase_le_C :
        (M * Real.exp (α * R)) * Real.exp (-α * |x|) ≤
          C * Real.exp (-α * |x|) :=
      mul_le_mul_of_nonneg_right
        (le_max_right C₀ (M * Real.exp (α * R))) (Real.exp_pos (-α * |x|)).le
    calc
      g x ≤ M := hglobal x
      _ ≤ M * Real.exp (α * (R - |x|)) := hM_to_base
      _ = (M * Real.exp (α * R)) * Real.exp (-α * |x|) := hbase_eq
      _ ≤ C * Real.exp (-α * |x|) := hbase_le_C


theorem ExponentialDecay (g : ℝ → ℝ) (hg : IsTotallyPositiveIntegrable g) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|) :=
  exponentialDecay_scaffold hg

end VendorE5ExpDecay
