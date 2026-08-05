import Mathlib
import LeanCode.Vendor.E5.Defs

open MeasureTheory











namespace Part7


def strip (c : ℝ) : Set ℂ := {s : ℂ | |s.re| < c}


noncomputable def F (g : ℝ → ℝ) (s : ℂ) : ℂ := ∫ x : ℝ, Complex.exp (-s * x) * g x


noncomputable def Efac (α : ℝ) (s : ℂ) : ℂ :=
  (1 + (α : ℂ) * s) * Complex.exp (-(α : ℂ) * s)



noncomputable def Psi (β : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' m : ℕ, ((β m / m.factorial : ℝ) : ℂ) * s ^ m






theorem exp_series (z : ℂ) :
    Summable (fun m : ℕ => ‖z ^ m / (m.factorial : ℂ)‖) ∧
    (∑' m : ℕ, ‖z‖ ^ m / (m.factorial : ℝ)) = Real.exp ‖z‖ ∧
    (∑' m : ℕ, z ^ m / (m.factorial : ℂ)) = Complex.exp z := by
  have hns : Summable (fun m : ℕ => ‖z‖ ^ m / (m.factorial : ℝ)) :=
    Real.summable_pow_div_factorial ‖z‖
  refine ⟨?_, ?_, ?_⟩
  · have heq : (fun m : ℕ => ‖z ^ m / (m.factorial : ℂ)‖)
        = (fun m : ℕ => ‖z‖ ^ m / (m.factorial : ℝ)) := by
      funext m; rw [norm_div, norm_pow, Complex.norm_natCast]
    rw [heq]; exact hns
  · rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  · rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]


theorem exp_abs_int (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) ∧
    (∫ x : ℝ, Real.exp (-a * |x|)) = 2 / a := by
  have hna : (-a : ℝ) < 0 := by linarith
  have hEqIoi : Set.EqOn (fun x : ℝ => Real.exp (-a * |x|))
      (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0) := by
    intro x hx; show Real.exp (-a * |x|) = Real.exp (-a * x); rw [abs_of_pos hx]
  have hEqIic : Set.EqOn (fun x : ℝ => Real.exp (-a * |x|))
      (fun x : ℝ => Real.exp (a * x)) (Set.Iic 0) := by
    intro x hx; show Real.exp (-a * |x|) = Real.exp (a * x)
    rw [abs_of_nonpos hx]; congr 1; ring
  have hIntIoi : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi hna 0).congr_fun hEqIoi.symm measurableSet_Ioi
  have hIntIic : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Set.Iic 0) :=
    (integrableOn_exp_mul_Iic ha 0).congr_fun hEqIic.symm measurableSet_Iic
  refine ⟨?_, ?_⟩
  · have hunion : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|))
        (Set.Iic 0 ∪ Set.Ioi 0) := hIntIic.union hIntIoi
    rw [Set.Iic_union_Ioi] at hunion
    exact integrableOn_univ.mp hunion
  · rw [← MeasureTheory.setIntegral_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)),
      MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hIntIic hIntIoi,
      MeasureTheory.setIntegral_congr_fun measurableSet_Iic hEqIic,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEqIoi,
      integral_exp_mul_Iic ha 0, integral_exp_mul_Ioi hna 0]
    simp only [mul_zero, Real.exp_zero]
    rw [neg_div_neg_eq]
    ring


theorem pow_le_exp (t : ℝ) (ht : 0 ≤ t) (m : ℕ) :
    t ^ m ≤ (m.factorial : ℝ) * Real.exp t := by
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hexp : Real.exp t = ∑' k : ℕ, t ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsum : Summable (fun k : ℕ => t ^ k / (k.factorial : ℝ)) :=
    Real.summable_pow_div_factorial t
  have hle : t ^ m / (m.factorial : ℝ) ≤ ∑' k : ℕ, t ^ k / (k.factorial : ℝ) :=
    hsum.le_tsum m (fun k _ => by positivity)
  rw [hexp, mul_comm (m.factorial : ℝ) (∑' k : ℕ, t ^ k / (k.factorial : ℝ))]
  exact (div_le_iff₀ hfac).mp hle


theorem poly_exp_int (a : ℝ) (ha : 0 < a) (m : ℕ) :
    Integrable (fun x : ℝ => |x| ^ m * Real.exp (-a * |x|)) ∧
    (∀ x : ℝ, |x| ^ m * Real.exp (-a * |x|)
      ≤ (m.factorial : ℝ) * (2 / a) ^ m * Real.exp (-(a / 2) * |x|)) ∧
    (∫ x : ℝ, |x| ^ m * Real.exp (-a * |x|)) ≤ (m.factorial : ℝ) * (2 / a) ^ m * (4 / a) := by
  have ha0 : a ≠ 0 := ha.ne'
  have haa : (2 / a) * (a / 2) = 1 := by field_simp
  have hbound : ∀ x : ℝ, |x| ^ m * Real.exp (-a * |x|)
      ≤ (m.factorial : ℝ) * (2 / a) ^ m * Real.exp (-(a / 2) * |x|) := by
    intro x
    have ht : (0 : ℝ) ≤ (a / 2) * |x| := by positivity
    have hple := pow_le_exp ((a / 2) * |x|) ht m
    have hxm : |x| ^ m = (2 / a) ^ m * ((a / 2) * |x|) ^ m := by
      rw [mul_pow, ← mul_assoc, ← mul_pow, haa, one_pow, one_mul]
    have hexp : Real.exp ((a / 2) * |x|) * Real.exp (-a * |x|) = Real.exp (-(a / 2) * |x|) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hxm]
    have hstep : (2 / a) ^ m * ((a / 2) * |x|) ^ m * Real.exp (-a * |x|)
        ≤ (2 / a) ^ m * ((m.factorial : ℝ) * Real.exp ((a / 2) * |x|)) * Real.exp (-a * |x|) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_left hple (by positivity)
    refine hstep.trans (le_of_eq ?_)
    rw [← hexp]; ring
  have hcont : Continuous (fun x : ℝ => |x| ^ m * Real.exp (-a * |x|)) := by fun_prop
  have hIntDom : Integrable (fun x : ℝ =>
      (m.factorial : ℝ) * (2 / a) ^ m * Real.exp (-(a / 2) * |x|)) :=
    ((exp_abs_int (a / 2) (by positivity)).1).const_mul _
  have hInt : Integrable (fun x : ℝ => |x| ^ m * Real.exp (-a * |x|)) := by
    apply Integrable.mono' hIntDom hcont.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound x
  refine ⟨hInt, hbound, ?_⟩
  calc (∫ x : ℝ, |x| ^ m * Real.exp (-a * |x|))
      ≤ ∫ x : ℝ, (m.factorial : ℝ) * (2 / a) ^ m * Real.exp (-(a / 2) * |x|) :=
        integral_mono hInt hIntDom hbound
    _ = (m.factorial : ℝ) * (2 / a) ^ m * (2 / (a / 2)) := by
        rw [integral_const_mul, (exp_abs_int (a / 2) (by positivity)).2]
    _ = (m.factorial : ℝ) * (2 / a) ^ m * (4 / a) := by congr 1; field_simp; ring


theorem moment_int (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg : Continuous g) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m * g x) ∧
    |mom g m| ≤ C * (m.factorial : ℝ) * (2 / c) ^ m * (4 / c) := by
  obtain ⟨hpInt, hpBound, hpIntegral⟩ := poly_exp_int c hc m
  have hDom : Integrable (fun x : ℝ => C * (|x| ^ m * Real.exp (-c * |x|))) := hpInt.const_mul C
  have hpt : ∀ x : ℝ, ‖x ^ m * g x‖ ≤ C * (|x| ^ m * Real.exp (-c * |x|)) := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    calc |x| ^ m * |g x|
        ≤ |x| ^ m * (C * Real.exp (-c * |x|)) :=
          mul_le_mul_of_nonneg_left (hbound x) (by positivity)
      _ = C * (|x| ^ m * Real.exp (-c * |x|)) := by ring
  have hcont : Continuous (fun x : ℝ => x ^ m * g x) := by fun_prop
  have hInt : Integrable (fun x : ℝ => x ^ m * g x) := by
    apply Integrable.mono' hDom hcont.aestronglyMeasurable
    filter_upwards with x using hpt x
  refine ⟨hInt, ?_⟩
  have hmomeq : mom g m = ∫ x : ℝ, x ^ m * g x := rfl
  rw [hmomeq, ← Real.norm_eq_abs]
  calc ‖∫ x : ℝ, x ^ m * g x‖
      ≤ ∫ x : ℝ, ‖x ^ m * g x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, C * (|x| ^ m * Real.exp (-c * |x|)) := integral_mono hInt.norm hDom hpt
    _ = C * ∫ x : ℝ, |x| ^ m * Real.exp (-c * |x|) := integral_const_mul C _
    _ ≤ C * ((m.factorial : ℝ) * (2 / c) ^ m * (4 / c)) :=
        mul_le_mul_of_nonneg_left hpIntegral (le_of_lt hC)
    _ = C * (m.factorial : ℝ) * (2 / c) ^ m * (4 / c) := by ring

end Part7
