import Mathlib
import LeanCode.Vendor.E5.Defs
open VendorE5

open MeasureTheory

















namespace Part5



def SignChangesFnGE (h : ℝ → ℝ) (s : ℕ) : Prop :=
  ∃ x : Fin (s + 1) → ℝ, StrictMono x ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ i : Fin (s + 1), 0 < ε * (-1 : ℝ) ^ (i : ℕ) * h (x i)


theorem exp_term_bound (k : ℕ) (lam t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t) :
    t ^ k * Real.exp (-lam * t) ≤ (k.factorial : ℝ) / lam ^ k := by
  have hlt : (0 : ℝ) < lam ^ k := pow_pos hlam k
  have hne : (lam : ℝ) ^ k ≠ 0 := hlt.ne'
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hexp : ((lam * t) ^ k) / (k.factorial : ℝ) ≤ Real.exp (lam * t) :=
    Real.pow_div_factorial_le_exp (x := lam * t) (mul_nonneg hlam.le ht) k
  have key : (lam * t) ^ k * Real.exp (-lam * t) ≤ (k.factorial : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hexp
      (mul_nonneg hfac.le (Real.exp_pos (-lam * t)).le)
    have hcancel : lam * t + -lam * t = 0 := by ring
    calc (lam * t) ^ k * Real.exp (-lam * t)
        = ((lam * t) ^ k / (k.factorial : ℝ)) *
            ((k.factorial : ℝ) * Real.exp (-lam * t)) := by field_simp
      _ ≤ Real.exp (lam * t) * ((k.factorial : ℝ) * Real.exp (-lam * t)) := hmul
      _ = (k.factorial : ℝ) *
            (Real.exp (lam * t) * Real.exp (-lam * t)) := by ring
      _ = (k.factorial : ℝ) * Real.exp (lam * t + -lam * t) := by rw [← Real.exp_add]
      _ = (k.factorial : ℝ) := by rw [hcancel, Real.exp_zero, mul_one]
  have hinv : (0 : ℝ) < (lam ^ k)⁻¹ := inv_pos.mpr hlt
  rw [div_eq_mul_inv]
  calc t ^ k * Real.exp (-lam * t)
      = (lam * t) ^ k * Real.exp (-lam * t) * (lam ^ k)⁻¹ := by
        field_simp; ring
    _ ≤ (k.factorial : ℝ) * (lam ^ k)⁻¹ :=
        mul_le_mul_of_nonneg_right key hinv.le


theorem exp_abs_integrable (a : ℝ) (ha : 0 < a) :
    MeasureTheory.Integrable (fun y : ℝ => Real.exp (-a * |y|)) := by
  rw [← MeasureTheory.integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  refine MeasureTheory.IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic ha (0 : ℝ)).congr_fun ?_ measurableSet_Iic
    intro y hy
    simp only [Set.mem_Iic] at hy
    dsimp only
    rw [abs_of_nonpos hy]; congr 1; ring
  · refine (exp_neg_integrableOn_Ioi (0 : ℝ) ha).congr_fun ?_ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    dsimp only
    rw [abs_of_pos hy]


theorem polyexp_integrable (k : ℕ) (c : ℝ) (hc : 0 < c) :
    MeasureTheory.Integrable (fun y : ℝ => |y| ^ k * Real.exp (-c * |y|)) := by
  have hc2 : (0 : ℝ) < c / 2 := by positivity
  set M : ℝ := (k.factorial : ℝ) * (2 / c) ^ k with hM
  have hMnn : (0 : ℝ) ≤ M :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt (div_pos (by norm_num) hc)) k)
  have hGint : MeasureTheory.Integrable (fun y : ℝ => M * Real.exp (-(c / 2) * |y|)) :=
    (exp_abs_integrable (c / 2) hc2).const_mul M
  refine hGint.mono ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards with y
    have hterm := exp_term_bound k (c / 2) |y| hc2 (abs_nonneg y)
    have hMeq : (k.factorial : ℝ) / (c / 2) ^ k = M := by
      rw [hM, div_eq_mul_inv, ← inv_pow, inv_div]
    rw [hMeq] at hterm
    have hsplit : Real.exp (-c * |y|)
        = Real.exp (-(c / 2) * |y|) * Real.exp (-(c / 2) * |y|) := by
      rw [← Real.exp_add]; congr 1; ring
    have hbound : |y| ^ k * Real.exp (-c * |y|) ≤ M * Real.exp (-(c / 2) * |y|) := by
      rw [hsplit, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hterm (Real.exp_pos _).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |y| ^ k * Real.exp (-c * |y|)),
      abs_of_nonneg (mul_nonneg hMnn (Real.exp_pos _).le)]
    exact hbound


theorem g_nonneg (g : ℝ → ℝ) (hg : IsTotallyPositive g) (t : ℝ) : 0 ≤ g t := by
  have h := hg 1 (fun _ => t) (fun _ => 0)
    (Subsingleton.strictMono _) (Subsingleton.strictMono _)
  rw [Matrix.det_fin_one] at h
  simpa using h



theorem moment_integrand (g : ℝ → ℝ) (hg : Continuous g) (C c : ℝ) (hC : 0 < C)
    (hc : 0 < c) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)) (i : ℕ) :
    MeasureTheory.Integrable (fun y : ℝ => y ^ i * g y) := by
  have hGint : MeasureTheory.Integrable
      (fun y : ℝ => C * (|y| ^ i * Real.exp (-c * |y|))) :=
    (polyexp_integrable i c hc).const_mul C
  refine hGint.mono (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (mul_nonneg hC.le (by positivity))]
  calc |y| ^ i * |g y|
      ≤ |y| ^ i * (C * Real.exp (-c * |y|)) :=
        mul_le_mul_of_nonneg_left (hbound y) (by positivity)
    _ = C * (|y| ^ i * Real.exp (-c * |y|)) := by ring


theorem mu0_pos (g : ℝ → ℝ) (hg : Continuous g) (hint : MeasureTheory.Integrable g)
    (hnonneg : ∀ t : ℝ, 0 ≤ g t) (hne : g ≠ 0) : 0 < mom g 0 := by
  have hmom : mom g 0 = ∫ y, g y := by simp [mom]
  rw [hmom, MeasureTheory.integral_pos_iff_support_of_nonneg hnonneg hint]
  have hopen : IsOpen (Function.support g) := by
    have hsupp : Function.support g = g ⁻¹' {y | y ≠ 0} := rfl
    rw [hsupp]; exact isOpen_ne.preimage hg
  have hnonempty : (Function.support g).Nonempty := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
    exact ⟨x, hx⟩
  exact hopen.measure_pos _ hnonempty



noncomputable def betaSeq (g : ℝ → ℝ) : ℕ → ℝ
  | 0 => (mom g 0)⁻¹
  | (m + 1) => -(mom g 0)⁻¹ * ∑ i ∈ Finset.range (m + 1),
      ((m + 1).choose (i + 1) : ℝ) * (-1 : ℝ) ^ (i + 1) * mom g (i + 1) * betaSeq g (m - i)
  decreasing_by exact Nat.lt_succ_of_le (Nat.sub_le m i)


theorem beta_exists (g : ℝ → ℝ) (hg : Continuous g) (hint : MeasureTheory.Integrable g)
    (htp : IsTotallyPositive g) (hne : g ≠ 0) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)) :
    ∃ β : ℕ → ℝ, MomentReciprocal g β ∧ 0 < β 0 := by
  have hmu0 : 0 < mom g 0 := mu0_pos g hg hint (g_nonneg g htp) hne
  have hmu0ne : mom g 0 ≠ 0 := hmu0.ne'
  refine ⟨betaSeq g, ⟨?_, ?_⟩, ?_⟩
  · have h0 : betaSeq g 0 = (mom g 0)⁻¹ := by rw [betaSeq]
    rw [h0, mul_inv_cancel₀ hmu0ne]
  · intro m hm
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hdef : betaSeq g (M + 1) = -(mom g 0)⁻¹ * ∑ i ∈ Finset.range (M + 1),
        ((M + 1).choose (i + 1) : ℝ) * (-1 : ℝ) ^ (i + 1) * mom g (i + 1) *
          betaSeq g (M - i) := by
      rw [betaSeq]
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul, Nat.sub_zero,
      mul_one, Nat.succ_sub_succ]
    rw [hdef]
    field_simp
    ring
  · have h0 : betaSeq g 0 = (mom g 0)⁻¹ := by rw [betaSeq]
    rw [h0]; exact inv_pos.mpr hmu0


private theorem conv_pow_integrable (g : ℝ → ℝ) (hg : Continuous g) (C c : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (x : ℝ) (k : ℕ) :
    MeasureTheory.Integrable (fun y : ℝ => g (x - y) * y ^ k) := by
  have hGint : MeasureTheory.Integrable
      (fun y : ℝ => (C * Real.exp (c * |x|)) * (|y| ^ k * Real.exp (-c * |y|))) :=
    (polyexp_integrable k c hc).const_mul _
  refine hGint.mono (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (mul_nonneg (mul_nonneg hC.le (Real.exp_pos _).le) (by positivity))]
  have htri : |y| ≤ |x - y| + |x| := by
    calc |y| = |-(x - y) + x| := by congr 1; ring
      _ ≤ |-(x - y)| + |x| := abs_add_le _ _
      _ = |x - y| + |x| := by rw [abs_neg]
  have hgb : |g (x - y)| ≤ C * Real.exp (c * |x|) * Real.exp (-c * |y|) := by
    calc |g (x - y)| ≤ C * Real.exp (-c * |x - y|) := hbound (x - y)
      _ ≤ C * (Real.exp (c * |x|) * Real.exp (-c * |y|)) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left htri hc.le])
      _ = C * Real.exp (c * |x|) * Real.exp (-c * |y|) := by ring
  calc |g (x - y)| * |y| ^ k
      ≤ (C * Real.exp (c * |x|) * Real.exp (-c * |y|)) * |y| ^ k :=
        mul_le_mul_of_nonneg_right hgb (by positivity)
    _ = C * Real.exp (c * |x|) * (|y| ^ k * Real.exp (-c * |y|)) := by ring


theorem conv_integrand (g : ℝ → ℝ) (hg : Continuous g) (C c : ℝ) (hC : 0 < C)
    (hc : 0 < c) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (p : Polynomial ℝ) (x : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ => g (x - y) * p.eval y) := by
  have heq : (fun y : ℝ => g (x - y) * p.eval y)
      = fun y => ∑ k ∈ Finset.range (p.natDegree + 1),
          p.coeff k * (g (x - y) * y ^ k) := by
    funext y
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [heq]
  refine MeasureTheory.integrable_finsetSum _ (fun k _ => ?_)
  exact (conv_pow_integrable g hg C c hC hc hbound x k).const_mul (p.coeff k)


noncomputable def convPoly (g : ℝ → ℝ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, g (x - y) * p.eval y

end Part5
