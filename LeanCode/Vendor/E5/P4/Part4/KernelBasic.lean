import LeanCode.Vendor.E5.P4.Part4.Defs
import LeanCode.Vendor.E5.Defs

open MeasureTheory

namespace Part4








theorem exp_two_side (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-b * |x|)) ∧
    (∫ x : ℝ, Real.exp (-b * |x|)) = 2 / b := by
  have hIic : Set.EqOn (fun x : ℝ => Real.exp (-b * |x|))
      (fun x => Real.exp (b * x)) (Set.Iic 0) := by
    intro x hx
    simp only [Set.mem_Iic] at hx
    simp only [abs_of_nonpos hx, neg_mul_neg]
  have hIoi : Set.EqOn (fun x : ℝ => Real.exp (-b * |x|))
      (fun x => Real.exp (-b * x)) (Set.Ioi 0) := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [abs_of_pos hx]
  have iIic : IntegrableOn (fun x : ℝ => Real.exp (-b * |x|)) (Set.Iic 0) :=
    (integrableOn_exp_mul_Iic hb 0).congr_fun hIic.symm measurableSet_Iic
  have iIoi : IntegrableOn (fun x : ℝ => Real.exp (-b * |x|)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show (-b) < 0 by linarith) 0).congr_fun hIoi.symm
      measurableSet_Ioi
  have hInt : Integrable (fun x : ℝ => Real.exp (-b * |x|)) := by
    have hunion : IntegrableOn (fun x : ℝ => Real.exp (-b * |x|))
        (Set.Iic 0 ∪ Set.Ioi 0) := integrableOn_union.mpr ⟨iIic, iIoi⟩
    rw [Set.Iic_union_Ioi] at hunion
    exact integrableOn_univ.mp hunion
  refine ⟨hInt, ?_⟩
  have hsplit := integral_add_compl (s := Set.Iic (0 : ℝ)) measurableSet_Iic hInt
  rw [Set.compl_Iic] at hsplit
  have p1 : (∫ x in Set.Iic (0 : ℝ), Real.exp (-b * |x|)) = 1 / b := by
    rw [setIntegral_congr_fun measurableSet_Iic hIic, integral_exp_mul_Iic hb 0]
    simp
  have p2 : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-b * |x|)) = 1 / b := by
    rw [setIntegral_congr_fun measurableSet_Ioi hIoi,
      integral_exp_mul_Ioi (show (-b) < 0 by linarith) 0]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
  rw [p1, p2] at hsplit
  rw [← hsplit]; ring


theorem kernel_meas (a : ℝ) : Measurable (expKernel a) := by
  unfold expKernel
  apply Measurable.ite
  · exact measurableSet_le measurable_const (measurable_const.mul measurable_id)
  · exact measurable_const.mul
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
  · exact measurable_const


theorem kernel_nonneg_bdd (a : ℝ) (t : ℝ) :
    0 ≤ expKernel a t ∧ expKernel a t ≤ |a| := by
  unfold expKernel
  split_ifs with h
  · refine ⟨by positivity, ?_⟩
    have hle : Real.exp (-(a * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc |a| * Real.exp (-(a * t)) ≤ |a| * 1 :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg a)
      _ = |a| := mul_one _
  · exact ⟨le_refl 0, abs_nonneg a⟩


theorem kernel_envelope (a : ℝ) (ha : a ≠ 0) (t : ℝ) :
    |expKernel a t| ≤ |a| * Real.exp (-|a| * |t|) := by
  unfold expKernel
  split_ifs with h
  · have hnn : (0 : ℝ) ≤ |a| * Real.exp (-(a * t)) := by positivity
    rw [abs_of_nonneg hnn]
    have hexp : -(a * t) = -|a| * |t| := by
      rw [neg_mul, ← abs_mul, abs_of_nonneg h]
    exact le_of_eq (by rw [hexp])
  · rw [abs_zero]; positivity


private theorem kernel_integrable (a : ℝ) (ha : a ≠ 0) : Integrable (expKernel a) := by
  have hb : 0 < |a| := abs_pos.mpr ha
  have hmaj : Integrable (fun t : ℝ => |a| * Real.exp (-|a| * |t|)) :=
    ((exp_two_side |a| hb).1).const_mul |a|
  exact hmaj.mono' (kernel_meas a).aestronglyMeasurable
    (ae_of_all _ (fun t => by simpa using kernel_envelope a ha t))


theorem kernel_int (a : ℝ) (ha : a ≠ 0) :
    Integrable (expKernel a) ∧ (∫ t : ℝ, expKernel a t) = 1 := by
  refine ⟨kernel_integrable a ha, ?_⟩
  rcases lt_or_gt_of_ne ha with hneg | hpos
  ·
    have hInt := kernel_integrable a ha
    have hzero : (∫ t in (Set.Iic (0 : ℝ))ᶜ, expKernel a t) = 0 := by
      rw [Set.compl_Iic]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      simp only [Set.mem_Ioi] at ht
      unfold expKernel
      rw [if_neg (not_le.mpr (mul_neg_of_neg_of_pos hneg ht))]
    have hsplit := integral_add_compl (s := Set.Iic (0 : ℝ)) measurableSet_Iic hInt
    rw [hzero, add_zero] at hsplit
    have hEq : Set.EqOn (expKernel a) (fun t => (-a) * Real.exp (-(a * t)))
        (Set.Iic 0) := by
      intro t ht
      simp only [Set.mem_Iic] at ht
      have hat : 0 ≤ a * t := by rw [← neg_mul_neg]; exact mul_nonneg (by linarith) (by linarith)
      unfold expKernel
      rw [if_pos hat, abs_of_neg hneg]
    have hfun : (fun t : ℝ => Real.exp (-(a * t))) = (fun t => Real.exp ((-a) * t)) := by
      funext t; rw [neg_mul]
    rw [← hsplit, setIntegral_congr_fun measurableSet_Iic hEq, integral_const_mul, hfun,
      integral_exp_mul_Iic (show (0 : ℝ) < -a by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    rw [mul_one_div, div_self (by linarith : (-a) ≠ 0)]
  ·
    have hInt := kernel_integrable a ha
    have hzero : (∫ t in (Set.Ici (0 : ℝ))ᶜ, expKernel a t) = 0 := by
      rw [Set.compl_Ici]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      simp only [Set.mem_Iio] at ht
      unfold expKernel
      rw [if_neg (not_le.mpr (mul_neg_of_pos_of_neg hpos ht))]
    have hsplit := integral_add_compl (s := Set.Ici (0 : ℝ)) measurableSet_Ici hInt
    rw [hzero, add_zero] at hsplit
    have hEq : Set.EqOn (expKernel a) (fun t => a * Real.exp (-(a * t))) (Set.Ici 0) := by
      intro t ht
      simp only [Set.mem_Ici] at ht
      unfold expKernel
      rw [if_pos (mul_nonneg hpos.le ht), abs_of_pos hpos]
    have hfun : (fun t : ℝ => Real.exp (-(a * t))) = (fun t => Real.exp ((-a) * t)) := by
      funext t; rw [neg_mul]
    rw [← hsplit, setIntegral_congr_fun measurableSet_Ici hEq, integral_Ici_eq_integral_Ioi,
      integral_const_mul, hfun, integral_exp_mul_Ioi (show (-a) < 0 by linarith) 0]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
    rw [mul_one_div, div_self hpos.ne']



theorem decay_integrable (g : ℝ → ℝ) (hg : Measurable g) (C c : ℝ)
    (_hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)) :
    Integrable g ∧ (∫ x : ℝ, |g x|) ≤ 2 * C / c := by
  have hmaj : Integrable (fun x : ℝ => C * Real.exp (-c * |x|)) :=
    ((exp_two_side c hc).1).const_mul C
  have hIntg : Integrable g :=
    hmaj.mono' hg.aestronglyMeasurable
      (ae_of_all _ (fun x => by simpa using hbound x))
  refine ⟨hIntg, ?_⟩
  have hle : (∫ x, |g x|) ≤ ∫ x, C * Real.exp (-c * |x|) :=
    integral_mono_of_nonneg (ae_of_all _ (fun x => abs_nonneg _)) hmaj
      (ae_of_all _ hbound)
  rw [integral_const_mul, (exp_two_side c hc).2] at hle
  calc (∫ x, |g x|) ≤ C * (2 / c) := hle
    _ = 2 * C / c := by ring

end Part4
