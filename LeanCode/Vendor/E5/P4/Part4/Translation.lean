import LeanCode.Vendor.E5.P4.Part4.Defs
import LeanCode.Vendor.E5.P4.Part4.KernelBasic
import LeanCode.Vendor.E5.Defs

open MeasureTheory

namespace Part4








theorem translate_pos (a : ℝ) (ha : 0 < a) (h : ℝ) (hh : 0 ≤ h) :
    Integrable (fun t : ℝ => |expKernel a (t + h) - expKernel a t|) ∧
    (∫ t : ℝ, |expKernel a (t + h) - expKernel a t|)
        = 2 * (1 - Real.exp (-a * h)) ∧
    2 * (1 - Real.exp (-a * h)) ≤ 2 * a * h := by
  set D : ℝ → ℝ := fun t => |expKernel a (t + h) - expKernel a t| with hD
  have haa : |a| = a := abs_of_pos ha
  have hker : Integrable (expKernel a) := (kernel_int a ha.ne').1
  have hkerInt : (∫ t, expKernel a t) = 1 := (kernel_int a ha.ne').2
  have hkerTr : Integrable (fun t : ℝ => expKernel a (t + h)) := by
    have : Integrable (fun t : ℝ => expKernel a (t + h)) volume :=
      (measurePreserving_add_right (volume : Measure ℝ) h).integrable_comp
        (kernel_meas a).aestronglyMeasurable |>.mpr hker
    exact this
  have hmeasD : Measurable D := by
    have h1 : Measurable (fun t : ℝ => expKernel a (t + h)) :=
      (kernel_meas a).comp (measurable_id.add_const h)
    exact ((h1.sub (kernel_meas a)).abs)
  have hmaj : Integrable (fun t : ℝ => expKernel a (t + h) + expKernel a t) :=
    hkerTr.add hker
  have hDbound : ∀ t, ‖D t‖ ≤ (fun t : ℝ => expKernel a (t + h) + expKernel a t) t := by
    intro t
    simp only [hD, Real.norm_eq_abs, abs_abs]
    have hnn1 := (kernel_nonneg_bdd a (t + h)).1
    have hnn2 := (kernel_nonneg_bdd a t).1
    calc |expKernel a (t + h) - expKernel a t|
        ≤ |expKernel a (t + h)| + |expKernel a t| := abs_sub _ _
      _ = expKernel a (t + h) + expKernel a t := by
          rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2]
  have hIntD : Integrable D :=
    hmaj.mono' hmeasD.aestronglyMeasurable (ae_of_all _ hDbound)
  refine ⟨hIntD, ?_, ?_⟩
  · have hsplit := integral_add_compl (s := Set.Ici (0 : ℝ)) measurableSet_Ici hIntD
    rw [Set.compl_Ici] at hsplit
    have hEqIci : Set.EqOn D (fun t => expKernel a t - expKernel a (t + h)) (Set.Ici 0) := by
      intro t ht
      simp only [Set.mem_Ici] at ht
      have hth : (0 : ℝ) ≤ t + h := by linarith
      have e1 : expKernel a (t + h) = a * Real.exp (-(a * (t + h))) := by
        simp only [expKernel, if_pos (mul_nonneg ha.le hth), haa]
      have e2 : expKernel a t = a * Real.exp (-(a * t)) := by
        simp only [expKernel, if_pos (mul_nonneg ha.le ht), haa]
      simp only [hD, e1, e2]
      have hle : Real.exp (-(a * (t + h))) ≤ Real.exp (-(a * t)) := by
        apply Real.exp_le_exp.mpr
        have : a * t ≤ a * (t + h) := by nlinarith
        linarith
      have hdiff : a * Real.exp (-(a * (t + h))) - a * Real.exp (-(a * t)) ≤ 0 := by
        have := mul_le_mul_of_nonneg_left hle ha.le
        linarith
      rw [abs_of_nonpos hdiff]
      ring
    have hEqIio : Set.EqOn D (fun t => expKernel a (t + h)) (Set.Iio 0) := by
      intro t ht
      simp only [Set.mem_Iio] at ht
      have e2 : expKernel a t = 0 := by
        simp only [expKernel, if_neg (not_le.mpr (mul_neg_of_pos_of_neg ha ht))]
      have hnn1 := (kernel_nonneg_bdd a (t + h)).1
      simp only [hD, e2, sub_zero, abs_of_nonneg hnn1]
    rw [setIntegral_congr_fun measurableSet_Ici hEqIci,
        setIntegral_congr_fun measurableSet_Iio hEqIio] at hsplit
    have hkerIci : IntegrableOn (expKernel a) (Set.Ici 0) := hker.integrableOn
    have hkerTrIci : IntegrableOn (fun t : ℝ => expKernel a (t + h)) (Set.Ici 0) :=
      hkerTr.integrableOn
    have hkerTrIio : IntegrableOn (fun t : ℝ => expKernel a (t + h)) (Set.Iio 0) :=
      hkerTr.integrableOn
    rw [integral_sub hkerIci hkerTrIci] at hsplit
    have intA : (∫ t in Set.Ici (0:ℝ), expKernel a t) = 1 := by
      have hEq : Set.EqOn (expKernel a) (fun t => a * Real.exp ((-a) * t)) (Set.Ici 0) := by
        intro t ht
        simp only [Set.mem_Ici] at ht
        simp only [expKernel, if_pos (mul_nonneg ha.le ht), haa, neg_mul]
      rw [setIntegral_congr_fun measurableSet_Ici hEq, integral_Ici_eq_integral_Ioi,
          integral_const_mul, integral_exp_mul_Ioi (show (-a) < 0 by linarith) 0]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
      rw [mul_one_div, div_self ha.ne']
    have intB : (∫ t in Set.Ici (0:ℝ), expKernel a (t + h)) = Real.exp (-a * h) := by
      have hmp := measurePreserving_add_right (volume : Measure ℝ) h
      have hme : MeasurableEmbedding (fun t : ℝ => t + h) :=
        (Homeomorph.addRight h).isClosedEmbedding.measurableEmbedding
      have hpre : (fun t : ℝ => t + h) ⁻¹' (Set.Ici h) = Set.Ici 0 := by
        ext t; simp [Set.mem_Ici]
      have hsub := hmp.setIntegral_preimage_emb hme (expKernel a) (Set.Ici h)
      rw [hpre] at hsub
      rw [hsub]
      have hEq : Set.EqOn (expKernel a) (fun u => a * Real.exp ((-a) * u)) (Set.Ici h) := by
        intro u hu
        simp only [Set.mem_Ici] at hu
        have : (0:ℝ) ≤ u := le_trans hh hu
        simp only [expKernel, if_pos (mul_nonneg ha.le this), haa, neg_mul]
      rw [setIntegral_congr_fun measurableSet_Ici hEq, integral_Ici_eq_integral_Ioi,
          integral_const_mul, integral_exp_mul_Ioi (show (-a) < 0 by linarith) h]
      field_simp
    have intC : (∫ t in Set.Iio (0:ℝ), expKernel a (t + h)) = 1 - Real.exp (-a * h) := by
      have hwhole : (∫ t : ℝ, expKernel a (t + h)) = 1 := by
        rw [integral_add_right_eq_self (expKernel a) h]; exact hkerInt
      have hsplit2 := integral_add_compl (s := Set.Ici (0:ℝ)) measurableSet_Ici hkerTr
      rw [Set.compl_Ici] at hsplit2
      rw [hwhole, intB] at hsplit2
      linarith
    rw [intA, intB, intC] at hsplit
    rw [← hsplit]; ring
  · have hexp : -a * h + 1 ≤ Real.exp (-a * h) := by
      have := Real.add_one_le_exp (-a * h)
      linarith
    nlinarith [hexp]



theorem translate_pos_all (a : ℝ) (ha : 0 < a) (h : ℝ) :
    Integrable (fun t : ℝ => |expKernel a (t + h) - expKernel a t|) ∧
    (∫ t : ℝ, |expKernel a (t + h) - expKernel a t|) ≤ 2 * a * |h| := by
  have hker : Integrable (expKernel a) := (kernel_int a ha.ne').1
  have hkerTr : Integrable (fun t : ℝ => expKernel a (t + h)) := by
    have : Integrable (fun t : ℝ => expKernel a (t + h)) volume :=
      (measurePreserving_add_right (volume : Measure ℝ) h).integrable_comp
        (kernel_meas a).aestronglyMeasurable |>.mpr hker
    exact this
  have hmeasD : Measurable (fun t : ℝ => |expKernel a (t + h) - expKernel a t|) := by
    have h1 : Measurable (fun t : ℝ => expKernel a (t + h)) :=
      (kernel_meas a).comp (measurable_id.add_const h)
    exact ((h1.sub (kernel_meas a)).abs)
  have hmaj : Integrable (fun t : ℝ => expKernel a (t + h) + expKernel a t) :=
    hkerTr.add hker
  have hDbound : ∀ t, ‖|expKernel a (t + h) - expKernel a t|‖
      ≤ (fun t : ℝ => expKernel a (t + h) + expKernel a t) t := by
    intro t
    simp only [Real.norm_eq_abs, abs_abs]
    have hnn1 := (kernel_nonneg_bdd a (t + h)).1
    have hnn2 := (kernel_nonneg_bdd a t).1
    calc |expKernel a (t + h) - expKernel a t|
        ≤ |expKernel a (t + h)| + |expKernel a t| := abs_sub _ _
      _ = expKernel a (t + h) + expKernel a t := by
          rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2]
  have hIntD : Integrable (fun t : ℝ => |expKernel a (t + h) - expKernel a t|) :=
    hmaj.mono' hmeasD.aestronglyMeasurable (ae_of_all _ hDbound)
  refine ⟨hIntD, ?_⟩
  rcases le_or_gt 0 h with hh | hh
  · obtain ⟨_, heq, hle⟩ := translate_pos a ha h hh
    rw [heq, abs_of_nonneg hh]
    exact hle
  · set k : ℝ := -h with hk
    have hkpos : 0 < k := by rw [hk]; linarith
    have hshift : (∫ t : ℝ, |expKernel a (t + h) - expKernel a t|)
        = ∫ u : ℝ, |expKernel a (u + k) - expKernel a u| := by
      have key := integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun u : ℝ => |expKernel a (u + k) - expKernel a u|) h
      rw [← key]
      apply integral_congr_ae
      refine ae_of_all _ (fun t => ?_)
      have he : t + h + k = t := by rw [hk]; abel
      simp only [he]
      rw [abs_sub_comm]
    rw [hshift]
    obtain ⟨_, heq, hle⟩ := translate_pos a ha k hkpos.le
    rw [heq]
    have hhk : |h| = k := by rw [hk, abs_of_neg hh]
    rw [hhk]
    exact hle



theorem translate (a : ℝ) (ha : a ≠ 0) (h : ℝ) :
    Integrable (fun t : ℝ => |expKernel a (t + h) - expKernel a t|) ∧
    (∫ t : ℝ, |expKernel a (t + h) - expKernel a t|) ≤ 2 * |a| * |h| := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · set b : ℝ := -a with hb
    have hbpos : 0 < b := by rw [hb]; linarith
    have hrefl : ∀ t : ℝ, expKernel a t = expKernel b (-t) := by
      intro t
      simp only [expKernel, hb, neg_mul_neg, abs_neg]
    have hbint := translate_pos_all b hbpos (-h)
    obtain ⟨hbInt, hble⟩ := hbint
    have hfun_eq : (fun t : ℝ => |expKernel a (t + h) - expKernel a t|)
        = (fun t : ℝ => |expKernel b (-t + (-h)) - expKernel b (-t)|) := by
      funext t
      rw [hrefl (t + h), hrefl t, neg_add]
    refine ⟨?_, ?_⟩
    · rw [hfun_eq]
      have hcomp : (fun t : ℝ => |expKernel b (-t + (-h)) - expKernel b (-t)|)
          = (fun u : ℝ => |expKernel b (u + (-h)) - expKernel b u|) ∘ (fun t => -t) := by
        funext t; simp
      rw [hcomp]
      exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp
        hbInt.aestronglyMeasurable |>.mpr hbInt
    · rw [hfun_eq]
      have hcomp : (∫ t : ℝ, |expKernel b (-t + (-h)) - expKernel b (-t)|)
          = ∫ u : ℝ, |expKernel b (u + (-h)) - expKernel b u| := by
        have := integral_neg_eq_self
          (fun u : ℝ => |expKernel b (u + (-h)) - expKernel b u|)
          (volume : Measure ℝ)
        simpa using this
      rw [hcomp]
      have hab : 2 * |a| * |h| = 2 * b * |(-h)| := by
        rw [abs_of_neg hneg, abs_neg, hb]
      rw [hab]
      exact hble
  · obtain ⟨hInt, hle⟩ := translate_pos_all a hpos h
    refine ⟨hInt, ?_⟩
    rw [abs_of_pos hpos]
    exact hle





theorem conv_kernel (a : ℝ) (ha : a ≠ 0) (M : ℝ) (hM : 0 ≤ M) (h : ℝ → ℝ)
    (hmeas : Measurable h) (hbdd : ∀ u : ℝ, |h u| ≤ M) :
    (∀ x : ℝ, Integrable (fun t : ℝ => expKernel a t * h (x - t))) ∧
    (∀ x : ℝ, |conv (expKernel a) h x| ≤ M) ∧
    (∀ x x' : ℝ, |conv (expKernel a) h x' - conv (expKernel a) h x|
        ≤ 2 * M * |a| * |x' - x|) := by
  have hker : Integrable (expKernel a) := (kernel_int a ha).1
  have hkerInt : (∫ t, expKernel a t) = 1 := (kernel_int a ha).2
  have hCV : ∀ (F : ℝ → ℝ) (y : ℝ), (∫ t : ℝ, F (y - t)) = ∫ u : ℝ, F u := by
    intro F y
    have h1 : (∫ t : ℝ, F (y - t)) = ∫ t : ℝ, (fun s => F (y + s)) (-t) := by
      simp only [sub_eq_add_neg]
    rw [h1, integral_neg_eq_self (fun s => F (y + s)) (volume : Measure ℝ),
        integral_add_left_eq_self (μ := (volume : Measure ℝ)) F y]
  have hcomp : ∀ x : ℝ, Measurable (fun t : ℝ => h (x - t)) := fun x =>
    hmeas.comp (measurable_const.sub measurable_id)
  have hnorm : ∀ x t : ℝ, ‖expKernel a t * h (x - t)‖ ≤ M * expKernel a t := by
    intro x t
    have hnn := (kernel_nonneg_bdd a t).1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    calc expKernel a t * |h (x - t)| ≤ expKernel a t * M :=
            mul_le_mul_of_nonneg_left (hbdd _) hnn
      _ = M * expKernel a t := by ring
  have hi : ∀ x : ℝ, Integrable (fun t : ℝ => expKernel a t * h (x - t)) := by
    intro x
    refine (hker.const_mul M).mono'
      ((kernel_meas a).mul (hcomp x)).aestronglyMeasurable
      (ae_of_all _ (fun t => hnorm x t))
  refine ⟨hi, ?_, ?_⟩
  · intro x
    have habs : |conv (expKernel a) h x| ≤ ∫ t, |expKernel a t * h (x - t)| := by
      unfold conv; exact abs_integral_le_integral_abs
    have hbound : (∫ t, |expKernel a t * h (x - t)|) ≤ ∫ t, M * expKernel a t := by
      refine integral_mono_of_nonneg (ae_of_all _ (fun t => abs_nonneg _))
        (hker.const_mul M) (ae_of_all _ (fun t => ?_))
      simpa [Real.norm_eq_abs] using hnorm x t
    rw [integral_const_mul, hkerInt, mul_one] at hbound
    exact le_trans habs hbound
  · intro x x'
    have hmpRefl : ∀ y : ℝ, MeasurePreserving (fun u : ℝ => y - u) (volume : Measure ℝ) volume := by
      intro y
      have hcomp : (fun u : ℝ => y - u) = (fun u : ℝ => y + u) ∘ (fun u : ℝ => -u) := by
        funext u; simp [sub_eq_add_neg]
      rw [hcomp]
      exact (measurePreserving_add_left volume y).comp (Measure.measurePreserving_neg volume)
    have hiRefl : ∀ y : ℝ, Integrable (fun u : ℝ => expKernel a (y - u) * h u) := by
      intro y
      have hbase := hi y
      have := (hmpRefl y).integrable_comp
        ((kernel_meas a).mul (hcomp y)).aestronglyMeasurable |>.mpr hbase
      refine this.congr (ae_of_all _ (fun u => ?_))
      simp only [Function.comp, sub_sub_cancel]
    have hcv : ∀ y : ℝ, conv (expKernel a) h y = ∫ u : ℝ, expKernel a (y - u) * h u := by
      intro y
      have key := hCV (fun t => expKernel a t * h (y - t)) y
      have hsimp : (∫ t : ℝ, expKernel a (y - t) * h (y - (y - t)))
          = ∫ u : ℝ, expKernel a (y - u) * h u := by
        apply integral_congr_ae; refine ae_of_all _ (fun t => ?_)
        simp only [sub_sub_cancel]
      unfold conv
      rw [← hsimp, key]
    rw [hcv x', hcv x]
    have hdiff : (∫ u : ℝ, expKernel a (x' - u) * h u) - (∫ u : ℝ, expKernel a (x - u) * h u)
        = ∫ u : ℝ, (expKernel a (x' - u) - expKernel a (x - u)) * h u := by
      rw [← integral_sub (hiRefl x') (hiRefl x)]
      apply integral_congr_ae; refine ae_of_all _ (fun u => ?_); ring
    rw [hdiff]
    have hkerDiffInt : Integrable (fun u : ℝ =>
        |expKernel a (u + (x' - x)) - expKernel a u|) := (translate a ha (x' - x)).1
    have hshift : ∀ u : ℝ, expKernel a (x' - u) - expKernel a (x - u)
        = expKernel a ((x - u) + (x' - x)) - expKernel a (x - u) := by
      intro u; congr 2; ring
    have hstepA : |∫ u : ℝ, (expKernel a (x' - u) - expKernel a (x - u)) * h u|
        ≤ ∫ u : ℝ, |(expKernel a (x' - u) - expKernel a (x - u)) * h u| :=
      abs_integral_le_integral_abs
    have hIntDiffAbs : Integrable (fun u : ℝ => |expKernel a (x' - u) - expKernel a (x - u)|) := by
      have hgint : Integrable (fun v : ℝ => |expKernel a (v + (x' - x)) - expKernel a v|) :=
        hkerDiffInt
      have hc := (hmpRefl x).integrable_comp hgint.aestronglyMeasurable |>.mpr hgint
      refine hc.congr (ae_of_all _ (fun u => ?_))
      simp only [Function.comp]
      rw [← hshift u]
    have hmajDiff : Integrable (fun u : ℝ =>
        M * |expKernel a (x' - u) - expKernel a (x - u)|) := hIntDiffAbs.const_mul M
    have hstepB : (∫ u : ℝ, |(expKernel a (x' - u) - expKernel a (x - u)) * h u|)
        ≤ ∫ u : ℝ, M * |expKernel a (x' - u) - expKernel a (x - u)| := by
      refine integral_mono_of_nonneg (ae_of_all _ (fun u => abs_nonneg _)) hmajDiff
        (ae_of_all _ (fun u => ?_))
      dsimp only
      rw [abs_mul]
      calc |expKernel a (x' - u) - expKernel a (x - u)| * |h u|
          ≤ |expKernel a (x' - u) - expKernel a (x - u)| * M :=
            mul_le_mul_of_nonneg_left (hbdd _) (abs_nonneg _)
        _ = M * |expKernel a (x' - u) - expKernel a (x - u)| := by ring
    have hIntShift : (∫ u : ℝ, |expKernel a (x' - u) - expKernel a (x - u)|)
        = ∫ v : ℝ, |expKernel a (v + (x' - x)) - expKernel a v| := by
      have hcongr : (fun u : ℝ => |expKernel a (x' - u) - expKernel a (x - u)|)
          = fun u : ℝ => |expKernel a ((x - u) + (x' - x)) - expKernel a (x - u)| := by
        funext u; rw [hshift u]
      rw [hcongr]
      exact hCV (fun v => |expKernel a (v + (x' - x)) - expKernel a v|) x
    have hTr : (∫ v : ℝ, |expKernel a (v + (x' - x)) - expKernel a v|) ≤ 2 * |a| * |x' - x| :=
      (translate a ha (x' - x)).2
    calc |∫ u : ℝ, (expKernel a (x' - u) - expKernel a (x - u)) * h u|
        ≤ ∫ u : ℝ, |(expKernel a (x' - u) - expKernel a (x - u)) * h u| := hstepA
      _ ≤ ∫ u : ℝ, M * |expKernel a (x' - u) - expKernel a (x - u)| := hstepB
      _ = M * ∫ u : ℝ, |expKernel a (x' - u) - expKernel a (x - u)| := by
            rw [integral_const_mul]
      _ = M * ∫ v : ℝ, |expKernel a (v + (x' - x)) - expKernel a v| := by rw [hIntShift]
      _ ≤ M * (2 * |a| * |x' - x|) := by
            apply mul_le_mul_of_nonneg_left hTr hM
      _ = 2 * M * |a| * |x' - x| := by ring

end Part4
