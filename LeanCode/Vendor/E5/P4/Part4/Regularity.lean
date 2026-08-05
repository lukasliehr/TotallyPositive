import LeanCode.Vendor.E5.P4.Part4.Defs
import LeanCode.Vendor.E5.P4.Part4.KernelBasic
import LeanCode.Vendor.E5.P4.Part4.Translation
import LeanCode.Vendor.E5.Defs
open VendorE5

open MeasureTheory

namespace Part4










theorem decay_conv (f h : ℝ → ℝ) (hf : Measurable f) (hh : Measurable h)
    (C₁ C₂ c₁ c₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hbf : ∀ x : ℝ, |f x| ≤ C₁ * Real.exp (-c₁ * |x|))
    (hbh : ∀ x : ℝ, |h x| ≤ C₂ * Real.exp (-c₂ * |x|)) :
    (∀ x : ℝ, Integrable (fun t : ℝ => f t * h (x - t))) ∧
    (∀ x : ℝ, |conv f h x|
        ≤ C₁ * C₂ * (4 / min c₁ c₂) * Real.exp (-(min c₁ c₂ / 2) * |x|)) := by
  set c := min c₁ c₂ with hcdef
  have hcpos : 0 < c := lt_min hc₁ hc₂

  have hdom : ∀ (x t : ℝ), |f t * h (x - t)|
      ≤ C₁ * C₂ * Real.exp (-(c / 2) * |x|) * Real.exp (-(c / 2) * |t|) := by
    intro x t
    rw [abs_mul]
    calc |f t| * |h (x - t)|
        ≤ (C₁ * Real.exp (-c₁ * |t|)) * (C₂ * Real.exp (-c₂ * |x - t|)) :=
          mul_le_mul (hbf t) (hbh (x - t)) (abs_nonneg _) (by positivity)
      _ = C₁ * C₂ * (Real.exp (-c₁ * |t|) * Real.exp (-c₂ * |x - t|)) := by ring
      _ ≤ C₁ * C₂ * (Real.exp (-(c / 2) * |x|) * Real.exp (-(c / 2) * |t|)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← Real.exp_add, ← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have h1 : c * |t| ≤ c₁ * |t| := mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)
          have h2 : c * |x - t| ≤ c₂ * |x - t| :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
          have h3 : |x| ≤ |t| + |x - t| := by linarith [abs_sub_abs_le_abs_sub x t]
          nlinarith [h1, h2, h3, hcpos, abs_nonneg t, abs_nonneg (x - t),
            mul_le_mul_of_nonneg_left h3 hcpos.le]
      _ = C₁ * C₂ * Real.exp (-(c / 2) * |x|) * Real.exp (-(c / 2) * |t|) := by ring

  have hmaj : ∀ x : ℝ, Integrable
      (fun t : ℝ => C₁ * C₂ * Real.exp (-(c / 2) * |x|) * Real.exp (-(c / 2) * |t|)) :=
    fun x => ((exp_two_side (c / 2) (by positivity)).1).const_mul _
  have hmeas : ∀ x : ℝ, Measurable (fun t : ℝ => f t * h (x - t)) :=
    fun x => hf.mul (hh.comp (measurable_const.sub measurable_id))
  have hintegrable : ∀ x : ℝ, Integrable (fun t : ℝ => f t * h (x - t)) :=
    fun x => (hmaj x).mono' (hmeas x).aestronglyMeasurable
      (ae_of_all _ (fun t => by rw [Real.norm_eq_abs]; exact hdom x t))
  refine ⟨hintegrable, fun x => ?_⟩
  calc |conv f h x| = |∫ t, f t * h (x - t)| := by rw [conv]
    _ ≤ ∫ t, |f t * h (x - t)| := by
        rw [← Real.norm_eq_abs]
        refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
        simp_rw [Real.norm_eq_abs]
    _ ≤ ∫ t, C₁ * C₂ * Real.exp (-(c / 2) * |x|) * Real.exp (-(c / 2) * |t|) :=
        integral_mono (hintegrable x).abs (hmaj x) (fun t => hdom x t)
    _ = C₁ * C₂ * Real.exp (-(c / 2) * |x|) * ∫ t, Real.exp (-(c / 2) * |t|) := by
        rw [integral_const_mul]
    _ = C₁ * C₂ * Real.exp (-(c / 2) * |x|) * (2 / (c / 2)) := by
        rw [(exp_two_side (c / 2) (by positivity)).2]
    _ = C₁ * C₂ * (4 / c) * Real.exp (-(c / 2) * |x|) := by ring





theorem conv_tonelli (f h : ℝ → ℝ) (hf : Measurable f) (hh : Measurable h)
    (C₁ c₁ C₂ c₂ : ℝ) (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hC₂ : 0 < C₂) (hc₂ : 0 < c₂)
    (hbf : ∀ x : ℝ, |f x| ≤ C₁ * Real.exp (-c₁ * |x|))
    (hbh : ∀ x : ℝ, |h x| ≤ C₂ * Real.exp (-c₂ * |x|)) :
    (∀ x : ℝ, Integrable (fun t : ℝ => f t * h (x - t))) ∧
    (Measurable (conv f h) ∧ Integrable (conv f h) ∧
      (∫ x : ℝ, conv f h x) = (∫ t : ℝ, f t) * (∫ u : ℝ, h u)) ∧
    ((∀ x, 0 ≤ f x) → (∀ x, 0 ≤ h x) → ∀ x, 0 ≤ conv f h x) := by
  have hfInt : Integrable f := (decay_integrable f hf C₁ c₁ hC₁ hc₁ hbf).1
  have hhInt : Integrable h := (decay_integrable h hh C₂ c₂ hC₂ hc₂ hbh).1
  have hbridge : conv f h = convolution f h (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext x; simp only [conv, convolution, ContinuousLinearMap.mul_apply']
  refine ⟨(decay_conv f h hf hh C₁ C₂ c₁ c₂ hC₁ hC₂ hc₁ hc₂ hbf hbh).1, ⟨?_, ?_, ?_⟩, ?_⟩
  · have hFmeas : Measurable (fun p : ℝ × ℝ => f p.2 * h (p.1 - p.2)) :=
      (hf.comp measurable_snd).mul (hh.comp (measurable_fst.sub measurable_snd))
    exact (hFmeas.stronglyMeasurable.integral_prod_right').measurable
  · rw [hbridge]; exact hfInt.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hhInt
  · rw [hbridge, integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hfInt hhInt,
      ContinuousLinearMap.mul_apply']
  · intro hfnn hhnn x
    exact integral_nonneg (fun t => mul_nonneg (hfnn t) (hhnn (x - t)))








theorem regularity (m : ℕ) (a : Fin (m + 1) → ℝ) (ha : ∀ j, a j ≠ 0) :
    Measurable (finiteType m a) ∧
    (∀ x : ℝ, 0 ≤ finiteType m a x ∧ finiteType m a x ≤ |a (Fin.last m)|) ∧
    HasExponentialDecay (finiteType m a) ∧
    (Integrable (finiteType m a) ∧ (∫ x : ℝ, finiteType m a x) = 1) ∧
    (1 ≤ m → Continuous (finiteType m a)) := by
  induction m with
  | zero =>
    have hlast : (Fin.last 0 : Fin 1) = 0 := rfl
    simp only [finiteType, hlast]
    refine ⟨kernel_meas (a 0), ?_, ?_, kernel_int (a 0) (ha 0), ?_⟩
    · exact fun x => kernel_nonneg_bdd (a 0) x
    · exact ⟨|a 0|, |a 0|, abs_pos.mpr (ha 0), abs_pos.mpr (ha 0),
        fun x => kernel_envelope (a 0) (ha 0) x⟩
    · intro h; exact absurd h (by norm_num)
  | succ m ih =>
    set a' : Fin (m + 1) → ℝ := fun i => a i.succ with ha'def
    have ha' : ∀ j, a' j ≠ 0 := fun j => ha j.succ
    have hlasteq : a' (Fin.last m) = a (Fin.last (m + 1)) := by
      simp only [ha'def, Fin.succ_last]
    obtain ⟨gmeas, gbdd, gdecay, ⟨gint, ghint⟩, _gcont⟩ := ih a' ha'
    set g : ℝ → ℝ := finiteType m a' with hgdef
    have hfeq : finiteType (m + 1) a = conv (expKernel (a 0)) g := rfl
    have gnn : ∀ x, 0 ≤ g x := fun x => (gbdd x).1
    have gub : ∀ x, g x ≤ |a (Fin.last (m + 1))| := fun x => hlasteq ▸ (gbdd x).2
    have gabs : ∀ x, |g x| ≤ |a (Fin.last (m + 1))| := fun x => by
      rw [abs_of_nonneg (gnn x)]; exact gub x
    obtain ⟨C', c', hC', hc', hgenv⟩ := gdecay
    have hkenv : ∀ t, |expKernel (a 0) t| ≤ |a 0| * Real.exp (-|a 0| * |t|) :=
      kernel_envelope (a 0) (ha 0)
    have ha0pos : (0 : ℝ) < |a 0| := abs_pos.mpr (ha 0)
    have hMnn : (0 : ℝ) ≤ |a (Fin.last (m + 1))| := abs_nonneg _
    obtain ⟨_ckint, ckbd, cklip⟩ :=
      conv_kernel (a 0) (ha 0) |a (Fin.last (m + 1))| hMnn g gmeas gabs
    have hcont : Continuous (conv (expKernel (a 0)) g) := by
      apply LipschitzWith.continuous
        (K := ⟨2 * |a (Fin.last (m + 1))| * |a 0|, by positivity⟩)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, Real.dist_eq]
      exact cklip y x
    have hmeas' : Measurable (conv (expKernel (a 0)) g) := hcont.measurable
    have hlb : ∀ x, 0 ≤ conv (expKernel (a 0)) g x := by
      intro x
      apply integral_nonneg
      intro t
      exact mul_nonneg (kernel_nonneg_bdd (a 0) t).1 (gnn (x - t))
    obtain ⟨_dcint, dcbd⟩ :=
      decay_conv (expKernel (a 0)) g (kernel_meas (a 0)) gmeas
        |a 0| C' |a 0| c' ha0pos hC' ha0pos hc' hkenv hgenv
    obtain ⟨_ctint, ⟨_ctmeas, ctintg, ctintegral⟩, _ctnn⟩ :=
      conv_tonelli (expKernel (a 0)) g (kernel_meas (a 0)) gmeas
        |a 0| |a 0| C' c' ha0pos ha0pos hC' hc' hkenv hgenv
    rw [hfeq]
    refine ⟨hmeas', ?_, ?_, ⟨ctintg, ?_⟩, fun _ => hcont⟩
    · intro x
      exact ⟨hlb x, le_trans (le_abs_self _) (ckbd x)⟩
    · refine ⟨|a 0| * C' * (4 / min |a 0| c'), min |a 0| c' / 2, by positivity,
        by positivity, ?_⟩
      intro x
      have := dcbd x
      rw [abs_of_nonneg (hlb x)] at this ⊢
      exact this
    · rw [ctintegral, (kernel_int (a 0) (ha 0)).2, ghint, one_mul]

end Part4
