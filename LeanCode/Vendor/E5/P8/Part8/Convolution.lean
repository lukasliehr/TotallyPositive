import LeanCode.Vendor.E5.P8.Part8.Kernels
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open scoped BigOperators

namespace Part8

noncomputable section


theorem conv_welldef (f h : ℝ → ℝ) (M : ℝ)
    (hf_meas : Measurable f) (hh_meas : Measurable h)
    (hf_nonneg : ∀ t : ℝ, 0 ≤ f t)
    (hh_bound : ∀ t : ℝ, 0 ≤ h t ∧ h t ≤ M)
    (hf_int : Integrable f) (hh_int : Integrable h) :
  (∀ x : ℝ, Integrable (fun t : ℝ => f t * h (x - t))) ∧
    (∀ x : ℝ, 0 ≤ conv f h x ∧ conv f h x ≤ M * ∫ t : ℝ, f t) ∧
    Measurable (conv f h) ∧
    Integrable (conv f h) ∧
    (∫ x : ℝ, conv f h x) = (∫ x : ℝ, f x) * (∫ x : ℝ, h x) := by
  let F : ℝ × ℝ → ℝ := fun p => f p.1 * h (p.2 - p.1)
  have hF_meas : Measurable F := by
    dsimp [F]
    exact hf_meas.comp (by fun_prop : Measurable fun p : ℝ × ℝ => p.1) |>.mul
      (hh_meas.comp (by fun_prop : Measurable fun p : ℝ × ℝ => p.2 - p.1))
  have hF_sm : StronglyMeasurable F := hF_meas.stronglyMeasurable
  have hF_int : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hF_meas.aestronglyMeasurable]
    constructor
    · filter_upwards with t
      dsimp [F]
      exact (hh_int.comp_sub_right t).const_mul (f t)
    · let C : ℝ := ∫ y : ℝ, ‖h y‖
      have hC_int : Integrable (fun t : ℝ => C * ‖f t‖) := hf_int.norm.const_mul C
      have h_eq :
          (fun t : ℝ => ∫ x : ℝ, ‖f t * h (x - t)‖) =
            fun t : ℝ => C * ‖f t‖ := by
        funext t
        calc
          (∫ x : ℝ, ‖f t * h (x - t)‖) =
              ∫ x : ℝ, ‖f t‖ * ‖h (x - t)‖ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [norm_mul]
          _ = ‖f t‖ * ∫ x : ℝ, ‖h (x - t)‖ := by
            rw [integral_const_mul]
          _ = ‖f t‖ * ∫ x : ℝ, ‖h x‖ := by
            congr 1
            exact integral_sub_right_eq_self (fun x : ℝ => ‖h x‖) t
          _ = C * ‖f t‖ := by
            dsimp [C]
            ring
      change Integrable (fun t : ℝ => ∫ x : ℝ, ‖f t * h (x - t)‖) volume
      rw [h_eq]
      exact hC_int
  have hsection : ∀ x : ℝ, Integrable (fun t : ℝ => f t * h (x - t)) := by
    intro x
    have hmeas_x : AEStronglyMeasurable (fun t : ℝ => f t * h (x - t)) := by
      exact
        (hf_meas.mul
          (hh_meas.comp (by fun_prop : Measurable fun t : ℝ => x - t))).aestronglyMeasurable
    refine (hf_int.norm.const_mul M).mono' hmeas_x ?_
    filter_upwards with t
    calc
      ‖f t * h (x - t)‖ = ‖f t‖ * h (x - t) := by
        simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hh_bound (x - t)).1]
      _ ≤ ‖f t‖ * M := by
        exact mul_le_mul_of_nonneg_left (hh_bound (x - t)).2 (norm_nonneg (f t))
      _ = M * ‖f t‖ := by
        ring
  have hpoint : ∀ x : ℝ, 0 ≤ conv f h x ∧ conv f h x ≤ M * ∫ t : ℝ, f t := by
    intro x
    refine ⟨?_, ?_⟩
    · unfold conv
      exact integral_nonneg (fun t => mul_nonneg (hf_nonneg t) (hh_bound (x - t)).1)
    · unfold conv
      have hMf_int : Integrable (fun t : ℝ => M * f t) := hf_int.const_mul M
      calc
        (∫ t : ℝ, f t * h (x - t)) ≤ ∫ t : ℝ, M * f t := by
          exact integral_mono (hsection x) hMf_int (fun t => by
            calc
              f t * h (x - t) ≤ f t * M := by
                exact mul_le_mul_of_nonneg_left (hh_bound (x - t)).2 (hf_nonneg t)
              _ = M * f t := by
                ring)
        _ = M * ∫ t : ℝ, f t := by
          rw [integral_const_mul]
  have hconv_meas : Measurable (conv f h) := by
    unfold conv
    have hsm : StronglyMeasurable (fun x : ℝ => ∫ t : ℝ, F (t, x) ∂volume) :=
      MeasureTheory.StronglyMeasurable.integral_prod_left' (μ := volume) hF_sm
    simpa [F] using hsm.measurable
  have hconv_int : Integrable (conv f h) := by
    unfold conv
    simpa [F] using hF_int.integral_prod_right
  refine ⟨hsection, hpoint, hconv_meas, hconv_int, ?_⟩
  calc
    (∫ x : ℝ, conv f h x) = ∫ x : ℝ, ∫ t : ℝ, F (t, x) ∂volume := by
      rfl
    _ = ∫ z : ℝ × ℝ, F z ∂(volume.prod volume) := by
      exact (integral_prod_symm F hF_int).symm
    _ = ∫ t : ℝ, ∫ x : ℝ, F (t, x) ∂volume ∂volume := by
      exact integral_prod F hF_int
    _ = ∫ t : ℝ, f t * (∫ x : ℝ, h x) := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp [F]
      calc
        (∫ x : ℝ, f t * h (x - t)) = f t * ∫ x : ℝ, h (x - t) := by
          rw [integral_const_mul]
        _ = f t * ∫ x : ℝ, h x := by
          congr 1
          exact integral_sub_right_eq_self (fun x : ℝ => h x) t
    _ = (∫ t : ℝ, f t) * (∫ x : ℝ, h x) := by
      rw [integral_mul_const]


theorem conv_FT (f h : ℝ → ℝ) (M : ℝ)
    (hf_meas : Measurable f) (hh_meas : Measurable h)
    (hf_nonneg : ∀ t : ℝ, 0 ≤ f t)
    (hh_bound : ∀ t : ℝ, 0 ≤ h t ∧ h t ≤ M)
    (hf_int : Integrable f) (hh_int : Integrable h) :
  ∀ ξ : ℝ, FT (conv f h) ξ = FT f ξ * FT h ξ := by
  intro ξ
  let e : ℝ → ℂ :=
    fun x => Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))
  let F : ℝ × ℝ → ℝ := fun p => f p.1 * h (p.2 - p.1)
  let H : ℝ × ℝ → ℂ := fun p => e p.2 * (F p : ℂ)
  have hconv := conv_welldef f h M hf_meas hh_meas hf_nonneg hh_bound hf_int hh_int
  have hF_meas : Measurable F := by
    dsimp [F]
    exact hf_meas.comp (by fun_prop : Measurable fun p : ℝ × ℝ => p.1) |>.mul
      (hh_meas.comp (by fun_prop : Measurable fun p : ℝ × ℝ => p.2 - p.1))
  have hF_int : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hF_meas.aestronglyMeasurable]
    constructor
    · filter_upwards with t
      dsimp [F]
      exact (hh_int.comp_sub_right t).const_mul (f t)
    · let C : ℝ := ∫ y : ℝ, ‖h y‖
      have hC_int : Integrable (fun t : ℝ => C * ‖f t‖) := hf_int.norm.const_mul C
      have h_eq :
          (fun t : ℝ => ∫ x : ℝ, ‖f t * h (x - t)‖) =
            fun t : ℝ => C * ‖f t‖ := by
        funext t
        calc
          (∫ x : ℝ, ‖f t * h (x - t)‖) =
              ∫ x : ℝ, ‖f t‖ * ‖h (x - t)‖ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [norm_mul]
          _ = ‖f t‖ * ∫ x : ℝ, ‖h (x - t)‖ := by
            rw [integral_const_mul]
          _ = ‖f t‖ * ∫ x : ℝ, ‖h x‖ := by
            congr 1
            exact integral_sub_right_eq_self (fun x : ℝ => ‖h x‖) t
          _ = C * ‖f t‖ := by
            dsimp [C]
            ring
      change Integrable (fun t : ℝ => ∫ x : ℝ, ‖f t * h (x - t)‖) volume
      rw [h_eq]
      exact hC_int
  have hH_meas : AEStronglyMeasurable H (volume.prod volume) := by
    dsimp [H, F, e]
    fun_prop
  have hH_int : Integrable H (volume.prod volume) := by
    refine hF_int.mono' hH_meas ?_
    filter_upwards with p
    have hnorme : ‖e p.2‖ = 1 := by
      dsimp [e]
      rw [Complex.norm_exp]
      simp
    have hF_nonneg : 0 ≤ F p := by
      dsimp [F]
      exact mul_nonneg (hf_nonneg p.1) (hh_bound (p.2 - p.1)).1
    have hH_norm : ‖H p‖ = F p := by
      calc
        ‖H p‖ = ‖e p.2‖ * ‖(F p : ℂ)‖ := by
          simp [H]
        _ = F p := by
          rw [hnorme]
          simp [abs_of_nonneg hF_nonneg]
    exact le_of_eq hH_norm
  have hinner : ∀ t : ℝ,
      (∫ x : ℝ, e x * (F (t, x) : ℂ)) = (e t * (f t : ℂ)) * FT h ξ := by
    intro t
    let G : ℝ → ℂ := fun y => e (y + t) * ((f t * h y : ℝ) : ℂ)
    calc
      (∫ x : ℝ, e x * (F (t, x) : ℂ)) = ∫ x : ℝ, G (x - t) := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [G, F, e]
        congr 2
        norm_num
      _ = ∫ y : ℝ, G y := by
        exact integral_sub_right_eq_self G t
      _ = ∫ y : ℝ, (e t * (f t : ℂ)) * (e y * (h y : ℂ)) := by
        apply integral_congr_ae
        filter_upwards with y
        dsimp [G]
        have hexp_split : e (y + t) = e t * e y := by
          dsimp [e]
          rw [← Complex.exp_add]
          congr 1
          norm_num
          ring
        rw [hexp_split]
        norm_num
        ring
      _ = (e t * (f t : ℂ)) * FT h ξ := by
        rw [integral_const_mul]
        rfl
  unfold FT conv
  calc
    (∫ x : ℝ, e x * ↑(∫ t : ℝ, f t * h (x - t))) =
        ∫ x : ℝ, ∫ t : ℝ, e x * (F (t, x) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      have _hx_int : Integrable (fun t : ℝ => f t * h (x - t)) := hconv.1 x
      have hx_ofReal : ((∫ t : ℝ, f t * h (x - t) : ℝ) : ℂ) =
          ∫ t : ℝ, ((f t * h (x - t) : ℝ) : ℂ) := by
        rw [integral_complex_ofReal]
      rw [hx_ofReal]
      rw [integral_const_mul]
    _ = ∫ t : ℝ, ∫ x : ℝ, e x * (F (t, x) : ℂ) := by
      exact (integral_prod_symm H hH_int).symm.trans (integral_prod H hH_int)
    _ = ∫ t : ℝ, (e t * (f t : ℂ)) * FT h ξ := by
      apply integral_congr_ae
      filter_upwards with t
      exact hinner t
    _ = FT f ξ * FT h ξ := by
      rw [integral_mul_const]
      rfl

private theorem integrable_exp_neg_mul_abs_aux (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => Real.exp (-a * |t|)) ∧
      (∫ t : ℝ, Real.exp (-a * |t|)) = 2 / a := by
  have hpa := p_int a (ne_of_gt ha)
  have hpna := p_int (-a) (neg_ne_zero.mpr (ne_of_gt ha))
  have h_ae : (fun t : ℝ => Real.exp (-a * |t|)) =ᵐ[volume]
      fun t : ℝ => (1 / a) * expKernel a t + (1 / a) * expKernel (-a) t := by
    have hne0_ae : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      rw [ae_iff]
      simp [MeasureTheory.NoAtoms.measure_singleton (μ := volume) (0 : ℝ)]
    filter_upwards [hne0_ae] with t ht0
    rcases lt_or_gt_of_ne ht0.symm with ht | ht
    · have ht_nonneg : 0 ≤ t := le_of_lt ht
      have hpos_formula := (p_formula a (ne_of_gt ha)).1 ha
      have hneg_formula :=
        (p_formula (-a) (neg_ne_zero.mpr (ne_of_gt ha))).2.1 (neg_neg_iff_pos.mpr ha)
      rw [hpos_formula.1 t ht_nonneg]
      rw [hneg_formula.2 t ht]
      have habs : |t| = t := abs_of_pos ht
      rw [habs]
      field_simp [ne_of_gt ha]
      ring
    · have ht_le : t ≤ 0 := le_of_lt ht
      have hneg_formula :=
        (p_formula (-a) (neg_ne_zero.mpr (ne_of_gt ha))).2.1 (neg_neg_iff_pos.mpr ha)
      have hpos_formula := (p_formula a (ne_of_gt ha)).1 ha
      rw [hneg_formula.1 t ht_le]
      rw [hpos_formula.2 t ht]
      have habs : |t| = -t := abs_of_neg ht
      rw [habs]
      field_simp [ne_of_gt ha]
      ring
  have hint_rhs : Integrable
      (fun t : ℝ => (1 / a) * expKernel a t + (1 / a) * expKernel (-a) t) := by
    exact (hpa.1.const_mul (1 / a)).add (hpna.1.const_mul (1 / a))
  constructor
  · exact (integrable_congr h_ae).mpr hint_rhs
  · calc
      (∫ t : ℝ, Real.exp (-a * |t|)) =
          ∫ t : ℝ, (1 / a) * expKernel a t + (1 / a) * expKernel (-a) t := by
        exact integral_congr_ae h_ae
      _ = 2 / a := by
        rw [integral_add (hpa.1.const_mul (1 / a)) (hpna.1.const_mul (1 / a))]
        rw [integral_const_mul, integral_const_mul, hpa.2, hpna.2]
        field_simp [ne_of_gt ha]
        norm_num


theorem conv_decay (f h : ℝ → ℝ) (C₁ C₂ c₁ c₂ : ℝ)
    (hf_meas : Measurable f) (hh_meas : Measurable h)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hf : ∀ t : ℝ, |f t| ≤ C₁ * Real.exp (-c₁ * |t|))
    (hh : ∀ t : ℝ, |h t| ≤ C₂ * Real.exp (-c₂ * |t|)) :
  (∀ x : ℝ, Integrable (fun t : ℝ => f t * h (x - t))) ∧
    ∀ x : ℝ,
      |conv f h x| ≤
        (4 * C₁ * C₂ / min c₁ c₂) * Real.exp (-(min c₁ c₂ / 2) * |x|) := by
  let c : ℝ := min c₁ c₂
  have hc : 0 < c := by dsimp [c]; exact lt_min hc₁ hc₂
  have hc2 : 0 < c / 2 := by positivity
  have hmaj : ∀ x t : ℝ,
      |f t * h (x - t)| ≤
        (C₁ * C₂ * Real.exp (-(c / 2) * |x|)) * Real.exp (-(c / 2) * |t|) := by
    intro x t
    have hc_le₁ : c ≤ c₁ := by dsimp [c]; exact min_le_left c₁ c₂
    have hc_le₂ : c ≤ c₂ := by dsimp [c]; exact min_le_right c₁ c₂
    have htri : |x| ≤ |t| + |x - t| := by
      have htriangle := abs_add_le t (x - t)
      have hx_eq : t + (x - t) = x := by ring
      simpa [hx_eq] using htriangle
    have ht_le : |t| ≤ |t| + |x - t| := by
      have hnon : 0 ≤ |x - t| := abs_nonneg (x - t)
      linarith
    have hbase : (c / 2) * |x| + (c / 2) * |t| ≤ c * (|t| + |x - t|) := by
      nlinarith [mul_le_mul_of_nonneg_left htri (show 0 ≤ c / 2 by positivity),
        mul_le_mul_of_nonneg_left ht_le (show 0 ≤ c / 2 by positivity)]
    have hcoeff : c * (|t| + |x - t|) ≤ c₁ * |t| + c₂ * |x - t| := by
      have h1 := mul_le_mul_of_nonneg_right hc_le₁ (abs_nonneg t)
      have h2 := mul_le_mul_of_nonneg_right hc_le₂ (abs_nonneg (x - t))
      nlinarith
    have hsum : (c / 2) * |x| + (c / 2) * |t| ≤ c₁ * |t| + c₂ * |x - t| :=
      hbase.trans hcoeff
    have hexp : Real.exp (-c₁ * |t|) * Real.exp (-c₂ * |x - t|) ≤
        Real.exp (-(c / 2) * |x|) * Real.exp (-(c / 2) * |t|) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      |f t * h (x - t)| = |f t| * |h (x - t)| := by
        rw [abs_mul]
      _ ≤ (C₁ * Real.exp (-c₁ * |t|)) * (C₂ * Real.exp (-c₂ * |x - t|)) := by
        exact mul_le_mul (hf t) (hh (x - t))
          (abs_nonneg (h (x - t))) (mul_nonneg hC₁.le (Real.exp_pos _).le)
      _ = (C₁ * C₂) * (Real.exp (-c₁ * |t|) * Real.exp (-c₂ * |x - t|)) := by
        ring
      _ ≤ (C₁ * C₂) * (Real.exp (-(c / 2) * |x|) *
          Real.exp (-(c / 2) * |t|)) := by
        exact mul_le_mul_of_nonneg_left hexp (mul_nonneg hC₁.le hC₂.le)
      _ = (C₁ * C₂ * Real.exp (-(c / 2) * |x|)) *
          Real.exp (-(c / 2) * |t|) := by
        ring
  have hmajor_int : ∀ x : ℝ,
      Integrable (fun t : ℝ => (C₁ * C₂ * Real.exp (-(c / 2) * |x|)) *
        Real.exp (-(c / 2) * |t|)) := by
    intro x
    exact (integrable_exp_neg_mul_abs_aux (c / 2) hc2).1.const_mul
      (C₁ * C₂ * Real.exp (-(c / 2) * |x|))
  have hsection : ∀ x : ℝ, Integrable (fun t : ℝ => f t * h (x - t)) := by
    intro x
    have hmeas_x : AEStronglyMeasurable (fun t : ℝ => f t * h (x - t)) volume :=
      (hf_meas.mul
        (hh_meas.comp (by fun_prop : Measurable fun t : ℝ => x - t))).aestronglyMeasurable
    refine (hmajor_int x).mono' hmeas_x ?_
    filter_upwards with t
    simpa [Real.norm_eq_abs] using hmaj x t
  refine ⟨hsection, ?_⟩
  intro x
  have hmajor_eq :
      (∫ t : ℝ, (C₁ * C₂ * Real.exp (-(c / 2) * |x|)) *
        Real.exp (-(c / 2) * |t|)) =
        (4 * C₁ * C₂ / c) * Real.exp (-(c / 2) * |x|) := by
    rw [integral_const_mul]
    rw [(integrable_exp_neg_mul_abs_aux (c / 2) hc2).2]
    field_simp [ne_of_gt hc]
    ring
  have hmono : (∫ t : ℝ, |f t * h (x - t)|) ≤
      ∫ t : ℝ, (C₁ * C₂ * Real.exp (-(c / 2) * |x|)) *
        Real.exp (-(c / 2) * |t|) := by
    have habs_int : Integrable (fun t : ℝ => |f t * h (x - t)|) := by
      simpa [Real.norm_eq_abs] using (hsection x).norm
    exact integral_mono habs_int (hmajor_int x) (fun t => hmaj x t)
  calc
    |conv f h x| ≤ ∫ t : ℝ, |f t * h (x - t)| := by
      unfold conv
      exact abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, (C₁ * C₂ * Real.exp (-(c / 2) * |x|)) *
        Real.exp (-(c / 2) * |t|) := hmono
    _ = (4 * C₁ * C₂ / c) * Real.exp (-(c / 2) * |x|) := hmajor_eq
    _ = (4 * C₁ * C₂ / min c₁ c₂) * Real.exp (-(min c₁ c₂ / 2) * |x|) := by
      dsimp [c]


theorem transl_left (u v : ℝ → ℝ) (c x : ℝ) :
  conv (translate c u) v x = conv u v (x - c) := by
  let f : ℝ → ℝ := fun y => u y * v (x - c - y)
  calc
    conv (translate c u) v x = ∫ t : ℝ, f (t + (-c)) := by
      unfold conv translate
      apply integral_congr_ae
      filter_upwards with t
      dsimp [f]
      congr 2
      ring
    _ = ∫ y : ℝ, f y := by
      exact MeasureTheory.integral_add_right_eq_self f (-c)
    _ = conv u v (x - c) := by
      unfold conv
      rfl


theorem transl_right (u v : ℝ → ℝ) (c x : ℝ) :
  conv u (translate c v) x = conv u v (x - c) := by
  unfold conv translate
  apply integral_congr_ae
  filter_upwards with t
  congr 2
  ring

private theorem q_L1_mod_pos_nonneg (α z : ℝ) (hα : 0 < α) (hz : 0 ≤ z) :
    Integrable (fun u : ℝ => |centeredExp α (u + z) - centeredExp α u|) ∧
      (∫ u : ℝ, |centeredExp α (u + z) - centeredExp α u|) ≤ 2 * z / α := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hq := q_formula α hαne
  have hpos := hq.1 hα
  let G : ℝ → ℝ := fun u =>
    (Set.Icc (-α - z) (-α)).indicator (fun _ : ℝ => 1 / α) u +
      (z / α) * centeredExp α u
  have hshift_int : Integrable (fun u : ℝ => centeredExp α (u + z)) := by
    exact hq.2.2.2.2.1.comp_add_right z
  have htarget_int : Integrable
      (fun u : ℝ => |centeredExp α (u + z) - centeredExp α u|) := by
    simpa [Real.norm_eq_abs] using (hshift_int.sub hq.2.2.2.2.1).norm
  have hI_int :
      Integrable (fun u : ℝ =>
        (Set.Icc (-α - z) (-α)).indicator (fun _ : ℝ => 1 / α) u) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (C := (1 / α : ℝ))
      (s := Set.Icc (-α - z) (-α))
      (μ := volume)
      (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (hC := by simp)
  have hG_int : Integrable G := by
    dsimp [G]
    exact hI_int.add (hq.2.2.2.2.1.const_mul (z / α))
  have hI_int_eq :
      (∫ u : ℝ,
        (Set.Icc (-α - z) (-α)).indicator (fun _ : ℝ => 1 / α) u) = z / α := by
    rw [integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    rw [Real.volume_real_Icc_of_le (by linarith)]
    simp
    ring
  have hG_eq : (∫ u : ℝ, G u) = 2 * z / α := by
    dsimp [G]
    rw [integral_add hI_int (hq.2.2.2.2.1.const_mul (z / α))]
    rw [hI_int_eq, integral_const_mul, hq.2.2.2.2.2]
    ring
  have hle : ∀ u : ℝ, |centeredExp α (u + z) - centeredExp α u| ≤ G u := by
    intro u
    by_cases hu : u ≤ -α
    · by_cases hstrip : -α - z ≤ u
      · have hmem : u ∈ Set.Icc (-α - z) (-α) := ⟨hstrip, hu⟩
        have hnonneg_tail : 0 ≤ (z / α) * centeredExp α u := by
          exact mul_nonneg (div_nonneg hz hα.le) (hq.2.2.2.1 u).1
        have hbound_shift : centeredExp α (u + z) ≤ 1 / α := by
          have hb := (hq.2.2.2.1 (u + z)).2
          simpa [abs_of_pos hα] using hb
        have hbound_u : centeredExp α u ≤ 1 / α := by
          have hb := (hq.2.2.2.1 u).2
          simpa [abs_of_pos hα] using hb
        have hnonneg_shift : 0 ≤ centeredExp α (u + z) := (hq.2.2.2.1 (u + z)).1
        have hnonneg_u : 0 ≤ centeredExp α u := (hq.2.2.2.1 u).1
        have habs : |centeredExp α (u + z) - centeredExp α u| ≤ 1 / α := by
          rw [abs_sub_le_iff]
          constructor <;> linarith
        dsimp [G]
        rw [Set.indicator_of_mem hmem]
        linarith
      · have hu0 : centeredExp α u = 0 := hpos.2 u (by linarith)
        have huz0 : centeredExp α (u + z) = 0 := hpos.2 (u + z) (by linarith)
        have hnotmem : u ∉ Set.Icc (-α - z) (-α) := by
          intro hm
          exact hstrip hm.1
        dsimp [G]
        rw [hu0, huz0, sub_self, abs_zero, Set.indicator_of_notMem hnotmem]
        simp
    · have hu_support : -α ≤ u := le_of_lt (lt_of_not_ge hu)
      have huz_support : -α ≤ u + z := by linarith
      have hnotmem : u ∉ Set.Icc (-α - z) (-α) := by
        intro hm
        exact hu hm.2
      have hratio : centeredExp α (u + z) =
          Real.exp (-(z / α)) * centeredExp α u := by
        rw [hpos.1 (u + z) huz_support, hpos.1 u hu_support]
        calc
          1 / α * Real.exp (-(u + z + α) / α) =
              1 / α * (Real.exp (-(z / α)) * Real.exp (-(u + α) / α)) := by
            congr 1
            rw [← Real.exp_add]
            congr 1
            field_simp [hαne]
            ring
          _ = Real.exp (-(z / α)) * (1 / α * Real.exp (-(u + α) / α)) := by
            ring
      have hexp_le_one : Real.exp (-(z / α)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by have := div_nonneg hz hα.le; linarith)
      have hle_q : centeredExp α (u + z) ≤ centeredExp α u := by
        rw [hratio]
        exact mul_le_of_le_one_left (hq.2.2.2.1 u).1 hexp_le_one
      have hone : 1 - Real.exp (-(z / α)) ≤ z / α := by
        have h := Real.one_sub_le_exp_neg (z / α)
        linarith
      have htail : |centeredExp α (u + z) - centeredExp α u| ≤
          (z / α) * centeredExp α u := by
        rw [abs_of_nonpos (sub_nonpos.mpr hle_q)]
        rw [hratio]
        have hnon : 0 ≤ centeredExp α u := (hq.2.2.2.1 u).1
        nlinarith [mul_le_mul_of_nonneg_right hone hnon]
      dsimp [G]
      rw [Set.indicator_of_notMem hnotmem]
      simpa using htail
  constructor
  · exact htarget_int
  · calc
      (∫ u : ℝ, |centeredExp α (u + z) - centeredExp α u|) ≤ ∫ u : ℝ, G u := by
        exact integral_mono htarget_int hG_int hle
      _ = 2 * z / α := hG_eq

private theorem q_L1_mod_neg_nonneg (α z : ℝ) (hα : α < 0) (hz : 0 ≤ z) :
    Integrable (fun u : ℝ => |centeredExp α (u + z) - centeredExp α u|) ∧
      (∫ u : ℝ, |centeredExp α (u + z) - centeredExp α u|) ≤ 2 * z / |α| := by
  let β : ℝ := -α
  have hβ : 0 < β := by dsimp [β]; linarith
  have hαne : α ≠ 0 := ne_of_lt hα
  have hq := q_formula α hαne
  have hneg := hq.2.1 hα
  let G : ℝ → ℝ := fun u =>
    (Set.Icc (-α - z) (-α)).indicator (fun _ : ℝ => 1 / β) u +
      (z / β) * centeredExp α (u + z)
  have hshift_int : Integrable (fun u : ℝ => centeredExp α (u + z)) := by
    exact hq.2.2.2.2.1.comp_add_right z
  have htarget_int : Integrable
      (fun u : ℝ => |centeredExp α (u + z) - centeredExp α u|) := by
    simpa [Real.norm_eq_abs] using (hshift_int.sub hq.2.2.2.2.1).norm
  have hI_int :
      Integrable (fun u : ℝ =>
        (Set.Icc (-α - z) (-α)).indicator (fun _ : ℝ => 1 / β) u) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (C := (1 / β : ℝ))
      (s := Set.Icc (-α - z) (-α))
      (μ := volume)
      (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (hC := by simp)
  have hG_int : Integrable G := by
    dsimp [G]
    exact hI_int.add (hshift_int.const_mul (z / β))
  have hI_int_eq :
      (∫ u : ℝ,
        (Set.Icc (-α - z) (-α)).indicator (fun _ : ℝ => 1 / β) u) = z / β := by
    rw [integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    rw [Real.volume_real_Icc_of_le (by linarith)]
    simp
    ring
  have hshift_mass : (∫ u : ℝ, centeredExp α (u + z)) = 1 := by
    rw [MeasureTheory.integral_add_right_eq_self (fun u : ℝ => centeredExp α u) z]
    exact hq.2.2.2.2.2
  have hG_eq : (∫ u : ℝ, G u) = 2 * z / β := by
    dsimp [G]
    rw [integral_add hI_int (hshift_int.const_mul (z / β))]
    rw [hI_int_eq, integral_const_mul, hshift_mass]
    ring
  have hle : ∀ u : ℝ, |centeredExp α (u + z) - centeredExp α u| ≤ G u := by
    intro u
    by_cases hu : u ≤ -α
    · by_cases hstrip : -α - z ≤ u
      · have hmem : u ∈ Set.Icc (-α - z) (-α) := ⟨hstrip, hu⟩
        have hbound_shift : centeredExp α (u + z) ≤ 1 / β := by
          have hb := (hq.2.2.2.1 (u + z)).2
          have habs : |α| = β := by dsimp [β]; rw [abs_of_neg hα]
          simpa [habs] using hb
        have hbound_u : centeredExp α u ≤ 1 / β := by
          have hb := (hq.2.2.2.1 u).2
          have habs : |α| = β := by dsimp [β]; rw [abs_of_neg hα]
          simpa [habs] using hb
        have hnonneg_shift : 0 ≤ centeredExp α (u + z) := (hq.2.2.2.1 (u + z)).1
        have hnonneg_u : 0 ≤ centeredExp α u := (hq.2.2.2.1 u).1
        have habs : |centeredExp α (u + z) - centeredExp α u| ≤ 1 / β := by
          rw [abs_sub_le_iff]
          constructor <;> linarith
        have hnonneg_tail : 0 ≤ (z / β) * centeredExp α (u + z) := by
          exact mul_nonneg (div_nonneg hz hβ.le) (hq.2.2.2.1 (u + z)).1
        dsimp [G]
        rw [Set.indicator_of_mem hmem]
        linarith
      · have huz_support : u + z ≤ -α := by linarith
        have hratio : centeredExp α u =
            Real.exp (-(z / β)) * centeredExp α (u + z) := by
          rw [hneg.1 u hu, hneg.1 (u + z) huz_support]
          dsimp [β]
          calc
            1 / -α * Real.exp ((u + α) / -α) =
                1 / -α * Real.exp (-(z / -α) + ((u + z) + α) / -α) := by
              congr 1
              congr 1
              field_simp [neg_ne_zero.mpr hαne]
              ring
            _ = 1 / -α *
                (Real.exp (-(z / -α)) * Real.exp (((u + z) + α) / -α)) := by
              rw [Real.exp_add]
            _ = Real.exp (-(z / -α)) *
                (1 / -α * Real.exp (((u + z) + α) / -α)) := by
              ring
        have hexp_le_one : Real.exp (-(z / β)) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by have := div_nonneg hz hβ.le; linarith)
        have hle_q : centeredExp α u ≤ centeredExp α (u + z) := by
          rw [hratio]
          exact mul_le_of_le_one_left (hq.2.2.2.1 (u + z)).1 hexp_le_one
        have hone : 1 - Real.exp (-(z / β)) ≤ z / β := by
          have h := Real.one_sub_le_exp_neg (z / β)
          linarith
        have htail : |centeredExp α (u + z) - centeredExp α u| ≤
            (z / β) * centeredExp α (u + z) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hle_q)]
          rw [hratio]
          have hnon : 0 ≤ centeredExp α (u + z) := (hq.2.2.2.1 (u + z)).1
          nlinarith [mul_le_mul_of_nonneg_right hone hnon]
        have hnotmem : u ∉ Set.Icc (-α - z) (-α) := by
          intro hm
          exact hstrip hm.1
        dsimp [G]
        rw [Set.indicator_of_notMem hnotmem]
        simpa using htail
    · have hu_gt : -α < u := lt_of_not_ge hu
      have hu0 : centeredExp α u = 0 := hneg.2 u hu_gt
      have huz0 : centeredExp α (u + z) = 0 := hneg.2 (u + z) (by linarith)
      have hnotmem : u ∉ Set.Icc (-α - z) (-α) := by
        intro hm
        exact hu hm.2
      dsimp [G]
      rw [hu0, huz0, sub_self, abs_zero, Set.indicator_of_notMem hnotmem]
      simp
  constructor
  · exact htarget_int
  · calc
      (∫ u : ℝ, |centeredExp α (u + z) - centeredExp α u|) ≤ ∫ u : ℝ, G u := by
        exact integral_mono htarget_int hG_int hle
      _ = 2 * z / β := hG_eq
      _ = 2 * z / |α| := by
        have habs : |α| = β := by dsimp [β]; rw [abs_of_neg hα]
        rw [habs]


theorem q_L1_mod (α y : ℝ) (hα : α ≠ 0) :
  Integrable (fun u : ℝ => |centeredExp α (u + y) - centeredExp α u|) ∧
    (∫ u : ℝ, |centeredExp α (u + y) - centeredExp α u|) ≤ 2 * |y| / |α| := by
  by_cases hy : 0 ≤ y
  · by_cases hαpos : 0 < α
    · have h := q_L1_mod_pos_nonneg α y hαpos hy
      have hyabs : |y| = y := abs_of_nonneg hy
      have hαabs : |α| = α := abs_of_pos hαpos
      constructor
      · exact h.1
      · calc
          (∫ u : ℝ, |centeredExp α (u + y) - centeredExp α u|) ≤ 2 * y / α := h.2
          _ = 2 * |y| / |α| := by rw [hyabs, hαabs]
    · have hαneg : α < 0 := lt_of_le_of_ne (le_of_not_gt hαpos) hα
      have h := q_L1_mod_neg_nonneg α y hαneg hy
      have hyabs : |y| = y := abs_of_nonneg hy
      constructor
      · exact h.1
      · calc
          (∫ u : ℝ, |centeredExp α (u + y) - centeredExp α u|) ≤
              2 * y / |α| := h.2
          _ = 2 * |y| / |α| := by rw [hyabs]
  · let z : ℝ := -y
    have hz : 0 ≤ z := by dsimp [z]; linarith
    by_cases hαpos : 0 < α
    · have h := q_L1_mod_pos_nonneg α z hαpos hz
      let F : ℝ → ℝ := fun u => |centeredExp α (u + z) - centeredExp α u|
      have hpoint :
          (fun u : ℝ => |centeredExp α (u + y) - centeredExp α u|) =
            fun u : ℝ => F (u + y) := by
        funext u
        dsimp [F, z]
        have harg : u + y + -y = u := by ring
        rw [harg]
        rw [abs_sub_comm]
      have hint : Integrable (fun u : ℝ =>
          |centeredExp α (u + y) - centeredExp α u|) := by
        rw [hpoint]
        exact h.1.comp_add_right y
      have hineq :
          (∫ u : ℝ, |centeredExp α (u + y) - centeredExp α u|) ≤
            2 * |y| / |α| := by
        rw [hpoint]
        calc
          (∫ u : ℝ, F (u + y)) = ∫ u : ℝ, F u := by
            exact MeasureTheory.integral_add_right_eq_self F y
          _ ≤ 2 * z / α := h.2
          _ = 2 * |y| / |α| := by
            have hyabs : |y| = z := by dsimp [z]; rw [abs_of_neg (lt_of_not_ge hy)]
            have hαabs : |α| = α := abs_of_pos hαpos
            rw [hyabs, hαabs]
      exact ⟨hint, hineq⟩
    · have hαneg : α < 0 := lt_of_le_of_ne (le_of_not_gt hαpos) hα
      have h := q_L1_mod_neg_nonneg α z hαneg hz
      let F : ℝ → ℝ := fun u => |centeredExp α (u + z) - centeredExp α u|
      have hpoint :
          (fun u : ℝ => |centeredExp α (u + y) - centeredExp α u|) =
            fun u : ℝ => F (u + y) := by
        funext u
        dsimp [F, z]
        have harg : u + y + -y = u := by ring
        rw [harg]
        rw [abs_sub_comm]
      have hint : Integrable (fun u : ℝ =>
          |centeredExp α (u + y) - centeredExp α u|) := by
        rw [hpoint]
        exact h.1.comp_add_right y
      have hineq :
          (∫ u : ℝ, |centeredExp α (u + y) - centeredExp α u|) ≤
            2 * |y| / |α| := by
        rw [hpoint]
        calc
          (∫ u : ℝ, F (u + y)) = ∫ u : ℝ, F u := by
            exact MeasureTheory.integral_add_right_eq_self F y
          _ ≤ 2 * z / |α| := h.2
          _ = 2 * |y| / |α| := by
            have hyabs : |y| = z := by dsimp [z]; rw [abs_of_neg (lt_of_not_ge hy)]
            rw [hyabs]
      exact ⟨hint, hineq⟩


theorem convmeas_basic (r : ℝ → ℝ) (μ : Measure ℝ) (M : ℝ)
    [IsProbabilityMeasure μ]
    (hr_meas : Measurable r) (hr_nonneg : ∀ s : ℝ, 0 ≤ r s)
    (hr_int : Integrable r) (hr_bound : ∀ s : ℝ, r s ≤ M) :
  (∀ x : ℝ, Integrable (fun y : ℝ => r (x - y)) μ ∧
    0 ≤ kernelMeasureConv r μ x ∧ kernelMeasureConv r μ x ≤ M) ∧
    Measurable (kernelMeasureConv r μ) ∧
    Integrable (kernelMeasureConv r μ) ∧
    (∫ x : ℝ, kernelMeasureConv r μ x) = ∫ x : ℝ, r x := by
  let F : ℝ × ℝ → ℝ := fun p => r (p.1 - p.2)
  have hF_meas : Measurable F := by
    dsimp [F]
    exact hr_meas.comp (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 - p.2)
  have hF_sm : StronglyMeasurable F := hF_meas.stronglyMeasurable
  have hF_int : Integrable F (volume.prod μ) := by
    rw [integrable_prod_iff' hF_meas.aestronglyMeasurable]
    constructor
    · filter_upwards with y
      dsimp [F]
      exact hr_int.comp_sub_right y
    · convert MeasureTheory.integrable_const (μ := μ) (∫ x : ℝ, ‖r x‖) using 1
      ext y
      dsimp [F]
      exact integral_sub_right_eq_self (fun x : ℝ => ‖r x‖) y
  have hsection : ∀ x : ℝ, Integrable (fun y : ℝ => r (x - y)) μ := by
    intro x
    have hmeas_x : AEStronglyMeasurable (fun y : ℝ => r (x - y)) μ := by
      exact (hr_meas.comp (by fun_prop : Measurable fun y : ℝ => x - y)).aestronglyMeasurable
    refine (MeasureTheory.integrable_const (μ := μ) M).mono' hmeas_x ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hr_nonneg (x - y))]
    exact hr_bound (x - y)
  have hbasic : ∀ x : ℝ, Integrable (fun y : ℝ => r (x - y)) μ ∧
      0 ≤ kernelMeasureConv r μ x ∧ kernelMeasureConv r μ x ≤ M := by
    intro x
    have hconst_int : Integrable (fun _ : ℝ => M) μ := MeasureTheory.integrable_const M
    refine ⟨hsection x, ?_, ?_⟩
    · unfold kernelMeasureConv
      exact integral_nonneg (fun y => hr_nonneg (x - y))
    · unfold kernelMeasureConv
      calc
        (∫ y : ℝ, r (x - y) ∂μ) ≤ ∫ _ : ℝ, M ∂μ := by
          exact integral_mono (hsection x) hconst_int (fun y => hr_bound (x - y))
        _ = M := by
          simp [MeasureTheory.integral_const, Measure.real, MeasureTheory.IsProbabilityMeasure.measure_univ]
  have hK_meas : Measurable (kernelMeasureConv r μ) := by
    unfold kernelMeasureConv
    have hK_sm : StronglyMeasurable (fun x : ℝ => ∫ y : ℝ, F (x, y) ∂μ) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := μ) hF_sm
    simpa [F] using hK_sm.measurable
  have hK_int : Integrable (kernelMeasureConv r μ) := by
    unfold kernelMeasureConv
    simpa [F] using hF_int.integral_prod_left
  refine ⟨hbasic, hK_meas, hK_int, ?_⟩
  calc
    (∫ x : ℝ, kernelMeasureConv r μ x) = ∫ x : ℝ, ∫ y : ℝ, F (x, y) ∂μ := by
      rfl
    _ = ∫ z : ℝ × ℝ, F z ∂(volume.prod μ) := by
      exact integral_integral hF_int
    _ = ∫ y : ℝ, ∫ x : ℝ, F (x, y) ∂volume ∂μ := by
      exact integral_prod_symm F hF_int
    _ = ∫ y : ℝ, ∫ x : ℝ, r x ∂volume ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp [F]
      exact integral_sub_right_eq_self (fun x : ℝ => r x) y
    _ = ∫ x : ℝ, r x := by
      simp [MeasureTheory.integral_const, Measure.real, MeasureTheory.IsProbabilityMeasure.measure_univ]


theorem convmeas_cont (r : ℝ → ℝ) (μ : Measure ℝ) (M ω δ : ℝ)
    [IsProbabilityMeasure μ]
    (hr_meas : Measurable r) (hr_nonneg : ∀ s : ℝ, 0 ≤ r s)
    (hr_int : Integrable r) (hr_bound : ∀ s : ℝ, r s ≤ M)
    (hω : 0 ≤ ω)
    (hδ : 0 < δ)
    (hmod : ∀ s s' : ℝ, |s - s'| ≤ δ → |r s - r s'| ≤ ω) :
  ∀ x x' : ℝ, |x - x'| ≤ δ →
    |kernelMeasureConv r μ x - kernelMeasureConv r μ x'| ≤ ω := by
  intro x x' hxx'
  have _hω : 0 ≤ ω := hω
  have _hδ : 0 < δ := hδ
  have hbasic := convmeas_basic r μ M hr_meas hr_nonneg hr_int hr_bound
  have hx_int : Integrable (fun y : ℝ => r (x - y)) μ := (hbasic.1 x).1
  have hx'_int : Integrable (fun y : ℝ => r (x' - y)) μ := (hbasic.1 x').1
  have hdiff_int : Integrable (fun y : ℝ => r (x - y) - r (x' - y)) μ := hx_int.sub hx'_int
  have habs_int : Integrable (fun y : ℝ => |r (x - y) - r (x' - y)|) μ := by
    simpa [Real.norm_eq_abs] using hdiff_int.norm
  have hconst_int : Integrable (fun _ : ℝ => ω) μ := MeasureTheory.integrable_const ω
  calc
    |kernelMeasureConv r μ x - kernelMeasureConv r μ x'| =
        |∫ y : ℝ, (r (x - y) - r (x' - y)) ∂μ| := by
      unfold kernelMeasureConv
      rw [integral_sub hx_int hx'_int]
    _ ≤ ∫ y : ℝ, |r (x - y) - r (x' - y)| ∂μ := by
      exact MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _ : ℝ, ω ∂μ := by
      exact integral_mono habs_int hconst_int (fun y => by
        have harg : |(x - y) - (x' - y)| ≤ δ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hxx'
        exact hmod (x - y) (x' - y) harg)
    _ = ω := by
      simp [MeasureTheory.integral_const, Measure.real, MeasureTheory.IsProbabilityMeasure.measure_univ]


theorem convmeas_FT (r : ℝ → ℝ) (μ : Measure ℝ) (M : ℝ)
    [IsProbabilityMeasure μ]
    (hr_meas : Measurable r) (hr_nonneg : ∀ s : ℝ, 0 ≤ r s)
    (hr_int : Integrable r) (hr_bound : ∀ s : ℝ, r s ≤ M) :
  ∀ ξ : ℝ, FT (kernelMeasureConv r μ) ξ = FT r ξ * measureFT μ ξ := by
  intro ξ
  let e : ℝ → ℂ :=
    fun x => Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))
  let F : ℝ × ℝ → ℝ := fun p => r (p.1 - p.2)
  let H : ℝ × ℝ → ℂ := fun p => e p.1 * (r (p.1 - p.2) : ℂ)
  have hbasic := convmeas_basic r μ M hr_meas hr_nonneg hr_int hr_bound
  have hF_meas : Measurable F := by
    dsimp [F]
    exact hr_meas.comp (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 - p.2)
  have hF_int : Integrable F (volume.prod μ) := by
    rw [integrable_prod_iff' hF_meas.aestronglyMeasurable]
    constructor
    · filter_upwards with y
      dsimp [F]
      exact hr_int.comp_sub_right y
    · convert MeasureTheory.integrable_const (μ := μ) (∫ x : ℝ, ‖r x‖) using 1
      ext y
      dsimp [F]
      exact integral_sub_right_eq_self (fun x : ℝ => ‖r x‖) y
  have hH_meas : AEStronglyMeasurable H (volume.prod μ) := by
    dsimp [H, e]
    fun_prop
  have hH_int : Integrable H (volume.prod μ) := by
    refine hF_int.mono' hH_meas ?_
    filter_upwards with p
    have hnorme : ‖e p.1‖ = 1 := by
      dsimp [e]
      rw [Complex.norm_exp]
      simp
    have hH_norm : ‖H p‖ = r (p.1 - p.2) := by
      calc
        ‖H p‖ = ‖e p.1‖ * ‖(r (p.1 - p.2) : ℂ)‖ := by
          simp [H]
        _ = r (p.1 - p.2) := by
          rw [hnorme]
          simp [abs_of_nonneg (hr_nonneg (p.1 - p.2))]
    simpa [F] using le_of_eq hH_norm
  have hinner : ∀ y : ℝ,
      (∫ x : ℝ, e x * (r (x - y) : ℂ)) = e y * FT r ξ := by
    intro y
    let G : ℝ → ℂ := fun s => e (s + y) * (r s : ℂ)
    calc
      (∫ x : ℝ, e x * (r (x - y) : ℂ)) = ∫ x : ℝ, G (x - y) := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [G, e]
        congr 2
        norm_num
      _ = ∫ s : ℝ, G s := by
        exact integral_sub_right_eq_self G y
      _ = ∫ s : ℝ, e y * (e s * (r s : ℂ)) := by
        apply integral_congr_ae
        filter_upwards with s
        dsimp [G]
        have hexp_split : e (s + y) = e y * e s := by
          dsimp [e]
          rw [← Complex.exp_add]
          congr 1
          norm_num
          ring
        rw [hexp_split]
        ring
      _ = e y * FT r ξ := by
        rw [integral_const_mul]
        rfl
  have _hK_int : Integrable (kernelMeasureConv r μ) := hbasic.2.2.1
  unfold FT kernelMeasureConv measureFT
  calc
    (∫ x : ℝ, e x * ↑(∫ y : ℝ, r (x - y) ∂μ)) =
        ∫ x : ℝ, ∫ y : ℝ, e x * (r (x - y) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      have hx_ofReal : ((∫ y : ℝ, r (x - y) ∂μ : ℝ) : ℂ) =
          ∫ y : ℝ, (r (x - y) : ℂ) ∂μ := by
        rw [integral_complex_ofReal]
      rw [hx_ofReal]
      rw [integral_const_mul]
    _ = ∫ y : ℝ, ∫ x : ℝ, e x * (r (x - y) : ℂ) ∂volume ∂μ := by
      exact integral_integral_swap (f := fun x y => e x * (r (x - y) : ℂ)) hH_int
    _ = ∫ y : ℝ, e y * FT r ξ ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      exact hinner y
    _ = (∫ y : ℝ, e y ∂μ) * FT r ξ := by
      rw [integral_mul_const]
    _ = FT r ξ * ∫ y : ℝ, e y ∂μ := by
      ring


theorem convmeas_lattice (r : ℝ → ℝ) (μ : Measure ℝ) (C c : ℝ)
    [IsProbabilityMeasure μ]
    (hC : 0 < C) (hc : 0 < c)
    (hr : ∀ s : ℝ, |r s| ≤ C * Real.exp (-c * |s|)) :
  LatticeDominated (kernelMeasureConv r μ) ∧
    ∃ B : ℤ → ℝ,
      LatticeEnvelope (kernelMeasureConv r μ) B ∧
      (∑' k : ℤ, B k) ≤ C * Real.exp (2 * c) * geomBound c := by
  let B : ℤ → ℝ := fun k => (C * Real.exp c) *
    ∫ y : ℝ, Real.exp (-c * |(k : ℝ) - y|) ∂μ
  have hbase_int : ∀ k : ℤ,
      Integrable (fun y : ℝ => Real.exp (-c * |(k : ℝ) - y|)) μ := by
    intro k
    refine (MeasureTheory.integrable_const (μ := μ) (1 : ℝ)).mono ?_ ?_
    · fun_prop
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith : -c ≤ 0) (abs_nonneg _))
  have hB_nonneg : ∀ k : ℤ, 0 ≤ B k := by
    intro k
    dsimp [B]
    have hint_nonneg : 0 ≤ ∫ y : ℝ, Real.exp (-c * |(k : ℝ) - y|) ∂μ := by
      exact integral_nonneg (fun y => (Real.exp_pos _).le)
    exact mul_nonneg (mul_nonneg hC.le (Real.exp_pos c).le) hint_nonneg
  have hB_finsum_bound : ∀ F : Finset ℤ,
      (∑ k ∈ F, B k) ≤ C * Real.exp (2 * c) * geomBound c := by
    intro F
    have hterm_int : ∀ k ∈ F,
        Integrable (fun y : ℝ => (C * Real.exp c) *
          Real.exp (-c * |(k : ℝ) - y|)) μ := by
      intro k _hk
      exact (hbase_int k).const_mul (C * Real.exp c)
    have hsum_int : Integrable
        (fun y : ℝ => ∑ k ∈ F, (C * Real.exp c) *
          Real.exp (-c * |(k : ℝ) - y|)) μ := by
      exact integrable_finsetSum F hterm_int
    have hconst_int : Integrable (fun _ : ℝ => (C * Real.exp c) *
        (Real.exp c * geomBound c)) μ := by
      exact MeasureTheory.integrable_const _
    have hpoint : ∀ y : ℝ,
        (∑ k ∈ F, (C * Real.exp c) * Real.exp (-c * |(k : ℝ) - y|)) ≤
          (C * Real.exp c) * (Real.exp c * geomBound c) := by
      intro y
      have hshift := (shifted_sum c (-y) hc).2.2 F
      have hsum_eq : (∑ k ∈ F, Real.exp (-c * |(k : ℝ) - y|)) =
          ∑ k ∈ F, Real.exp (-c * |-y + (k : ℝ)|) := by
        apply Finset.sum_congr rfl
        intro k _hk
        congr 2
        ring_nf
      calc
        (∑ k ∈ F, (C * Real.exp c) * Real.exp (-c * |(k : ℝ) - y|)) =
            (C * Real.exp c) * ∑ k ∈ F, Real.exp (-c * |(k : ℝ) - y|) := by
          rw [Finset.mul_sum]
        _ = (C * Real.exp c) * ∑ k ∈ F, Real.exp (-c * |-y + (k : ℝ)|) := by
          rw [hsum_eq]
        _ ≤ (C * Real.exp c) * (Real.exp c * geomBound c) := by
          exact mul_le_mul_of_nonneg_left hshift (by positivity)
    have hsum_bound_integral :
        (∫ y : ℝ, ∑ k ∈ F, (C * Real.exp c) *
          Real.exp (-c * |(k : ℝ) - y|) ∂μ) ≤
        ∫ _ : ℝ, (C * Real.exp c) * (Real.exp c * geomBound c) ∂μ := by
      exact integral_mono hsum_int hconst_int hpoint
    have hsum_eq_int :
        (∑ k ∈ F, B k) =
        ∫ y : ℝ, ∑ k ∈ F, (C * Real.exp c) *
          Real.exp (-c * |(k : ℝ) - y|) ∂μ := by
      calc
        (∑ k ∈ F, B k) =
            ∑ k ∈ F, ∫ y : ℝ, (C * Real.exp c) *
              Real.exp (-c * |(k : ℝ) - y|) ∂μ := by
          apply Finset.sum_congr rfl
          intro k _hk
          dsimp [B]
          rw [integral_const_mul]
        _ = ∫ y : ℝ, ∑ k ∈ F, (C * Real.exp c) *
              Real.exp (-c * |(k : ℝ) - y|) ∂μ := by
          exact (integral_finsetSum F hterm_int).symm
    calc
      (∑ k ∈ F, B k) ≤ ∫ _ : ℝ, (C * Real.exp c) *
          (Real.exp c * geomBound c) ∂μ := by
        rw [hsum_eq_int]
        exact hsum_bound_integral
      _ = (C * Real.exp c) * (Real.exp c * geomBound c) := by
        simp [MeasureTheory.integral_const, Measure.real, MeasureTheory.IsProbabilityMeasure.measure_univ]
      _ = C * Real.exp (2 * c) * geomBound c := by
        rw [show 2 * c = c + c by ring_nf, Real.exp_add]
        ring_nf
  have hB_sum : Summable B := summable_of_sum_le hB_nonneg hB_finsum_bound
  have hB_tsum_bound : (∑' k : ℤ, B k) ≤ C * Real.exp (2 * c) * geomBound c :=
    Real.tsum_le_of_sum_le hB_nonneg hB_finsum_bound
  have henv : LatticeEnvelope (kernelMeasureConv r μ) B := by
    refine ⟨hB_sum, ?_⟩
    intro k x hx
    have hxabs : |x| ≤ (1 : ℝ) := by
      rcases hx with ⟨hx0, hx1⟩
      rw [abs_of_nonneg hx0]
      exact hx1
    have hint_le :
        (∫ y : ℝ, |r (x + k - y)| ∂μ) ≤ B k := by
      have hupper_int : Integrable (fun y : ℝ => (C * Real.exp c) *
          Real.exp (-c * |(k : ℝ) - y|)) μ :=
        (hbase_int k).const_mul (C * Real.exp c)
      have hnonneg_ae : 0 ≤ᵐ[μ] fun y : ℝ => |r (x + k - y)| := by
        exact Filter.Eventually.of_forall (fun y => abs_nonneg _)
      have hle_ae : (fun y : ℝ => |r (x + k - y)|) ≤ᵐ[μ]
          fun y : ℝ => (C * Real.exp c) * Real.exp (-c * |(k : ℝ) - y|) := by
        filter_upwards with y
        have htri_y : |(k : ℝ) - y| - |x| ≤ |x + ((k : ℝ) - y)| := by
          exact rev_triangle x ((k : ℝ) - y)
        have hlower : |(k : ℝ) - y| - 1 ≤ |x + ((k : ℝ) - y)| := by
          linarith
        have harg : -c * |x + ((k : ℝ) - y)| ≤ c + (-c * |(k : ℝ) - y|) := by
          have hmul := mul_le_mul_of_nonpos_left hlower (by linarith : -c ≤ 0)
          nlinarith
        have hexp : Real.exp (-c * |x + ((k : ℝ) - y)|) ≤
            Real.exp c * Real.exp (-c * |(k : ℝ) - y|) := by
          calc
            Real.exp (-c * |x + ((k : ℝ) - y)|) ≤
                Real.exp (c + (-c * |(k : ℝ) - y|)) := Real.exp_le_exp.mpr harg
            _ = Real.exp c * Real.exp (-c * |(k : ℝ) - y|) := by
              rw [Real.exp_add]
        calc
          |r (x + k - y)| ≤ C * Real.exp (-c * |x + ((k : ℝ) - y)|) := by
            simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hr (x + k - y)
          _ ≤ C * (Real.exp c * Real.exp (-c * |(k : ℝ) - y|)) := by
            exact mul_le_mul_of_nonneg_left hexp hC.le
          _ = (C * Real.exp c) * Real.exp (-c * |(k : ℝ) - y|) := by
            ring_nf
      have hmono := integral_mono_of_nonneg hnonneg_ae hupper_int hle_ae
      dsimp [B]
      rwa [integral_const_mul] at hmono
    calc
      |kernelMeasureConv r μ (x + k)| ≤ ∫ y : ℝ, |r (x + k - y)| ∂μ := by
        unfold kernelMeasureConv
        exact abs_integral_le_integral_abs
      _ ≤ B k := hint_le
  exact ⟨⟨B, henv.1, henv.2⟩, ⟨B, henv, hB_tsum_bound⟩⟩


theorem mass_window (μ : Measure ℝ) [IsProbabilityMeasure μ] :
  ∃ n : ℤ, 0 < μ (Set.Ico (n : ℝ) ((n : ℝ) + 1)) := by
  by_contra h
  have hzero : ∀ n : ℤ, μ (Set.Ico (n : ℝ) ((n : ℝ) + 1)) = 0 := by
    intro n
    exact le_antisymm (not_lt.mp (fun hp => h ⟨n, hp⟩)) bot_le
  have hcover : (⋃ n : ℤ, Set.Ico (n : ℝ) ((n : ℝ) + 1)) = (Set.univ : Set ℝ) := by
    ext y
    constructor
    · intro hy
      trivial
    · intro hy
      refine Set.mem_iUnion.2 ⟨⌊y⌋, ?_⟩
      exact ⟨Int.floor_le y, Int.lt_floor_add_one y⟩
  have hnull : μ (⋃ n : ℤ, Set.Ico (n : ℝ) ((n : ℝ) + 1)) = 0 := by
    exact MeasureTheory.measure_iUnion_null hzero
  have huniv0 : μ (Set.univ : Set ℝ) = 0 := by
    rw [← hcover]
    exact hnull
  have hprob : μ (Set.univ : Set ℝ) = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
  rw [huniv0] at hprob
  norm_num at hprob

private theorem kernelMeasureConv_pos_of_pos_on_Icc
    (r : ℝ → ℝ) (μ : Measure ℝ) (v v' x : ℝ) [IsProbabilityMeasure μ]
    (hr_cont : Continuous r) (hr_nonneg : ∀ s : ℝ, 0 ≤ r s)
    (hx_int : Integrable (fun y : ℝ => r (x - y)) μ)
    (hvv : v < v') (hμ : 0 < μ (Set.Ico v v'))
    (hpos : ∀ y : ℝ, y ∈ Set.Icc v v' → 0 < r (x - y)) :
    0 < kernelMeasureConv r μ x := by
  let f : ℝ → ℝ := fun y => r (x - y)
  have hf_cont : Continuous f := by
    dsimp [f]
    fun_prop
  have hIcc_nonempty : (Set.Icc v v').Nonempty := ⟨v, le_rfl, le_of_lt hvv⟩
  rcases isCompact_Icc.exists_isMinOn hIcc_nonempty hf_cont.continuousOn with
    ⟨y0, hy0, hy0min⟩
  have hy0_pos : 0 < f y0 := by
    dsimp [f]
    exact hpos y0 hy0
  have hμreal_pos : 0 < μ.real (Set.Ico v v') := by
    exact ENNReal.toReal_pos hμ.ne' (measure_ne_top μ (Set.Ico v v'))
  have hconst_le : ∀ y ∈ Set.Ico v v', f y0 ≤ f y := by
    intro y hy
    exact hy0min ⟨hy.1, le_of_lt hy.2⟩
  have hset_ge :
      f y0 * μ.real (Set.Ico v v') ≤ ∫ y in Set.Ico v v', f y ∂μ := by
    exact setIntegral_ge_of_const_le_real measurableSet_Ico
      (measure_ne_top μ (Set.Ico v v')) hconst_le hx_int.integrableOn
  have hset_pos : 0 < ∫ y in Set.Ico v v', f y ∂μ :=
    lt_of_lt_of_le (mul_pos hy0_pos hμreal_pos) hset_ge
  have hset_le : ∫ y in Set.Ico v v', f y ∂μ ≤ ∫ y, f y ∂μ := by
    exact setIntegral_le_integral hx_int
      (Filter.Eventually.of_forall (fun y => hr_nonneg (x - y)))
  have htotal_pos : 0 < ∫ y, f y ∂μ := lt_of_lt_of_le hset_pos hset_le
  simpa [kernelMeasureConv, f] using htotal_pos


theorem convmeas_pos (r : ℝ → ℝ) (μ : Measure ℝ) (v v' : ℝ)
    [IsProbabilityMeasure μ]
    (hr_cont : Continuous r) (hr_nonneg : ∀ s : ℝ, 0 ≤ r s)
    (hK_int : ∀ x : ℝ, Integrable (fun y : ℝ => r (x - y)) μ)
    (hvv : v < v') (hμ : 0 < μ (Set.Ico v v')) :
  (∀ u : ℝ, (∀ s : ℝ, u < s → 0 < r s) →
      ∀ x : ℝ, u + v' < x → 0 < kernelMeasureConv r μ x) ∧
    (∀ u : ℝ, (∀ s : ℝ, s < u → 0 < r s) →
      ∀ x : ℝ, x < u + v → 0 < kernelMeasureConv r μ x) ∧
    ((∀ s : ℝ, 0 < r s) → ∀ x : ℝ, 0 < kernelMeasureConv r μ x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hright x hx
    exact kernelMeasureConv_pos_of_pos_on_Icc r μ v v' x hr_cont hr_nonneg (hK_int x)
      hvv hμ (fun y hy => hright (x - y) (by
        have hy_le : y ≤ v' := hy.2
        linarith))
  · intro u hleft x hx
    exact kernelMeasureConv_pos_of_pos_on_Icc r μ v v' x hr_cont hr_nonneg (hK_int x)
      hvv hμ (fun y hy => hleft (x - y) (by
        have hy_ge : v ≤ y := hy.1
        linarith))
  · intro hall x
    exact kernelMeasureConv_pos_of_pos_on_Icc r μ v v' x hr_cont hr_nonneg (hK_int x)
      hvv hμ (fun y _hy => hall (x - y))


def rightNestedCentered : (m : ℕ) → (Fin m → ℝ) → (ℝ → ℝ)
  | 0, _ => fun _ => 0
  | 1, β => centeredExp (β 0)
  | m + 2, β => conv (centeredExp (β 0))
      (rightNestedCentered (m + 1) (fun i => β i.succ))


theorem rm_basic (m : ℕ) (β : Fin (m + 1) → ℝ)
    (hβ : ∀ j, β j ≠ 0) :
  Measurable (rightNestedCentered (m + 1) β) ∧
    (∀ x : ℝ, 0 ≤ rightNestedCentered (m + 1) β x) ∧
    (∃ M : ℝ, ∀ x : ℝ, rightNestedCentered (m + 1) β x ≤ M) ∧
    Integrable (rightNestedCentered (m + 1) β) ∧
    (∫ x : ℝ, rightNestedCentered (m + 1) β x) = 1 ∧
    (1 ≤ m → ∀ x : ℝ, ∃ integrand : ℝ → ℝ, Integrable integrand) := by
  induction m with
  | zero =>
      have hq := q_formula (β 0) (hβ 0)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [rightNestedCentered] using hq.2.2.1
      · intro x
        simpa [rightNestedCentered] using (hq.2.2.2.1 x).1
      · refine ⟨1 / |β 0|, ?_⟩
        intro x
        simpa [rightNestedCentered] using (hq.2.2.2.1 x).2
      · simpa [rightNestedCentered] using hq.2.2.2.2.1
      · simpa [rightNestedCentered] using hq.2.2.2.2.2
      · intro hm
        norm_num at hm
  | succ m ih =>
      let βtail : Fin (m + 1) → ℝ := fun i => β i.succ
      have htail : ∀ j, βtail j ≠ 0 := by
        intro j
        exact hβ j.succ
      rcases ih βtail htail with
        ⟨htail_meas, htail_nonneg, ⟨M, htail_bound⟩, htail_int, htail_mass,
          _htail_genuine⟩
      have hq := q_formula (β 0) (hβ 0)
      have hconv :=
        conv_welldef (centeredExp (β 0)) (rightNestedCentered (m + 1) βtail) M
          hq.2.2.1 htail_meas (fun t => (hq.2.2.2.1 t).1)
          (fun t => ⟨htail_nonneg t, htail_bound t⟩) hq.2.2.2.2.1 htail_int
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [rightNestedCentered, βtail] using hconv.2.2.1
      · intro x
        simpa [rightNestedCentered, βtail] using (hconv.2.1 x).1
      · refine ⟨M, ?_⟩
        intro x
        have hb := (hconv.2.1 x).2
        simpa [rightNestedCentered, βtail, hq.2.2.2.2.2] using hb
      · simpa [rightNestedCentered, βtail] using hconv.2.2.2.1
      · simpa [rightNestedCentered, βtail, hq.2.2.2.2.2, htail_mass] using
          hconv.2.2.2.2
      · intro _hm x
        exact ⟨fun _ : ℝ => (0 : ℝ), by simp⟩


theorem rm_FT (m : ℕ) (β : Fin m → ℝ)
    (hm : 1 ≤ m) (hβ : ∀ j, β j ≠ 0) :
  ∀ ξ : ℝ, FT (rightNestedCentered m β) ξ =
    ∏ j : Fin m, expFactor (β j) ξ := by
  induction m with
  | zero =>
      norm_num at hm
  | succ m ih =>
      cases m with
      | zero =>
          intro ξ
          have hq := (q_FT (β 0) (hβ 0)).1 ξ
          simpa [rightNestedCentered, Fin.prod_univ_one] using hq
      | succ n =>
          intro ξ
          let βtail : Fin (n + 1) → ℝ := fun i => β i.succ
          have htail : ∀ j, βtail j ≠ 0 := by
            intro j
            exact hβ j.succ
          have htail_basic := rm_basic n βtail htail
          rcases htail_basic.2.2.1 with ⟨M, htail_bound⟩
          have hq := q_formula (β 0) (hβ 0)
          have hconv :=
            conv_FT (centeredExp (β 0)) (rightNestedCentered (n + 1) βtail) M
              hq.2.2.1 htail_basic.1 (fun t => (hq.2.2.2.1 t).1)
              (fun t => ⟨htail_basic.2.1 t, htail_bound t⟩)
              hq.2.2.2.2.1 htail_basic.2.2.2.1 ξ
          have htail_ft := ih βtail (by omega) htail ξ
          have hqft := (q_FT (β 0) (hβ 0)).1 ξ
          calc
            FT (rightNestedCentered (Nat.succ (Nat.succ n)) β) ξ =
                FT (conv (centeredExp (β 0)) (rightNestedCentered (n + 1) βtail)) ξ := by
              rfl
            _ = FT (centeredExp (β 0)) ξ *
                FT (rightNestedCentered (n + 1) βtail) ξ := hconv
            _ = expFactor (β 0) ξ *
                ∏ j : Fin (n + 1), expFactor (βtail j) ξ := by
              rw [hqft, htail_ft]
            _ = ∏ j : Fin (Nat.succ (Nat.succ n)), expFactor (β j) ξ := by
              symm
              rw [Fin.prod_univ_succ]

private theorem centeredExp_decay_aux (α : ℝ) (hα : α ≠ 0) :
    ∀ t : ℝ, |centeredExp α t| ≤
      (Real.exp 1 / |α|) * Real.exp (-(1 / |α|) * |t|) := by
  intro t
  have hq := q_formula α hα
  have hp := p_formula (1 / α) (one_div_ne_zero hα)
  have hp_bound := hp.2.2.2.2 (t + α)
  have hnonneg : 0 ≤ centeredExp α t := (hq.2.2.2.1 t).1
  have htri : |t| ≤ |t + α| + |α| := by
    have h := abs_add_le (t + α) (-α)
    have ht : t + α + -α = t := by ring
    simpa [ht, abs_neg] using h
  have hdist : |t| - |α| ≤ |t + α| := by
    linarith
  have hinv_pos : 0 < 1 / |α| :=
    one_div_pos.mpr (abs_pos.mpr hα)
  have hexp_arg : -((1 / |α|) * |t + α|) ≤ 1 + -((1 / |α|) * |t|) := by
    have hmul := mul_le_mul_of_nonpos_left hdist (show -(1 / |α|) ≤ 0 by linarith)
    have hunit : (1 / |α|) * |α| = 1 := by
      field_simp [abs_ne_zero.mpr hα]
    nlinarith
  have hexp : Real.exp (-(1 / |α|) * |t + α|) ≤
      Real.exp 1 * Real.exp (-(1 / |α|) * |t|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hexp_arg]
  calc
    |centeredExp α t| = centeredExp α t := abs_of_nonneg hnonneg
    _ = expKernel (1 / α) (t + α) := rfl
    _ ≤ |1 / α| * Real.exp (-|1 / α| * |t + α|) := hp_bound
    _ = (1 / |α|) * Real.exp (-(1 / |α|) * |t + α|) := by
      rw [abs_one_div]
    _ ≤ (1 / |α|) * (Real.exp 1 * Real.exp (-(1 / |α|) * |t|)) := by
      exact mul_le_mul_of_nonneg_left hexp (le_of_lt hinv_pos)
    _ = (Real.exp 1 / |α|) * Real.exp (-(1 / |α|) * |t|) := by
      ring


theorem rm_decay (m : ℕ) (β : Fin m → ℝ)
    (hm : 1 ≤ m) (hβ : ∀ j, β j ≠ 0) :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ x : ℝ, |rightNestedCentered m β x| ≤ C * Real.exp (-c * |x|) := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      cases m with
      | zero =>
          let C : ℝ := Real.exp 1 / |β 0|
          let c : ℝ := 1 / |β 0|
          have hβabs : 0 < |β 0| := abs_pos.mpr (hβ 0)
          have hC : 0 < C := by
            dsimp [C]
            exact div_pos (Real.exp_pos 1) hβabs
          have hc : 0 < c := by
            dsimp [c]
            exact one_div_pos.mpr hβabs
          refine ⟨C, c, hC, hc, ?_⟩
          intro x
          simpa [rightNestedCentered, C, c] using centeredExp_decay_aux (β 0) (hβ 0) x
      | succ n =>
          let βtail : Fin (n + 1) → ℝ := fun i => β i.succ
          have htail : ∀ j, βtail j ≠ 0 := by
            intro j
            exact hβ j.succ
          rcases ih βtail (by omega) htail with ⟨Ct, ct, hCt, hct, htail_decay⟩
          let Cq : ℝ := Real.exp 1 / |β 0|
          let cq : ℝ := 1 / |β 0|
          have hβabs : 0 < |β 0| := abs_pos.mpr (hβ 0)
          have hCq : 0 < Cq := by
            dsimp [Cq]
            exact div_pos (Real.exp_pos 1) hβabs
          have hcq : 0 < cq := by
            dsimp [cq]
            exact one_div_pos.mpr hβabs
          have hq_meas : Measurable (centeredExp (β 0)) :=
            (q_formula (β 0) (hβ 0)).2.2.1
          have htail_meas : Measurable (rightNestedCentered (n + 1) βtail) :=
            (rm_basic n βtail htail).1
          have hconv := conv_decay (centeredExp (β 0))
            (rightNestedCentered (n + 1) βtail) Cq Ct cq ct
            hq_meas htail_meas hCq hCt hcq hct
            (centeredExp_decay_aux (β 0) (hβ 0)) htail_decay
          let C : ℝ := 4 * Cq * Ct / min cq ct
          let cnew : ℝ := min cq ct / 2
          have hmin : 0 < min cq ct := lt_min hcq hct
          have hC : 0 < C := by
            dsimp [C]
            exact div_pos (mul_pos (mul_pos (by norm_num) hCq) hCt) hmin
          have hcnew : 0 < cnew := by
            dsimp [cnew]
            exact half_pos hmin
          refine ⟨C, cnew, hC, hcnew, ?_⟩
          intro x
          have hx := hconv.2 x
          simpa [rightNestedCentered, βtail, C, cnew, Cq, cq] using hx

private theorem continuous_of_real_lipschitz (f : ℝ → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (h : ∀ x y : ℝ, |f x - f y| ≤ Λ * |x - y|) : Continuous f := by
  have hLip : LipschitzWith ⟨Λ, hΛ⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |f x - f y| ≤ Λ * |x - y|
    exact h x y
  exact hLip.continuous

private theorem rm_cont_base_bound (β : Fin 2 → ℝ) (hβ : ∀ j, β j ≠ 0) :
    ∀ x x' : ℝ,
      |rightNestedCentered 2 β x - rightNestedCentered 2 β x'| ≤
        (2 / (|β 0| * |β 1|)) * |x - x'| := by
  intro x x'
  let q0 : ℝ → ℝ := centeredExp (β 0)
  let q1 : ℝ → ℝ := centeredExp (β 1)
  have hq0 := q_formula (β 0) (hβ 0)
  have hq1 := q_formula (β 1) (hβ 1)
  have hconv := conv_welldef q0 q1 (1 / |β 1|)
    (by simpa [q0] using hq0.2.2.1)
    (by simpa [q1] using hq1.2.2.1)
    (by intro t; simpa [q0] using (hq0.2.2.2.1 t).1)
    (by intro t; exact ⟨by simpa [q1] using (hq1.2.2.2.1 t).1,
      by simpa [q1, one_div] using (hq1.2.2.2.1 t).2⟩)
    (by simpa [q0] using hq0.2.2.2.2.1)
    (by simpa [q1] using hq1.2.2.2.2.1)
  have hx_int : Integrable (fun t : ℝ => q0 t * q1 (x - t)) := hconv.1 x
  have hx'_int : Integrable (fun t : ℝ => q0 t * q1 (x' - t)) := hconv.1 x'
  have hprod_diff_int :
      Integrable (fun t : ℝ => q0 t * (q1 (x - t) - q1 (x' - t))) := by
    have hsub := hx_int.sub hx'_int
    change Integrable (fun t : ℝ => q0 t * q1 (x - t) - q0 t * q1 (x' - t)) at hsub
    convert hsub using 1
    ext t
    ring_nf
  let F : ℝ → ℝ := fun u => |q1 (u + (x - x')) - q1 u|
  have hF_mod := q_L1_mod (β 1) (x - x') (hβ 1)
  have hF_int : Integrable F := by
    simpa [F, q1] using hF_mod.1
  have hD_int : Integrable (fun t : ℝ => |q1 (x - t) - q1 (x' - t)|) := by
    have hcomp := hF_int.comp_sub_left x'
    convert hcomp using 1
    ext t
    dsimp [F]
    congr 1
    ring_nf
  have hD_eq :
      (∫ t : ℝ, |q1 (x - t) - q1 (x' - t)|) = ∫ u : ℝ, F u := by
    calc
      (∫ t : ℝ, |q1 (x - t) - q1 (x' - t)|) = ∫ t : ℝ, F (x' - t) := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp [F]
        congr 1
        ring_nf
      _ = ∫ u : ℝ, F u := by
        exact integral_sub_left_eq_self F volume x'
  have hD_bound :
      (∫ t : ℝ, |q1 (x - t) - q1 (x' - t)|) ≤ 2 * |x - x'| / |β 1| := by
    rw [hD_eq]
    simpa [F, q1] using hF_mod.2
  have hmajor_int :
      Integrable (fun t : ℝ => (1 / |β 0|) * |q1 (x - t) - q1 (x' - t)|) :=
    hD_int.const_mul (1 / |β 0|)
  have hq0_bound : ∀ t : ℝ, q0 t ≤ 1 / |β 0| := by
    intro t
    simpa [q0] using (hq0.2.2.2.1 t).2
  calc
    |rightNestedCentered 2 β x - rightNestedCentered 2 β x'| =
        |(∫ t : ℝ, q0 t * q1 (x - t)) - ∫ t : ℝ, q0 t * q1 (x' - t)| := by
      rfl
    _ = |∫ t : ℝ, (q0 t * q1 (x - t) - q0 t * q1 (x' - t))| := by
      rw [integral_sub hx_int hx'_int]
    _ = |∫ t : ℝ, q0 t * (q1 (x - t) - q1 (x' - t))| := by
      apply congrArg abs
      apply integral_congr_ae
      filter_upwards with t
      ring_nf
    _ ≤ ∫ t : ℝ, |q0 t * (q1 (x - t) - q1 (x' - t))| := by
      exact abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, (1 / |β 0|) * |q1 (x - t) - q1 (x' - t)| := by
      exact integral_mono (by simpa [abs_mul] using hprod_diff_int.norm) hmajor_int (fun t => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by
          rw [abs_of_nonneg]
          · exact hq0_bound t
          · simpa [q0] using (hq0.2.2.2.1 t).1) (abs_nonneg _))
    _ = (1 / |β 0|) * ∫ t : ℝ, |q1 (x - t) - q1 (x' - t)| := by
      rw [integral_const_mul]
    _ ≤ (1 / |β 0|) * (2 * |x - x'| / |β 1|) := by
      exact mul_le_mul_of_nonneg_left hD_bound (by positivity)
    _ = (2 / (|β 0| * |β 1|)) * |x - x'| := by
      have hb0 : |β 0| ≠ 0 := abs_ne_zero.mpr (hβ 0)
      have hb1 : |β 1| ≠ 0 := abs_ne_zero.mpr (hβ 1)
      field_simp [hb0, hb1]

private theorem conv_centered_lipschitz_bound (a : ℝ) (f : ℝ → ℝ) (M Λ : ℝ)
    (ha : a ≠ 0) (hf_meas : Measurable f) (hf_nonneg : ∀ y : ℝ, 0 ≤ f y)
    (hf_bound : ∀ y : ℝ, f y ≤ M) (hf_int : Integrable f)
    (hlip : ∀ x x' : ℝ, |f x - f x'| ≤ Λ * |x - x'|) :
    ∀ x x' : ℝ, |conv (centeredExp a) f x - conv (centeredExp a) f x'| ≤
      Λ * |x - x'| := by
  intro x x'
  have hq := q_formula a ha
  have hconv := conv_welldef (centeredExp a) f M
    hq.2.2.1 hf_meas (fun t => (hq.2.2.2.1 t).1)
    (fun t => ⟨hf_nonneg t, hf_bound t⟩) hq.2.2.2.2.1 hf_int
  have hx_int : Integrable (fun t : ℝ => centeredExp a t * f (x - t)) := hconv.1 x
  have hx'_int : Integrable (fun t : ℝ => centeredExp a t * f (x' - t)) := hconv.1 x'
  have hprod_diff_int :
      Integrable (fun t : ℝ => centeredExp a t * (f (x - t) - f (x' - t))) := by
    have hsub := hx_int.sub hx'_int
    change Integrable
      (fun t : ℝ => centeredExp a t * f (x - t) - centeredExp a t * f (x' - t)) at hsub
    convert hsub using 1
    ext t
    ring_nf
  have hmajor_int : Integrable (fun t : ℝ => (Λ * |x - x'|) * centeredExp a t) :=
    hq.2.2.2.2.1.const_mul (Λ * |x - x'|)
  calc
    |conv (centeredExp a) f x - conv (centeredExp a) f x'| =
        |(∫ t : ℝ, centeredExp a t * f (x - t)) -
          ∫ t : ℝ, centeredExp a t * f (x' - t)| := by
      rfl
    _ = |∫ t : ℝ, (centeredExp a t * f (x - t) - centeredExp a t * f (x' - t))| := by
      rw [integral_sub hx_int hx'_int]
    _ = |∫ t : ℝ, centeredExp a t * (f (x - t) - f (x' - t))| := by
      apply congrArg abs
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ ≤ ∫ t : ℝ, |centeredExp a t * (f (x - t) - f (x' - t))| := by
      exact abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, (Λ * |x - x'|) * centeredExp a t := by
      exact integral_mono (by simpa [abs_mul] using hprod_diff_int.norm) hmajor_int (fun t => by
        have hq_nonneg : 0 ≤ centeredExp a t := (hq.2.2.2.1 t).1
        have harg : |(x - t) - (x' - t)| = |x - x'| := by
          congr 1
          ring
        have hdiff := hlip (x - t) (x' - t)
        rw [harg] at hdiff
        rw [abs_mul, abs_of_nonneg hq_nonneg]
        have hmul := mul_le_mul_of_nonneg_left hdiff hq_nonneg
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    _ = Λ * |x - x'| := by
      rw [integral_const_mul, hq.2.2.2.2.2]
      ring


theorem rm_cont (m : ℕ) (β : Fin m → ℝ)
    (hm : 2 ≤ m) (hβ : ∀ j, β j ≠ 0) :
  ∃ Λ : ℝ, 0 < Λ ∧
    (∀ x x' : ℝ,
      |rightNestedCentered m β x - rightNestedCentered m β x'| ≤ Λ * |x - x'|) ∧
    Continuous (rightNestedCentered m β) := by
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              let Λ : ℝ := 2 / (|β 0| * |β 1|)
              have hΛ : 0 < Λ := by
                dsimp [Λ]
                exact div_pos (by norm_num) (mul_pos (abs_pos.mpr (hβ 0)) (abs_pos.mpr (hβ 1)))
              have hbound : ∀ x x' : ℝ,
                  |rightNestedCentered 2 β x - rightNestedCentered 2 β x'| ≤
                    Λ * |x - x'| := by
                simpa [Λ] using rm_cont_base_bound β hβ
              exact ⟨Λ, hΛ, hbound, continuous_of_real_lipschitz _ Λ hΛ.le hbound⟩
          | succ k =>
              let βtail : Fin (Nat.succ (Nat.succ k)) → ℝ := fun i => β i.succ
              have htail_ne : ∀ j, βtail j ≠ 0 := by
                intro j
                exact hβ j.succ
              rcases ih βtail (by omega) htail_ne with ⟨Λ, hΛ, htail_lip, _htail_cont⟩
              have htail_basic := rm_basic (Nat.succ k) βtail htail_ne
              rcases htail_basic.2.2.1 with ⟨M, hM⟩
              have hbound : ∀ x x' : ℝ,
                  |rightNestedCentered (Nat.succ (Nat.succ (Nat.succ k))) β x -
                    rightNestedCentered (Nat.succ (Nat.succ (Nat.succ k))) β x'| ≤
                    Λ * |x - x'| := by
                intro x x'
                have h := conv_centered_lipschitz_bound (β 0)
                  (rightNestedCentered (Nat.succ (Nat.succ k)) βtail) M Λ
                  (hβ 0) htail_basic.1 htail_basic.2.1 hM htail_basic.2.2.2.1
                  htail_lip x x'
                simpa [rightNestedCentered, βtail] using h
              exact ⟨Λ, hΛ, hbound, continuous_of_real_lipschitz _ Λ hΛ.le hbound⟩

private theorem centeredExp_conv_pos_of_interval (a b x l u : ℝ)
    (ha_ne : a ≠ 0) (hb_ne : b ≠ 0) (hlu : l < u)
    (ha_pos : ∀ t : ℝ, t ∈ Set.Ioo l u → 0 < centeredExp a t)
    (hb_pos : ∀ t : ℝ, t ∈ Set.Ioo l u → 0 < centeredExp b (x - t)) :
    0 < conv (centeredExp a) (centeredExp b) x := by
  have hqa := q_formula a ha_ne
  have hqb := q_formula b hb_ne
  have hconv := conv_welldef (centeredExp a) (centeredExp b) (1 / |b|)
    hqa.2.2.1 hqb.2.2.1 (fun t => (hqa.2.2.2.1 t).1)
    (fun t => ⟨(hqb.2.2.2.1 t).1, (hqb.2.2.2.1 t).2⟩)
    hqa.2.2.2.2.1 hqb.2.2.2.2.1
  have hnonneg : ∀ t : ℝ, 0 ≤ centeredExp a t * centeredExp b (x - t) := by
    intro t
    exact mul_nonneg (hqa.2.2.2.1 t).1 (hqb.2.2.2.1 (x - t)).1
  have hsupport_pos :
      0 < volume (Function.support fun t : ℝ => centeredExp a t * centeredExp b (x - t)) := by
    have hsubset : Set.Ioo l u ⊆
        Function.support (fun t : ℝ => centeredExp a t * centeredExp b (x - t)) := by
      intro t ht
      exact ne_of_gt (mul_pos (ha_pos t ht) (hb_pos t ht))
    have hvol : 0 < volume (Set.Ioo l u) :=
      (Measure.measure_Ioo_pos (μ := volume)).mpr hlu
    exact lt_of_lt_of_le hvol (measure_mono hsubset)
  have hpos := (integral_pos_iff_support_of_nonneg hnonneg (hconv.1 x)).2 hsupport_pos
  simpa [conv] using hpos


theorem r2_pos (β : Fin 2 → ℝ) (hβ : ∀ j, β j ≠ 0) :
  ((0 < β 0 ∧ 0 < β 1) →
      ∀ x : ℝ, -β 0 - β 1 < x → 0 < rightNestedCentered 2 β x) ∧
    ((β 0 < 0 ∧ β 1 < 0) →
      ∀ x : ℝ, x < -β 0 - β 1 → 0 < rightNestedCentered 2 β x) ∧
    (((0 < β 0 ∧ β 1 < 0) ∨ (β 0 < 0 ∧ 0 < β 1)) →
      ∀ x : ℝ, 0 < rightNestedCentered 2 β x) := by
  rcases q_window (β 0) (hβ 0) with ⟨_, _, _, _, hw0⟩
  rcases q_window (β 1) (hβ 1) with ⟨_, _, _, _, hw1⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hβ0_pos, hβ1_pos⟩ x hx
    let δ : ℝ := min 1 (x + β 0 + β 1)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact lt_min zero_lt_one (by linarith)
    have hδ_le : δ ≤ x + β 0 + β 1 := by
      dsimp [δ]
      exact min_le_right 1 (x + β 0 + β 1)
    have hq0_pos := (hw0.1 hβ0_pos).2
    have hq1_pos := (hw1.1 hβ1_pos).2
    have hconv := centeredExp_conv_pos_of_interval (β 0) (β 1) x
      (-β 0) (-β 0 + δ) (hβ 0) (hβ 1) (by linarith)
      (fun t ht => hq0_pos t (by linarith [ht.1]))
      (fun t ht => hq1_pos (x - t) (by linarith [ht.2, hδ_le]))
    simpa [rightNestedCentered] using hconv
  · rintro ⟨hβ0_neg, hβ1_neg⟩ x hx
    let δ : ℝ := min 1 (-β 0 - β 1 - x)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact lt_min zero_lt_one (by linarith)
    have hδ_le : δ ≤ -β 0 - β 1 - x := by
      dsimp [δ]
      exact min_le_right 1 (-β 0 - β 1 - x)
    have hq0_pos := (hw0.2 hβ0_neg).2
    have hq1_pos := (hw1.2 hβ1_neg).2
    have hconv := centeredExp_conv_pos_of_interval (β 0) (β 1) x
      (-β 0 - δ) (-β 0) (hβ 0) (hβ 1) (by linarith)
      (fun t ht => hq0_pos t (by linarith [ht.2]))
      (fun t ht => hq1_pos (x - t) (by linarith [ht.1, hδ_le]))
    simpa [rightNestedCentered] using hconv
  · intro hsign x
    rcases hsign with ⟨hβ0_pos, hβ1_neg⟩ | ⟨hβ0_neg, hβ1_pos⟩
    · let T : ℝ := max (-β 0) (x + β 1)
      have hT0 : -β 0 ≤ T := by
        dsimp [T]
        exact le_max_left (-β 0) (x + β 1)
      have hT1 : x + β 1 ≤ T := by
        dsimp [T]
        exact le_max_right (-β 0) (x + β 1)
      have hq0_pos := (hw0.1 hβ0_pos).2
      have hq1_pos := (hw1.2 hβ1_neg).2
      have hconv := centeredExp_conv_pos_of_interval (β 0) (β 1) x
        T (T + 1) (hβ 0) (hβ 1) (by linarith)
        (fun t ht => hq0_pos t (by linarith [ht.1, hT0]))
        (fun t ht => hq1_pos (x - t) (by linarith [ht.1, hT1]))
      simpa [rightNestedCentered] using hconv
    · let T : ℝ := min (-β 0) (x + β 1)
      have hT0 : T ≤ -β 0 := by
        dsimp [T]
        exact min_le_left (-β 0) (x + β 1)
      have hT1 : T ≤ x + β 1 := by
        dsimp [T]
        exact min_le_right (-β 0) (x + β 1)
      have hq0_pos := (hw0.2 hβ0_neg).2
      have hq1_pos := (hw1.1 hβ1_pos).2
      have hconv := centeredExp_conv_pos_of_interval (β 0) (β 1) x
        (T - 1) T (hβ 0) (hβ 1) (by linarith)
        (fun t ht => hq0_pos t (by linarith [ht.2, hT0]))
        (fun t ht => hq1_pos (x - t) (by linarith [ht.2, hT1]))
      simpa [rightNestedCentered] using hconv

private theorem centeredExp_conv_tail_pos_of_interval
    (a x l u : ℝ) (f : ℝ → ℝ) (M : ℝ)
    (ha_ne : a ≠ 0) (hf_meas : Measurable f) (hf_nonneg : ∀ y : ℝ, 0 ≤ f y)
    (hf_bound : ∀ y : ℝ, f y ≤ M) (hf_int : Integrable f) (hlu : l < u)
    (ha_pos : ∀ t : ℝ, t ∈ Set.Ioo l u → 0 < centeredExp a t)
    (hf_pos : ∀ t : ℝ, t ∈ Set.Ioo l u → 0 < f (x - t)) :
    0 < conv (centeredExp a) f x := by
  have hqa := q_formula a ha_ne
  have hconv := conv_welldef (centeredExp a) f M
    hqa.2.2.1 hf_meas (fun t => (hqa.2.2.2.1 t).1)
    (fun t => ⟨hf_nonneg t, hf_bound t⟩) hqa.2.2.2.2.1 hf_int
  have hnonneg : ∀ t : ℝ, 0 ≤ centeredExp a t * f (x - t) := by
    intro t
    exact mul_nonneg (hqa.2.2.2.1 t).1 (hf_nonneg (x - t))
  have hsupport_pos :
      0 < volume (Function.support fun t : ℝ => centeredExp a t * f (x - t)) := by
    have hsubset : Set.Ioo l u ⊆
        Function.support (fun t : ℝ => centeredExp a t * f (x - t)) := by
      intro t ht
      exact ne_of_gt (mul_pos (ha_pos t ht) (hf_pos t ht))
    have hvol : 0 < volume (Set.Ioo l u) :=
      (Measure.measure_Ioo_pos (μ := volume)).mpr hlu
    exact lt_of_lt_of_le hvol (measure_mono hsubset)
  have hpos := (integral_pos_iff_support_of_nonneg hnonneg (hconv.1 x)).2 hsupport_pos
  simpa [conv] using hpos


theorem rm_pos (m : ℕ) (β : Fin m → ℝ)
    (hm : 2 ≤ m) (hβ : ∀ j, β j ≠ 0) :
  PositivityTrichotomy (rightNestedCentered m β) := by
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              have hr2 := r2_pos β hβ
              rcases lt_or_gt_of_ne (hβ 0) with h0neg | h0pos
              · rcases lt_or_gt_of_ne (hβ 1) with h1neg | h1pos
                · exact Or.inr (Or.inl ⟨-β 0 - β 1, hr2.2.1 ⟨h0neg, h1neg⟩⟩)
                · exact Or.inr (Or.inr (hr2.2.2 (Or.inr ⟨h0neg, h1pos⟩)))
              · rcases lt_or_gt_of_ne (hβ 1) with h1neg | h1pos
                · exact Or.inr (Or.inr (hr2.2.2 (Or.inl ⟨h0pos, h1neg⟩)))
                · exact Or.inl ⟨-β 0 - β 1, hr2.1 ⟨h0pos, h1pos⟩⟩
          | succ k =>
              let βtail : Fin (Nat.succ (Nat.succ k)) → ℝ := fun i => β i.succ
              have htail_ne : ∀ j, βtail j ≠ 0 := by
                intro j
                exact hβ j.succ
              have htail_tri :
                  PositivityTrichotomy
                    (rightNestedCentered (Nat.succ (Nat.succ k)) βtail) := by
                exact ih βtail (by omega) htail_ne
              have htail_basic := rm_basic (Nat.succ k) βtail htail_ne
              rcases htail_basic.2.2.1 with ⟨M, hM⟩
              have hconv_pos : ∀ x l u : ℝ, l < u →
                  (∀ t : ℝ, t ∈ Set.Ioo l u → 0 < centeredExp (β 0) t) →
                  (∀ t : ℝ, t ∈ Set.Ioo l u →
                    0 < rightNestedCentered (Nat.succ (Nat.succ k)) βtail (x - t)) →
                  0 < rightNestedCentered (Nat.succ (Nat.succ (Nat.succ k))) β x := by
                intro x l u hlu hqpos htailpos
                have h := centeredExp_conv_tail_pos_of_interval (β 0) x l u
                  (rightNestedCentered (Nat.succ (Nat.succ k)) βtail) M
                  (hβ 0) htail_basic.1 htail_basic.2.1 hM htail_basic.2.2.2.1
                  hlu hqpos htailpos
                simpa [rightNestedCentered, βtail] using h
              rcases lt_or_gt_of_ne (hβ 0) with h0neg | h0pos
              · rcases q_window (β 0) (hβ 0) with ⟨_, _, _, _, hw⟩
                have hq_left := (hw.2 h0neg).2
                rcases htail_tri with ⟨u, htail_right⟩ | ⟨u, htail_left⟩ | htail_all
                · refine Or.inr (Or.inr ?_)
                  intro x
                  let T : ℝ := min (-β 0) (x - u)
                  have hTβ : T ≤ -β 0 := by
                    dsimp [T]
                    exact min_le_left (-β 0) (x - u)
                  have hTxu : T ≤ x - u := by
                    dsimp [T]
                    exact min_le_right (-β 0) (x - u)
                  exact hconv_pos x (T - 1) T (by linarith)
                    (fun t ht => hq_left t (by linarith [ht.2, hTβ]))
                    (fun t ht => htail_right (x - t) (by linarith [ht.2, hTxu]))
                · refine Or.inr (Or.inl ?_)
                  refine ⟨u - β 0, ?_⟩
                  intro x hx
                  exact hconv_pos x (x - u) (-β 0) (by linarith)
                    (fun t ht => hq_left t (by linarith [ht.2]))
                    (fun t ht => htail_left (x - t) (by linarith [ht.1]))
                · refine Or.inr (Or.inr ?_)
                  intro x
                  exact hconv_pos x (-β 0 - 1) (-β 0) (by linarith)
                    (fun t ht => hq_left t (by linarith [ht.2]))
                    (fun t ht => htail_all (x - t))
              · rcases q_window (β 0) (hβ 0) with ⟨_, _, _, _, hw⟩
                have hq_right := (hw.1 h0pos).2
                rcases htail_tri with ⟨u, htail_right⟩ | ⟨u, htail_left⟩ | htail_all
                · refine Or.inl ?_
                  refine ⟨u - β 0, ?_⟩
                  intro x hx
                  exact hconv_pos x (-β 0) (x - u) (by linarith)
                    (fun t ht => hq_right t (by linarith [ht.1]))
                    (fun t ht => htail_right (x - t) (by linarith [ht.2]))
                · refine Or.inr (Or.inr ?_)
                  intro x
                  let T : ℝ := max (-β 0) (x - u)
                  have hTβ : -β 0 ≤ T := by
                    dsimp [T]
                    exact le_max_left (-β 0) (x - u)
                  have hTxu : x - u ≤ T := by
                    dsimp [T]
                    exact le_max_right (-β 0) (x - u)
                  exact hconv_pos x T (T + 1) (by linarith)
                    (fun t ht => hq_right t (by linarith [ht.1, hTβ]))
                    (fun t ht => htail_left (x - t) (by linarith [ht.1, hTxu]))
                · refine Or.inr (Or.inr ?_)
                  intro x
                  exact hconv_pos x (-β 0) (-β 0 + 1) (by linarith)
                    (fun t ht => hq_right t (by linarith [ht.1]))
                    (fun t ht => htail_all (x - t))


theorem untranslate (m : ℕ) (β : Fin (m + 1) → ℝ)
    (hβ : ∀ j, β j ≠ 0) :
  ∃ (a : Fin (m + 1) → ℝ) (A : ℝ),
    (∀ j, a j ≠ 0) ∧
      ∀ x : ℝ, rightNestedCentered (m + 1) β x = finiteType m a (x + A) := by
  induction m with
  | zero =>
      let a : Fin 1 → ℝ := fun j => 1 / β j
      refine ⟨a, β 0, ?_, ?_⟩
      · intro j
        dsimp [a]
        exact one_div_ne_zero (hβ j)
      · intro x
        simp [rightNestedCentered, finiteType, centeredExp, a]
  | succ n ih =>
      let βtail : Fin (n + 1) → ℝ := fun i => β i.succ
      have hβtail : ∀ j, βtail j ≠ 0 := by
        intro j
        exact hβ j.succ
      rcases ih βtail hβtail with ⟨atail, Atail, hatail, htail⟩
      let a : Fin (n + 2) → ℝ := fun j => Fin.cases (1 / β 0) atail j
      refine ⟨a, β 0 + Atail, ?_, ?_⟩
      · intro j
        cases j using Fin.cases with
        | zero =>
            dsimp [a]
            exact one_div_ne_zero (hβ 0)
        | succ j =>
            dsimp [a]
            exact hatail j
      · intro x
        have hcenter : centeredExp (β 0) = translate (-(β 0)) (expKernel (1 / β 0)) := by
          funext t
          unfold centeredExp translate
          congr 1
          ring
        have htail_fun :
            rightNestedCentered (n + 1) βtail = translate (-Atail) (finiteType n atail) := by
          funext y
          unfold translate
          rw [htail y]
          congr 1
          ring
        calc
          rightNestedCentered (n + 2) β x =
              conv (centeredExp (β 0)) (rightNestedCentered (n + 1) βtail) x := by
            rfl
          _ = conv (translate (-(β 0)) (expKernel (1 / β 0)))
              (translate (-Atail) (finiteType n atail)) x := by
            rw [hcenter, htail_fun]
          _ = conv (expKernel (1 / β 0)) (translate (-Atail) (finiteType n atail))
              (x - (-(β 0))) := by
            exact transl_left
              (expKernel (1 / β 0)) (translate (-Atail) (finiteType n atail)) (-(β 0)) x
          _ = conv (expKernel (1 / β 0)) (finiteType n atail)
              ((x - (-(β 0))) - (-Atail)) := by
            exact transl_right
              (expKernel (1 / β 0)) (finiteType n atail) (-Atail) (x - (-(β 0)))
          _ = finiteType (n + 1) a (x + (β 0 + Atail)) := by
            change conv (expKernel (1 / β 0)) (finiteType n atail)
                ((x - (-(β 0))) - (-Atail)) =
              conv (expKernel (1 / β 0)) (finiteType n atail) (x + (β 0 + Atail))
            congr 1
            ring

end

end Part8
