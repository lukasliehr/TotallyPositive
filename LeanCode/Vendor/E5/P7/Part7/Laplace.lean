import LeanCode.Vendor.E5.P7.Part7.Basic
import LeanCode.Vendor.E5.Defs

open MeasureTheory



namespace Part7

private lemma strip_eq (c : ℝ) :
    strip c = {s : ℂ | s.re < c} ∩ {s : ℂ | -c < s.re} := by
  ext s
  simp only [strip, Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
  tauto


theorem strip_open (c : ℝ) : IsOpen (strip c) := by
  rw [strip_eq]
  exact (isOpen_lt Complex.continuous_re continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_re)


theorem strip_conn (c : ℝ) : IsPreconnected (strip c) := by
  have hconv : Convex ℝ (strip c) := by
    rw [strip_eq]
    exact (convex_halfSpace_re_lt c).inter (convex_halfSpace_re_gt (-c))
  exact hconv.isPreconnected


theorem F_defined (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg : Continuous g) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (s : ℂ) (hs : s ∈ strip c) :
    Integrable (fun x : ℝ => Complex.exp (-s * x) * g x) ∧
    ‖F g s‖ ≤ 2 * C / (c - |s.re|) := by
  have hσ : |s.re| < c := hs
  have ha : (0 : ℝ) < c - |s.re| := by linarith
  set a := c - |s.re| with ha_def
  have hpt : ∀ x : ℝ, ‖Complex.exp (-s * (x : ℂ)) * (g x : ℂ)‖ ≤ C * Real.exp (-a * |x|) := by
    intro x
    rw [norm_mul, Complex.norm_exp]
    have hre : (-s * (x : ℂ)).re = -(s.re * x) := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
    rw [hre]
    have hgnorm : ‖(g x : ℂ)‖ = |g x| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hgnorm]
    have h1 : Real.exp (-(s.re * x)) ≤ Real.exp (|s.re| * |x|) := by
      apply Real.exp_le_exp.mpr
      calc -(s.re * x) ≤ |s.re * x| := neg_le_abs _
        _ = |s.re| * |x| := abs_mul _ _
    calc Real.exp (-(s.re * x)) * |g x|
        ≤ Real.exp (|s.re| * |x|) * (C * Real.exp (-c * |x|)) :=
          mul_le_mul h1 (hbound x) (abs_nonneg _) (Real.exp_nonneg _)
      _ = C * Real.exp (-a * |x|) := by
          rw [ha_def, show -(c - |s.re|) * |x| = |s.re| * |x| + -c * |x| from by ring,
            Real.exp_add]
          ring
  have hDom : Integrable (fun x : ℝ => C * Real.exp (-a * |x|)) :=
    ((exp_abs_int a ha).1).const_mul C
  have hcont : Continuous (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (g x : ℂ)) := by fun_prop
  have hInt : Integrable (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (g x : ℂ)) := by
    apply Integrable.mono' hDom hcont.aestronglyMeasurable
    filter_upwards with x using hpt x
  refine ⟨hInt, ?_⟩
  have hF : F g s = ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * (g x : ℂ) := rfl
  rw [hF]
  calc ‖∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * (g x : ℂ)‖
      ≤ ∫ x : ℝ, ‖Complex.exp (-s * (x : ℂ)) * (g x : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, C * Real.exp (-a * |x|) := integral_mono hInt.norm hDom hpt
    _ = C * (2 / a) := by rw [integral_const_mul, (exp_abs_int a ha).2]
    _ = 2 * C / a := by ring


theorem FT_eq_F (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg : Continuous g) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)) (ξ : ℝ) :
    (2 * Real.pi * Complex.I * ξ) ∈ strip c ∧
    FT g ξ = F g (2 * Real.pi * Complex.I * ξ) := by
  have hre0 : (2 * Real.pi * Complex.I * (ξ : ℂ)).re = 0 := by
    rw [show (2 * Real.pi * Complex.I * (ξ : ℂ)) = ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
    simp [Complex.mul_re, Complex.mul_im]
  refine ⟨?_, ?_⟩
  · simp only [strip, Set.mem_setOf_eq, hre0, abs_zero]; exact hc
  · unfold FT F
    congr 1
    funext x
    congr 2
    ring


theorem F_analytic (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg : Continuous g) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)) :
    (∀ s ∈ strip c,
      HasDerivAt (F g) (∫ x : ℝ, (-(x : ℂ)) * Complex.exp (-s * x) * g x) s) ∧
    AnalyticOnNhd ℂ (F g) (strip c) := by
  have hcontF : ∀ s : ℂ, Continuous (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (g x : ℂ)) := by
    intro s; fun_prop
  have hcontF' : ∀ s : ℂ,
      Continuous (fun x : ℝ => (-(x : ℂ)) * Complex.exp (-s * (x : ℂ)) * (g x : ℂ)) := by
    intro s; fun_prop
  have key : ∀ s₀ ∈ strip c,
      HasDerivAt (F g) (∫ x : ℝ, (-(x : ℂ)) * Complex.exp (-s₀ * x) * g x) s₀ := by
    intro s₀ hs₀
    have hσ : |s₀.re| < c := hs₀
    set ε := (c - |s₀.re|) / 2 with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    have hballnhds : Metric.ball s₀ ε ∈ nhds s₀ := Metric.ball_mem_nhds s₀ hε
    have hF_meas : ∀ᶠ s in nhds s₀,
        AEStronglyMeasurable (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (g x : ℂ))
          (volume : Measure ℝ) :=
      Filter.Eventually.of_forall (fun s => (hcontF s).aestronglyMeasurable)
    have hF_int : Integrable (fun x : ℝ => Complex.exp (-s₀ * (x : ℂ)) * (g x : ℂ)) :=
      (F_defined g C c hC hc hg hbound s₀ hs₀).1
    have hF'_meas : AEStronglyMeasurable
        (fun x : ℝ => (-(x : ℂ)) * Complex.exp (-s₀ * (x : ℂ)) * (g x : ℂ)) (volume : Measure ℝ) :=
      (hcontF' s₀).aestronglyMeasurable
    have hbnd_int : Integrable (fun x : ℝ => C * (|x| ^ 1 * Real.exp (-ε * |x|))) :=
      ((poly_exp_int ε hε 1).1).const_mul C
    have h_bound : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), ∀ s ∈ Metric.ball s₀ ε,
        ‖(-(x : ℂ)) * Complex.exp (-s * (x : ℂ)) * (g x : ℂ)‖
          ≤ C * (|x| ^ 1 * Real.exp (-ε * |x|)) := by
      apply Filter.Eventually.of_forall
      intro x s hsb
      have hsre : |s.re| ≤ c - ε := by
        have hd : ‖s - s₀‖ < ε := by
          have h := Metric.mem_ball.mp hsb; rwa [dist_eq_norm] at h
        have hre2 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
          have hh : (s - s₀).re = s.re - s₀.re := by simp
          rw [← hh]; exact Complex.abs_re_le_norm _
        have h3 : |s.re| - |s₀.re| ≤ |s.re - s₀.re| := abs_sub_abs_le_abs_sub _ _
        rw [hε_def]; linarith
      rw [norm_mul, norm_mul, Complex.norm_exp]
      have hre : (-s * (x : ℂ)).re = -(s.re * x) := by
        simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
      rw [hre]
      have hnx : ‖(-(x : ℂ))‖ = |x| := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
      have hgn : ‖(g x : ℂ)‖ = |g x| := by rw [Complex.norm_real, Real.norm_eq_abs]
      rw [hnx, hgn]
      have hle1 : Real.exp (-(s.re * x)) ≤ Real.exp ((c - ε) * |x|) := by
        apply Real.exp_le_exp.mpr
        calc -(s.re * x) ≤ |s.re * x| := neg_le_abs _
          _ = |s.re| * |x| := abs_mul _ _
          _ ≤ (c - ε) * |x| := mul_le_mul_of_nonneg_right hsre (abs_nonneg _)
      calc |x| * Real.exp (-(s.re * x)) * |g x|
          ≤ |x| * Real.exp ((c - ε) * |x|) * (C * Real.exp (-c * |x|)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hle1 (abs_nonneg _)) (hbound x)
              (abs_nonneg _) (by positivity)
        _ = C * (|x| ^ 1 * Real.exp (-ε * |x|)) := by
            rw [pow_one, show -ε * |x| = (c - ε) * |x| + -c * |x| from by ring, Real.exp_add]
            ring
    have h_diff : ∀ᵐ (x : ℝ) ∂(volume : Measure ℝ), ∀ s ∈ Metric.ball s₀ ε,
        HasDerivAt (fun s => Complex.exp (-s * (x : ℂ)) * (g x : ℂ))
          ((-(x : ℂ)) * Complex.exp (-s * (x : ℂ)) * (g x : ℂ)) s := by
      apply Filter.Eventually.of_forall
      intro x s _
      have hu : HasDerivAt (fun s : ℂ => -s * (x : ℂ)) (-(x : ℂ)) s := by
        simpa using ((hasDerivAt_id s).neg.mul_const (x : ℂ))
      have hd := hu.cexp.mul_const (g x : ℂ)
      have heqd : Complex.exp (-s * (x : ℂ)) * (-(x : ℂ)) * (g x : ℂ)
          = (-(x : ℂ)) * Complex.exp (-s * (x : ℂ)) * (g x : ℂ) := by ring
      rw [heqd] at hd
      exact hd
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s x => Complex.exp (-s * (x : ℂ)) * (g x : ℂ))
      (F' := fun s x => (-(x : ℂ)) * Complex.exp (-s * (x : ℂ)) * (g x : ℂ))
      (bound := fun x => C * (|x| ^ 1 * Real.exp (-ε * |x|)))
      hballnhds hF_meas hF_int hF'_meas h_bound hbnd_int h_diff
    exact hmain.2
  refine ⟨key, ?_⟩
  apply DifferentiableOn.analyticOnNhd _ (strip_open c)
  intro s₀ hs₀
  exact ((key s₀ hs₀).differentiableAt).differentiableWithinAt


theorem taylor (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg : Continuous g) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (s : ℂ) (hs : ‖s‖ < c) :
    Summable (fun m : ℕ => ‖((-1 : ℂ)) ^ m * (mom g m : ℂ) / (m.factorial : ℂ) * s ^ m‖) ∧
    (∑' m : ℕ, ‖((-1 : ℂ)) ^ m * (mom g m : ℂ) / (m.factorial : ℂ) * s ^ m‖)
      ≤ 2 * C / (c - ‖s‖) ∧
    F g s = ∑' m : ℕ, ((-1 : ℂ)) ^ m * (mom g m : ℂ) / (m.factorial : ℂ) * s ^ m := by
  have ha : (0 : ℝ) < c - ‖s‖ := by linarith
  set Fam : ℕ → ℝ → ℂ := fun m x => (-s * (x : ℂ)) ^ m / (m.factorial : ℂ) * (g x : ℂ)
    with hFam_def
  have h1n : ∀ x : ℝ, ‖(-s * (x : ℂ))‖ = ‖s‖ * |x| := by
    intro x; rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hFnorm : ∀ m x, ‖Fam m x‖ = (‖s‖ * |x|) ^ m / (m.factorial : ℝ) * |g x| := by
    intro m x
    simp only [hFam_def]
    rw [norm_mul, norm_div, norm_pow, h1n, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs]
  have hFcont : ∀ m, Continuous (Fam m) := by intro m; simp only [hFam_def]; fun_prop
  have hFameq : ∀ m x, Fam m x = ((-s) ^ m / (m.factorial : ℂ)) * ((x ^ m * g x : ℝ) : ℂ) := by
    intro m x; simp only [hFam_def]; push_cast; ring
  have hFint : ∀ m, Integrable (Fam m) := by
    intro m
    have h1 : Integrable (fun x => ((x ^ m * g x : ℝ) : ℂ)) :=
      ((moment_int g C c hC hc hg hbound m).1).ofReal
    have h2 := h1.const_mul ((-s) ^ m / (m.factorial : ℂ))
    simpa only [← hFameq] using h2
  have hP2 : ∀ m, (∫ x, Fam m x)
      = (-1 : ℂ) ^ m * (mom g m : ℂ) / (m.factorial : ℂ) * s ^ m := by
    intro m
    have hint_eq : (∫ x, Fam m x)
        = ((-s) ^ m / (m.factorial : ℂ)) * ∫ x, ((x ^ m * g x : ℝ) : ℂ) := by
      simp_rw [hFameq]; rw [integral_const_mul]
    rw [hint_eq, integral_complex_ofReal, show (∫ x, x ^ m * g x) = mom g m from rfl]
    have hns : (-s) ^ m = (-1 : ℂ) ^ m * s ^ m := by rw [← neg_one_mul, mul_pow]
    rw [hns]; ring
  have hP3 : ∀ x, HasSum (fun m => Fam m x) (Complex.exp (-s * (x : ℂ)) * (g x : ℂ)) := by
    intro x
    have hz : Summable (fun m => (-s * (x : ℂ)) ^ m / (m.factorial : ℂ)) :=
      (exp_series (-s * (x : ℂ))).1.of_norm
    have hexp_sum : HasSum (fun m => (-s * (x : ℂ)) ^ m / (m.factorial : ℂ))
        (Complex.exp (-s * (x : ℂ))) := by
      rw [← (exp_series (-s * (x : ℂ))).2.2]; exact hz.hasSum
    simpa only [hFam_def] using hexp_sum.mul_right (g x : ℂ)

  have hbound_pt : ∀ m x, ‖‖Fam m x‖‖
      ≤ (‖s‖ * |x|) ^ m / (m.factorial : ℝ) * (C * Real.exp (-c * |x|)) := by
    intro m x
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hFnorm]
    exact mul_le_mul_of_nonneg_left (hbound x) (by positivity)
  have hdom_int : Integrable (fun x => Real.exp (‖s‖ * |x|) * (C * Real.exp (-c * |x|))) := by
    have heq : (fun x => Real.exp (‖s‖ * |x|) * (C * Real.exp (-c * |x|)))
        = (fun x => C * Real.exp (-(c - ‖s‖) * |x|)) := by
      funext x
      rw [show -(c - ‖s‖) * |x| = ‖s‖ * |x| + -c * |x| from by ring, Real.exp_add]; ring
    rw [heq]; exact ((exp_abs_int (c - ‖s‖) ha).1).const_mul C
  have hEnv : HasSum (fun m => ∫ x, ‖Fam m x‖) (∫ x, Real.exp (‖s‖ * |x|) * |g x|) := by
    apply hasSum_integral_of_dominated_convergence
      (bound := fun m x => (‖s‖ * |x|) ^ m / (m.factorial : ℝ) * (C * Real.exp (-c * |x|)))
    · exact fun m => ((hFcont m).norm).aestronglyMeasurable
    · exact fun m => Filter.Eventually.of_forall (fun x => hbound_pt m x)
    · refine Filter.Eventually.of_forall (fun x => ?_)
      exact (Real.summable_pow_div_factorial (‖s‖ * |x|)).mul_right _
    · have heq : (fun x => ∑' m, (‖s‖ * |x|) ^ m / (m.factorial : ℝ) * (C * Real.exp (-c * |x|)))
          = (fun x => Real.exp (‖s‖ * |x|) * (C * Real.exp (-c * |x|))) := by
        funext x
        rw [tsum_mul_right]
        congr 1
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      rw [heq]; exact hdom_int
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hsum := (Real.summable_pow_div_factorial (‖s‖ * |x|)).hasSum
      have hexp : ∑' m, (‖s‖ * |x|) ^ m / (m.factorial : ℝ) = Real.exp (‖s‖ * |x|) := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      rw [hexp] at hsum
      simpa only [← hFnorm] using hsum.mul_right |g x|
  have hP4summable : Summable (fun m => ∫ x, ‖Fam m x‖) := hEnv.summable
  have hP4bound : ∑' m, (∫ x, ‖Fam m x‖) ≤ 2 * C / (c - ‖s‖) := by
    rw [hEnv.tsum_eq]
    have hf_int : Integrable (fun x => Real.exp (‖s‖ * |x|) * |g x|) := by
      apply Integrable.mono' (((exp_abs_int (c - ‖s‖) ha).1).const_mul C)
        (by fun_prop : Continuous (fun x : ℝ => Real.exp (‖s‖ * |x|) * |g x|)).aestronglyMeasurable
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc Real.exp (‖s‖ * |x|) * |g x|
          ≤ Real.exp (‖s‖ * |x|) * (C * Real.exp (-c * |x|)) :=
            mul_le_mul_of_nonneg_left (hbound x) (Real.exp_nonneg _)
        _ = C * Real.exp (-(c - ‖s‖) * |x|) := by
            rw [show -(c - ‖s‖) * |x| = ‖s‖ * |x| + -c * |x| from by ring, Real.exp_add]; ring
    calc (∫ x, Real.exp (‖s‖ * |x|) * |g x|) ≤ ∫ x, C * Real.exp (-(c - ‖s‖) * |x|) := by
          apply integral_mono hf_int (((exp_abs_int (c - ‖s‖) ha).1).const_mul C)
          intro x
          calc Real.exp (‖s‖ * |x|) * |g x|
              ≤ Real.exp (‖s‖ * |x|) * (C * Real.exp (-c * |x|)) :=
                mul_le_mul_of_nonneg_left (hbound x) (Real.exp_nonneg _)
            _ = C * Real.exp (-(c - ‖s‖) * |x|) := by
                rw [show -(c - ‖s‖) * |x| = ‖s‖ * |x| + -c * |x| from by ring, Real.exp_add]; ring
      _ = 2 * C / (c - ‖s‖) := by
          rw [integral_const_mul, (exp_abs_int (c - ‖s‖) ha).2]; ring
  refine ⟨?_, ?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => by rw [← hP2 m]; exact norm_integral_le_integral_norm _) hP4summable
  · have hle : ∀ m, ‖(-1 : ℂ) ^ m * (mom g m : ℂ) / (m.factorial : ℂ) * s ^ m‖
        ≤ ∫ x, ‖Fam m x‖ :=
      fun m => by rw [← hP2 m]; exact norm_integral_le_integral_norm _
    have hsn : Summable
        (fun m => ‖(-1 : ℂ) ^ m * (mom g m : ℂ) / (m.factorial : ℂ) * s ^ m‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hle hP4summable
    exact le_trans (hsn.tsum_le_tsum hle hP4summable) hP4bound
  · have hsum := hasSum_integral_of_summable_integral_norm hFint hP4summable
    have hfx : (∫ x, ∑' m, Fam m x) = F g s := by
      have hpt : (fun x => ∑' m, Fam m x)
          = fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (g x : ℂ) := by
        funext x; exact (hP3 x).tsum_eq
      rw [hpt]; rfl
    rw [hfx] at hsum
    simp_rw [hP2] at hsum
    exact hsum.tsum_eq.symm

end Part7
