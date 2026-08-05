import LeanCode.Vendor.E5.P7.Part7.Basic
import LeanCode.Vendor.E5.P7.Part7.Laplace
import LeanCode.Vendor.E5.Defs



namespace Part7


theorem psi_coeff_bound (β : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (hconv : Summable (fun m : ℕ => (β m / m.factorial) * (2 * r) ^ m)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, |β m| / (m.factorial : ℝ) * (2 * r) ^ m ≤ A := by
  have habs : Summable (fun m : ℕ => |(β m / m.factorial) * (2 * r) ^ m|) :=
    summable_abs_iff.mpr hconv
  refine ⟨∑' m, |(β m / m.factorial) * (2 * r) ^ m|, tsum_nonneg (fun m => abs_nonneg _), ?_⟩
  intro m
  have h1 : |(β m / m.factorial) * (2 * r) ^ m|
      = |β m| / (m.factorial : ℝ) * (2 * r) ^ m := by
    rw [abs_mul, abs_div, abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ (m.factorial : ℝ) by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ 2 * r by positivity)]
  rw [← h1]
  exact habs.le_tsum m (fun k _ => abs_nonneg _)


theorem psi_norm_summable (β : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (hconv : Summable (fun m : ℕ => (β m / m.factorial) * (2 * r) ^ m))
    (s : ℂ) (hs : ‖s‖ ≤ r) :
    Summable (fun m : ℕ => ‖((β m / m.factorial : ℝ) : ℂ) * s ^ m‖) := by
  obtain ⟨A, hA0, hA⟩ := psi_coeff_bound β r hr hconv
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) ?_
    ((summable_geometric_of_lt_one (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)).mul_left A)
  intro m
  have hcoeff : ‖((β m / m.factorial : ℝ) : ℂ)‖ = |β m| / (m.factorial : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ (m.factorial : ℝ) by positivity)]
  rw [norm_mul, norm_pow, hcoeff]
  have hb : |β m| / (m.factorial : ℝ) * (2 * r) ^ m ≤ A := hA m
  have hsr : ‖s‖ ^ m ≤ r ^ m := pow_le_pow_left₀ (norm_nonneg s) hs m
  calc |β m| / (m.factorial : ℝ) * ‖s‖ ^ m
      ≤ |β m| / (m.factorial : ℝ) * r ^ m :=
        mul_le_mul_of_nonneg_left hsr (by positivity)
    _ ≤ A * ((1 : ℝ) / 2) ^ m := by
        rw [div_pow, one_pow, mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)]
        have hthis : |β m| / (m.factorial : ℝ) * r ^ m * 2 ^ m
            = |β m| / (m.factorial : ℝ) * (2 * r) ^ m := by rw [mul_pow]; ring
        rw [hthis]; exact hb


theorem psi_entire (β : ℕ → ℝ)
    (hconv : ∀ s : ℂ, Summable (fun m : ℕ => ((β m / m.factorial : ℝ) : ℂ) * s ^ m)) :
    AnalyticOnNhd ℂ (Psi β) Set.univ := by

  have hsummable_real : ∀ ρ : ℝ, Summable (fun m : ℕ => (β m / m.factorial) * ρ ^ m) := by
    intro ρ
    have h := hconv (ρ : ℂ)
    have heq : (fun m : ℕ => ((β m / m.factorial : ℝ) : ℂ) * (ρ : ℂ) ^ m)
        = (fun m : ℕ => (((β m / m.factorial) * ρ ^ m : ℝ) : ℂ)) := by
      funext m; push_cast; ring
    rw [heq] at h
    exact Complex.summable_ofReal.mp h

  have hnormsum : ∀ ρ : ℝ, 0 ≤ ρ →
      Summable (fun n : ℕ => ‖((β n / n.factorial : ℝ) : ℂ)‖ * ρ ^ n) := by
    intro ρ hρ
    have hR : (0 : ℝ) < ρ + 1 := by linarith
    have hconv2 : Summable (fun m : ℕ => (β m / m.factorial) * (2 * (ρ + 1)) ^ m) :=
      hsummable_real (2 * (ρ + 1))
    have hs : ‖(ρ : ℂ)‖ ≤ ρ + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]; linarith
    have hpns := psi_norm_summable β (ρ + 1) hR hconv2 (ρ : ℂ) hs
    have heq : (fun m : ℕ => ‖((β m / m.factorial : ℝ) : ℂ) * (ρ : ℂ) ^ m‖)
        = (fun n : ℕ => ‖((β n / n.factorial : ℝ) : ℂ)‖ * ρ ^ n) := by
      funext m
      rw [norm_mul, norm_pow]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]
    rw [heq] at hpns
    exact hpns

  set p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun m => ((β m / m.factorial : ℝ) : ℂ)) with hp_def
  have hrad : p.radius = ⊤ := by
    apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
    intro r'
    have hsum := hnormsum (r' : ℝ) r'.coe_nonneg
    simpa only [hp_def, FormalMultilinearSeries.ofScalars_norm] using hsum
  have hball : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by simp [hrad])
  have hpsum : p.sum = fun x : ℂ => ∑' n : ℕ, ((β n / n.factorial : ℝ) : ℂ) • x ^ n := by
    rw [hp_def]
    exact FormalMultilinearSeries.ofScalarsSum_eq_tsum (fun m => ((β m / m.factorial : ℝ) : ℂ))
  have hfun : Psi β = p.sum := by
    rw [hpsum]; funext x; simp only [Psi, smul_eq_mul]
  have hsub : Set.univ ⊆ Metric.eball (0 : ℂ) p.radius := by
    intro x _
    rw [Metric.mem_eball, hrad]
    exact edist_lt_top x 0
  rw [hfun]
  exact (hball.analyticOnNhd).mono hsub


theorem cauchy (u v : ℕ → ℂ)
    (hu : Summable (fun i => ‖u i‖)) (hv : Summable (fun j => ‖v j‖)) :
    Summable (fun k : ℕ => ‖∑ i ∈ Finset.range (k + 1), u i * v (k - i)‖) ∧
    (∑' i, u i) * (∑' j, v j)
      = ∑' k : ℕ, ∑ i ∈ Finset.range (k + 1), u i * v (k - i) :=
  ⟨summable_norm_sum_mul_range_of_summable_norm hu hv,
   tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hu hv⟩


theorem coeff_identity (μ β : ℕ → ℝ)
    (h0 : μ 0 * β 0 = 1)
    (hrec : ∀ m : ℕ, 0 < m →
      (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (-1) ^ i * μ i * β (m - i)) = 0)
    (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
      ((-1 : ℝ) ^ i * μ i / (i.factorial : ℝ)) * (β (k - i) / ((k - i).factorial : ℝ)))
      = if k = 0 then 1 else 0 := by
  have key : (∑ i ∈ Finset.range (k + 1),
      ((-1 : ℝ) ^ i * μ i / (i.factorial : ℝ)) * (β (k - i) / ((k - i).factorial : ℝ)))
      = (1 / (k.factorial : ℝ)) * ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * (-1) ^ i * μ i * β (k - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    have hcmf : (k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ)
        = (k.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have hi0 : (i.factorial : ℝ) ≠ 0 := by positivity
    have hki0 : ((k - i).factorial : ℝ) ≠ 0 := by positivity
    have hk0 : (k.factorial : ℝ) ≠ 0 := by positivity
    have hchoose : (k.choose i : ℝ)
        = (k.factorial : ℝ) / ((i.factorial : ℝ) * ((k - i).factorial : ℝ)) := by
      rw [eq_div_iff (by positivity)]; linear_combination hcmf
    rw [hchoose]; field_simp
  rw [key]
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl, Finset.sum_range_one]
    simp only [Nat.choose_self, Nat.factorial_zero, Nat.cast_one, pow_zero, Nat.sub_self,
      one_mul, mul_one, div_one]
    linarith [h0]
  · rw [if_neg hk, hrec k (Nat.pos_of_ne_zero hk), mul_zero]



private theorem conv_real (β : ℕ → ℝ)
    (hconv : ∀ s : ℂ, Summable (fun m : ℕ => ((β m / m.factorial : ℝ) : ℂ) * s ^ m)) :
    ∀ ρ : ℝ, Summable (fun m : ℕ => (β m / m.factorial) * ρ ^ m) := by
  intro ρ
  have h := hconv (ρ : ℂ)
  have heq : (fun m : ℕ => ((β m / m.factorial : ℝ) : ℂ) * (ρ : ℂ) ^ m)
      = (fun m : ℕ => (((β m / m.factorial) * ρ ^ m : ℝ) : ℂ)) := by
    funext m; push_cast; ring
  rw [heq] at h
  exact Complex.summable_ofReal.mp h


theorem FPsi_disk (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg : Continuous g) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (β : ℕ → ℝ) (hβ : MomentReciprocal g β)
    (hconv : ∀ s : ℂ, Summable (fun m : ℕ => ((β m / m.factorial : ℝ) : ℂ) * s ^ m))
    (s : ℂ) (hs : ‖s‖ < c) :
    F g s * Psi β s = 1 := by
  set u : ℕ → ℂ := fun m => (-1 : ℂ) ^ m * (mom g m : ℂ) / (m.factorial : ℂ) * s ^ m with hu_def
  set v : ℕ → ℂ := fun m => ((β m / m.factorial : ℝ) : ℂ) * s ^ m with hv_def
  have htaylor := taylor g C c hC hc hg hbound s hs
  have hu_norm : Summable (fun i => ‖u i‖) := htaylor.1
  have hv_norm : Summable (fun j => ‖v j‖) :=
    psi_norm_summable β (‖s‖ + 1) (by positivity) (conv_real β hconv (2 * (‖s‖ + 1))) s (by linarith)
  have hu_sum : (∑' i, u i) = F g s := htaylor.2.2.symm
  have hv_sum : (∑' j, v j) = Psi β s := rfl
  have hinner : ∀ k, (∑ i ∈ Finset.range (k + 1), u i * v (k - i))
      = if k = 0 then (1 : ℂ) else 0 := by
    intro k
    have hstep : (∑ i ∈ Finset.range (k + 1), u i * v (k - i))
        = ((∑ i ∈ Finset.range (k + 1),
            ((-1 : ℝ) ^ i * mom g i / (i.factorial : ℝ)) *
              (β (k - i) / ((k - i).factorial : ℝ)) : ℝ) : ℂ) * s ^ k := by
      rw [Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      have hpow : s ^ i * s ^ (k - i) = s ^ k := by
        rw [← pow_add, add_tsub_cancel_of_le hi]
      simp only [hu_def, hv_def]
      rw [mul_mul_mul_comm, hpow]
      push_cast; ring
    rw [hstep, coeff_identity (mom g) β hβ.1 hβ.2 k]
    split_ifs with hk
    · subst hk; simp
    · simp
  have hcauchy := cauchy u v hu_norm hv_norm
  have hprod := hcauchy.2
  rw [hu_sum, hv_sum] at hprod
  rw [hprod]
  simp_rw [hinner]
  rw [tsum_eq_single 0 (fun k hk => if_neg hk), if_pos rfl]


theorem FPsi_strip (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg : Continuous g) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (β : ℕ → ℝ) (hβ : MomentReciprocal g β)
    (hconv : ∀ s : ℂ, Summable (fun m : ℕ => ((β m / m.factorial : ℝ) : ℂ) * s ^ m))
    (s : ℂ) (hs : s ∈ strip c) :
    F g s * Psi β s = 1 := by
  have hFanal : AnalyticOnNhd ℂ (F g) (strip c) := (F_analytic g C c hC hc hg hbound).2
  have hPsianal : AnalyticOnNhd ℂ (Psi β) (strip c) :=
    (psi_entire β hconv).mono (Set.subset_univ _)
  have hf : AnalyticOnNhd ℂ (fun z => F g z * Psi β z) (strip c) := hFanal.mul hPsianal
  have hg1 : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) (strip c) := analyticOnNhd_const
  have h0 : (0 : ℂ) ∈ strip c := by
    show |(0 : ℂ).re| < c; simp only [Complex.zero_re, abs_zero]; exact hc
  have hfg : (fun z => F g z * Psi β z) =ᶠ[nhds 0] (fun _ => (1 : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hc] with z hz
    have hzc : ‖z‖ < c := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hz
    exact FPsi_disk g C c hC hc hg hbound β hβ hconv z hzc
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg1 (strip_conn c) h0 hfg hs


theorem F_nonzero (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg : Continuous g) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (β : ℕ → ℝ) (hβ : MomentReciprocal g β)
    (hconv : ∀ s : ℂ, Summable (fun m : ℕ => ((β m / m.factorial : ℝ) : ℂ) * s ^ m))
    (s : ℂ) (hs : s ∈ strip c) :
    F g s ≠ 0 ∧ Psi β s ≠ 0 ∧ F g s = (Psi β s)⁻¹ := by
  have h1 : F g s * Psi β s = 1 := FPsi_strip g C c hC hc hg hbound β hβ hconv s hs
  have hFne : F g s ≠ 0 := by
    intro h; rw [h, zero_mul] at h1; exact one_ne_zero h1.symm
  have hPne : Psi β s ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact one_ne_zero h1.symm
  refine ⟨hFne, hPne, ?_⟩
  rw [← one_mul (Psi β s)⁻¹, ← h1, mul_assoc, mul_inv_cancel₀ hPne, mul_one]

end Part7
