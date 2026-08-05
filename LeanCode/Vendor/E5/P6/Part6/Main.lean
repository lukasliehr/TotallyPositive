import LeanCode.Vendor.E5.P6.Part6.Basic
import LeanCode.Vendor.E5.P6.Part6.Products
import LeanCode.Vendor.E5.P6.Part6.Jensen
import LeanCode.Vendor.E5.P6.Part6.Convergence
import LeanCode.Vendor.E5.Defs

open scoped BigOperators

namespace Part6











theorem tail_expansion : ∀ (M R : ℝ) (μ : ℕ → ℝ), 0 ≤ M → 0 < R →
    (∀ j : ℕ, |μ j| ≤ Real.sqrt (M / ((j : ℝ) + 1))) →
    (∀ J : ℕ, ∑ j ∈ Finset.range J, (μ j) ^ 2 ≤ M) →
    ∀ (N J : ℕ) (z : ℂ), ‖z‖ ≤ R → 1 ≤ N → 4 * R ^ 2 * M ≤ (N : ℝ) → N < J →
      ∃ ρ : ℂ,
        (∏ j ∈ Finset.Ico N J, E ((μ j : ℂ) * z))
          = Complex.exp ((-(z ^ 2) / 2) * ((∑ j ∈ Finset.Ico N J, (μ j) ^ 2 : ℝ) : ℂ) + ρ) ∧
        ‖ρ‖ ≤ epsN R M N := by
  intro M R μ hM hR hμbound hμsum N J z hz hN hRN hNJ
  have hRpos : (0:ℝ) < R := hR
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hznn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hsqrtN_nonneg : (0:ℝ) ≤ Real.sqrt (M / (N:ℝ)) := Real.sqrt_nonneg _
  have habs_le : ∀ j : ℕ, N ≤ j → |μ j| ≤ Real.sqrt (M / (N:ℝ)) := by
    intro j hj
    refine le_trans (hμbound j) ?_
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left hM hNpos
    have : (N:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
    linarith
  have hRsqrt : R * Real.sqrt (M / (N:ℝ)) ≤ 1/2 := by
    have hMNnn : (0:ℝ) ≤ M / (N:ℝ) := div_nonneg hM (le_of_lt hNpos)
    have hsq : (R * Real.sqrt (M / (N:ℝ)))^2 = R^2 * (M / (N:ℝ)) := by
      rw [mul_pow, Real.sq_sqrt hMNnn]
    have hle14 : R^2 * (M / (N:ℝ)) ≤ 1/4 := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ hNpos]
      nlinarith [hRN]
    have hlhs_nn : (0:ℝ) ≤ R * Real.sqrt (M / (N:ℝ)) := mul_nonneg (le_of_lt hRpos) hsqrtN_nonneg
    nlinarith [hsq, hle14, hlhs_nn]
  have hsmall : ∀ j : ℕ, N ≤ j → ‖(μ j : ℂ) * z‖ ≤ 1/2 := by
    intro j hj
    rw [norm_mul, Complex.norm_real]
    calc ‖μ j‖ * ‖z‖ = |μ j| * ‖z‖ := by rw [Real.norm_eq_abs]
      _ ≤ Real.sqrt (M / (N:ℝ)) * R := by
            apply mul_le_mul (habs_le j hj) hz hznn hsqrtN_nonneg
      _ = R * Real.sqrt (M / (N:ℝ)) := by ring
      _ ≤ 1/2 := hRsqrt
  classical
  set ρ_ : ℕ → ℂ := fun j =>
    if h : ‖(μ j : ℂ) * z‖ ≤ 1/2 then (logE ((μ j : ℂ) * z) h).choose else 0 with hρ_def
  have hρspec : ∀ j : ℕ, N ≤ j →
      E ((μ j : ℂ) * z) = Complex.exp (-((μ j : ℂ) * z) ^ 2 / 2 + ρ_ j) ∧
        ‖ρ_ j‖ ≤ (3 / 2) * ‖(μ j : ℂ) * z‖ ^ 3 := by
    intro j hj
    have hs := hsmall j hj
    have hspec := (logE ((μ j : ℂ) * z) hs).choose_spec
    have hval : ρ_ j = (logE ((μ j : ℂ) * z) hs).choose := by
      rw [hρ_def]; simp only [dif_pos hs]
    rw [hval]
    exact hspec
  have hprod_eq : (∏ j ∈ Finset.Ico N J, E ((μ j : ℂ) * z))
      = ∏ j ∈ Finset.Ico N J, Complex.exp (-((μ j : ℂ) * z) ^ 2 / 2 + ρ_ j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact (hρspec j hj.1).1
  refine ⟨∑ j ∈ Finset.Ico N J, ρ_ j, ?_, ?_⟩
  · rw [hprod_eq, ← Complex.exp_sum]
    congr 1
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    ring
  · have hR3nn : (0:ℝ) ≤ R^3 := by positivity
    have hzcube : ‖z‖^3 ≤ R^3 := pow_le_pow_left₀ hznn hz 3
    have hterm : ∀ j ∈ Finset.Ico N J,
        ‖ρ_ j‖ ≤ (3/2) * R^3 * Real.sqrt (M / (N:ℝ)) * (μ j)^2 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hjN := hj.1
      refine le_trans (hρspec j hjN).2 ?_
      have hnormcube : ‖(μ j : ℂ) * z‖^3 = |μ j|^3 * ‖z‖^3 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; ring
      rw [hnormcube]
      have habsj := habs_le j hjN
      have habsnn : (0:ℝ) ≤ |μ j| := abs_nonneg _
      have hmusq : (μ j)^2 = |μ j|^2 := (sq_abs (μ j)).symm
      have hcube : |μ j|^3 ≤ Real.sqrt (M / (N:ℝ)) * |μ j|^2 := by
        nlinarith [habsj, habsnn, sq_nonneg (|μ j|)]
      rw [hmusq]
      have h1 : |μ j|^3 * ‖z‖^3 ≤ |μ j|^3 * R^3 :=
        mul_le_mul_of_nonneg_left hzcube (by positivity)
      have h2 : |μ j|^3 * R^3 ≤ (Real.sqrt (M / (N:ℝ)) * |μ j|^2) * R^3 :=
        mul_le_mul_of_nonneg_right hcube hR3nn
      nlinarith [h1, h2]
    calc ‖∑ j ∈ Finset.Ico N J, ρ_ j‖
        ≤ ∑ j ∈ Finset.Ico N J, ‖ρ_ j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Ico N J, (3/2) * R^3 * Real.sqrt (M / (N:ℝ)) * (μ j)^2 :=
            Finset.sum_le_sum hterm
      _ = (3/2) * R^3 * Real.sqrt (M / (N:ℝ)) * (∑ j ∈ Finset.Ico N J, (μ j)^2) := by
            rw [Finset.mul_sum]
      _ ≤ (3/2) * R^3 * Real.sqrt (M / (N:ℝ)) * M := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine le_trans ?_ (hμsum J)
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              rw [Finset.mem_Ico] at hx
              rw [Finset.mem_range]
              exact hx.2
            · intro i _ _; positivity
      _ ≤ epsN R M N := by
            rw [epsN]
            have hsqrtnn := hsqrtN_nonneg
            nlinarith [hR3nn, hM, hsqrtnn, mul_nonneg (mul_nonneg hR3nn hM) hsqrtnn]







theorem multipliable_lemma : ∀ (M : ℝ) (α : ℕ → ℝ),
    (∀ N : ℕ, ∑ j ∈ Finset.range N, (α j) ^ 2 ≤ M) → ∀ s : ℂ,
      Summable (fun j => ‖E ((α j : ℂ) * s) - 1‖) ∧
      Multipliable (fun j => E ((α j : ℂ) * s)) ∧
      Filter.Tendsto (fun J => ∏ j ∈ Finset.range J, E ((α j : ℂ) * s)) Filter.atTop
          (nhds (∏' j, E ((α j : ℂ) * s))) ∧
      (∀ N : ℕ, ∃ LN : ℂ,
        Filter.Tendsto (fun J => ∏ j ∈ Finset.Ico N J, E ((α j : ℂ) * s)) Filter.atTop (nhds LN) ∧
        (∏' j, E ((α j : ℂ) * s)) = (∏ j ∈ Finset.range N, E ((α j : ℂ) * s)) * LN) := by
  intro M α hM s
  have hsummable : Summable (fun j => ‖E ((α j : ℂ) * s) - 1‖) := by
    by_cases hs : s = 0
    · subst hs
      have hz : (fun j : ℕ => ‖E ((α j : ℂ) * 0) - 1‖) = fun _ => (0 : ℝ) := by
        funext j; simp [E]
      rw [hz]; exact summable_zero
    · have hs0 : (0 : ℝ) < ‖s‖ := by rw [norm_pos_iff]; exact hs
      have hα2 : Summable (fun j => (α j) ^ 2) :=
        summable_of_sum_range_le (fun j => sq_nonneg _) hM
      have hg : Summable (fun j => ‖s‖ ^ 2 * (α j) ^ 2) := hα2.mul_left _
      set F : Set ℕ := {j | ¬ (‖(α j : ℂ) * s‖ ≤ 1 / 2)} with hF_def
      have hnormeq : ∀ j, ‖(α j : ℂ) * s‖ = |α j| * ‖s‖ := by
        intro j; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hthr : (0 : ℝ) < 1 / (4 * ‖s‖ ^ 2) := by positivity
      have hFsub : F ⊆ {j | 1 / (4 * ‖s‖ ^ 2) < (α j) ^ 2} := by
        intro j hj
        simp only [hF_def, Set.mem_setOf_eq, not_le] at hj
        rw [hnormeq] at hj
        simp only [Set.mem_setOf_eq]
        have hsq : (1 / 2 : ℝ) ^ 2 < (|α j| * ‖s‖) ^ 2 := by
          apply sq_lt_sq' <;> nlinarith [abs_nonneg (α j), hs0.le]
        rw [mul_pow, sq_abs] at hsq
        have h4 : (0 : ℝ) < 4 * ‖s‖ ^ 2 := by positivity
        rw [div_lt_iff₀ h4]; nlinarith [hsq]
      have hFin_thr : {j : ℕ | 1 / (4 * ‖s‖ ^ 2) < (α j) ^ 2}.Finite := by
        have htend := hα2.tendsto_cofinite_zero
        have hev : ∀ᶠ j in Filter.cofinite, (α j) ^ 2 < 1 / (4 * ‖s‖ ^ 2) := by
          have : {x : ℝ | x < 1 / (4 * ‖s‖ ^ 2)} ∈ nhds (0 : ℝ) :=
            IsOpen.mem_nhds isOpen_Iio (by simpa using hthr)
          exact htend.eventually this
        rw [Filter.eventually_cofinite] at hev
        apply hev.subset
        intro j hj
        simp only [Set.mem_setOf_eq, not_lt] at *
        exact le_of_lt hj
      have hFin : F.Finite := hFin_thr.subset hFsub
      set f : ℕ → ℝ := fun j => ‖E ((α j : ℂ) * s) - 1‖ with hf_def
      set fF : ℕ → ℝ := fun j => if j ∈ F then f j else 0 with hfF_def
      set fFc : ℕ → ℝ := fun j => if j ∈ F then 0 else f j with hfFc_def
      have hfF_sum : Summable fF := by
        apply summable_of_hasFiniteSupport
        apply Set.Finite.subset hFin
        intro j hj
        simp only [Function.mem_support, hfF_def, ne_eq] at hj
        by_contra hjF
        rw [if_neg hjF] at hj
        exact hj rfl
      have hfFc_sum : Summable fFc := by
        refine Summable.of_nonneg_of_le ?_ ?_ (hg.mul_left (3 / 4))
        · intro j
          simp only [hfFc_def]
          split <;> [exact le_refl 0; exact norm_nonneg _]
        · intro j
          simp only [hfFc_def]
          split
          · positivity
          · rename_i hjF
            simp only [hF_def, Set.mem_setOf_eq, not_not] at hjF
            have hb := E_series.2.1 ((α j : ℂ) * s) hjF
            have hnn : ‖(α j : ℂ) * s‖ ^ 2 = ‖s‖ ^ 2 * (α j) ^ 2 := by
              rw [hnormeq, mul_pow, sq_abs]; ring
            rw [hnn] at hb
            exact hb
      have hsplit : f = fun j => fF j + fFc j := by
        funext j
        simp only [hfF_def, hfFc_def]
        split <;> simp
      rw [hsplit]
      exact hfF_sum.add hfFc_sum
  have hrw : (fun ν => 1 + (E ((α ν : ℂ) * s) - 1)) = (fun ν => E ((α ν : ℂ) * s)) := by
    funext ν; ring
  obtain ⟨hMult0, hTendsto0, hHead0⟩ := prod_conv (fun j => E ((α j : ℂ) * s) - 1) hsummable
  rw [hrw] at hMult0 hTendsto0
  refine ⟨hsummable, hMult0, hTendsto0, ?_⟩
  intro N
  obtain ⟨LN, hLN_tendsto, _, hLN_eq⟩ := hHead0 N
  rw [hrw] at hLN_tendsto hLN_eq
  exact ⟨LN, hLN_tendsto, hLN_eq⟩





theorem tail_value : ∀ (M R : ℝ) (α : ℕ → ℝ), 0 ≤ M → 0 < R →
    (∀ j : ℕ, |α j| ≤ Real.sqrt (M / ((j : ℝ) + 1))) →
    (∀ N : ℕ, ∑ j ∈ Finset.range N, (α j) ^ 2 ≤ M) →
    Summable (fun j => (α j) ^ 2) →
    ∀ (z : ℂ) (N : ℕ), ‖z‖ ≤ R → 1 ≤ N → 4 * R ^ 2 * M ≤ (N : ℝ) →
      ∀ LN : ℂ,
        Filter.Tendsto (fun J => ∏ j ∈ Finset.Ico N J, E ((α j : ℂ) * z)) Filter.atTop (nhds LN) →
        ∃ θ : ℂ,
          LN = Complex.exp ((-(z ^ 2) / 2)
                * (((∑' j, (α j) ^ 2) - ∑ j ∈ Finset.range N, (α j) ^ 2 : ℝ) : ℂ)) * (1 + θ) ∧
          ‖θ‖ ≤ Real.exp (epsN R M N) - 1 := by
  intro M R α hM hR hbound hsum hsummable z N hz hN hRN LN hLN
  set SN : ℝ := ((∑' j, (α j) ^ 2) - ∑ j ∈ Finset.range N, (α j) ^ 2 : ℝ) with hSN
  set a : ℕ → ℂ := fun J =>
    (∏ j ∈ Finset.Ico N J, E ((α j : ℂ) * z)) *
      Complex.exp ((z ^ 2 / 2) * ((∑ j ∈ Finset.Ico N J, (α j) ^ 2 : ℝ) : ℂ)) with ha
  have step1 : ∀ J, N < J → ‖a J - 1‖ ≤ Real.exp (epsN R M N) - 1 := by
    intro J hNJ
    obtain ⟨ρ, hprod, hρ⟩ := tail_expansion M R α hM hR hbound hsum N J z hz hN hRN hNJ
    have haJ : a J = Complex.exp ρ := by
      rw [ha]
      simp only
      rw [hprod, ← Complex.exp_add]
      congr 1
      ring
    rw [haJ]
    have hE := (exp_diff.2 ρ).1
    calc ‖Complex.exp ρ - 1‖ ≤ Real.exp ‖ρ‖ - 1 := hE
      _ ≤ Real.exp (epsN R M N) - 1 := by
          have := Real.exp_le_exp.mpr hρ
          linarith
  have hsum_tendsto :
      Filter.Tendsto (fun J => (∑ j ∈ Finset.Ico N J, (α j) ^ 2 : ℝ)) Filter.atTop (nhds SN) := by
    have hrange : Filter.Tendsto (fun J => (∑ j ∈ Finset.range J, (α j) ^ 2 : ℝ))
        Filter.atTop (nhds (∑' j, (α j) ^ 2)) :=
      hsummable.hasSum.tendsto_sum_nat
    have hconst : Filter.Tendsto (fun _ : ℕ => (∑ j ∈ Finset.range N, (α j) ^ 2 : ℝ))
        Filter.atTop (nhds (∑ j ∈ Finset.range N, (α j) ^ 2 : ℝ)) := tendsto_const_nhds
    have hdiff := hrange.sub hconst
    rw [hSN]
    refine hdiff.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N] with J hJ
    rw [Finset.sum_Ico_eq_sub _ hJ]
  have hsumC : Filter.Tendsto (fun J => ((∑ j ∈ Finset.Ico N J, (α j) ^ 2 : ℝ) : ℂ))
      Filter.atTop (nhds ((SN : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto SN).comp hsum_tendsto
  have hexpC : Filter.Tendsto
      (fun J => Complex.exp ((z ^ 2 / 2) * ((∑ j ∈ Finset.Ico N J, (α j) ^ 2 : ℝ) : ℂ)))
      Filter.atTop (nhds (Complex.exp ((z ^ 2 / 2) * ((SN : ℝ) : ℂ)))) := by
    have hcont := Complex.continuous_exp.tendsto ((z ^ 2 / 2) * ((SN : ℝ) : ℂ))
    exact hcont.comp (hsumC.const_mul (z ^ 2 / 2))
  set A : ℂ := LN * Complex.exp ((z ^ 2 / 2) * ((SN : ℝ) : ℂ)) with hA
  have ha_tendsto : Filter.Tendsto a Filter.atTop (nhds A) := by
    rw [ha, hA]
    exact hLN.mul hexpC
  have hboundA : ‖A - 1‖ ≤ Real.exp (epsN R M N) - 1 := by
    have hnorm : Filter.Tendsto (fun J => ‖a J - 1‖) Filter.atTop (nhds ‖A - 1‖) :=
      (continuous_norm.tendsto (A - 1)).comp (ha_tendsto.sub_const 1)
    refine le_of_tendsto hnorm ?_
    filter_upwards [Filter.eventually_gt_atTop N] with J hJ using step1 J hJ
  refine ⟨A - 1, ?_, hboundA⟩
  have h1θ : (1 : ℂ) + (A - 1) = A := by ring
  rw [h1θ, hA]
  rw [mul_comm LN _, ← mul_assoc, ← Complex.exp_add]
  have hzero : (-(z ^ 2) / 2) * ((SN : ℝ) : ℂ) + (z ^ 2 / 2) * ((SN : ℝ) : ℂ) = 0 := by ring
  rw [hzero, Complex.exp_zero, one_mul]





theorem identify : ∀ (β : ℕ → ℝ), HypH β → ∀ (Λ : ℕ → ℕ → ℝ), IsLambdaFamily β Λ →
    ∀ (φ : ℕ → ℕ) (α : ℕ → ℝ) (γ : ℝ),
      StrictMono φ →
      (∀ j : ℕ, Filter.Tendsto (fun k => Λ (φ k) j) Filter.atTop (nhds (α j))) →
      (∀ j : ℕ, |α j| ≤ Real.sqrt (Mconst β / ((j : ℝ) + 1))) →
      (∀ N : ℕ, ∑ j ∈ Finset.range N, (α j) ^ 2 ≤ Bconst β) →
      Summable (fun j => (α j) ^ 2) →
      0 ≤ γ → Bconst β = 2 * γ + ∑' j, (α j) ^ 2 →
      ∀ z : ℂ,
        (∑' m, ((β m / (β 0 * (m.factorial : ℝ)) : ℝ) : ℂ) * z ^ m)
          = Complex.exp (-(γ : ℂ) * z ^ 2 + (delta β : ℂ) * z) * ∏' j, E ((α j : ℂ) * z) := by
  intro β hβ Λ hΛ φ α γ hφ hΛα hα_decay hα_Bc hα_sum hγ hBc z
  set R : ℝ := ‖z‖ + 1 with hR_def
  have hR0 : 0 < R := by rw [hR_def]; positivity
  have hzR : ‖z‖ ≤ R := by rw [hR_def]; linarith
  set M : ℝ := Mconst β with hM_def
  set Bc : ℝ := Bconst β with hBc_def
  set K : ℝ := Kbound (|delta β|) M R with hK_def
  have hβ0 : 0 < β 0 := hβ.1
  have hM0 : 0 ≤ M := by
    rw [hM_def, Mconst]
    have : 0 ≤ |β 2| / β 0 := div_nonneg (abs_nonneg _) hβ0.le
    positivity
  have hBcM : Bc ≤ M := by rw [hBc_def, hM_def]; exact (B_limit β hβ).2.2
  have hα_M : ∀ N : ℕ, ∑ j ∈ Finset.range N, (α j) ^ 2 ≤ M := by
    intro N; exact le_trans (hα_Bc N) hBcM
  have hKpos : 0 < K := by rw [hK_def, Kbound]; exact Real.exp_pos _
  set P : ℂ := ∑' m, ((β m / (β 0 * (m.factorial : ℝ)) : ℝ) : ℂ) * z ^ m with hP_def
  set V : ℂ := Complex.exp (-(γ : ℂ) * z ^ 2 + (delta β : ℂ) * z) * ∏' j, E ((α j : ℂ) * z) with hV_def
  have hPn_P : Filter.Tendsto (fun k => Pn β (φ k) z) Filter.atTop (nhds P) := by
    have hbase : Filter.Tendsto (fun n => Pn β n z) Filter.atTop (nhds P) :=
      (Pn_converges β hβ).2.2 z
    exact hbase.comp hφ.tendsto_atTop
  have hEcont : Continuous E := by unfold E; fun_prop
  have hepsN0 : Filter.Tendsto (fun N : ℕ => epsN R M N) Filter.atTop (nhds 0) := by
    have hdiv : Filter.Tendsto (fun N : ℕ => M / (N : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat M
    have hsqrt : Filter.Tendsto (fun N : ℕ => Real.sqrt (M / (N : ℝ))) Filter.atTop (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hdiv
      rw [Real.sqrt_zero] at h; exact h
    have h2 : Filter.Tendsto (fun N : ℕ => 2 * R ^ 3 * M * Real.sqrt (M / (N : ℝ))) Filter.atTop
        (nhds (2 * R ^ 3 * M * 0)) := hsqrt.const_mul _
    simpa [epsN, mul_zero] using h2
  have hPn_V : Filter.Tendsto (fun k => Pn β (φ k) z) Filter.atTop (nhds V) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN1, hN2, hNeps, hNscaled⟩ :
        ∃ N : ℕ, 1 ≤ N ∧ 4 * R ^ 2 * M ≤ (N : ℝ) ∧ epsN R M N ≤ 1 ∧
          Real.exp 2 * K * epsN R M N ≤ ε / 3 := by
      have h1 : ∀ᶠ N : ℕ in Filter.atTop, epsN R M N ≤ 1 := by
        have := hepsN0.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
        filter_upwards [this] with N hN using le_of_lt hN
      have hscaled : Filter.Tendsto (fun N : ℕ => Real.exp 2 * K * epsN R M N) Filter.atTop (nhds 0) := by
        have := hepsN0.const_mul (Real.exp 2 * K); simpa using this
      have h2 : ∀ᶠ N : ℕ in Filter.atTop, Real.exp 2 * K * epsN R M N ≤ ε / 3 := by
        have := hscaled.eventually (gt_mem_nhds (show (0:ℝ) < ε/3 by positivity))
        filter_upwards [this] with N hN using le_of_lt hN
      have h3 : ∀ᶠ N : ℕ in Filter.atTop, 4 * R ^ 2 * M ≤ (N : ℝ) :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
      have h4 : ∀ᶠ N : ℕ in Filter.atTop, 1 ≤ N := Filter.eventually_ge_atTop 1
      obtain ⟨N, ⟨hN1, hN3⟩, hNe, hNs⟩ := ((h4.and h3).and (h1.and h2)).exists
      exact ⟨N, hN1, hN3, hNe, hNs⟩
    set e0 : ℝ := Real.exp (epsN R M N) with he0_def
    have he0pos : 0 < e0 := Real.exp_pos _
    have hepsNnn : (0:ℝ) ≤ epsN R M N := by rw [epsN]; positivity
    have he0ge1 : (1:ℝ) ≤ e0 := by rw [he0_def]; exact Real.one_le_exp hepsNnn
    set bnd : ℝ := K * e0 * (e0 - 1) with hbnd_def
    set Gk : ℕ → ℂ := fun k => Complex.exp ((delta β : ℂ) * z) *
        (∏ j ∈ Finset.range N, E ((Λ (φ k) j : ℂ) * z)) *
        Complex.exp ((-(z ^ 2) / 2) *
          ((∑ j ∈ Finset.Ico N (max (φ k) (N + 1)), (Λ (φ k) j) ^ 2 : ℝ) : ℂ)) with hGk_def
    set GNval : ℂ := Complex.exp ((delta β : ℂ) * z) *
        (∏ j ∈ Finset.range N, E ((α j : ℂ) * z)) *
        Complex.exp ((-(z ^ 2) / 2) * ((Bc - ∑ j ∈ Finset.range N, (α j) ^ 2 : ℝ) : ℂ)) with hGNval_def
    have hS1 : ∀ k : ℕ, 1 ≤ φ k →
        ‖Pn β (φ k) z - Gk k‖ ≤ bnd ∧ ‖Gk k‖ ≤ K * e0 := by
      intro k hφk1
      set n := φ k with hn_def
      have hdecay : ∀ j : ℕ, |Λ n j| ≤ Real.sqrt (M / ((j : ℝ) + 1)) := by
        intro j; rw [hM_def]; exact (lambda_decay β hβ Λ hΛ n hφk1).2 j
      have hpartial : ∀ J : ℕ, ∑ j ∈ Finset.range J, (Λ n j) ^ 2 ≤ M := by
        intro J; rw [hM_def]; exact (lambda_decay β hβ Λ hΛ n hφk1).1 J
      set J : ℕ := max n (N + 1) with hJ_def
      have hJn : n ≤ J := le_max_left _ _
      have hNJ : N < J := lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_right _ _)
      have hNJ' : N ≤ J := le_of_lt hNJ
      have hEprod : Pn β n z =
          Complex.exp ((delta β : ℂ) * z) * ∏ j ∈ Finset.range J, E ((Λ n j : ℂ) * z) :=
        E_product β hβ Λ hΛ n hφk1 J hJn z
      obtain ⟨ρ, hρeq, hρbd⟩ :=
        tail_expansion M R (fun j => Λ n j) hM0 hR0 hdecay hpartial N J z hzR hN1 hN2 hNJ
      have hsplit : (∏ j ∈ Finset.range J, E ((Λ n j : ℂ) * z))
          = (∏ j ∈ Finset.range N, E ((Λ n j : ℂ) * z)) * (∏ j ∈ Finset.Ico N J, E ((Λ n j : ℂ) * z)) :=
        (Finset.prod_range_mul_prod_Ico (fun j => E ((Λ n j : ℂ) * z)) hNJ').symm
      have hPnG : Pn β n z = Gk k * Complex.exp ρ := by
        rw [hEprod, hsplit, hρeq]
        show _ = (Complex.exp ((delta β : ℂ) * z) *
          (∏ j ∈ Finset.range N, E ((Λ n j : ℂ) * z)) *
          Complex.exp ((-(z ^ 2) / 2) *
            ((∑ j ∈ Finset.Ico N (max n (N + 1)), (Λ n j) ^ 2 : ℝ) : ℂ))) * Complex.exp ρ
        rw [← hJ_def, Complex.exp_add]; ring
      have hPnbd : ‖Pn β n z‖ ≤ K := by
        rw [hK_def, hM_def]; exact Pn_bounded β hβ n hφk1 R hR0 z hzR
      have hexpneg : ‖Complex.exp (-ρ)‖ ≤ e0 := by
        rw [he0_def, Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have h1 : (-ρ).re = -ρ.re := by simp
        rw [h1]
        have h2 : -ρ.re ≤ |ρ.re| := neg_le_abs _
        have h3 : |ρ.re| ≤ ‖ρ‖ := Complex.abs_re_le_norm ρ
        linarith
      have hGeq : Gk k = Pn β n z * Complex.exp (-ρ) := by
        rw [hPnG, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
      have hGnorm : ‖Gk k‖ ≤ K * e0 := by
        rw [hGeq, norm_mul]
        exact mul_le_mul hPnbd hexpneg (norm_nonneg _) hKpos.le
      have hexpm1 : ‖Complex.exp ρ - 1‖ ≤ e0 - 1 := by
        have h1 : ‖Complex.exp ρ - 1‖ ≤ Real.exp ‖ρ‖ - 1 := (exp_diff.2 ρ).1
        have h2 : Real.exp ‖ρ‖ - 1 ≤ e0 - 1 := by
          rw [he0_def]; have := Real.exp_le_exp.mpr hρbd; linarith
        linarith
      have hPnGdiff : ‖Pn β n z - Gk k‖ ≤ bnd := by
        have hfactor : Pn β n z - Gk k = Gk k * (Complex.exp ρ - 1) := by rw [hPnG]; ring
        rw [hfactor, norm_mul, hbnd_def]
        exact mul_le_mul hGnorm hexpm1 (norm_nonneg _) (by positivity)
      exact ⟨hPnGdiff, hGnorm⟩
    have hS2 : Filter.Tendsto Gk Filter.atTop (nhds GNval) := by
      rw [hGk_def, hGNval_def]
      have hprod : Filter.Tendsto
          (fun k => ∏ j ∈ Finset.range N, E ((Λ (φ k) j : ℂ) * z)) Filter.atTop
          (nhds (∏ j ∈ Finset.range N, E ((α j : ℂ) * z))) := by
        apply tendsto_finsetProd
        intro j _
        have hcoe : Filter.Tendsto (fun k => ((Λ (φ k) j : ℝ) : ℂ)) Filter.atTop
            (nhds ((α j : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp (hΛα j)
        have hmul : Filter.Tendsto (fun k => ((Λ (φ k) j : ℂ)) * z) Filter.atTop
            (nhds ((α j : ℂ) * z)) := hcoe.mul_const z
        exact (hEcont.tendsto _).comp hmul
      have hφk1 : ∀ᶠ k in Filter.atTop, 1 ≤ φ k := by
        filter_upwards [Filter.eventually_ge_atTop 1] with k hk
        exact le_trans hk ((subseq_facts.1 φ hφ) k)
      have htail_eq : ∀ᶠ k in Filter.atTop,
          (∑ j ∈ Finset.Ico N (max (φ k) (N + 1)), (Λ (φ k) j) ^ 2 : ℝ)
            = ((delta β) ^ 2 - ((φ k : ℝ) - 1) / (φ k) * (β 2 / β 0))
              - ∑ j ∈ Finset.range N, (Λ (φ k) j) ^ 2 := by
        filter_upwards [hφk1] with k hk
        set n := φ k with hn
        have hJn : n ≤ max n (N + 1) := le_max_left _ _
        have hNJ' : N ≤ max n (N + 1) := le_trans (Nat.le_succ N) (le_max_right _ _)
        have hlamprod : ∀ w : ℂ,
            (∏ j ∈ Finset.range (max n (N + 1)), (1 + (Λ n j : ℂ) * w)) = Pn β n w := by
          intro w; exact ((hΛ n hk).2.2 (max n (N + 1)) hJn w).symm
        have hsym := (symmetric β hβ n hk (max n (N + 1)) (fun j => Λ n j) hlamprod).2.2.1
        rw [Finset.sum_Ico_eq_sub _ hNJ', hsym]
      have hbracket : Filter.Tendsto
          (fun k => (delta β) ^ 2 - ((φ k : ℝ) - 1) / (φ k) * (β 2 / β 0)) Filter.atTop (nhds Bc) := by
        rw [hBc_def]; exact ((B_limit β hβ).1).comp hφ.tendsto_atTop
      have hrangeN : Filter.Tendsto
          (fun k => ∑ j ∈ Finset.range N, (Λ (φ k) j) ^ 2) Filter.atTop
          (nhds (∑ j ∈ Finset.range N, (α j) ^ 2)) := by
        apply tendsto_finsetSum
        intro j _; have := (hΛα j).pow 2; simpa using this
      have htail : Filter.Tendsto
          (fun k => (∑ j ∈ Finset.Ico N (max (φ k) (N + 1)), (Λ (φ k) j) ^ 2 : ℝ)) Filter.atTop
          (nhds (Bc - ∑ j ∈ Finset.range N, (α j) ^ 2)) := by
        apply Filter.Tendsto.congr' (Filter.EventuallyEq.symm htail_eq)
        exact hbracket.sub hrangeN
      have hexpfactor : Filter.Tendsto
          (fun k => Complex.exp ((-(z ^ 2) / 2) *
            ((∑ j ∈ Finset.Ico N (max (φ k) (N + 1)), (Λ (φ k) j) ^ 2 : ℝ) : ℂ))) Filter.atTop
          (nhds (Complex.exp ((-(z ^ 2) / 2) *
            ((Bc - ∑ j ∈ Finset.range N, (α j) ^ 2 : ℝ) : ℂ)))) := by
        have hcoe : Filter.Tendsto
            (fun k => ((∑ j ∈ Finset.Ico N (max (φ k) (N + 1)), (Λ (φ k) j) ^ 2 : ℝ) : ℂ))
            Filter.atTop (nhds ((Bc - ∑ j ∈ Finset.range N, (α j) ^ 2 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto _).comp htail
        have hmul := hcoe.const_mul (-(z ^ 2) / 2)
        exact (Complex.continuous_exp.tendsto _).comp hmul
      exact (Filter.Tendsto.mul (Filter.Tendsto.const_mul _ hprod) hexpfactor)
    have hGNnorm : ‖GNval‖ ≤ K * e0 := by
      have hev : ∀ᶠ k in Filter.atTop, ‖Gk k‖ ≤ K * e0 := by
        filter_upwards [Filter.eventually_ge_atTop 1] with k hk
        exact (hS1 k (le_trans hk ((subseq_facts.1 φ hφ) k))).2
      exact le_of_tendsto (hS2.norm) hev
    have hS3 : ‖V - GNval‖ ≤ bnd := by
      obtain ⟨LN, hLNtend, hprodeq⟩ := (multipliable_lemma M α hα_M z).2.2.2 N
      obtain ⟨θ, hLNval, hθbd⟩ :=
        tail_value M R α hM0 hR0 (by rw [hM_def] at hα_decay ⊢; exact hα_decay) hα_M hα_sum z N hzR hN1 hN2 LN hLNtend
      set SN : ℝ := (∑' j, (α j) ^ 2) - ∑ j ∈ Finset.range N, (α j) ^ 2 with hSN_def
      have hprodfull : (∏' j, E ((α j : ℂ) * z))
          = (∏ j ∈ Finset.range N, E ((α j : ℂ) * z))
            * Complex.exp ((-(z ^ 2) / 2) * (SN : ℂ)) * (1 + θ) := by
        rw [hprodeq, hLNval, hSN_def]; ring
      have hTN : ((Bc - ∑ j ∈ Finset.range N, (α j) ^ 2 : ℝ) : ℂ)
          = 2 * (γ : ℂ) + (SN : ℂ) := by
        rw [hSN_def]
        have hh : (Bc - ∑ j ∈ Finset.range N, (α j) ^ 2 : ℝ)
            = 2 * γ + ((∑' j, (α j) ^ 2) - ∑ j ∈ Finset.range N, (α j) ^ 2) := by
          rw [hBc]; ring
        rw [hh]; push_cast; ring
      have hexpsplit : Complex.exp ((-(z ^ 2) / 2) * ((Bc - ∑ j ∈ Finset.range N, (α j) ^ 2 : ℝ) : ℂ))
          = Complex.exp (-(γ : ℂ) * z ^ 2) * Complex.exp ((-(z ^ 2) / 2) * (SN : ℂ)) := by
        rw [hTN, mul_add, Complex.exp_add]; congr 1; congr 1; ring
      have hexpaddδ : Complex.exp (-(γ : ℂ) * z ^ 2 + (delta β : ℂ) * z)
          = Complex.exp (-(γ : ℂ) * z ^ 2) * Complex.exp ((delta β : ℂ) * z) := Complex.exp_add _ _
      have hVeq : V = GNval * (1 + θ) := by
        rw [hV_def, hGNval_def, hprodfull, hexpsplit, hexpaddδ]; ring
      have hnormeq : ‖V - GNval‖ = ‖GNval‖ * ‖θ‖ := by
        rw [hVeq, show GNval * (1 + θ) - GNval = GNval * θ by ring, norm_mul]
      rw [hnormeq, hbnd_def]
      have hθnn : (0:ℝ) ≤ e0 - 1 := by linarith [he0ge1]
      have hθbd' : ‖θ‖ ≤ e0 - 1 := by rw [he0_def]; exact hθbd
      exact mul_le_mul hGNnorm hθbd' (norm_nonneg _) (by positivity)
    have hbnd_le : bnd ≤ ε / 3 := by
      rw [hbnd_def]
      have hem1 : e0 - 1 ≤ epsN R M N * e0 := by
        rw [he0_def]; exact exp_diff.1 (epsN R M N) hepsNnn
      have hstep : K * e0 * (e0 - 1) ≤ Real.exp 2 * K * epsN R M N := by
        have h1 : K * e0 * (e0 - 1) ≤ K * e0 * (epsN R M N * e0) := by
          apply mul_le_mul_of_nonneg_left hem1 (by positivity)
        have h2 : K * e0 * (epsN R M N * e0) = K * epsN R M N * e0 ^ 2 := by ring
        have h3 : e0 ^ 2 ≤ Real.exp 2 := by
          have hsq : e0 ^ 2 = Real.exp (epsN R M N + epsN R M N) := by
            rw [he0_def, pow_two, ← Real.exp_add]
          rw [hsq]; exact Real.exp_le_exp.mpr (by linarith [hNeps])
        calc K * e0 * (e0 - 1) ≤ K * epsN R M N * e0 ^ 2 := by rw [← h2]; exact h1
          _ ≤ K * epsN R M N * Real.exp 2 :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = Real.exp 2 * K * epsN R M N := by ring
      linarith [hstep, hNscaled]
    rw [Metric.tendsto_atTop] at hS2
    obtain ⟨k1, hk1⟩ := hS2 (ε / 3) (by positivity)
    refine ⟨max k1 1, fun k hk => ?_⟩
    have hkk1 : k1 ≤ k := le_trans (le_max_left _ _) hk
    have hk1' : 1 ≤ k := le_trans (le_max_right _ _) hk
    have hφk1 : 1 ≤ φ k := le_trans hk1' ((subseq_facts.1 φ hφ) k)
    have hA : ‖Pn β (φ k) z - Gk k‖ ≤ bnd := (hS1 k hφk1).1
    have hB : dist (Gk k) GNval < ε / 3 := hk1 k hkk1
    have hB' : ‖Gk k - GNval‖ < ε / 3 := by rw [← Complex.dist_eq]; exact hB
    have hC : ‖GNval - V‖ ≤ bnd := by rw [← norm_neg, neg_sub]; exact hS3
    rw [Complex.dist_eq]
    have htri : ‖Pn β (φ k) z - V‖
        ≤ ‖Pn β (φ k) z - Gk k‖ + ‖Gk k - GNval‖ + ‖GNval - V‖ := by
      have heq : Pn β (φ k) z - V
          = (Pn β (φ k) z - Gk k) + (Gk k - GNval) + (GNval - V) := by ring
      rw [heq]; exact norm_add₃_le
    have hsum : ‖Pn β (φ k) z - Gk k‖ + ‖Gk k - GNval‖ + ‖GNval - V‖ < ε := by
      have hlt : ‖Pn β (φ k) z - Gk k‖ + ‖Gk k - GNval‖ + ‖GNval - V‖ < ε / 3 + ε / 3 + ε / 3 := by
        apply add_lt_add_of_lt_of_le
        · exact add_lt_add_of_le_of_lt (le_trans hA hbnd_le) hB'
        · exact le_trans hC hbnd_le
      linarith
    linarith [htri, hsum]
  exact tendsto_nhds_unique hPn_P hPn_V

end Part6






theorem Part_6_main : Statement_Part_6 := by
  intro β hβ0 hrr
  have hβ : Part6.HypH β := ⟨hβ0, hrr⟩
  obtain ⟨Λ, hΛ⟩ := Part6.Lambda_family β hβ
  obtain ⟨φ, α, γ, hφ, hconv, hαbound, hαpartial, hαsummable, hαtsum, hγ0, hBeq⟩ :=
    Part6.alpha_family β hβ Λ hΛ
  refine ⟨γ, Part6.delta β, α, hγ0, hαsummable, fun s => ?_⟩
  have hfactor : (fun ν : ℕ => (1 + (α ν : ℂ) * s) * Complex.exp (-(α ν : ℂ) * s))
      = (fun ν => Part6.E ((α ν : ℂ) * s)) := by
    funext ν; rw [Part6.E, neg_mul]
  have hmult := Part6.multipliable_lemma (Part6.Bconst β) α hαpartial s
  refine ⟨?_, ?_⟩
  · rw [hfactor]; exact hmult.2.1
  · have hid := Part6.identify β hβ Λ hΛ φ α γ hφ hconv hαbound hαpartial hαsummable hγ0 hBeq s
    have hPsum := (Part6.Pn_converges β hβ).2.1 s
    have hb0 : β 0 ≠ 0 := hβ0.ne'
    have hseries_eq : (fun m : ℕ => ((β m / (m.factorial : ℝ) : ℝ) : ℂ) * s ^ m)
        = (fun m => (β 0 : ℂ) * (((β m / (β 0 * (m.factorial : ℝ)) : ℝ) : ℂ) * s ^ m)) := by
      funext m
      have hfac : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
      rw [← mul_assoc]
      congr 1
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp
    have hHasSum : HasSum (fun m => ((β m / (m.factorial : ℝ) : ℝ) : ℂ) * s ^ m)
        ((β 0 : ℂ) * ∑' m, ((β m / (β 0 * (m.factorial : ℝ)) : ℝ) : ℂ) * s ^ m) := by
      rw [hseries_eq]
      exact hPsum.hasSum.mul_left (β 0 : ℂ)
    rw [hid, ← hfactor, ← mul_assoc] at hHasSum
    exact hHasSum
