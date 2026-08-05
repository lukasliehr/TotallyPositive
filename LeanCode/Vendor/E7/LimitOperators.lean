import LeanCode.Vendor.E7.Defs
import LeanCode.Vendor.E7.BanachFacts
import Mathlib.Topology.UniformSpace.Dini








open scoped ENNReal
open Filter Topology
noncomputable section
namespace LimitOps




theorem norm_shiftCLM (m : ℤ) (c : ℓ1) : ‖shiftCLM m c‖ = ‖c‖ := by
  rw [norm_eq_tsum, norm_eq_tsum]
  have := (Equiv.subRight m).tsum_eq (fun k => ‖(c : ℤ → ℂ) k‖)
  simp only [Equiv.subRight_apply] at this

  calc ∑' k : ℤ, ‖(shiftCLM m c : ℤ → ℂ) k‖
      = ∑' k : ℤ, ‖(c : ℤ → ℂ) (k - m)‖ := by
        simp only [shiftCLM_apply]
    _ = ∑' k : ℤ, ‖(c : ℤ → ℂ) k‖ := this




def QCLM (n : ℕ) : ℓ1 →L[ℂ] ℓ1 := 1 - projCLM n

theorem QCLM_apply (n : ℕ) (c : ℓ1) (k : ℤ) :
    (QCLM n c : ℤ → ℂ) k = if |k| ≤ (n : ℤ) then 0 else (c : ℤ → ℂ) k := by
  simp only [QCLM, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    lp.coeFn_sub, Pi.sub_apply, projCLM_apply]
  by_cases hk : |k| ≤ (n : ℤ)
  · rw [if_pos hk, if_pos hk, sub_self]
  · rw [if_neg hk, if_neg hk, sub_zero]


theorem projCLM_norm_eq_sum (n : ℕ) (c : ℓ1) :
    ‖projCLM n c‖ = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ‖(c : ℤ → ℂ) k‖ := by
  rw [norm_eq_tsum]
  rw [tsum_eq_sum (s := Finset.Icc (-(n : ℤ)) (n : ℤ))]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have : |k| ≤ (n : ℤ) := abs_le.mpr ⟨hk.1, hk.2⟩
    rw [projCLM_apply, if_pos this]
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hnk : ¬ |k| ≤ (n : ℤ) := by
      rw [abs_le]; push_neg; intro h1; omega
    rw [projCLM_apply, if_neg hnk, norm_zero]


theorem norm_split (n : ℕ) (c : ℓ1) : ‖c‖ = ‖projCLM n c‖ + ‖QCLM n c‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, norm_eq_tsum]
  have hcP : Summable (fun k : ℤ => ‖(projCLM n c : ℤ → ℂ) k‖) :=
    memℓp_one_iff.mp (lp.memℓp (projCLM n c))
  have hcQ : Summable (fun k : ℤ => ‖(QCLM n c : ℤ → ℂ) k‖) :=
    memℓp_one_iff.mp (lp.memℓp (QCLM n c))
  rw [← hcP.tsum_add hcQ]
  apply tsum_congr
  intro k
  by_cases hk : |k| ≤ (n : ℤ)
  · rw [projCLM_apply, if_pos hk, QCLM_apply, if_pos hk, norm_zero, add_zero]
  · rw [projCLM_apply, if_neg hk, QCLM_apply, if_neg hk, norm_zero, zero_add]


theorem tendsto_Icc_atTop :
    Tendsto (fun n : ℕ => Finset.Icc (-(n : ℤ)) (n : ℤ)) atTop atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro a b hab k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · intro k
    refine ⟨k.natAbs, ?_⟩
    rw [Finset.mem_Icc]
    omega


theorem tendsto_norm_projCLM (c : ℓ1) :
    Tendsto (fun n : ℕ => ‖projCLM n c‖) atTop (𝓝 ‖c‖) := by
  have hnorm : HasSum (fun k : ℤ => ‖(c : ℤ → ℂ) k‖) ‖c‖ := by
    have hp : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
    have := lp.hasSum_norm hp c
    simpa only [ENNReal.toReal_one, Real.rpow_one] using this

  have key : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ‖(c : ℤ → ℂ) k‖)
      atTop (𝓝 ‖c‖) := hnorm.comp tendsto_Icc_atTop
  refine key.congr ?_
  intro n
  rw [projCLM_norm_eq_sum]


theorem monotone_norm_projCLM (c : ℓ1) : Monotone (fun n : ℕ => ‖projCLM n c‖) := by
  intro a b hab
  simp only
  rw [projCLM_norm_eq_sum, projCLM_norm_eq_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · intro k _ _
    positivity


theorem antitone_norm_QCLM (c : ℓ1) : Antitone (fun n : ℕ => ‖QCLM n c‖) := by
  intro a b hab
  simp only
  have ha := norm_split a c
  have hb := norm_split b c
  have := monotone_norm_projCLM c hab
  simp only at this
  linarith


theorem tendsto_norm_QCLM (c : ℓ1) :
    Tendsto (fun n : ℕ => ‖QCLM n c‖) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ‖c‖ - ‖projCLM n c‖) atTop (𝓝 (‖c‖ - ‖c‖)) :=
    (tendsto_const_nhds).sub (tendsto_norm_projCLM c)
  rw [sub_self] at h
  refine h.congr ?_
  intro n
  have := norm_split n c
  linarith







theorem finiteDim_tail_small (U : Submodule ℂ ℓ1) [FiniteDimensional ℂ U]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∀ u : ℓ1, u ∈ U → ‖QCLM R u‖ ≤ ε * ‖u‖ := by
  haveI : ProperSpace U := FiniteDimensional.proper ℂ U

  set s : Set U := Metric.sphere (0 : U) 1 with hs_def
  have hs_compact : IsCompact s := isCompact_sphere (0 : U) 1

  set F : ℕ → U → ℝ := fun n v => ‖QCLM n (↑v : ℓ1)‖ with hF_def

  have hF_cont : ∀ n, Continuous (F n) := by
    intro n
    exact (continuous_norm.comp ((QCLM n).continuous.comp continuous_subtype_val))

  have hF_anti : ∀ v ∈ s, Antitone (F · v) := by
    intro v _ a b hab
    exact antitone_norm_QCLM (↑v : ℓ1) hab

  have hF_tendsto : ∀ v ∈ s, Tendsto (F · v) atTop (𝓝 (0 : ℝ)) := by
    intro v _
    exact tendsto_norm_QCLM (↑v : ℓ1)

  have hunif : TendstoUniformlyOn F (fun _ => (0 : ℝ)) atTop s :=
    Antitone.tendstoUniformlyOn_of_forall_tendsto hs_compact (fun n => (hF_cont n).continuousOn)
      hF_anti continuousOn_const hF_tendsto

  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨R, hR⟩ := (hunif ε hε).exists
  refine ⟨R, ?_⟩
  intro u hu
  by_cases hu0 : u = 0
  · subst hu0; simp
  ·
    have hunorm : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0

    have hcnorm : ‖((‖u‖⁻¹ : ℝ) : ℂ)‖ = ‖u‖⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    set w : U := ((‖u‖⁻¹ : ℝ) : ℂ) • (⟨u, hu⟩ : U) with hw_def
    have hw_sphere : w ∈ s := by
      rw [hs_def, Metric.mem_sphere, dist_zero_right, hw_def, norm_smul, hcnorm]
      have huu : ‖(⟨u, hu⟩ : U)‖ = ‖u‖ := rfl
      rw [huu, inv_mul_cancel₀ (ne_of_gt hunorm)]
    have hbound := hR w hw_sphere
    rw [dist_zero_left, norm_norm] at hbound

    have hFw : ‖QCLM R (↑w : ℓ1)‖ = ‖u‖⁻¹ * ‖QCLM R u‖ := by
      rw [hw_def, Submodule.coe_smul, map_smul, norm_smul, hcnorm]
    rw [hFw] at hbound

    have hstep : ‖QCLM R u‖ < ε * ‖u‖ := by
      have := (mul_lt_mul_of_pos_left hbound hunorm)
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hunorm), one_mul, mul_comm] at this
      exact this
    linarith [hstep]





theorem shift_proj_eq_zero {u : ℓ1} {N : ℕ} (hsupp : ∀ k : ℤ, (N : ℤ) < |k| → (u : ℤ → ℂ) k = 0)
    {m : ℤ} {R : ℕ} (hm : (R : ℤ) + (N : ℤ) < |m|) :
    projCLM R (shiftCLM m u) = 0 := by
  apply lp.ext
  funext k
  rw [projCLM_apply]
  simp only [lp.coeFn_zero, Pi.zero_apply]
  by_cases hk : |k| ≤ (R : ℤ)
  · rw [if_pos hk, shiftCLM_apply]
    apply hsupp

    have h1 : |m| - |k| ≤ |k - m| := by
      have := abs_sub_abs_le_abs_sub m k
      have h2 : |m - k| = |k - m| := abs_sub_comm m k
      rw [h2] at this
      omega
    omega
  · rw [if_neg hk]




theorem step1_lower (M : Submodule ℂ ℓ1) [FiniteDimensional ℂ M]
    (u : ℓ1) (N : ℕ) (hsupp : ∀ k : ℤ, (N : ℤ) < |k| → (u : ℤ → ℂ) k = 0)
    (h : ℕ → ℤ) (hh : ∀ P : ℤ, ∃ K : ℕ, ∀ j : ℕ, K ≤ j → P ≤ |h j|)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, (1 - 2 * ε) * ‖u‖ ≤ Metric.infDist (shiftCLM (h j) u) (M : Set ℓ1) := by

  obtain ⟨R, hR⟩ := finiteDim_tail_small M hε

  obtain ⟨K, hK⟩ := hh ((R : ℤ) + (N : ℤ) + 1)
  refine (eventually_atTop.2 ⟨K, fun j hj => ?_⟩)
  have hmj : (R : ℤ) + (N : ℤ) < |h j| := by have := hK j hj; omega

  have hQ : QCLM R (shiftCLM (h j) u) = shiftCLM (h j) u := by
    rw [QCLM]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [shift_proj_eq_zero hsupp hmj, sub_zero]

  have hnormV : ‖shiftCLM (h j) u‖ = ‖u‖ := norm_shiftCLM (h j) u

  have hMne : (M : Set ℓ1).Nonempty := ⟨0, M.zero_mem⟩
  rw [Metric.le_infDist hMne]
  intro m hm
  rw [dist_eq_norm]

  have hmM : m ∈ M := hm

  by_cases hcase : 2 * ‖u‖ < ‖m‖
  ·
    have h1 : ‖shiftCLM (h j) u‖ - ‖m‖ ≤ ‖shiftCLM (h j) u - m‖ := by
      have := norm_sub_norm_le (shiftCLM (h j) u) m
      linarith [this]

    have h2 : ‖m‖ - ‖shiftCLM (h j) u‖ ≤ ‖shiftCLM (h j) u - m‖ := by
      have := norm_sub_norm_le m (shiftCLM (h j) u)
      rw [norm_sub_rev] at this
      linarith [this]
    have hunn : 0 ≤ ‖u‖ := norm_nonneg u
    nlinarith [h2, hnormV, hcase, hε, hunn]
  ·
    push_neg at hcase
    have hQm := hR m hmM

    have hle1 : ‖QCLM R (shiftCLM (h j) u - m)‖ ≤ ‖shiftCLM (h j) u - m‖ := by
      have := norm_split R (shiftCLM (h j) u - m)
      have hpnn : 0 ≤ ‖projCLM R (shiftCLM (h j) u - m)‖ := norm_nonneg _
      linarith [this, hpnn]
    have hsplit : QCLM R (shiftCLM (h j) u - m) = shiftCLM (h j) u - QCLM R m := by
      rw [map_sub, hQ]
    rw [hsplit] at hle1
    have hge : ‖shiftCLM (h j) u‖ - ‖QCLM R m‖ ≤ ‖shiftCLM (h j) u - QCLM R m‖ :=
      norm_sub_norm_le _ _
    have hunn : 0 ≤ ‖u‖ := norm_nonneg u

    nlinarith [hle1, hge, hnormV, hQm, hcase, hε, hunn]




theorem thm_limitOperators_injective (A : ℓ1 →L[ℂ] ℓ1) (hA : Fredholm A) :
    ∀ B ∈ operatorSpectrum A, Function.Injective B := by
  intro B hB

  obtain ⟨h, hh, hconv⟩ := hB

  set M : Submodule ℂ ℓ1 := LinearMap.ker A.toLinearMap with hM
  haveI : FiniteDimensional ℂ M := hA.finiteDimensional_ker

  obtain ⟨c, hc_pos, hKato⟩ := exists_lower_bound_of_isClosed_range A hA.isClosed_range

  rw [injective_iff_map_eq_zero B]
  intro x hBx
  by_contra hx0

  have hxnorm : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0


  have hPtend : Tendsto (fun n : ℕ => ‖projCLM n x‖) atTop (𝓝 ‖x‖) := tendsto_norm_projCLM x
  have hQtend : Tendsto (fun n : ℕ => ‖B‖ * ‖QCLM n x‖) atTop (𝓝 0) := by
    have := (tendsto_norm_QCLM x).const_mul ‖B‖
    simpa using this

  have hev1 : ∀ᶠ n in atTop, ‖x‖ / 2 < ‖projCLM n x‖ :=
    hPtend.eventually_const_lt (by linarith)

  have hev2 : ∀ᶠ n in atTop, ‖B‖ * ‖QCLM n x‖ < (c / 8) * (‖x‖ / 2) := by
    apply hQtend.eventually_lt_const
    positivity
  obtain ⟨N, hN1, hN2⟩ := (hev1.and hev2).exists
  set u : ℓ1 := projCLM N x with hu_def
  have hunorm : (0 : ℝ) < ‖u‖ := by rw [hu_def]; linarith [hN1]
  have hune : u ≠ 0 := norm_pos_iff.mp hunorm

  have hBQ : ‖B‖ * ‖QCLM N x‖ < (c / 8) * ‖u‖ := by
    have : (c / 8) * (‖x‖ / 2) ≤ (c / 8) * ‖u‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hu_def]; linarith [hN1]
    linarith [hN2, this]

  have hsupp : ∀ k : ℤ, (N : ℤ) < |k| → (u : ℤ → ℂ) k = 0 := by
    intro k hk
    rw [hu_def, projCLM_apply, if_neg (by omega)]

  have hBu : B u = - B (QCLM N x) := by
    have hxsplit : projCLM N x + QCLM N x = x := by
      rw [QCLM]; simp
    have hsum : B (projCLM N x) + B (QCLM N x) = 0 := by rw [← map_add, hxsplit, hBx]
    rw [hu_def]
    exact eq_neg_of_add_eq_zero_left hsum

  have hBu_small : ‖B u‖ < (c / 8) * ‖u‖ := by
    rw [hBu, norm_neg]
    calc ‖B (QCLM N x)‖ ≤ ‖B‖ * ‖QCLM N x‖ := B.le_opNorm _
      _ < (c / 8) * ‖u‖ := hBQ

  set Aseq : ℕ → ℓ1 →L[ℂ] ℓ1 := fun j => shiftCLM (-h j) ∘L A ∘L shiftCLM (h j) with hAseq

  have hnorm_Aj : ∀ j, ‖A (shiftCLM (h j) u)‖ = ‖Aseq j u‖ := by
    intro j
    rw [hAseq]
    simp only [ContinuousLinearMap.comp_apply]
    rw [norm_shiftCLM]

  have hev_conv : ∀ᶠ j in atTop, ‖(Aseq j - B) u‖ < (c / 8) * ‖u‖ := by

    have hδ : 0 < (c / 8) * ‖u‖ / (‖x‖ + 1) := by positivity
    obtain ⟨K, hK⟩ := hconv N ((c / 8) * ‖u‖ / (‖x‖ + 1)) hδ
    refine eventually_atTop.2 ⟨K, fun j hj => ?_⟩
    have hbnd := hK j hj

    have hterm : ‖(Aseq j - B) ∘L projCLM N‖ < (c / 8) * ‖u‖ / (‖x‖ + 1) := by
      have hp1 : 0 ≤ ‖projCLM N ∘L (Aseq j - B)‖ := norm_nonneg _
      linarith [hbnd, hp1]

    have hcompu : (Aseq j - B) u = ((Aseq j - B) ∘L projCLM N) x := by
      rw [ContinuousLinearMap.comp_apply, hu_def]
    rw [hcompu]
    calc ‖((Aseq j - B) ∘L projCLM N) x‖
        ≤ ‖(Aseq j - B) ∘L projCLM N‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((c / 8) * ‖u‖ / (‖x‖ + 1)) * ‖x‖ := by
          apply mul_le_mul_of_nonneg_right (le_of_lt hterm) (norm_nonneg x)
      _ < (c / 8) * ‖u‖ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          have : ‖x‖ < ‖x‖ + 1 := by linarith
          nlinarith [hunorm, hc_pos, this, norm_nonneg x]

  have hev_dist : ∀ᶠ j in atTop,
      (3 / 4 : ℝ) * ‖u‖ ≤ Metric.infDist (shiftCLM (h j) u) (M : Set ℓ1) := by
    have := step1_lower M u N hsupp h hh (ε := (1 / 16 : ℝ)) (by norm_num)
    filter_upwards [this] with j hj
    have h116 : (1 - 2 * (1 / 16 : ℝ)) = 7 / 8 := by norm_num
    rw [h116] at hj
    nlinarith [hj, hunorm]

  obtain ⟨j, hjc, hjd⟩ := (hev_conv.and hev_dist).exists

  have hupper : ‖A (shiftCLM (h j) u)‖ < (c / 4) * ‖u‖ := by
    rw [hnorm_Aj j]
    have htri : ‖Aseq j u‖ ≤ ‖(Aseq j - B) u‖ + ‖B u‖ := by
      have : Aseq j u = (Aseq j - B) u + B u := by
        rw [ContinuousLinearMap.sub_apply]; abel
      rw [this]; exact norm_add_le _ _
    linarith [htri, hjc, hBu_small]

  have hlower : (3 * c / 4) * ‖u‖ ≤ ‖A (shiftCLM (h j) u)‖ := by
    have hk := hKato (shiftCLM (h j) u)

    have : c * ((3 / 4) * ‖u‖) ≤ c * Metric.infDist (shiftCLM (h j) u) (M : Set ℓ1) :=
      mul_le_mul_of_nonneg_left hjd (le_of_lt hc_pos)
    have heq : c * ((3 / 4) * ‖u‖) = (3 * c / 4) * ‖u‖ := by ring
    rw [heq] at this

    calc (3 * c / 4) * ‖u‖ ≤ c * Metric.infDist (shiftCLM (h j) u) (M : Set ℓ1) := this
      _ ≤ ‖A (shiftCLM (h j) u)‖ := hk

  have : (3 * c / 4) * ‖u‖ < (c / 4) * ‖u‖ := lt_of_le_of_lt hlower hupper
  nlinarith [this, hunorm, hc_pos]

end LimitOps
