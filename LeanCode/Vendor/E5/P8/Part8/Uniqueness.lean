import LeanCode.Vendor.E5.P8.Part8.Convolution
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open scoped BigOperators

namespace Part8

noncomputable section


theorem charfun_bridge (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  ((∀ ξ : ℝ, measureFT μ ξ = measureFT ν ξ) ↔
    (∀ t : ℝ, MeasureTheory.charFun μ t = MeasureTheory.charFun ν t)) := by
  have hrel : ∀ (ρ : Measure ℝ) (ξ : ℝ),
      measureFT ρ ξ = MeasureTheory.charFun ρ (-2 * Real.pi * ξ) := by
    intro ρ ξ
    unfold measureFT
    rw [MeasureTheory.charFun_apply]
    congr with y
    congr 1
    simp [RCLike.inner_apply]
    ring_nf
  constructor
  · intro h t
    let ξ : ℝ := -t / (2 * Real.pi)
    have hscale : -2 * Real.pi * ξ = t := by
      dsimp [ξ]
      field_simp [Real.pi_ne_zero]
    rw [← hscale]
    rw [← hrel μ ξ, ← hrel ν ξ]
    exact h ξ
  · intro h ξ
    rw [hrel μ ξ, hrel ν ξ]
    exact h (-2 * Real.pi * ξ)


theorem measure_unique (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ ξ : ℝ, measureFT μ ξ = measureFT ν ξ) :
  μ = ν := by
  exact MeasureTheory.Measure.ext_of_charFun (funext ((charfun_bridge μ ν).mp h))


theorem FT_density (f : ℝ → ℝ)
    (hf_meas : Measurable f) (hf_nonneg : ∀ x : ℝ, 0 ≤ f x)
    (hf_int : Integrable f) :
  ∃ μ : Measure ℝ, (∃ _ : IsFiniteMeasure μ, True) ∧
    μ Set.univ = ENNReal.ofReal (∫ x : ℝ, f x) ∧
    ∀ ξ : ℝ, measureFT μ ξ = FT f ξ := by
  let μ : Measure ℝ := (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (f x))
  haveI hμfin : IsFiniteMeasure μ := by
    dsimp [μ]
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hf_int.hasFiniteIntegral
  refine ⟨μ, ⟨hμfin, trivial⟩, ?_, ?_⟩
  · dsimp [μ]
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int
      (Filter.Eventually.of_forall hf_nonneg)).symm
  · intro ξ
    have hdens_meas : Measurable (fun x : ℝ => ENNReal.ofReal (f x)) :=
      hf_meas.ennreal_ofReal
    have hdens_top : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), ENNReal.ofReal (f x) < ⊤ := by
      exact Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
    unfold measureFT FT μ
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
    apply integral_congr_ae
    filter_upwards with y
    rw [ENNReal.toReal_ofReal (hf_nonneg y)]
    simp [mul_comm]


theorem fn_unique (f h : ℝ → ℝ)
    (hf_meas : Measurable f) (hh_meas : Measurable h)
    (hf_nonneg : ∀ x : ℝ, 0 ≤ f x) (hh_nonneg : ∀ x : ℝ, 0 ≤ h x)
    (hf_int : Integrable f) (hh_int : Integrable h)
    (hFT : ∀ ξ : ℝ, FT f ξ = FT h ξ) :
  f =ᵐ[volume] h := by
  let μf : Measure ℝ := (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (f x))
  let μh : Measure ℝ := (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (h x))
  haveI hμffin : IsFiniteMeasure μf := by
    dsimp [μf]
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hf_int.hasFiniteIntegral
  haveI hμhfin : IsFiniteMeasure μh := by
    dsimp [μh]
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hh_int.hasFiniteIntegral
  have hμfFT : ∀ ξ : ℝ, measureFT μf ξ = FT f ξ := by
    intro ξ
    have hdens_meas : Measurable (fun x : ℝ => ENNReal.ofReal (f x)) :=
      hf_meas.ennreal_ofReal
    have hdens_top : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), ENNReal.ofReal (f x) < ⊤ := by
      exact Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
    unfold measureFT FT μf
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
    apply integral_congr_ae
    filter_upwards with y
    rw [ENNReal.toReal_ofReal (hf_nonneg y)]
    simp [mul_comm]
  have hμhFT : ∀ ξ : ℝ, measureFT μh ξ = FT h ξ := by
    intro ξ
    have hdens_meas : Measurable (fun x : ℝ => ENNReal.ofReal (h x)) :=
      hh_meas.ennreal_ofReal
    have hdens_top : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), ENNReal.ofReal (h x) < ⊤ := by
      exact Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
    unfold measureFT FT μh
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
    apply integral_congr_ae
    filter_upwards with y
    rw [ENNReal.toReal_ofReal (hh_nonneg y)]
    simp [mul_comm]
  have hmeq : μf = μh := by
    exact measure_unique μf μh (fun ξ => by rw [hμfFT ξ, hμhFT ξ, hFT ξ])
  have hdens_eq :
      (fun x : ℝ => ENNReal.ofReal (f x)) =ᵐ[volume]
        (fun x : ℝ => ENNReal.ofReal (h x)) := by
    exact (MeasureTheory.withDensity_eq_iff_of_sigmaFinite
      (hf_meas.ennreal_ofReal.aemeasurable) (hh_meas.ennreal_ofReal.aemeasurable)).mp hmeq
  filter_upwards [hdens_eq] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hf_nonneg x) (hh_nonneg x)).mp hx


theorem cont_ae (f h : ℝ → ℝ) (hf : Continuous f) (hh : Continuous h)
    (hae : f =ᵐ[volume] h) :
  ∀ x : ℝ, f x = h x := by
  exact fun x => congr_fun ((Continuous.ae_eq_iff_eq volume hf hh).mp hae) x


theorem dirac_exclusion :
  ¬ ∃ h : ℝ → ℝ,
    Measurable h ∧ (∀ x : ℝ, 0 ≤ h x) ∧ Integrable h ∧
      (∀ ξ : ℝ, FT h ξ = 1) := by
  rintro ⟨h, hh_meas, hh_nonneg, hh_int, hFT⟩
  let μh : Measure ℝ := (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (h x))
  let δ : Measure ℝ := Measure.dirac (0 : ℝ)
  haveI hμhfin : IsFiniteMeasure μh := by
    dsimp [μh]
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hh_int.hasFiniteIntegral
  have hμhFT : ∀ ξ : ℝ, measureFT μh ξ = FT h ξ := by
    intro ξ
    have hdens_meas : Measurable (fun x : ℝ => ENNReal.ofReal (h x)) :=
      hh_meas.ennreal_ofReal
    have hdens_top : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), ENNReal.ofReal (h x) < ⊤ := by
      exact Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
    unfold measureFT FT μh
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
    apply integral_congr_ae
    filter_upwards with y
    rw [ENNReal.toReal_ofReal (hh_nonneg y)]
    simp [mul_comm]
  have hδFT : ∀ ξ : ℝ, measureFT δ ξ = 1 := by
    intro ξ
    unfold measureFT δ
    rw [MeasureTheory.integral_dirac]
    simp
  have hmeq : μh = δ := by
    exact measure_unique μh δ (fun ξ => by rw [hμhFT ξ, hδFT ξ, hFT ξ])
  have hμsingle : μh ({0} : Set ℝ) = 0 := by
    have hvolsingle : (volume : Measure ℝ) ({0} : Set ℝ) = 0 := by
      simp
    exact MeasureTheory.withDensity_absolutelyContinuous (volume : Measure ℝ)
      (fun x => ENNReal.ofReal (h x))
      hvolsingle
  have hδzero : δ ({0} : Set ℝ) = 0 := by
    simpa [hmeq] using hμsingle
  have hδone : δ ({0} : Set ℝ) = 1 := by
    simp [δ]
  rw [hδone] at hδzero
  norm_num at hδzero

private theorem exists_ae_eq_in_Ioo (f g : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hae : f =ᵐ[volume] g) :
    ∃ x, x ∈ Set.Ioo a b ∧ f x = g x := by
  have hμ : (volume : Measure ℝ) (Set.Ioo a b) ≠ 0 := by
    apply ne_of_gt
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact Measure.exists_mem_of_measure_ne_zero_of_ae (μ := volume) (s := Set.Ioo a b) hμ
    (ae_restrict_of_ae hae)

private theorem continuous_close (h : ℝ → ℝ) (t0 eps : ℝ) (hh : Continuous h)
    (heps : 0 < eps) :
    ∃ δ > 0, ∀ x, |x - t0| < δ → |h x - h t0| < eps := by
  have htend : Filter.Tendsto h (nhds t0) (nhds (h t0)) := hh.continuousAt
  rw [Metric.tendsto_nhds_nhds] at htend
  rcases htend eps heps with ⟨δ, hδ, hδprop⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hd : dist x t0 < δ := by simpa [Real.dist_eq, abs_sub_comm] using hx
  have := hδprop hd
  simpa [Real.dist_eq] using this


theorem one_factor (β : ℝ) (hβ : β ≠ 0) :
  ¬ ∃ h : ℝ → ℝ,
    Continuous h ∧ (∀ x : ℝ, 0 ≤ h x) ∧ Integrable h ∧
      (∀ ξ : ℝ, FT h ξ = expFactor β ξ) := by
  rintro ⟨h, hh_cont, hh_nonneg, hh_int, hFT⟩
  rcases q_formula β hβ with ⟨hq_pos, hq_neg, hq_meas, hq_bound, hq_int, _hq_mass⟩
  have hae_qh : centeredExp β =ᵐ[volume] h := by
    exact fn_unique (centeredExp β) h hq_meas hh_cont.measurable
      (fun x => (hq_bound x).1) hh_nonneg hq_int hh_int
      (fun ξ => by rw [(q_FT β hβ).1 ξ, hFT ξ])
  have hae_hq : h =ᵐ[volume] centeredExp β := hae_qh.symm
  by_cases hβpos : 0 < β
  · let t0 : ℝ := -β
    have hbranch := hq_pos hβpos
    have ht0_zero : h t0 = 0 := by
      have hnotpos : ¬ 0 < h t0 := by
        intro ht0_pos
        rcases continuous_close h t0 (h t0 / 2) hh_cont (by linarith) with
          ⟨δ, hδ, hδclose⟩
        let η : ℝ := δ / 2
        have hη : 0 < η := by change 0 < δ / 2; linarith
        rcases exists_ae_eq_in_Ioo h (centeredExp β) (a := t0 - η) (b := t0)
            (by linarith) hae_hq with ⟨x, hxI, hx_eq⟩
        have hx_lt : x < -β := by simpa [t0] using hxI.2
        have hqx : centeredExp β x = 0 := hbranch.2 x hx_lt
        have hxzero : h x = 0 := by rw [hx_eq, hqx]
        have hdist : |x - t0| < δ := by
          have hx_lower : t0 - η < x := hxI.1
          have hx_upper : x < t0 := hxI.2
          have hnonpos : x - t0 < 0 := by linarith
          rw [abs_of_neg hnonpos]
          change -(x - t0) < δ
          linarith [show η = δ / 2 by rfl]
        have hclose := hδclose x hdist
        rw [hxzero] at hclose
        have habs : |0 - h t0| = h t0 := by simpa using abs_of_pos ht0_pos
        rw [habs] at hclose
        linarith
      exact le_antisymm (not_lt.mp hnotpos) (hh_nonneg t0)
    let c : ℝ := (1 / β) * Real.exp (-1)
    have hc_pos : 0 < c := by
      dsimp [c]
      exact mul_pos (one_div_pos.mpr hβpos) (Real.exp_pos _)
    rcases continuous_close h t0 (c / 2) hh_cont (by linarith) with
      ⟨δ, hδ, hδclose⟩
    let η : ℝ := min δ β / 2
    have hmin_pos : 0 < min δ β := lt_min hδ hβpos
    have hη : 0 < η := by change 0 < min δ β / 2; linarith
    rcases exists_ae_eq_in_Ioo h (centeredExp β) (a := t0) (b := t0 + η)
        (by linarith) hae_hq with ⟨y, hyI, hy_eq⟩
    have hy_dist : |y - t0| < δ := by
      have hy_lower : t0 < y := hyI.1
      have hy_upper : y < t0 + η := hyI.2
      have hposdiff : 0 ≤ y - t0 := by linarith
      rw [abs_of_nonneg hposdiff]
      have hη_lt_delta : η < δ := by
        change min δ β / 2 < δ
        have hmin_le : min δ β ≤ δ := min_le_left δ β
        linarith
      linarith
    have hy_le_branch : -β ≤ y := by simpa [t0] using le_of_lt hyI.1
    have hqy_formula : centeredExp β y = (1 / β) * Real.exp (-(y + β) / β) :=
      hbranch.1 y hy_le_branch
    have hu_le_one : (y + β) / β ≤ 1 := by
      have hy_upper : y < t0 + η := hyI.2
      have hη_le_beta : η ≤ β := by
        change min δ β / 2 ≤ β
        have hmin_le : min δ β ≤ β := min_le_right δ β
        linarith
      have hyb_le : y + β ≤ β := by
        dsimp [t0] at hy_upper
        linarith
      exact (div_le_one hβpos).mpr hyb_le
    have hexp_ge : Real.exp (-1) ≤ Real.exp (-(y + β) / β) := by
      apply Real.exp_le_exp.mpr
      have hneg : -1 ≤ -((y + β) / β) := by linarith
      convert hneg using 1
      ring
    have hq_ge : c ≤ centeredExp β y := by
      rw [hqy_formula]
      dsimp [c]
      exact mul_le_mul_of_nonneg_left hexp_ge (le_of_lt (one_div_pos.mpr hβpos))
    have hy_ge : c ≤ h y := by rwa [hy_eq]
    have hclose := hδclose y hy_dist
    rw [ht0_zero] at hclose
    have habs : |h y - 0| = h y := by simpa using abs_of_nonneg (hh_nonneg y)
    rw [habs] at hclose
    linarith
  · have hβneg : β < 0 := lt_of_le_of_ne (le_of_not_gt hβpos) hβ
    let t0 : ℝ := -β
    have hbranch := hq_neg hβneg
    have ht0_zero : h t0 = 0 := by
      have hnotpos : ¬ 0 < h t0 := by
        intro ht0_pos
        rcases continuous_close h t0 (h t0 / 2) hh_cont (by linarith) with
          ⟨δ, hδ, hδclose⟩
        let η : ℝ := δ / 2
        have hη : 0 < η := by change 0 < δ / 2; linarith
        rcases exists_ae_eq_in_Ioo h (centeredExp β) (a := t0) (b := t0 + η)
            (by linarith) hae_hq with ⟨x, hxI, hx_eq⟩
        have hx_gt : -β < x := by simpa [t0] using hxI.1
        have hqx : centeredExp β x = 0 := hbranch.2 x hx_gt
        have hxzero : h x = 0 := by rw [hx_eq, hqx]
        have hdist : |x - t0| < δ := by
          have hx_lower : t0 < x := hxI.1
          have hx_upper : x < t0 + η := hxI.2
          have hnonneg : 0 ≤ x - t0 := by linarith
          rw [abs_of_nonneg hnonneg]
          change x - t0 < δ
          linarith [show η = δ / 2 by rfl]
        have hclose := hδclose x hdist
        rw [hxzero] at hclose
        have habs : |0 - h t0| = h t0 := by simpa using abs_of_pos ht0_pos
        rw [habs] at hclose
        linarith
      exact le_antisymm (not_lt.mp hnotpos) (hh_nonneg t0)
    let c : ℝ := (1 / (-β)) * Real.exp (-1)
    have hnegb_pos : 0 < -β := by linarith
    have hc_pos : 0 < c := by
      dsimp [c]
      exact mul_pos (one_div_pos.mpr hnegb_pos) (Real.exp_pos _)
    rcases continuous_close h t0 (c / 2) hh_cont (by linarith) with
      ⟨δ, hδ, hδclose⟩
    let η : ℝ := min δ (-β) / 2
    have hmin_pos : 0 < min δ (-β) := lt_min hδ hnegb_pos
    have hη : 0 < η := by change 0 < min δ (-β) / 2; linarith
    rcases exists_ae_eq_in_Ioo h (centeredExp β) (a := t0 - η) (b := t0)
        (by linarith) hae_hq with ⟨y, hyI, hy_eq⟩
    have hy_dist : |y - t0| < δ := by
      have hy_lower : t0 - η < y := hyI.1
      have hy_upper : y < t0 := hyI.2
      have hnegdiff : y - t0 < 0 := by linarith
      rw [abs_of_neg hnegdiff]
      have hη_lt_delta : η < δ := by
        change min δ (-β) / 2 < δ
        have hmin_le : min δ (-β) ≤ δ := min_le_left δ (-β)
        linarith
      linarith
    have hy_le_branch : y ≤ -β := by simpa [t0] using le_of_lt hyI.2
    have hqy_formula : centeredExp β y = (1 / (-β)) * Real.exp ((y + β) / (-β)) :=
      hbranch.1 y hy_le_branch
    have hu_ge_neg_one : -1 ≤ (y + β) / (-β) := by
      have hy_lower : t0 - η < y := hyI.1
      have hη_le_negb : η ≤ -β := by
        change min δ (-β) / 2 ≤ -β
        have hmin_le : min δ (-β) ≤ -β := min_le_right δ (-β)
        linarith
      have hy_nonneg : 0 ≤ y := by
        dsimp [t0] at hy_lower
        linarith
      have hmul : -1 * (-β) ≤ y + β := by linarith
      exact (le_div_iff₀ hnegb_pos).mpr hmul
    have hexp_ge : Real.exp (-1) ≤ Real.exp ((y + β) / (-β)) := by
      exact Real.exp_le_exp.mpr hu_ge_neg_one
    have hq_ge : c ≤ centeredExp β y := by
      rw [hqy_formula]
      dsimp [c]
      exact mul_le_mul_of_nonneg_left hexp_ge (le_of_lt (one_div_pos.mpr hnegb_pos))
    have hy_ge : c ≤ h y := by rwa [hy_eq]
    have hclose := hδclose y hy_dist
    rw [ht0_zero] at hclose
    have habs : |h y - 0| = h y := by simpa using abs_of_nonneg (hh_nonneg y)
    rw [habs] at hclose
    linarith


def gaussianKernel (γ : ℝ) : ℝ → ℝ :=
  fun x => Real.sqrt (Real.pi / γ) * Real.exp (-(Real.pi ^ 2) * x ^ 2 / γ)


theorem gaussian (γ : ℝ) (hγ : 0 < γ) :
  Continuous (gaussianKernel γ) ∧
    (∀ x : ℝ, 0 < gaussianKernel γ x) ∧
    Integrable (gaussianKernel γ) ∧
    (∫ x : ℝ, gaussianKernel γ x) = 1 ∧
    (∃ A L : ℝ, 0 < A ∧ 0 < L ∧
      (∀ x : ℝ, gaussianKernel γ x ≤ A) ∧
      (∀ x y : ℝ, |gaussianKernel γ x - gaussianKernel γ y| ≤ L * |x - y|)) ∧
    ∀ ξ : ℝ, FT (gaussianKernel γ) ξ = Complex.exp (-(γ : ℂ) * ξ ^ 2) := by
  have hcont : Continuous (gaussianKernel γ) := by
    unfold gaussianKernel
    fun_prop
  have hpos : ∀ x : ℝ, 0 < gaussianKernel γ x := by
    intro x
    unfold gaussianKernel
    positivity
  have hint : Integrable (gaussianKernel γ) := by
    unfold gaussianKernel
    have hB : 0 < Real.pi ^ 2 / γ := by positivity
    convert (integrable_exp_neg_mul_sq hB).const_mul (Real.sqrt (Real.pi / γ)) using 1
    ext x
    congr 1
    field_simp [ne_of_gt hγ]
  have hmass : (∫ x : ℝ, gaussianKernel γ x) = 1 := by
    unfold gaussianKernel
    have hfun : (fun x : ℝ => Real.exp (-(Real.pi ^ 2) * x ^ 2 / γ)) =
        fun x : ℝ => Real.exp (-(Real.pi ^ 2 / γ) * x ^ 2) := by
      funext x
      congr 1
      field_simp [ne_of_gt hγ]
    calc
      (∫ x : ℝ, Real.sqrt (Real.pi / γ) *
          Real.exp (-(Real.pi ^ 2) * x ^ 2 / γ)) =
          Real.sqrt (Real.pi / γ) *
            ∫ x : ℝ, Real.exp (-(Real.pi ^ 2) * x ^ 2 / γ) := by
        rw [integral_const_mul]
      _ = Real.sqrt (Real.pi / γ) *
            ∫ x : ℝ, Real.exp (-(Real.pi ^ 2 / γ) * x ^ 2) := by
        rw [hfun]
      _ = Real.sqrt (Real.pi / γ) * Real.sqrt (Real.pi / (Real.pi ^ 2 / γ)) := by
        rw [integral_gaussian]
      _ = 1 := by
        have h1 : Real.pi / (Real.pi ^ 2 / γ) = γ / Real.pi := by
          field_simp [Real.pi_ne_zero, ne_of_gt hγ]
        rw [h1]
        have hnonneg1 : 0 ≤ Real.pi / γ := by positivity
        rw [← Real.sqrt_mul hnonneg1 (γ / Real.pi)]
        have hmul : Real.pi / γ * (γ / Real.pi) = 1 := by
          field_simp [Real.pi_ne_zero, ne_of_gt hγ]
        rw [hmul, Real.sqrt_one]
  have hLip : ∃ A L : ℝ, 0 < A ∧ 0 < L ∧
      (∀ x : ℝ, gaussianKernel γ x ≤ A) ∧
      (∀ x y : ℝ, |gaussianKernel γ x - gaussianKernel γ y| ≤ L * |x - y|) := by
    let A : ℝ := Real.sqrt (Real.pi / γ)
    let B : ℝ := Real.pi ^ 2 / γ
    let L : ℝ := A * (2 * B) * (Real.sqrt B)⁻¹
    have hA : 0 < A := by dsimp [A]; positivity
    have hB : 0 < B := by dsimp [B]; positivity
    have hL : 0 < L := by dsimp [L]; positivity
    have hfun : gaussianKernel γ = fun x : ℝ => A * Real.exp (-(B * x ^ 2)) := by
      funext x
      unfold gaussianKernel
      dsimp [A, B]
      congr 1
      field_simp [ne_of_gt hγ]
    refine ⟨A, L, hA, hL, ?_, ?_⟩
    · intro x
      rw [hfun]
      have hexp_le : Real.exp (-(B * x ^ 2)) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hnonneg : 0 ≤ B * x ^ 2 := mul_nonneg hB.le (sq_nonneg x)
        linarith
      exact mul_le_of_le_one_right hA.le hexp_le
    · intro x y
      have hdiff : ∀ z ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (gaussianKernel γ) z := by
        intro z _hz
        rw [hfun]
        fun_prop
      have hbound : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv (gaussianKernel γ) z‖ ≤ L := by
        intro z _hz
        rw [hfun]
        have hderiv : deriv (fun x : ℝ => A * Real.exp (-(B * x ^ 2))) z =
            A * (Real.exp (-(B * z ^ 2)) * (-(2 * B * z))) := by
          have hdiff_exp : DifferentiableAt ℝ
              (fun x : ℝ => Real.exp (-(B * x ^ 2))) z := by
            fun_prop
          rw [deriv_const_mul A hdiff_exp]
          rw [deriv_exp (by fun_prop :
            DifferentiableAt ℝ (fun x : ℝ => -(B * x ^ 2)) z)]
          have hinner : deriv (fun x : ℝ => -(B * x ^ 2)) z = -(2 * B * z) := by
            have hfun_inner : (fun x : ℝ => -(B * x ^ 2)) =
                fun x : ℝ => (-B) * x ^ 2 := by
              funext w
              ring
            rw [hfun_inner]
            rw [deriv_const_mul (-B)
              (by fun_prop : DifferentiableAt ℝ (fun x : ℝ => x ^ 2) z)]
            rw [deriv_fun_pow (differentiableAt_fun_id :
              DifferentiableAt ℝ (fun x : ℝ => x) z) 2]
            simp
            ring
          rw [hinner]
        rw [hderiv]
        dsimp [L]
        have hrewrite : A * (Real.exp (-(B * z ^ 2)) * (-(2 * B * z))) =
            -(A * (2 * B)) * Real.mulExpNegMulSq B z := by
          unfold Real.mulExpNegMulSq
          rw [show B * z * z = B * z ^ 2 by ring]
          ring
        rw [hrewrite, abs_mul, abs_neg]
        have hfactor_pos : 0 < A * (2 * B) := by positivity
        rw [abs_of_pos hfactor_pos]
        exact mul_le_mul_of_nonneg_left (Real.abs_mulExpNegMulSq_le hB) hfactor_pos.le
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
        (f := gaussianKernel γ) (C := L) hdiff hbound convex_univ
        (Set.mem_univ y) (Set.mem_univ x)
      simpa [Real.norm_eq_abs] using hmv
  have hFT : ∀ ξ : ℝ, FT (gaussianKernel γ) ξ = Complex.exp (-(γ : ℂ) * ξ ^ 2) := by
    intro ξ
    have hFT_as_fourier :
        FT (gaussianKernel γ) ξ =
          (Real.sqrt (Real.pi / γ) : ℂ) *
            FourierTransform.fourier
              (fun x : ℝ => Complex.exp (-Real.pi * (Real.pi / γ : ℂ) * x ^ 2)) ξ := by
      unfold FT gaussianKernel
      rw [Real.fourier_real_eq_integral_exp_smul]
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp [Complex.ofReal_exp]
      ring_nf
    have hb : 0 < ((Real.pi / γ : ℂ).re) := by
      simp
      positivity
    have hfourier := congrFun (fourier_gaussian_pi hb) ξ
    have hpref :
        (Real.sqrt (Real.pi / γ) : ℂ) *
          (1 / ((Real.pi / γ : ℂ) ^ (1 / 2 : ℂ))) = 1 := by
      have ha_pos : 0 < Real.pi / γ := by positivity
      have hpow : ((Real.pi / γ : ℂ) ^ (1 / 2 : ℂ)) =
          (Real.sqrt (Real.pi / γ) : ℂ) := by
        have ha : 0 ≤ Real.pi / γ := by positivity
        rw [← Complex.ofReal_div]
        rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha]
        norm_num
      rw [hpow]
      rw [one_div]
      exact mul_inv_cancel₀
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr ha_pos)))
    have harg :
        -↑Real.pi / (↑Real.pi / ↑γ : ℂ) * ↑ξ ^ 2 = -↑γ * ↑ξ ^ 2 := by
      have hb_ne : (↑Real.pi / ↑γ : ℂ) ≠ 0 := by
        exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
          (Complex.ofReal_ne_zero.mpr (ne_of_gt hγ))
      field_simp [hb_ne]
    rw [hFT_as_fourier, hfourier]
    calc
      (Real.sqrt (Real.pi / γ) : ℂ) *
          (1 / (Real.pi / γ : ℂ) ^ (1 / 2 : ℂ) *
            Complex.exp (-↑Real.pi / (↑Real.pi / ↑γ) * ↑ξ ^ 2)) =
          ((Real.sqrt (Real.pi / γ) : ℂ) *
            (1 / (Real.pi / γ : ℂ) ^ (1 / 2 : ℂ))) *
            Complex.exp (-↑Real.pi / (↑Real.pi / ↑γ) * ↑ξ ^ 2) := by
        ring
      _ = Complex.exp (-↑Real.pi / (↑Real.pi / ↑γ) * ↑ξ ^ 2) := by
        rw [hpref]
        simp
      _ = Complex.exp (-(γ : ℂ) * ξ ^ 2) := by
        rw [harg]
  exact ⟨hcont, hpos, hint, hmass, hLip, hFT⟩

end

end Part8
