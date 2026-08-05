import LeanCode.Vendor.E5.P5.Part5.Basic
import LeanCode.Vendor.E5.P5.Part5.SignChanges
import LeanCode.Vendor.E5.Defs
open VendorE5






open MeasureTheory

namespace Part5


noncomputable def roundMap (N : ℕ) (y : ℝ) : ℝ := (⌈(N : ℝ) * y⌉ : ℝ) / (N : ℝ)


noncomputable def gridPoint (N j : ℕ) : ℝ := ((j : ℝ) - (N : ℝ) ^ 2) / (N : ℝ)


noncomputable def riemannSum (g : ℝ → ℝ) (p : Polynomial ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (2 * N ^ 2),
    (1 / (N : ℝ)) * g (x - gridPoint N j) * p.eval (gridPoint N j)



theorem phi_props (N : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    0 ≤ roundMap N y - y ∧ roundMap N y - y < 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : (N : ℝ) * y ≤ (⌈(N : ℝ) * y⌉ : ℝ) := Int.le_ceil _
  have hlt : (⌈(N : ℝ) * y⌉ : ℝ) < (N : ℝ) * y + 1 := Int.ceil_lt_add_one _
  have hy : (N : ℝ) * y / (N : ℝ) = y := mul_div_cancel_left₀ y hNpos.ne'
  have heq : roundMap N y - y = ((⌈(N : ℝ) * y⌉ : ℝ) - (N : ℝ) * y) / (N : ℝ) := by
    unfold roundMap; rw [sub_div, hy]
  rw [heq]
  refine ⟨div_nonneg (by linarith) hNpos.le, ?_⟩
  have hnum : (0 : ℝ) < 1 - ((⌈(N : ℝ) * y⌉ : ℝ) - (N : ℝ) * y) := by linarith
  have hdiv := div_pos hnum hNpos
  rw [sub_div] at hdiv
  linarith



theorem rounding_identity (g : ℝ → ℝ) (hg : Continuous g) (C c : ℝ) (hC : 0 < C)
    (hc : 0 < c) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (p : Polynomial ℝ) (x : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∫ y in Set.Ioc (-(N : ℝ)) (N : ℝ),
        g (x - roundMap N y) * p.eval (roundMap N y))
      = riemannSum g p N x := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  set a : ℕ → ℝ := fun k => ((k : ℝ) - (N : ℝ) ^ 2) / (N : ℝ) with ha_def
  set F : ℝ → ℝ := fun y => g (x - roundMap N y) * p.eval (roundMap N y) with hF_def
  have ha0 : a 0 = -(N : ℝ) := by
    simp only [ha_def, Nat.cast_zero, zero_sub, neg_div]
    rw [sq, mul_div_assoc, div_self hNne, mul_one]
  have haN : a (2 * N ^ 2) = (N : ℝ) := by
    simp only [ha_def]
    have hcast : ((2 * N ^ 2 : ℕ) : ℝ) = 2 * (N : ℝ) ^ 2 := by push_cast; ring
    rw [hcast, show 2 * (N : ℝ) ^ 2 - (N : ℝ) ^ 2 = (N : ℝ) ^ 2 by ring, sq,
      mul_div_assoc, div_self hNne, mul_one]
  have ha_mono : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k
    simp only [ha_def]
    apply div_le_div_of_nonneg_right ?_ hNpos.le
    push_cast; linarith
  have ha_len : ∀ k : ℕ, a (k + 1) - a k = 1 / (N : ℝ) := by
    intro k
    simp only [ha_def]
    rw [div_sub_div_same]
    congr 1
    push_cast; ring
  have hceil : ∀ (k : ℕ), ∀ y ∈ Set.Ioc (a k) (a (k+1)),
      (⌈(N : ℝ) * y⌉ : ℝ) = ((k : ℝ) + 1 - (N : ℝ) ^ 2) := by
    intro k y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hlow : (k : ℝ) - (N : ℝ) ^ 2 < (N : ℝ) * y := by
      have h := (div_lt_iff₀ hNpos).mp hy1
      rw [mul_comm] at h; linarith
    have hupp : (N : ℝ) * y ≤ (k : ℝ) + 1 - (N : ℝ) ^ 2 := by
      have h := (le_div_iff₀ hNpos).mp hy2
      rw [mul_comm] at h
      have hcast : ((k : ℝ) + 1 - (N : ℝ) ^ 2) = ((↑(k+1) : ℝ) - (N : ℝ) ^ 2) := by
        push_cast; ring
      rw [hcast]; exact h
    have hz : ⌈(N : ℝ) * y⌉ = ((k : ℤ) + 1 - (N : ℤ) ^ 2) := by
      rw [Int.ceil_eq_iff]
      refine ⟨?_, ?_⟩
      · push_cast; linarith
      · push_cast; linarith
    rw [hz]; push_cast; ring
  have hround : ∀ (k : ℕ), ∀ y ∈ Set.Ioc (a k) (a (k+1)),
      roundMap N y = gridPoint N (k+1) := by
    intro k y hy
    unfold roundMap gridPoint
    rw [hceil k y hy]; push_cast; ring
  have hcell : ∀ (k : ℕ), ∀ y ∈ Set.Ioc (a k) (a (k+1)),
      F y = g (x - gridPoint N (k+1)) * p.eval (gridPoint N (k+1)) := by
    intro k y hy
    simp only [hF_def, hround k y hy]
  have hint : ∀ k < 2 * N ^ 2, IntervalIntegrable F MeasureTheory.volume (a k) (a (k+1)) := by
    intro k _
    have hEq : Set.EqOn (fun _ : ℝ => g (x - gridPoint N (k+1)) * p.eval (gridPoint N (k+1))) F
        (Set.uIoc (a k) (a (k+1))) := by
      intro y hy
      rw [Set.uIoc_of_le (ha_mono k)] at hy
      exact (hcell k y hy).symm
    exact (intervalIntegrable_const).congr hEq
  have hval : ∀ k : ℕ,
      (∫ y in a k..a (k+1), F y)
        = (1 / (N : ℝ)) * g (x - gridPoint N (k+1)) * p.eval (gridPoint N (k+1)) := by
    intro k
    have hEqOo : Set.EqOn F (fun _ => g (x - gridPoint N (k+1)) * p.eval (gridPoint N (k+1)))
        (Set.Ioo (a k) (a (k+1))) := by
      intro y hy
      exact hcell k y ⟨hy.1, hy.2.le⟩
    rw [intervalIntegral.integral_congr_Ioo_of_le (ha_mono k) hEqOo,
      intervalIntegral.integral_const, ha_len k, smul_eq_mul]
    ring
  have hle : a 0 ≤ a (2 * N ^ 2) := by rw [ha0, haN]; linarith
  have hstep1 : (∫ y in Set.Ioc (-(N : ℝ)) (N : ℝ), F y)
      = ∑ k ∈ Finset.range (2 * N ^ 2),
          (1 / (N : ℝ)) * g (x - gridPoint N (k+1)) * p.eval (gridPoint N (k+1)) := by
    have e1 : (∫ y in Set.Ioc (-(N : ℝ)) (N : ℝ), F y)
        = ∫ y in Set.Ioc (a 0) (a (2 * N ^ 2)), F y := by rw [ha0, haN]
    rw [e1, ← intervalIntegral.integral_of_le hle,
      ← intervalIntegral.sum_integral_adjacent_intervals hint]
    exact Finset.sum_congr rfl (fun k _ => hval k)
  rw [show (∫ y in Set.Ioc (-(N : ℝ)) (N : ℝ),
        g (x - roundMap N y) * p.eval (roundMap N y))
      = ∫ y in Set.Ioc (-(N : ℝ)) (N : ℝ), F y from rfl, hstep1]
  unfold riemannSum
  refine Finset.sum_bij' (fun k _ => k + 1) (fun j _ => j - 1) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc]
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_range]
    omega
  · intro k hk
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    omega
  · intro k hk
    rfl



private theorem envProfile_integrable (d : ℕ) (c : ℝ) (hc : 0 < c) :
    MeasureTheory.Integrable
      (fun y : ℝ => (|y| + 1) ^ d * Real.exp (-c * |y|)) := by
  have heq : (fun y : ℝ => (|y| + 1) ^ d * Real.exp (-c * |y|))
      = fun y => ∑ m ∈ Finset.range (d + 1),
          (d.choose m : ℝ) * (|y| ^ m * Real.exp (-c * |y|)) := by
    funext y
    rw [add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [one_pow, mul_one]
    ring
  rw [heq]
  refine MeasureTheory.integrable_finsetSum _ (fun m _ => ?_)
  exact (polyexp_integrable m c hc).const_mul (d.choose m : ℝ)


private theorem env_pointwise_bound (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)) (p : Polynomial ℝ) (x : ℝ)
    (y z : ℝ) (hz : |z - y| ≤ 1) :
    |g (x - z) * p.eval z|
      ≤ C * Real.exp (c * (|x| + 1))
          * (∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|)
          * ((|y| + 1) ^ p.natDegree * Real.exp (-c * |y|)) := by
  have habsz : |z| ≤ |y| + 1 := by
    have h := abs_add_le (z - y) y
    have : |z| ≤ |z - y| + |y| := by simpa [sub_add_cancel] using h
    linarith
  have hxz : |x - z| ≥ |x - y| - 1 := by
    have h := abs_add_le (x - z) (z - y)
    have heq : (x - z) + (z - y) = x - y := by ring
    rw [heq] at h; linarith
  have hgbound : |g (x - z)| ≤ C * Real.exp (c * (|x| + 1)) * Real.exp (-c * |y|) := by
    have htri2 : |x - y| ≥ |y| - |x| := by
      have h := abs_add_le (y - x) x
      have heq : (y - x) + x = y := by ring
      rw [heq, abs_sub_comm] at h; linarith
    calc |g (x - z)| ≤ C * Real.exp (-c * |x - z|) := hbound (x - z)
      _ ≤ C * Real.exp (c * (|x| + 1)) * Real.exp (-c * |y|) := by
          rw [mul_assoc, ← Real.exp_add]
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left hxz hc.le,
            mul_le_mul_of_nonneg_left htri2 hc.le]
  have hpbound : |p.eval z|
      ≤ (∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|) * (|y| + 1) ^ p.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun k hk => ?_)
    rw [abs_mul, abs_pow]
    have hbase : (1 : ℝ) ≤ |y| + 1 := by have := abs_nonneg y; linarith
    have hzk : |z| ^ k ≤ (|y| + 1) ^ p.natDegree :=
      le_trans (pow_le_pow_left₀ (abs_nonneg z) habsz k)
        (pow_le_pow_right₀ hbase (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    exact mul_le_mul_of_nonneg_left hzk (abs_nonneg _)
  rw [abs_mul]
  calc |g (x - z)| * |p.eval z|
      ≤ (C * Real.exp (c * (|x| + 1)) * Real.exp (-c * |y|))
          * ((∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|)
              * (|y| + 1) ^ p.natDegree) :=
        mul_le_mul hgbound hpbound (abs_nonneg _) (by positivity)
    _ = C * Real.exp (c * (|x| + 1))
          * (∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|)
          * ((|y| + 1) ^ p.natDegree * Real.exp (-c * |y|)) := by ring



theorem envelope (g : ℝ → ℝ) (hg : Continuous g) (C c : ℝ) (hC : 0 < C)
    (hc : 0 < c) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (p : Polynomial ℝ) (x : ℝ) :
    ∃ G : ℝ → ℝ, MeasureTheory.Integrable G ∧
      (∀ y : ℝ, |g (x - y) * p.eval y| ≤ G y) ∧
      (∀ (N : ℕ), 1 ≤ N → ∀ y : ℝ,
        |Set.indicator (Set.Ioc (-(N : ℝ)) (N : ℝ))
          (fun y => g (x - roundMap N y) * p.eval (roundMap N y)) y| ≤ G y) := by
  refine ⟨fun y => C * Real.exp (c * (|x| + 1))
      * (∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|)
      * ((|y| + 1) ^ p.natDegree * Real.exp (-c * |y|)), ?_, ?_, ?_⟩
  · exact (envProfile_integrable p.natDegree c hc).const_mul _
  · intro y
    exact env_pointwise_bound g C c hC hc hbound p x y y (by simp)
  · intro N hN y
    have hphi := phi_props N hN y
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hinv : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact_mod_cast hN
    have hzy : |roundMap N y - y| ≤ 1 := by
      rw [abs_of_nonneg hphi.1]; linarith [hphi.2]
    calc |Set.indicator (Set.Ioc (-(N : ℝ)) (N : ℝ))
            (fun y => g (x - roundMap N y) * p.eval (roundMap N y)) y|
        ≤ |g (x - roundMap N y) * p.eval (roundMap N y)| := by
          rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
          exact norm_indicator_le_norm_self _ _
      _ ≤ C * Real.exp (c * (|x| + 1))
            * (∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|)
            * ((|y| + 1) ^ p.natDegree * Real.exp (-c * |y|)) :=
          env_pointwise_bound g C c hC hc hbound p x y (roundMap N y) hzy


theorem tail_truncation (f : ℝ → ℝ) (hf : MeasureTheory.Integrable f) :
    Filter.Tendsto (fun N : ℕ => ∫ y in Set.Ioc (-(N : ℝ)) (N : ℝ), f y)
      Filter.atTop (nhds (∫ y, f y)) := by
  have hconv : ∀ N : ℕ, (∫ y in Set.Ioc (-(N : ℝ)) (N : ℝ), f y)
      = ∫ y, (Set.Ioc (-(N : ℝ)) (N : ℝ)).indicator f y := by
    intro N; rw [MeasureTheory.integral_indicator measurableSet_Ioc]
  simp_rw [hconv]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun y => ‖f y‖)
  · exact fun N => (hf.indicator measurableSet_Ioc).aestronglyMeasurable
  · exact hf.norm
  · exact fun N => Filter.Eventually.of_forall
      (fun y => norm_indicator_le_norm_self f y)
  · filter_upwards with y
    have hev : ∀ᶠ N : ℕ in Filter.atTop,
        (Set.Ioc (-(N : ℝ)) (N : ℝ)).indicator f y = f y := by
      filter_upwards [Filter.eventually_gt_atTop ⌈|y|⌉₊] with N hN
      have hlt : |y| < (N : ℝ) := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)
      have hmem : y ∈ Set.Ioc (-(N : ℝ)) (N : ℝ) :=
        Set.mem_Ioc.mpr ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
      exact Set.indicator_of_mem hmem f
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hev)


theorem rounding_convergence (g : ℝ → ℝ) (hg : Continuous g) (C c : ℝ) (hC : 0 < C)
    (hc : 0 < c) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (p : Polynomial ℝ) (x : ℝ) :
    Filter.Tendsto (fun N : ℕ => riemannSum g p N x) Filter.atTop
      (nhds (convPoly g p x)) := by
  classical
  obtain ⟨G, hGint, hGbound1, hGbound2⟩ := envelope g hg C c hC hc hbound p x
  set H : ℕ → ℝ → ℝ := fun N y =>
    Set.indicator (Set.Ioc (-(N : ℝ)) (N : ℝ))
      (fun y => g (x - roundMap N y) * p.eval (roundMap N y)) y with hH_def
  set f : ℝ → ℝ := fun y => g (x - y) * p.eval y with hf_def
  have hround_meas : ∀ N : ℕ, Measurable (roundMap N) := by
    intro N
    unfold roundMap
    have h1 : Measurable fun y : ℝ => (N : ℝ) * y := measurable_const_mul _
    have h3 : Measurable fun y : ℝ => ((⌈(N : ℝ) * y⌉ : ℤ) : ℝ) :=
      Int.cast_continuous.measurable.comp (Int.measurable_ceil.comp h1)
    exact h3.div_const _
  have hRS : ∀ N : ℕ, 1 ≤ N → riemannSum g p N x = ∫ y, H N y := by
    intro N hN
    rw [← rounding_identity g hg C c hC hc hbound p x N hN,
      MeasureTheory.integral_indicator measurableSet_Ioc]
  have hEqEv : (fun N : ℕ => riemannSum g p N x) =ᶠ[Filter.atTop]
      (fun N : ℕ => ∫ y, H N y) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN using hRS N hN
  have hDCT : Filter.Tendsto (fun N : ℕ => ∫ y, H N y) Filter.atTop
      (nhds (∫ y, f y)) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence G
    · intro N
      refine (Measurable.aestronglyMeasurable ?_)
      refine Measurable.indicator ?_ measurableSet_Ioc
      exact ((hg.measurable.comp (measurable_const.sub (hround_meas N))).mul
        (p.continuous.measurable.comp (hround_meas N)))
    · exact hGint
    · intro N
      refine Filter.Eventually.of_forall (fun y => ?_)
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · have hempty : Set.Ioc (-((0 : ℕ) : ℝ)) ((0 : ℕ) : ℝ) = (∅ : Set ℝ) := by
          simp
        have h0 : H 0 y = 0 := by
          simp only [hH_def, hN0, hempty, Set.indicator_empty]
        rw [hN0, h0, norm_zero]
        exact (abs_nonneg _).trans (hGbound1 y)
      · rw [Real.norm_eq_abs]
        exact hGbound2 N hNpos y
    · refine Filter.Eventually.of_forall (fun y => ?_)
      have hrm : Filter.Tendsto (fun N : ℕ => roundMap N y) Filter.atTop (nhds y) := by
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
          (g := fun _ : ℕ => y) (h := fun N : ℕ => y + 1 / (N : ℝ))
          tendsto_const_nhds ?_ ?_ ?_
        · have h2 := (tendsto_const_nhds (x := y)).add
            tendsto_one_div_atTop_nhds_zero_nat
          simpa using h2
        · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
          have := (phi_props N hN y).1
          linarith
        · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
          have := (phi_props N hN y).2
          linarith
      have hcont : Filter.Tendsto
          (fun N : ℕ => g (x - roundMap N y) * p.eval (roundMap N y))
          Filter.atTop (nhds (f y)) := by
        have hg' : Filter.Tendsto (fun N : ℕ => g (x - roundMap N y))
            Filter.atTop (nhds (g (x - y))) :=
          (hg.tendsto (x - y)).comp (tendsto_const_nhds.sub hrm)
        have hp' : Filter.Tendsto (fun N : ℕ => p.eval (roundMap N y))
            Filter.atTop (nhds (p.eval y)) :=
          (p.continuous.tendsto y).comp hrm
        exact hg'.mul hp'
      refine hcont.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop ⌈|y|⌉₊,
        Filter.eventually_ge_atTop 1] with N hNgt hN1
      have hlt : |y| < (N : ℝ) := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNgt)
      have hmem : y ∈ Set.Ioc (-(N : ℝ)) (N : ℝ) :=
        Set.mem_Ioc.mpr ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
      simp only [hH_def, Set.indicator_of_mem hmem]
  have hgoal : convPoly g p x = ∫ y, f y := rfl
  rw [hgoal]
  exact hDCT.congr' hEqEv.symm


theorem matrix_TN (g : ℝ → ℝ) (htp : IsTotallyPositive g) (m K : ℕ) (hm : 1 ≤ m)
    (hK : 1 ≤ K) (x : Fin m → ℝ) (hx : StrictMono x) (y : Fin K → ℝ)
    (hy : StrictMono y) :
    TotallyNonneg (Matrix.of (fun i j => g (x i - y j))) := by
  intro k r c hr hc
  exact htp k (fun i => x (r i)) (fun j => y (c j)) (hx.comp hr) (hy.comp hc)



theorem integral_VD (h3 : Statement_Part_3) (g : ℝ → ℝ) (hg : Continuous g)
    (htp : IsTotallyPositive g) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)) (p : Polynomial ℝ)
    (s : ℕ) (hsc : SignChangesFnGE (fun x => convPoly g p x) s) :
    SignChangesFnGE (fun x => p.eval x) s := by
  classical
  obtain ⟨xx, hxmono, ε, hε, hpos0⟩ := hsc
  have hpos : ∀ i : Fin (s + 1), 0 < ε * (-1 : ℝ) ^ (i : ℕ) * convPoly g p (xx i) :=
    fun i => hpos0 i
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hne : ∀ i, convPoly g p (xx i) ≠ 0 := by
    intro i hzero
    have := hpos i
    rw [hzero, mul_zero] at this
    exact lt_irrefl _ this
  set δ : ℝ := (1 / 2) *
      Finset.inf' Finset.univ ⟨0, Finset.mem_univ 0⟩
        (fun i => |convPoly g p (xx i)|) with hδ_def
  have hδpos : 0 < δ := by
    rw [hδ_def]
    apply mul_pos (by norm_num)
    rw [Finset.lt_inf'_iff]
    intro i _
    exact abs_pos.mpr (hne i)
  have hsign : ∀ i : Fin (s + 1), |ε * (-1 : ℝ) ^ (i : ℕ)| = 1 := by
    intro i
    rw [abs_mul, hεabs, one_mul, abs_pow, abs_neg, abs_one, one_pow]
  have hge : ∀ i : Fin (s + 1), ε * (-1 : ℝ) ^ (i : ℕ) * convPoly g p (xx i) ≥ 2 * δ := by
    intro i
    have hp := hpos i
    have habs : ε * (-1 : ℝ) ^ (i : ℕ) * convPoly g p (xx i)
        = |convPoly g p (xx i)| := by
      rw [← abs_of_nonneg (le_of_lt hp), abs_mul, hsign i, one_mul]
    rw [habs, hδ_def]
    have hmin : Finset.inf' Finset.univ ⟨0, Finset.mem_univ 0⟩
        (fun i => |convPoly g p (xx i)|) ≤ |convPoly g p (xx i)| :=
      Finset.inf'_le _ (Finset.mem_univ i)
    linarith
  have hconv : ∀ i, Filter.Tendsto (fun N : ℕ => riemannSum g p N (xx i))
      Filter.atTop (nhds (convPoly g p (xx i))) :=
    fun i => rounding_convergence g hg C c hC hc hbound p (xx i)
  have hNi : ∀ i, ∃ M : ℕ, ∀ N ≥ M,
      |riemannSum g p N (xx i) - convPoly g p (xx i)| < δ := by
    intro i
    obtain ⟨M, hM⟩ := (Metric.tendsto_atTop).mp (hconv i) δ hδpos
    exact ⟨M, fun N hN => by
      have := hM N hN
      rwa [Real.dist_eq] at this⟩
  choose Nfun hNfun using hNi
  set N : ℕ := (Finset.univ.sup Nfun) ⊔ 1 with hN_def
  have hN1 : 1 ≤ N := le_sup_right
  have hNge : ∀ i, N ≥ Nfun i :=
    fun i => le_trans (Finset.le_sup (Finset.mem_univ i)) le_sup_left
  have hrpos : ∀ i : Fin (s + 1), 0 < ε * (-1 : ℝ) ^ (i : ℕ) * riemannSum g p N (xx i) := by
    intro i
    have hclose := hNfun i N (hNge i)
    have hgei := hge i
    have hdiff : |ε * (-1 : ℝ) ^ (i : ℕ) *
        (riemannSum g p N (xx i) - convPoly g p (xx i))| < δ := by
      rw [abs_mul, hsign i, one_mul]; exact hclose
    have hlb : ε * (-1 : ℝ) ^ (i : ℕ) *
        (riemannSum g p N (xx i) - convPoly g p (xx i)) > -δ :=
      neg_lt_of_abs_lt hdiff
    have hexpand : ε * (-1 : ℝ) ^ (i : ℕ) * riemannSum g p N (xx i)
        = ε * (-1 : ℝ) ^ (i : ℕ) *
            (riemannSum g p N (xx i) - convPoly g p (xx i))
          + ε * (-1 : ℝ) ^ (i : ℕ) * convPoly g p (xx i) := by ring
    rw [hexpand]; linarith
  set K : ℕ := 2 * N ^ 2 with hK_def
  have hKpos : 1 ≤ K := by
    rw [hK_def]
    have : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  set yv : Fin K → ℝ := fun j => gridPoint N ((j : ℕ) + 1) with hyv_def
  have hNRpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hgrid_mono : ∀ a b : ℕ, a < b → gridPoint N a < gridPoint N b := by
    intro a b hab
    unfold gridPoint
    apply div_lt_div_of_pos_right ?_ hNRpos
    have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    linarith
  have hyv_mono : StrictMono yv := by
    intro a b hab
    rw [hyv_def]
    apply hgrid_mono
    have : (a : ℕ) < (b : ℕ) := hab
    omega
  set A : Matrix (Fin (s + 1)) (Fin K) ℝ :=
    Matrix.of (fun (i : Fin (s + 1)) (j : Fin K) => g (xx i - yv j)) with hA_def
  set cc : Fin K → ℝ := fun j => (1 / (N : ℝ)) * p.eval (yv j) with hcc_def
  have hAc : ∀ i, (A.mulVec cc) i = riemannSum g p N (xx i) := by
    intro i
    have hmv : (A.mulVec cc) i
        = ∑ j : Fin K,
            g (xx i - gridPoint N ((j : ℕ) + 1))
              * ((1 / (N : ℝ)) * p.eval (gridPoint N ((j : ℕ) + 1))) := by
      rw [hA_def, hcc_def, hyv_def]
      rfl
    rw [hmv, Fin.sum_univ_eq_sum_range
      (fun n => g (xx i - gridPoint N (n + 1))
        * ((1 / (N : ℝ)) * p.eval (gridPoint N (n + 1)))) K]
    unfold riemannSum
    apply Finset.sum_bij' (fun (n : ℕ) (_ : n ∈ Finset.range K) => n + 1)
      (fun (k : ℕ) (_ : k ∈ Finset.Icc 1 K) => k - 1)
    · intro n hn
      rw [Finset.mem_range] at hn
      rw [Finset.mem_Icc]; omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_range]; omega
    · intro n hn
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      omega
    · intro n hn
      ring
  have hTN : TotallyNonneg A := by
    rw [hA_def]
    exact matrix_TN g htp (s + 1) K (by omega) hKpos xx hxmono yv hyv_mono
  have hscvec : SignChangesGE (A.mulVec cc) s := by
    apply alt_to_vec s (A.mulVec cc)
    refine ⟨ε, hε, fun i => ?_⟩
    rw [hAc i]
    exact hrpos i
  have hsccc : SignChangesGE cc s := h3 (s + 1) K A hTN cc s hscvec
  apply weighted_transfer K hKpos yv hyv_mono (fun _ => 1 / (N : ℝ))
    (fun j => by positivity) (fun y => p.eval y) s
  have hshape : (fun j => (fun _ => 1 / (N : ℝ)) j * (fun y => p.eval y) (yv j)) = cc := by
    funext j; rw [hcc_def]
  rw [hshape]
  exact hsccc

end Part5
