import LeanCode.Vendor.E5.P10.Part10.Kernels
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open scoped BigOperators ENNReal


theorem H_conv (a : ℝ) (ha : a ≠ 0) (F : ℝ → ℝ)
    (hF_cont : Continuous F) (b : ℤ → ℝ) (hb_sum : Summable b)
    (hb : ∀ (k : ℤ), ∀ x ∈ Set.Icc (0 : ℝ) 1, |F (x + k)| ≤ b k) :
  ∀ x : ℝ,
    Summable (fun k : ℤ => (-1 : ℝ) ^ k * conv (expKernel a) F (x + k)) ∧
    MeasureTheory.Integrable (fun t : ℝ => expKernel a t * Halt F (x - t)) ∧
    Halt (conv (expKernel a) F) x =
      ∫ t : ℝ, expKernel a t * Halt F (x - t) := by
  intro x
  classical
  let B : ℝ := ∑' k : ℤ, b k
  let u : ℤ → ℝ → ℝ :=
    fun k t => (-1 : ℝ) ^ k * (expKernel a t * F (x + k - t))
  have hk := expker_int a ha
  have henv := env_lattice F b hb_sum hb
  have hglob := lattice_global F b hb_sum hb
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact tsum_nonneg henv.1
  have hF_bound : ∀ y : ℝ, |F y| ≤ B := by
    intro y
    simpa [B] using hglob.1 y
  have hu_meas : ∀ k : ℤ, Measurable (u k) := by
    intro k
    dsimp [u]
    exact measurable_const.mul
      ((expker_meas a).mul
        (hF_cont.measurable.comp ((measurable_const.add measurable_const).sub measurable_id)))
  have hu_aemeas : ∀ k : ℤ, AEStronglyMeasurable (u k) volume := by
    intro k
    exact (hu_meas k).aestronglyMeasurable
  have hu_int : ∀ k : ℤ, Integrable (u k) := by
    intro k
    have hbase := (conv_bounded a ha F B hF_cont.measurable hF_bound (x + k)).1
    simpa [u, mul_assoc] using hbase.const_mul ((-1 : ℝ) ^ k)
  have hpoint_bound :
      (fun t : ℝ => ∑' k : ℤ, ‖u k t‖ₑ) ≤
        fun t : ℝ => ENNReal.ofReal B * ENNReal.ofReal (expKernel a t) := by
    intro t
    have hsum_abs := (hglob.2 (x - t)).1
    have hsum_abs_le := (hglob.2 (x - t)).2.1
    have hp_nonneg : 0 ≤ expKernel a t := hk.2.1 t
    calc
      (∑' k : ℤ, ‖u k t‖ₑ) =
          ∑' k : ℤ, ENNReal.ofReal (expKernel a t * |F ((x - t) + k)|) := by
        apply tsum_congr
        intro k
        dsimp [u]
        rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq, coe_nnnorm]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_zpow, abs_of_nonneg hp_nonneg]
        norm_num
        congr 2
        ring_nf
      _ = ∑' k : ℤ, ENNReal.ofReal (expKernel a t) *
            ENNReal.ofReal (|F ((x - t) + k)|) := by
        apply tsum_congr
        intro k
        rw [ENNReal.ofReal_mul hp_nonneg]
      _ = ENNReal.ofReal (expKernel a t) *
            ∑' k : ℤ, ENNReal.ofReal (|F ((x - t) + k)|) := by
        rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (expKernel a t) *
            ENNReal.ofReal (∑' k : ℤ, |F ((x - t) + k)|) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun k => abs_nonneg _) hsum_abs]
      _ ≤ ENNReal.ofReal (expKernel a t) * ENNReal.ofReal B := by
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hsum_abs_le) _
      _ = ENNReal.ofReal B * ENNReal.ofReal (expKernel a t) := by
        ring
  have htotal_lt :
      (∑' k : ℤ, ∫⁻ t : ℝ, ‖u k t‖ₑ) < ⊤ := by
    calc
      (∑' k : ℤ, ∫⁻ t : ℝ, ‖u k t‖ₑ) =
          ∫⁻ t : ℝ, ∑' k : ℤ, ‖u k t‖ₑ := by
        rw [MeasureTheory.lintegral_tsum]
        intro k
        exact (hu_meas k).enorm.aemeasurable
      _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal B * ENNReal.ofReal (expKernel a t) :=
        MeasureTheory.lintegral_mono hpoint_bound
      _ = ENNReal.ofReal B * ∫⁻ t : ℝ, ENNReal.ofReal (expKernel a t) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal B * ENNReal.ofReal (∫ t : ℝ, expKernel a t) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hk.1
          (Filter.Eventually.of_forall hk.2.1)]
      _ = ENNReal.ofReal B := by
        rw [hk.2.2.1]
        simp
      _ < ⊤ := ENNReal.ofReal_lt_top
  have htotal_ne :
      (∑' k : ℤ, ∫⁻ t : ℝ, ‖u k t‖ₑ) ≠ ⊤ :=
    ne_of_lt htotal_lt
  have hsum_int_norm : Summable (fun k : ℤ => ∫ t : ℝ, ‖u k t‖) := by
    have hlintegral_eq : ∀ k : ℤ,
        ∫⁻ t : ℝ, ‖u k t‖ₑ =
          ‖∫ t : ℝ, ‖u k t‖‖ₑ := by
      intro k
      dsimp [enorm]
      rw [MeasureTheory.lintegral_coe_eq_integral _ (hu_int k).norm]
      rw [ENNReal.coe_nnreal_eq, coe_nnnorm]
      rw [Real.norm_of_nonneg]
      · simp
      · exact MeasureTheory.integral_nonneg (fun t => norm_nonneg (u k t))
    have hsum_enorm :
        (∑' k : ℤ, ‖∫ t : ℝ, ‖u k t‖‖ₑ) ≠ ⊤ := by
      simpa [hlintegral_eq] using htotal_ne
    have hsum_norm_norm :
        Summable (fun k : ℤ => ‖∫ t : ℝ, ‖u k t‖‖) :=
      tsum_enorm_ne_top_iff_summable_norm.mp hsum_enorm
    convert hsum_norm_norm using 1
    ext k
    rw [Real.norm_of_nonneg]
    exact MeasureTheory.integral_nonneg (fun t => norm_nonneg (u k t))
  have hu_integral : ∀ k : ℤ,
      (∫ t : ℝ, u k t) =
        (-1 : ℝ) ^ k * conv (expKernel a) F (x + k) := by
    intro k
    dsimp [u, conv]
    rw [MeasureTheory.integral_const_mul]
  have hsum_integrals : Summable (fun k : ℤ => ∫ t : ℝ, u k t) := by
    exact Summable.of_norm_bounded hsum_int_norm
      (fun k => MeasureTheory.norm_integral_le_integral_norm (u k))
  have hconv_sum :
      Summable (fun k : ℤ => (-1 : ℝ) ^ k * conv (expKernel a) F (x + k)) := by
    convert hsum_integrals using 1
    ext k
    exact (hu_integral k).symm
  have hseries_integrable : Integrable (fun t : ℝ => ∑' k : ℤ, u k t) := by
    refine ⟨MeasureTheory.AEStronglyMeasurable.tsum hu_aemeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ t : ℝ, ‖∑' k : ℤ, u k t‖ₑ) ≤
          ∫⁻ t : ℝ, ∑' k : ℤ, ‖u k t‖ₑ := by
        exact MeasureTheory.lintegral_mono (fun t => enorm_tsum_le_tsum_enorm)
      _ = ∑' k : ℤ, ∫⁻ t : ℝ, ‖u k t‖ₑ := by
        rw [MeasureTheory.lintegral_tsum]
        intro k
        exact (hu_meas k).enorm.aemeasurable
      _ < ⊤ := htotal_lt
  have htsum_point :
      (fun t : ℝ => ∑' k : ℤ, u k t) =
        fun t : ℝ => expKernel a t * Halt F (x - t) := by
    funext t
    unfold Halt
    calc
      (∑' k : ℤ, u k t) =
          ∑' k : ℤ, expKernel a t * ((-1 : ℝ) ^ k * F ((x - t) + k)) := by
        apply tsum_congr
        intro k
        dsimp [u]
        have harg : x + (k : ℝ) - t = x - t + (k : ℝ) := by ring
        rw [harg]
        ring
      _ = expKernel a t * (∑' k : ℤ, (-1 : ℝ) ^ k * F (x - t + k)) := by
        rw [tsum_mul_left]
  have htarget_integrable :
      Integrable (fun t : ℝ => expKernel a t * Halt F (x - t)) :=
    hseries_integrable.congr (Filter.Eventually.of_forall fun t => congrFun htsum_point t)
  have hswap :
      (∫ t : ℝ, ∑' k : ℤ, u k t) =
        ∑' k : ℤ, ∫ t : ℝ, u k t :=
    MeasureTheory.integral_tsum hu_aemeas htotal_ne
  constructor
  · exact hconv_sum
  constructor
  · exact htarget_integrable
  · calc
      Halt (conv (expKernel a) F) x =
          ∑' k : ℤ, ∫ t : ℝ, u k t := by
        unfold Halt
        apply tsum_congr
        intro k
        rw [hu_integral k]
      _ = ∫ t : ℝ, ∑' k : ℤ, u k t := hswap.symm
      _ = ∫ t : ℝ, expKernel a t * Halt F (x - t) := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun t => congrFun htsum_point t

private theorem resum_pos_substitution (a y : ℝ) (φ : ℝ → ℝ) :
    (∫ t in Set.Ici (0 : ℝ), a * Real.exp (-a * t) * φ (y - t)) =
      (a * Real.exp (-a * y)) *
        (∫ s in Set.Iic y, Real.exp (a * s) * φ s) := by
  let q : ℝ → ℝ := fun s => a * Real.exp (-a * (y - s)) * φ s
  have hmp := (volume : Measure ℝ).measurePreserving_sub_left y
  have hsub := hmp.setIntegral_preimage_emb (measurableEmbedding_subLeft y) q (Set.Iic y)
  have hpre : (fun t : ℝ => y - t) ⁻¹' Set.Iic y = Set.Ici (0 : ℝ) := by
    ext t
    simp
  have hleft :
      (∫ t in Set.Ici (0 : ℝ), a * Real.exp (-a * t) * φ (y - t)) =
        ∫ t in (fun t : ℝ => y - t) ⁻¹' Set.Iic y, q (y - t) := by
    rw [hpre]
    apply setIntegral_congr_fun measurableSet_Ici
    intro t ht
    dsimp [q]
    congr 2
    ring_nf
  have hright :
      (∫ s in Set.Iic y, q s) =
        (a * Real.exp (-a * y)) *
          (∫ s in Set.Iic y, Real.exp (a * s) * φ s) := by
    have hpoint : (fun s : ℝ => q s) =
        fun s : ℝ => (a * Real.exp (-a * y)) * (Real.exp (a * s) * φ s) := by
      funext s
      dsimp [q]
      rw [show -a * (y - s) = -a * y + a * s by ring, Real.exp_add]
      ring
    rw [hpoint]
    rw [integral_const_mul]
  rw [hleft, hsub, hright]

private theorem resum_pos_Iic (a y : ℝ) (ha : 0 < a) (φ : ℝ → ℝ)
    (hφ_cont : Continuous φ) (M : ℝ) (hφ_bound : ∀ x : ℝ, |φ x| ≤ M)
    (hφ_anti : ∀ x : ℝ, φ (x + 1) = -φ x) :
    (∫ s in Set.Iic y, Real.exp (a * s) * φ s) =
      (1 / (1 + Real.exp (-a))) *
        (∫ s in (y - 1)..y, Real.exp (a * s) * φ s) := by
  let I : ℝ → ℝ := fun s => Real.exp (a * s) * φ s
  let J : ℝ := ∫ s in (y - 1)..y, I s
  let S : ℕ → Set ℝ := fun j => Set.Ioc (y - (j : ℝ) - 1) (y - (j : ℝ))
  have hcover : (⋃ j : ℕ, S j) = Set.Iic y := by
    dsimp [S]
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
      exact hj.2.trans (by linarith : y - (j : ℝ) ≤ y)
    · intro hxy
      let d : ℝ := y - x
      have hd_nonneg : 0 ≤ d := by
        dsimp [d]
        have hxy' : x ≤ y := hxy
        linarith
      let j : ℕ := Nat.floor d
      have hj_le : (j : ℝ) ≤ d := by
        dsimp [j]
        exact Nat.floor_le hd_nonneg
      have hd_lt : d < (j : ℝ) + 1 := by
        dsimp [j]
        exact Nat.lt_floor_add_one d
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      constructor
      · dsimp [d] at hd_lt
        linarith
      · dsimp [d] at hj_le
        linarith
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    let f : ℕ → ℝ := fun j => y - (j : ℝ)
    have hf : Antitone f := by
      intro i j hij
      dsimp [f]
      have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    have hdisj0 := hf.pairwise_disjoint_on_Ioc_succ
    simpa [S, f, Nat.cast_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdisj0
  have hI_int : IntegrableOn I (Set.Iic y) := by
    have hbase : IntegrableOn (fun s : ℝ => Real.exp (a * s)) (Set.Iic y) :=
      (exp_halfline a y (ne_of_gt ha)).1 ha
    change Integrable I (volume.restrict (Set.Iic y))
    have hbound_ae : ∀ᵐ s ∂(volume.restrict (Set.Iic y)), ‖φ s‖ ≤ M :=
      Filter.Eventually.of_forall fun s => by
        simpa [Real.norm_eq_abs] using hφ_bound s
    exact hbase.mul_bdd hφ_cont.aestronglyMeasurable hbound_ae
  have hsum :
      (∫ s in Set.Iic y, I s) = ∑' j : ℕ, ∫ s in S j, I s := by
    rw [← hcover]
    exact MeasureTheory.integral_iUnion (fun j : ℕ => measurableSet_Ioc) hdisj
      (by simpa [hcover] using hI_int)
  have hpiece : ∀ j : ℕ, (∫ s in S j, I s) = (-Real.exp (-a)) ^ j * J := by
    intro j
    have hle : y - (j : ℝ) - 1 ≤ y - (j : ℝ) := by linarith
    rw [show (∫ s in S j, I s) =
        ∫ s in (y - (j : ℝ) - 1)..(y - (j : ℝ)), I s by
      rw [intervalIntegral.integral_of_le hle]]
    dsimp [I, J]
    let K : ℝ → ℝ := fun s => Real.exp (a * s) * φ s
    have htrans := intervalIntegral.integral_comp_sub_right K (j : ℝ) (a := y - 1) (b := y)
    have hcongr : (∫ x in y - 1..y, K (x - (j : ℝ))) =
        ∫ x in y - 1..y, ((-Real.exp (-a)) ^ j) * K x := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp [K]
      have hanti0 := antiper_nfold φ hφ_anti x (-(j : ℤ))
      have hanti : φ (x - (j : ℝ)) = (-1 : ℝ) ^ j * φ x := by
        have hpow : (-1 : ℝ) ^ (-(j : ℤ)) = (-1 : ℝ) ^ j := by
          rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg_one]
        simpa [Int.cast_neg, Int.cast_natCast, sub_eq_add_neg, hpow] using hanti0
      rw [hanti]
      have hexp : Real.exp (a * (x - (j : ℝ))) = Real.exp (-a) ^ j * Real.exp (a * x) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      have hpowmul : Real.exp (-a) ^ j * (-1 : ℝ) ^ j = (-Real.exp (-a)) ^ j := by
        rw [← mul_pow]
        congr 1
        ring
      rw [← hpowmul]
      ring
    have htrans_piece : (∫ s in (y - (j : ℝ) - 1)..(y - (j : ℝ)), K s) =
        ∫ x in y - 1..y, K (x - (j : ℝ)) := by
      rw [htrans]
      congr 1
      ring
    rw [htrans_piece, hcongr]
    rw [intervalIntegral.integral_const_mul]
  have hgeom_norm : ‖(-Real.exp (-a) : ℝ)‖ < 1 := by
    have hlt := (exp_ratio a ha).2
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos (-a))]
    exact hlt
  have hgeom :
      (∑' j : ℕ, (-Real.exp (-a) : ℝ) ^ j) = 1 / (1 + Real.exp (-a)) := by
    rw [tsum_geometric_of_norm_lt_one hgeom_norm]
    field_simp [ne_of_gt (by positivity : 0 < 1 + Real.exp (-a))]
    ring
  calc
    (∫ s in Set.Iic y, Real.exp (a * s) * φ s) = ∫ s in Set.Iic y, I s := rfl
    _ = ∑' j : ℕ, ∫ s in S j, I s := hsum
    _ = ∑' j : ℕ, (-Real.exp (-a) : ℝ) ^ j * J := by
      apply tsum_congr
      intro j
      exact hpiece j
    _ = (∑' j : ℕ, (-Real.exp (-a) : ℝ) ^ j) * J := by
      rw [tsum_mul_right]
    _ = (1 / (1 + Real.exp (-a))) *
        (∫ s in (y - 1)..y, Real.exp (a * s) * φ s) := by
      rw [hgeom]


theorem resum_pos (a : ℝ) (ha : 0 < a) (φ : ℝ → ℝ)
    (hφ_cont : Continuous φ) (M : ℝ) (hφ_bound : ∀ x : ℝ, |φ x| ≤ M)
    (hφ_anti : ∀ x : ℝ, φ (x + 1) = -φ x) :
  ∀ y : ℝ,
    MeasureTheory.Integrable (fun t : ℝ => expKernel a t * φ (y - t)) ∧
    conv (expKernel a) φ y =
      (a * Real.exp (-a * y) / (1 + Real.exp (-a))) *
        (∫ s in (y - 1)..y, Real.exp (a * s) * φ s) := by
  intro y
  have hconv := conv_bounded a (ne_of_gt ha) φ M hφ_cont.measurable hφ_bound y
  constructor
  · exact hconv.1
  · have hkernel_integrand :
        (fun t : ℝ => expKernel a t * φ (y - t)) =
          (Set.Ici (0 : ℝ)).indicator
            (fun t : ℝ => a * Real.exp (-a * t) * φ (y - t)) := by
      funext t
      by_cases ht : 0 ≤ t
      · have hk := (expker_cases a).1 ha |>.1 t ht
        simp [hk, ht]
      · have htlt : t < 0 := lt_of_not_ge ht
        have hk := (expker_cases a).1 ha |>.2 t htlt
        simp [hk, ht]
    unfold conv
    rw [hkernel_integrand]
    rw [integral_indicator measurableSet_Ici]
    rw [resum_pos_substitution a y φ]
    rw [resum_pos_Iic a y ha φ hφ_cont M hφ_bound hφ_anti]
    ring

private theorem resum_neg_substitution (a y : ℝ) (φ : ℝ → ℝ) :
    (∫ t in Set.Iic (0 : ℝ), (-a) * Real.exp (-a * t) * φ (y - t)) =
      ((-a) * Real.exp (-a * y)) *
        (∫ s in Set.Ici y, Real.exp (a * s) * φ s) := by
  let q : ℝ → ℝ := fun s => (-a) * Real.exp (-a * (y - s)) * φ s
  have hmp := (volume : Measure ℝ).measurePreserving_sub_left y
  have hsub := hmp.setIntegral_preimage_emb (measurableEmbedding_subLeft y) q (Set.Ici y)
  have hpre : (fun t : ℝ => y - t) ⁻¹' Set.Ici y = Set.Iic (0 : ℝ) := by
    ext t
    simp
  have hleft :
      (∫ t in Set.Iic (0 : ℝ), (-a) * Real.exp (-a * t) * φ (y - t)) =
        ∫ t in (fun t : ℝ => y - t) ⁻¹' Set.Ici y, q (y - t) := by
    rw [hpre]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    dsimp [q]
    congr 2
    ring_nf
  have hright :
      (∫ s in Set.Ici y, q s) =
        ((-a) * Real.exp (-a * y)) *
          (∫ s in Set.Ici y, Real.exp (a * s) * φ s) := by
    have hpoint : (fun s : ℝ => q s) =
        fun s : ℝ => ((-a) * Real.exp (-a * y)) * (Real.exp (a * s) * φ s) := by
      funext s
      dsimp [q]
      rw [show -a * (y - s) = -a * y + a * s by ring, Real.exp_add]
      ring
    rw [hpoint]
    rw [integral_const_mul]
  rw [hleft, hsub, hright]

private theorem resum_neg_Ici (a y : ℝ) (ha : a < 0) (φ : ℝ → ℝ)
    (hφ_cont : Continuous φ) (M : ℝ) (hφ_bound : ∀ x : ℝ, |φ x| ≤ M)
    (hφ_anti : ∀ x : ℝ, φ (x + 1) = -φ x) :
    (∫ s in Set.Ici y, Real.exp (a * s) * φ s) =
      (1 / (1 + Real.exp a)) *
        (∫ s in y..(y + 1), Real.exp (a * s) * φ s) := by
  let I : ℝ → ℝ := fun s => Real.exp (a * s) * φ s
  let J : ℝ := ∫ s in y..(y + 1), I s
  let S : ℕ → Set ℝ := fun j => Set.Ioc (y + (j : ℝ)) (y + (j : ℝ) + 1)
  have hcover : (⋃ j : ℕ, S j) = Set.Ioi y := by
    let f : ℕ → ℝ := fun j => y + (j : ℝ)
    have hf0 : ∀ j : ℕ, f ⊥ ≤ f j := by
      intro j
      dsimp [f]
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num]
      linarith
    have hunbdd : ¬ BddAbove (Set.range f) := by
      rintro ⟨B, hB⟩
      rcases exists_nat_gt (B - y) with ⟨n, hn⟩
      have hBn : f n ≤ B := hB ⟨n, rfl⟩
      dsimp [f] at hBn
      linarith
    simpa [S, f, Nat.cast_add, add_assoc] using
      (iUnion_Ioc_map_succ_eq_Ioi (f := f) hf0 hunbdd)
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    let f : ℕ → ℝ := fun j => y + (j : ℝ)
    have hf : Monotone f := by
      intro i j hij
      dsimp [f]
      have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    have hdisj0 := hf.pairwise_disjoint_on_Ioc_succ
    simpa [S, f, Nat.cast_add, add_assoc] using hdisj0
  have hI_int_Ici : IntegrableOn I (Set.Ici y) := by
    have hbase : IntegrableOn (fun s : ℝ => Real.exp (a * s)) (Set.Ici y) :=
      (exp_halfline a y (ne_of_lt ha)).2 ha
    change Integrable I (volume.restrict (Set.Ici y))
    have hbound_ae : ∀ᵐ s ∂(volume.restrict (Set.Ici y)), ‖φ s‖ ≤ M :=
      Filter.Eventually.of_forall fun s => by
        simpa [Real.norm_eq_abs] using hφ_bound s
    exact hbase.mul_bdd hφ_cont.aestronglyMeasurable hbound_ae
  have hI_int_Ioi : IntegrableOn I (Set.Ioi y) := hI_int_Ici.mono_set Set.Ioi_subset_Ici_self
  have hsum :
      (∫ s in Set.Ioi y, I s) = ∑' j : ℕ, ∫ s in S j, I s := by
    rw [← hcover]
    exact MeasureTheory.integral_iUnion (fun j : ℕ => measurableSet_Ioc) hdisj
      (by simpa [hcover] using hI_int_Ioi)
  have hpiece : ∀ j : ℕ, (∫ s in S j, I s) = (-Real.exp a) ^ j * J := by
    intro j
    have hle : y + (j : ℝ) ≤ y + (j : ℝ) + 1 := by linarith
    rw [show (∫ s in S j, I s) =
        ∫ s in (y + (j : ℝ))..(y + (j : ℝ) + 1), I s by
      rw [intervalIntegral.integral_of_le hle]]
    dsimp [I, J]
    let K : ℝ → ℝ := fun s => Real.exp (a * s) * φ s
    have htrans := intervalIntegral.integral_comp_add_right K (j : ℝ) (a := y) (b := y + 1)
    have hcongr : (∫ x in y..y + 1, K (x + (j : ℝ))) =
        ∫ x in y..y + 1, ((-Real.exp a) ^ j) * K x := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp [K]
      have hanti0 := antiper_nfold φ hφ_anti x (j : ℤ)
      have hanti : φ (x + (j : ℝ)) = (-1 : ℝ) ^ j * φ x := by
        simpa [Int.cast_natCast] using hanti0
      rw [hanti]
      have hexp : Real.exp (a * (x + (j : ℝ))) = Real.exp a ^ j * Real.exp (a * x) := by
        rw [show a * (x + (j : ℝ)) = a * x + (j : ℝ) * a by ring]
        rw [Real.exp_add, Real.exp_nat_mul]
        ring
      rw [hexp]
      have hpowmul : Real.exp a ^ j * (-1 : ℝ) ^ j = (-Real.exp a) ^ j := by
        rw [← mul_pow]
        congr 1
        ring
      rw [← hpowmul]
      ring
    have htrans_piece :
        (∫ s in (y + (j : ℝ))..(y + (j : ℝ) + 1), K s) =
          ∫ x in y..y + 1, K (x + (j : ℝ)) := by
      rw [htrans]
      congr 1
      ring
    rw [htrans_piece, hcongr]
    rw [intervalIntegral.integral_const_mul]
  have hgeom_norm : ‖(-Real.exp a : ℝ)‖ < 1 := by
    have hlt := (exp_ratio (-a) (neg_pos.mpr ha)).2
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos a)]
    simpa using hlt
  have hgeom :
      (∑' j : ℕ, (-Real.exp a : ℝ) ^ j) = 1 / (1 + Real.exp a) := by
    rw [tsum_geometric_of_norm_lt_one hgeom_norm]
    field_simp [ne_of_gt (by positivity : 0 < 1 + Real.exp a)]
    ring
  calc
    (∫ s in Set.Ici y, Real.exp (a * s) * φ s) = ∫ s in Set.Ioi y, I s := by
      rw [integral_Ici_eq_integral_Ioi]
    _ = ∑' j : ℕ, ∫ s in S j, I s := hsum
    _ = ∑' j : ℕ, (-Real.exp a : ℝ) ^ j * J := by
      apply tsum_congr
      intro j
      exact hpiece j
    _ = (∑' j : ℕ, (-Real.exp a : ℝ) ^ j) * J := by
      rw [tsum_mul_right]
    _ = (1 / (1 + Real.exp a)) *
        (∫ s in y..(y + 1), Real.exp (a * s) * φ s) := by
      rw [hgeom]


theorem resum_neg (a : ℝ) (ha : a < 0) (φ : ℝ → ℝ)
    (hφ_cont : Continuous φ) (M : ℝ) (hφ_bound : ∀ x : ℝ, |φ x| ≤ M)
    (hφ_anti : ∀ x : ℝ, φ (x + 1) = -φ x) :
  ∀ y : ℝ,
    MeasureTheory.Integrable (fun t : ℝ => expKernel a t * φ (y - t)) ∧
    conv (expKernel a) φ y =
      ((-a) * Real.exp (-a * y) / (1 + Real.exp a)) *
        (∫ s in y..(y + 1), Real.exp (a * s) * φ s) := by
  intro y
  have hconv := conv_bounded a (ne_of_lt ha) φ M hφ_cont.measurable hφ_bound y
  constructor
  · exact hconv.1
  · have hkernel_integrand :
        (fun t : ℝ => expKernel a t * φ (y - t)) =
          (Set.Iic (0 : ℝ)).indicator
            (fun t : ℝ => (-a) * Real.exp (-a * t) * φ (y - t)) := by
      funext t
      by_cases ht : t ≤ 0
      · have hk := (expker_cases a).2.1 ha |>.1 t ht
        simp [hk, ht]
      · have htpos : 0 < t := lt_of_not_ge ht
        have hk := (expker_cases a).2.1 ha |>.2 t htpos
        simp [hk, ht]
    unfold conv
    rw [hkernel_integrand]
    rw [integral_indicator measurableSet_Iic]
    rw [resum_neg_substitution a y φ]
    rw [resum_neg_Ici a y ha φ hφ_cont M hφ_bound hφ_anti]
    ring


theorem vanish_int (h : ℝ → ℝ) (hh_cont : Continuous h)
    (α β : ℝ) (hαβ : α < β)
    (hvanish : ∀ y₁ y₂ : ℝ, α < y₁ → y₁ ≤ y₂ → y₂ < β →
      (∫ s in y₁..y₂, h s) = 0) :
    ∀ x : ℝ, α < x → x < β → h x = 0 := by
  have _ : α < β := hαβ
  intro x hαx hxβ
  let y0 : ℝ := (α + x) / 2
  have hαy0 : α < y0 := by
    dsimp [y0]
    linarith
  have hy0x : y0 < x := by
    dsimp [y0]
    linarith
  have hFx_zero : (fun y : ℝ => ∫ s in y0..y, h s) =ᶠ[nhds x] fun _ : ℝ => 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hy0x, hxβ⟩] with y hy
    exact hvanish y0 y hαy0 (le_of_lt hy.1) hy.2
  have hderiv_zero : HasDerivAt (fun y : ℝ => ∫ s in y0..y, h s) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hFx_zero
  have hderiv_h : HasDerivAt (fun y : ℝ => ∫ s in y0..y, h s) (h x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hh_cont.intervalIntegrable y0 x)
      (hh_cont.stronglyMeasurableAtFilter volume (nhds x))
      (hh_cont.continuousAt)
  exact hderiv_h.unique hderiv_zero


theorem weighted_vanish (w h : ℝ → ℝ) (hw_cont : Continuous w)
    (hh_cont : Continuous h) (hw_pos : ∀ s : ℝ, 0 < w s)
    (α β : ℝ) (hαβ : α < β)
    (hvanish : ∀ y₁ y₂ : ℝ, α < y₁ → y₁ ≤ y₂ → y₂ < β →
      (∫ s in y₁..y₂, w s * h s) = 0) :
    ∀ x : ℝ, α < x → x < β → h x = 0 := by
  intro x hαx hxβ
  have hprod_zero : w x * h x = 0 :=
    vanish_int (fun s : ℝ => w s * h s) (hw_cont.mul hh_cont)
      α β hαβ hvanish x hαx hxβ
  exact (mul_eq_zero.mp hprod_zero).resolve_left (ne_of_gt (hw_pos x))


theorem increment_pos (a : ℝ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (hφ_anti : ∀ x : ℝ, φ (x + 1) = -φ x) :
  let J : ℝ → ℝ := fun y => ∫ s in (y - 1)..y, Real.exp (a * s) * φ s
  ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ →
    J y₂ - J y₁ =
      ∫ s in y₁..y₂, (Real.exp (a * s) + Real.exp (a * (s - 1))) * φ s := by
  let I : ℝ → ℝ := fun s => Real.exp (a * s) * φ s
  let K : ℝ → ℝ := fun s => Real.exp (a * (s - 1)) * φ s
  have hI_cont : Continuous I := by
    dsimp [I]
    continuity
  have hK_cont : Continuous K := by
    dsimp [K]
    continuity
  have hI_int : ∀ u v : ℝ, IntervalIntegrable I volume u v := fun u v =>
    hI_cont.intervalIntegrable u v
  have hK_int : ∀ u v : ℝ, IntervalIntegrable K volume u v := fun u v =>
    hK_cont.intervalIntegrable u v
  dsimp
  intro y₁ y₂ hy
  have hbig1 : (∫ s in (y₁ - 1)..y₁, I s) + (∫ s in y₁..y₂, I s) =
      ∫ s in (y₁ - 1)..y₂, I s :=
    intervalIntegral.integral_add_adjacent_intervals (hI_int (y₁ - 1) y₁) (hI_int y₁ y₂)
  have hbig2 : (∫ s in (y₁ - 1)..(y₂ - 1), I s) + (∫ s in (y₂ - 1)..y₂, I s) =
      ∫ s in (y₁ - 1)..y₂, I s :=
    intervalIntegral.integral_add_adjacent_intervals (hI_int (y₁ - 1) (y₂ - 1))
      (hI_int (y₂ - 1) y₂)
  have hdiff : (∫ s in (y₂ - 1)..y₂, I s) - (∫ s in (y₁ - 1)..y₁, I s) =
      (∫ s in y₁..y₂, I s) - (∫ s in (y₁ - 1)..(y₂ - 1), I s) := by
    nlinarith
  have hlower : (∫ s in (y₁ - 1)..(y₂ - 1), I s) = -∫ s in y₁..y₂, K s := by
    rw [← intervalIntegral.integral_comp_sub_right I (1 : ℝ)]
    have hcongr : (∫ s in y₁..y₂, I (s - 1)) = ∫ s in y₁..y₂, -K s := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp [I, K]
      have hprev : φ (s - 1) = -φ s := by
        have h := hφ_anti (s - 1)
        have harg : s - 1 + 1 = s := by ring
        rw [harg] at h
        linarith
      rw [hprev]
      ring
    rw [hcongr, intervalIntegral.integral_neg]
  have hright : (∫ s in y₁..y₂, (Real.exp (a * s) + Real.exp (a * (s - 1))) * φ s) =
      (∫ s in y₁..y₂, I s) + (∫ s in y₁..y₂, K s) := by
    have hcongr : (∫ s in y₁..y₂, (Real.exp (a * s) + Real.exp (a * (s - 1))) * φ s) =
        ∫ s in y₁..y₂, I s + K s := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp [I, K]
      ring
    rw [hcongr]
    exact intervalIntegral.integral_add (hI_int y₁ y₂) (hK_int y₁ y₂)
  calc
    (∫ s in (y₂ - 1)..y₂, I s) - (∫ s in (y₁ - 1)..y₁, I s) =
        (∫ s in y₁..y₂, I s) - (∫ s in (y₁ - 1)..(y₂ - 1), I s) := hdiff
    _ = (∫ s in y₁..y₂, I s) + (∫ s in y₁..y₂, K s) := by rw [hlower]; ring
    _ = ∫ s in y₁..y₂, (Real.exp (a * s) + Real.exp (a * (s - 1))) * φ s :=
      hright.symm


theorem increment_neg (a : ℝ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (hφ_anti : ∀ x : ℝ, φ (x + 1) = -φ x) :
  let Jneg : ℝ → ℝ := fun y => ∫ s in y..(y + 1), Real.exp (a * s) * φ s
  ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ →
    Jneg y₂ - Jneg y₁ =
      -(∫ s in y₁..y₂, (Real.exp (a * s) + Real.exp (a * (s + 1))) * φ s) := by
  let I : ℝ → ℝ := fun s => Real.exp (a * s) * φ s
  let K : ℝ → ℝ := fun s => Real.exp (a * (s + 1)) * φ s
  have hI_cont : Continuous I := by
    dsimp [I]
    continuity
  have hK_cont : Continuous K := by
    dsimp [K]
    continuity
  have hI_int : ∀ u v : ℝ, IntervalIntegrable I volume u v := fun u v =>
    hI_cont.intervalIntegrable u v
  have hK_int : ∀ u v : ℝ, IntervalIntegrable K volume u v := fun u v =>
    hK_cont.intervalIntegrable u v
  dsimp
  intro y₁ y₂ hy
  have hbig1 : (∫ s in y₁..(y₁ + 1), I s) + (∫ s in (y₁ + 1)..(y₂ + 1), I s) =
      ∫ s in y₁..(y₂ + 1), I s :=
    intervalIntegral.integral_add_adjacent_intervals (hI_int y₁ (y₁ + 1))
      (hI_int (y₁ + 1) (y₂ + 1))
  have hbig2 : (∫ s in y₁..y₂, I s) + (∫ s in y₂..(y₂ + 1), I s) =
      ∫ s in y₁..(y₂ + 1), I s :=
    intervalIntegral.integral_add_adjacent_intervals (hI_int y₁ y₂) (hI_int y₂ (y₂ + 1))
  have hdiff : (∫ s in y₂..(y₂ + 1), I s) - (∫ s in y₁..(y₁ + 1), I s) =
      (∫ s in (y₁ + 1)..(y₂ + 1), I s) - (∫ s in y₁..y₂, I s) := by
    nlinarith
  have hupper : (∫ s in (y₁ + 1)..(y₂ + 1), I s) = -∫ s in y₁..y₂, K s := by
    rw [← intervalIntegral.integral_comp_add_right I (1 : ℝ)]
    have hcongr : (∫ s in y₁..y₂, I (s + 1)) = ∫ s in y₁..y₂, -K s := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp [I, K]
      rw [hφ_anti s]
      ring
    rw [hcongr, intervalIntegral.integral_neg]
  have hright : (∫ s in y₁..y₂, (Real.exp (a * s) + Real.exp (a * (s + 1))) * φ s) =
      (∫ s in y₁..y₂, I s) + (∫ s in y₁..y₂, K s) := by
    have hcongr : (∫ s in y₁..y₂, (Real.exp (a * s) + Real.exp (a * (s + 1))) * φ s) =
        ∫ s in y₁..y₂, I s + K s := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp [I, K]
      ring
    rw [hcongr]
    exact intervalIntegral.integral_add (hI_int y₁ y₂) (hK_int y₁ y₂)
  calc
    (∫ s in y₂..(y₂ + 1), I s) - (∫ s in y₁..(y₁ + 1), I s) =
        (∫ s in (y₁ + 1)..(y₂ + 1), I s) - (∫ s in y₁..y₂, I s) := hdiff
    _ = -((∫ s in y₁..y₂, I s) + (∫ s in y₁..y₂, K s)) := by rw [hupper]; ring
    _ = -(∫ s in y₁..y₂, (Real.exp (a * s) + Real.exp (a * (s + 1))) * φ s) := by
      rw [hright]


theorem deconv (σ : ℝ) (hσ : σ ≠ 0) (F : ℝ → ℝ)
    (hF_cont : Continuous F) (hF_lattice : LatticeDominated F)
    (α β : ℝ) (hαβ : α < β)
    (hflat : ∀ x : ℝ, α < x → x < β → Halt (conv (centeredExp σ) F) x = 0) :
  ∀ y : ℝ, α + σ < y → y < β + σ → Halt F y = 0 := by
  classical
  rcases hF_lattice with ⟨b, hb_sum, hb⟩
  let a : ℝ := 1 / σ
  let φ : ℝ → ℝ := Halt F
  let αp : ℝ := α + σ
  let βp : ℝ := β + σ
  let B : ℝ := ∑' k : ℤ, b k
  have ha : a ≠ 0 := by
    simpa [a, one_div] using inv_ne_zero hσ
  have hαpβp : αp < βp := by
    dsimp [αp, βp]
    linarith
  have henv := env_lattice F b hb_sum hb
  have hglob := lattice_global F b hb_sum hb
  have hφ_cont : Continuous φ := by
    dsimp [φ]
    exact H_cont F hF_cont henv.2
  have hφ_bound : ∀ x : ℝ, |φ x| ≤ B := by
    intro x
    dsimp [φ, B]
    exact (hglob.2 x).2.2.2
  have hφ_anti : ∀ x : ℝ, φ (x + 1) = -φ x := by
    intro x
    dsimp [φ]
    exact (H_antiper F x).1
  have hflat_a :
      ∀ y : ℝ, αp < y → y < βp → Halt (conv (expKernel a) F) y = 0 := by
    intro y hyα hyβ
    have hxα : α < y - σ := by
      dsimp [αp] at hyα
      linarith
    have hxβ : y - σ < β := by
      dsimp [βp] at hyβ
      linarith
    have hz := hflat (y - σ) hxα hxβ
    have htransport :
        Halt (conv (centeredExp σ) F) (y - σ) =
          Halt (conv (expKernel a) F) y := by
      unfold Halt
      apply tsum_congr
      intro k
      rw [conv_shift σ hσ F (y - σ + k)]
      dsimp [a]
      congr 2
      ring
    rwa [htransport] at hz
  have hconv_zero :
      ∀ y : ℝ, αp < y → y < βp → conv (expKernel a) φ y = 0 := by
    intro y hyα hyβ
    have hH := (H_conv a ha F hF_cont b hb_sum hb y).2.2
    unfold conv
    dsimp [φ]
    rw [← hH]
    exact hflat_a y hyα hyβ
  have hpos_case :
      0 < a → ∀ y : ℝ, αp < y → y < βp → φ y = 0 := by
    intro ha_pos
    let J : ℝ → ℝ := fun y => ∫ s in (y - 1)..y, Real.exp (a * s) * φ s
    have hJ_zero : ∀ y : ℝ, αp < y → y < βp → J y = 0 := by
      intro y hyα hyβ
      have hres := (resum_pos a ha_pos φ hφ_cont B hφ_bound hφ_anti y).2
      have hz := hconv_zero y hyα hyβ
      have hpref_pos : 0 < a * Real.exp (-a * y) / (1 + Real.exp (-a)) := by
        exact div_pos (mul_pos ha_pos (Real.exp_pos _))
          (by positivity)
      rw [hres] at hz
      simpa [J] using (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpref_pos)
    have hvanish :
        ∀ y₁ y₂ : ℝ, αp < y₁ → y₁ ≤ y₂ → y₂ < βp →
          (∫ s in y₁..y₂,
            (Real.exp (a * s) + Real.exp (a * (s - 1))) * φ s) = 0 := by
      intro y₁ y₂ hy₁α hy₁₂ hy₂β
      have hinc := increment_pos a φ hφ_cont hφ_anti
      dsimp [J] at hinc
      have hd := hinc y₁ y₂ hy₁₂
      have hJ₁ : J y₁ = 0 := hJ_zero y₁ hy₁α (lt_of_le_of_lt hy₁₂ hy₂β)
      have hJ₂ : J y₂ = 0 := hJ_zero y₂ (lt_of_lt_of_le hy₁α hy₁₂) hy₂β
      dsimp [J] at hJ₁ hJ₂
      rw [hJ₂, hJ₁] at hd
      simpa using hd.symm
    exact weighted_vanish
      (fun s : ℝ => Real.exp (a * s) + Real.exp (a * (s - 1))) φ
      (by continuity) hφ_cont
      (by intro s; positivity) αp βp hαpβp hvanish
  have hneg_case :
      a < 0 → ∀ y : ℝ, αp < y → y < βp → φ y = 0 := by
    intro ha_neg
    let Jneg : ℝ → ℝ := fun y => ∫ s in y..(y + 1), Real.exp (a * s) * φ s
    have hJ_zero : ∀ y : ℝ, αp < y → y < βp → Jneg y = 0 := by
      intro y hyα hyβ
      have hres := (resum_neg a ha_neg φ hφ_cont B hφ_bound hφ_anti y).2
      have hz := hconv_zero y hyα hyβ
      have hpref_pos : 0 < (-a) * Real.exp (-a * y) / (1 + Real.exp a) := by
        exact div_pos (mul_pos (neg_pos.mpr ha_neg) (Real.exp_pos _))
          (by positivity)
      rw [hres] at hz
      simpa [Jneg] using (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpref_pos)
    have hvanish :
        ∀ y₁ y₂ : ℝ, αp < y₁ → y₁ ≤ y₂ → y₂ < βp →
          (∫ s in y₁..y₂,
            (Real.exp (a * s) + Real.exp (a * (s + 1))) * φ s) = 0 := by
      intro y₁ y₂ hy₁α hy₁₂ hy₂β
      have hinc := increment_neg a φ hφ_cont hφ_anti
      dsimp [Jneg] at hinc
      have hd := hinc y₁ y₂ hy₁₂
      have hJ₁ : Jneg y₁ = 0 := hJ_zero y₁ hy₁α (lt_of_le_of_lt hy₁₂ hy₂β)
      have hJ₂ : Jneg y₂ = 0 := hJ_zero y₂ (lt_of_lt_of_le hy₁α hy₁₂) hy₂β
      dsimp [Jneg] at hJ₁ hJ₂
      rw [hJ₂, hJ₁] at hd
      linarith
    exact weighted_vanish
      (fun s : ℝ => Real.exp (a * s) + Real.exp (a * (s + 1))) φ
      (by continuity) hφ_cont
      (by intro s; positivity) αp βp hαpβp hvanish
  rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
  · intro y hyα hyβ
    exact hneg_case ha_neg y hyα hyβ
  · intro y hyα hyβ
    exact hpos_case ha_pos y hyα hyβ


theorem iterate (g : ℝ → ℝ) (Cst η : ℝ) (F : ℕ → ℝ → ℝ) (σ : ℕ → ℝ)
    (hCst : 0 < Cst)
    (hg : ∀ x : ℝ, g x = Cst * F 2 (x - η))
    (hF : ∀ m : ℕ, 2 ≤ m → Continuous (F m) ∧ LatticeDominated (F m))
    (hstep : ∀ m : ℕ, 3 ≤ m → σ m ≠ 0 ∧
      ∀ x : ℝ, F (m - 1) x = conv (centeredExp (σ m)) (F m) x)
    (u v : ℝ) (huv : u < v)
    (hflat : ∀ x : ℝ, u < x → x < v → Halt g x = 0) :
  ∀ N : ℕ, 2 ≤ N →
    ∀ y : ℝ,
      u - η + (Finset.Icc 3 N).sum (fun j => σ j) < y →
      y < v - η + (Finset.Icc 3 N).sum (fun j => σ j) →
      Halt (F N) y = 0 := by
  let P : (N : ℕ) → 2 ≤ N → Prop := fun N _ =>
    ∀ y : ℝ,
      u - η + (Finset.Icc 3 N).sum (fun j => σ j) < y →
      y < v - η + (Finset.Icc 3 N).sum (fun j => σ j) →
      Halt (F N) y = 0
  have hbase : P 2 (by norm_num) := by
    intro y hyu hyv
    have hsum2 : (Finset.Icc 3 2).sum (fun j => σ j) = 0 := by
      simp
    have hyu' : u < y + η := by
      rw [hsum2] at hyu
      linarith
    have hyv' : y + η < v := by
      rw [hsum2] at hyv
      linarith
    have hz := hflat (y + η) hyu' hyv'
    have hHg : Halt g (y + η) = Cst * Halt (F 2) y := by
      calc
        Halt g (y + η) =
            Halt (fun z : ℝ => Cst * F 2 (z - η)) (y + η) := by
          congr 1
          funext z
          exact hg z
        _ = Cst * Halt (F 2) ((y + η) - η) := H_scale (F 2) Cst η (y + η)
        _ = Cst * Halt (F 2) y := by
          congr 1
          ring_nf
    rw [hHg] at hz
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hCst)
  have hsucc :
      ∀ (n : ℕ) (hn : 2 ≤ n), P n hn → P (n + 1) (by omega) := by
    intro n hn ih y hyu hyv
    have h3 : 3 ≤ n + 1 := by omega
    rcases hstep (n + 1) h3 with ⟨hσn, hconvstep⟩
    have hFn_eq :
        F n = conv (centeredExp (σ (n + 1))) (F (n + 1)) := by
      funext x
      have h := hconvstep x
      simpa using h
    let αn : ℝ := u - η + (Finset.Icc 3 n).sum (fun j => σ j)
    let βn : ℝ := v - η + (Finset.Icc 3 n).sum (fun j => σ j)
    have hαβn : αn < βn := by
      dsimp [αn, βn]
      simpa [add_comm, add_left_comm, add_assoc] using
        add_lt_add_right (sub_lt_sub_right huv η)
          ((Finset.Icc 3 n).sum (fun j => σ j))
    have hflatn :
        ∀ x : ℝ, αn < x → x < βn →
          Halt (conv (centeredExp (σ (n + 1))) (F (n + 1))) x = 0 := by
      intro x hxα hxβ
      have hz := ih x (by simpa [αn] using hxα) (by simpa [βn] using hxβ)
      rwa [hFn_eq] at hz
    have hFN := hF (n + 1) (by omega)
    have hdec := deconv (σ (n + 1)) hσn (F (n + 1)) hFN.1 hFN.2
      αn βn hαβn hflatn
    have hsum_succ :
        (Finset.Icc 3 (n + 1)).sum (fun j => σ j) =
          (Finset.Icc 3 n).sum (fun j => σ j) + σ (n + 1) := by
      rw [Finset.sum_Icc_succ_top]
      omega
    have hyα : αn + σ (n + 1) < y := by
      dsimp [αn]
      rw [hsum_succ] at hyu
      linarith
    have hyβ : y < βn + σ (n + 1) := by
      dsimp [βn]
      rw [hsum_succ] at hyv
      linarith
    exact hdec y hyα hyβ
  intro N hN
  exact Nat.le_induction hbase hsucc N hN
