import LeanCode.Vocab














open Filter Topology Set
open scoped Uniformity

namespace Assembly.SelfSim




instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩







theorem denseRange_zsmul_addCircle (θ : ℝ) (hθ : Irrational θ) :
    DenseRange (fun n : ℤ => (n • θ : AddCircle (1 : ℝ))) := by
  rw [AddCircle.denseRange_zsmul_coe_iff]
  simpa using hθ






theorem exists_large_nsmul_mem_nhds_zero (θ : ℝ)
    {U : Set (AddCircle (1 : ℝ))} (hU : U ∈ 𝓝 (0 : AddCircle (1 : ℝ))) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ (k • θ : AddCircle (1 : ℝ)) ∈ U := by


  set x : ℕ → AddCircle (1 : ℝ) := fun n => (n • θ : AddCircle (1 : ℝ)) with hx
  obtain ⟨a, φ, hφ, hconv⟩ := CompactSpace.tendsto_subseq x
  have hCauchy : CauchySeq (x ∘ φ) := hconv.cauchySeq

  have hVunif : {p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) | p.2 - p.1 ∈ U} ∈ 𝓤 (AddCircle (1 : ℝ)) := by
    rw [uniformity_eq_comap_nhds_zero]
    exact ⟨U, hU, fun p hp => hp⟩

  obtain ⟨k₀, hk₀⟩ := hCauchy.mem_entourage hVunif

  have hgrow : ∀ᶠ j in Filter.atTop, k₀ ≤ j ∧ N + φ k₀ + 1 ≤ φ j := by
    have h1 : ∀ᶠ j in Filter.atTop, k₀ ≤ j := Filter.eventually_ge_atTop k₀
    have h2 : ∀ᶠ j in Filter.atTop, N + φ k₀ + 1 ≤ φ j :=
      hφ.tendsto_atTop.eventually_ge_atTop (N + φ k₀ + 1)
    exact h1.and h2
  obtain ⟨j, hj_ge, hj_grow⟩ := hgrow.exists

  have hmem : x (φ j) - x (φ k₀) ∈ U := hk₀ k₀ j le_rfl hj_ge
  refine ⟨φ j - φ k₀, by omega, ?_⟩
  have hsplit : x (φ j) - x (φ k₀) = ((φ j - φ k₀) • θ : AddCircle (1 : ℝ)) := by
    simp only [hx]
    have hkey : (φ j) • (θ : AddCircle (1 : ℝ))
        = (φ j - φ k₀) • (θ : AddCircle (1 : ℝ)) + (φ k₀) • (θ : AddCircle (1 : ℝ)) := by
      rw [← add_nsmul]
      congr 1
      omega
    rw [hkey]
    abel
  rw [hsplit] at hmem
  exact hmem



theorem denseRange_nsmul_addCircle (θ : ℝ) (hθ : Irrational θ) :
    DenseRange (fun n : ℕ => (n • θ : AddCircle (1 : ℝ))) := by
  have hZ : DenseRange (fun n : ℤ => (n • θ : AddCircle (1 : ℝ))) :=
    denseRange_zsmul_addCircle θ hθ

  rw [DenseRange, dense_iff_inter_open]
  intro V hVopen hVne

  obtain ⟨p, hpV, m, hpm⟩ := (dense_iff_inter_open.1 hZ) V hVopen hVne
  subst hpm

  have hVnhds : V ∈ 𝓝 ((m • θ : AddCircle (1 : ℝ))) := hVopen.mem_nhds hpV
  set W : Set (AddCircle (1 : ℝ)) := (fun w => (m • θ : AddCircle (1 : ℝ)) + w) ⁻¹' V with hW
  have hWnhds : W ∈ 𝓝 (0 : AddCircle (1 : ℝ)) := by
    have hcont : Continuous (fun w => (m • θ : AddCircle (1 : ℝ)) + w) := by
      fun_prop
    have := hcont.continuousAt.preimage_mem_nhds (x := (0 : AddCircle (1 : ℝ)))
      (by simpa using hVnhds)
    simpa [hW] using this

  obtain ⟨k, hk_ge, hk_mem⟩ := exists_large_nsmul_mem_nhds_zero θ hWnhds (-m).toNat

  have hmem : (m • θ : AddCircle (1 : ℝ)) + (k • θ : AddCircle (1 : ℝ)) ∈ V := hk_mem
  have hnn : 0 ≤ m + (k : ℤ) := by
    rcases le_or_gt 0 m with hm | hm
    · positivity
    · have hcast : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
      have hk_ge' : ((-m).toNat : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk_ge
      rw [hcast] at hk_ge'; omega
  refine ⟨(m + k).toNat • θ, ?_, ?_⟩
  ·
    have hcast : ((m + k).toNat : ℤ) = m + (k : ℤ) := Int.toNat_of_nonneg hnn
    have hsmul : ((m + k).toNat • (θ : AddCircle (1 : ℝ)))
        = (m • θ : AddCircle (1 : ℝ)) + (k • θ : AddCircle (1 : ℝ)) := by
      rw [← natCast_zsmul, hcast, add_zsmul, natCast_zsmul]
    rw [hsmul]; exact hmem
  · exact Set.mem_range_self _




noncomputable def distZ : AddCircle (1 : ℝ) → ℝ :=
  AddCircle.liftIco 1 0 (fun x => |x - round x|)



theorem abs_sub_round_eqOn_Icc :
    Set.EqOn (fun x : ℝ => |x - round x|) (fun x => min x (1 - x)) (Set.Icc 0 1) := by
  intro x hx
  simp only [Set.mem_Icc] at hx
  simp only
  rcases lt_or_ge x (1 / 2) with hlt | hge
  ·
    have hr : round x = 0 := by
      rw [round_eq_zero_iff]; constructor <;> [linarith [hx.1]; linarith]
    rw [hr]
    simp only [Int.cast_zero, sub_zero, abs_of_nonneg hx.1]
    rw [min_eq_left (by linarith)]
  ·
    have hr : round x = 1 := by
      rw [round_eq_iff]; constructor <;> [linarith; linarith [hx.2]]
    rw [hr]
    simp only [Int.cast_one]
    rw [abs_of_nonpos (by linarith), neg_sub, min_eq_right (by linarith)]

theorem continuous_distZ : Continuous distZ := by
  apply AddCircle.liftIco_zero_continuous
  · simp [round_zero, round_one]
  · apply ContinuousOn.congr _ abs_sub_round_eqOn_Icc
    exact (continuous_id.min (continuous_const.sub continuous_id)).continuousOn


theorem distZ_coe (x : ℝ) : distZ (↑x : AddCircle (1 : ℝ)) = |x - round x| := by
  have hfract : distZ (↑x : AddCircle (1 : ℝ))
      = |Int.fract x - round (Int.fract x)| := by
    unfold distZ
    rw [show (↑x : AddCircle (1 : ℝ)) = ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) from
      (AddCircle.coe_fract x).symm]
    have hmem : Int.fract x ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
    rw [AddCircle.liftIco_zero_coe_apply hmem]
  rw [hfract]

  have hround : round (Int.fract x) = round x - ⌊x⌋ := by
    rw [Int.fract, round_sub_intCast]
  rw [hround, Int.fract]
  push_cast
  ring_nf

theorem distZ_zero : distZ (0 : AddCircle (1 : ℝ)) = 0 := by
  rw [show (0 : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) by simp, distZ_coe]
  simp









theorem exists_qn_dist_to_int (α : ℝ) (hα : Irrational (1 / α)) :
    ∃ q : ℕ → ℕ, StrictMono q ∧
      Filter.Tendsto (fun n => |(q n : ℝ) / α - round ((q n : ℝ) / α)|)
        Filter.atTop (nhds 0) := by
  set θ : ℝ := 1 / α with hθdef

  have key : ∀ (N : ℕ) (ε : ℝ), 0 < ε →
      ∃ k : ℕ, N ≤ k ∧ distZ (k • θ : AddCircle (1 : ℝ)) < ε := by
    intro N ε hε

    have hUopen : IsOpen (distZ ⁻¹' Set.Iio ε) := continuous_distZ.isOpen_preimage _ isOpen_Iio
    have hUmem : (0 : AddCircle (1 : ℝ)) ∈ distZ ⁻¹' Set.Iio ε := by
      simp only [Set.mem_preimage, Set.mem_Iio, distZ_zero]; exact hε
    obtain ⟨k, hk_ge, hk_mem⟩ :=
      exists_large_nsmul_mem_nhds_zero θ (hUopen.mem_nhds hUmem) N
    exact ⟨k, hk_ge, hk_mem⟩

  choose! f hf_ge hf_lt using key

  set q : ℕ → ℕ := fun n => Nat.rec (f 0 1)
    (fun n qn => f (qn + 1) (1 / (n + 2))) n with hq
  have hq0 : q 0 = f 0 1 := rfl
  have hqsucc : ∀ n, q (n + 1) = f (q n + 1) (1 / (n + 2)) := fun n => rfl

  have hmono : StrictMono q := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hqsucc n]
    have := hf_ge (q n + 1) (1 / (n + 2)) (by positivity)
    omega
  refine ⟨q, hmono, ?_⟩

  have hbound : ∀ n, distZ (q n • θ : AddCircle (1 : ℝ)) < 1 / (n + 1) := by
    intro n
    cases n with
    | zero => rw [hq0]; simpa using hf_lt 0 1 one_pos
    | succ m =>
      rw [hqsucc m]
      have := hf_lt (q m + 1) (1 / (m + 2)) (by positivity)
      convert this using 2
      push_cast; ring

  have hrw : ∀ n, distZ (q n • θ : AddCircle (1 : ℝ))
      = |(q n : ℝ) / α - round ((q n : ℝ) / α)| := by
    intro n
    have hcoe : (q n • θ : AddCircle (1 : ℝ)) = (((q n : ℝ) / α : ℝ) : AddCircle (1 : ℝ)) := by
      rw [← AddCircle.coe_nsmul]
      congr 1
      simp only [nsmul_eq_mul, hθdef]; ring
    rw [hcoe, distZ_coe]

  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ => (0 : ℝ)) (h := fun n : ℕ => 1 / ((n : ℝ) + 1))
    tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n => abs_nonneg _) (fun n => ?_)
  rw [← hrw n]
  exact (hbound n).le



section UniformCont

variable (g : ℝ → ℝ)



noncomputable def bj (R : ℝ) (j : ℤ) : ℝ :=
  sSup ((fun v => |g ((j : ℝ) + v)|) '' Set.Icc (-R) R)



theorem bj_nonneg (hg : Continuous g) {R : ℝ} (hR : 0 ≤ R) (j : ℤ) :
    0 ≤ bj g R j := by
  have hcont : Continuous (fun v => |g ((j : ℝ) + v)|) :=
    (continuous_abs.comp (hg.comp (continuous_const.add continuous_id)))
  have hbdd : BddAbove ((fun v => |g ((j : ℝ) + v)|) '' Set.Icc (-R) R) :=
    (isCompact_Icc.bddAbove_image (hcont.continuousOn))
  have h0 : (0 : ℝ) ∈ Set.Icc (-R) R := by constructor <;> linarith
  have := le_csSup hbdd (Set.mem_image_of_mem _ h0)
  exact (abs_nonneg _).trans this


theorem le_bj (hg : Continuous g) {R : ℝ} (j : ℤ) {v : ℝ} (hv : v ∈ Set.Icc (-R) R) :
    |g ((j : ℝ) + v)| ≤ bj g R j := by
  have hcont : Continuous (fun w => |g ((j : ℝ) + w)|) :=
    (continuous_abs.comp (hg.comp (continuous_const.add continuous_id)))
  have hbdd : BddAbove ((fun w => |g ((j : ℝ) + w)|) '' Set.Icc (-R) R) :=
    (isCompact_Icc.bddAbove_image (hcont.continuousOn))
  exact le_csSup hbdd ⟨v, hv, rfl⟩



theorem bj_summable (hg : Continuous g) (hdec : Assembly.HasPolynomialDecay g)
    {R : ℝ} (hR : 0 < R) : Summable (bj g R) := by
  obtain ⟨C, η, hC, hη, hbound⟩ := hdec

  have hmaj : Summable (fun j : ℤ => C * 2 ^ η * |(j : ℝ)| ^ (-η)) :=
    (Real.summable_abs_int_rpow hη).mul_left (C * 2 ^ η)
  refine hmaj.of_norm_bounded_eventually ?_

  set N : ℤ := ⌈2 * R + 1⌉ with hN
  have hcofin : {j : ℤ | (2 * R + 1 : ℝ) ≤ |(j : ℝ)|}ᶜ.Finite := by
    apply Set.Finite.subset (Set.finite_Icc (-N) N)
    intro j hj
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hj
    rw [abs_lt] at hj
    have hNc : (2 * R + 1 : ℝ) ≤ (N : ℝ) := Int.le_ceil _
    simp only [Set.mem_Icc]
    constructor
    · rw [← @Int.cast_le ℝ]; push_cast; linarith [hj.1]
    · rw [← @Int.cast_le ℝ]; linarith [hj.2]
  rw [Filter.eventually_cofinite]
  refine hcofin.subset ?_
  intro j hj
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hj ⊢

  intro hle'
  apply hj

  have hjpos : (0 : ℝ) < |(j : ℝ)| := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (bj_nonneg g hg hR.le j)]

  have hcont : Continuous (fun v => |g ((j : ℝ) + v)|) :=
    (continuous_abs.comp (hg.comp (continuous_const.add continuous_id)))
  have hbdd : BddAbove ((fun v => |g ((j : ℝ) + v)|) '' Set.Icc (-R) R) :=
    (isCompact_Icc.bddAbove_image (hcont.continuousOn))
  unfold bj
  apply Real.sSup_le _ (by positivity)
  rintro y ⟨v, hv, rfl⟩
  simp only [Set.mem_Icc] at hv

  have hstep1 : |g ((j : ℝ) + v)| ≤ C / (1 + |(j : ℝ) + v|) ^ η := hbound _
  refine hstep1.trans ?_

  have hgeom : |(j : ℝ)| / 2 ≤ 1 + |(j : ℝ) + v| := by
    have h1 : |(j : ℝ)| - |v| ≤ |(j : ℝ) + v| := by
      have := abs_sub_abs_le_abs_sub (j : ℝ) (-v)
      simp only [sub_neg_eq_add, abs_neg] at this
      linarith
    have h2 : |v| ≤ R := by rw [abs_le]; exact ⟨hv.1, hv.2⟩
    have : |(j : ℝ)| / 2 ≤ |(j : ℝ)| - R := by nlinarith [hle']
    linarith
  have hbase_pos : (0 : ℝ) < |(j : ℝ)| / 2 := by positivity

  have hpow : (|(j : ℝ)| / 2) ^ η ≤ (1 + |(j : ℝ) + v|) ^ η :=
    Real.rpow_le_rpow hbase_pos.le hgeom (by linarith)
  have hpow_pos : (0 : ℝ) < (|(j : ℝ)| / 2) ^ η := Real.rpow_pos_of_pos hbase_pos _

  have hstep2 : C / (1 + |(j : ℝ) + v|) ^ η ≤ C / (|(j : ℝ)| / 2) ^ η :=
    div_le_div_of_nonneg_left hC.le hpow_pos hpow
  refine hstep2.trans_eq ?_

  rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (abs_nonneg _)]
  field_simp



theorem uniformCont_shiftSup (hg : Continuous g) (hdec : Assembly.HasPolynomialDecay g)
    {R : ℝ} (hR : 0 < R) (u : ℕ → ℝ) (u₀ : ℝ)
    (hu : ∀ n, u n ∈ Set.Icc (-R) R) (hu₀ : u₀ ∈ Set.Icc (-R) R)
    (htend : Filter.Tendsto u Filter.atTop (nhds u₀)) :
    Filter.Tendsto (fun n => ⨆ m : ℤ, |g ((m : ℝ) + u n) - g ((m : ℝ) + u₀)|)
      Filter.atTop (nhds 0) := by
  set h : ℕ → ℤ → ℝ := fun n m => |g ((m : ℝ) + u n) - g ((m : ℝ) + u₀)| with hh
  have hbj : Summable (bj g R) := bj_summable g hg hdec hR

  have hdom : ∀ n m, h n m ≤ 2 * bj g R m := by
    intro n m
    rw [hh]
    have h1 : |g ((m : ℝ) + u n)| ≤ bj g R m := le_bj g hg m (hu n)
    have h2 : |g ((m : ℝ) + u₀)| ≤ bj g R m := le_bj g hg m hu₀
    have htri : |g ((m : ℝ) + u n) - g ((m : ℝ) + u₀)|
        ≤ |g ((m : ℝ) + u n)| + |g ((m : ℝ) + u₀)| := by
      have := abs_sub_le (g ((m : ℝ) + u n)) 0 (g ((m : ℝ) + u₀))
      simpa using this
    calc |g ((m : ℝ) + u n) - g ((m : ℝ) + u₀)|
        ≤ |g ((m : ℝ) + u n)| + |g ((m : ℝ) + u₀)| := htri
      _ ≤ bj g R m + bj g R m := by gcongr
      _ = 2 * bj g R m := by ring
  have hh_nonneg : ∀ n m, 0 ≤ h n m := fun n m => by rw [hh]; exact abs_nonneg _
  have hbj_nonneg : ∀ m, 0 ≤ bj g R m := fun m => bj_nonneg g hg hR.le m

  have hbj_cofin : Filter.Tendsto (bj g R) Filter.cofinite (nhds 0) :=
    hbj.tendsto_cofinite_zero

  have hbj_bdd : ∃ B, ∀ m, bj g R m ≤ B := by
    have hfin : {m : ℤ | 1 ≤ bj g R m}.Finite := by
      have hev : ∀ᶠ m in Filter.cofinite, bj g R m < 1 :=
        hbj_cofin.eventually (eventually_lt_nhds (by norm_num))
      rw [Filter.eventually_cofinite] at hev
      exact hev.subset (fun m hm => not_lt.mpr hm)
    obtain ⟨B₀, hB₀⟩ := (hfin.image (bj g R)).bddAbove
    refine ⟨max 1 B₀, fun m => ?_⟩
    rcases lt_or_ge (bj g R m) 1 with h | h
    · exact h.le.trans (le_max_left _ _)
    · exact (hB₀ (Set.mem_image_of_mem _ h)).trans (le_max_right _ _)
  obtain ⟨B, hB⟩ := hbj_bdd

  have hBdd : ∀ n, BddAbove (Set.range (fun m => h n m)) := by
    intro n
    refine ⟨2 * B, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact (hdom n m).trans (by have := hB m; nlinarith [hbj_nonneg m])

  rw [Metric.tendsto_atTop]
  intro ε hε

  have hSfin : {m : ℤ | ε / 2 ≤ 2 * bj g R m}.Finite := by
    have h2bj : Filter.Tendsto (fun m => 2 * bj g R m) Filter.cofinite (nhds 0) := by
      have := hbj_cofin.const_mul (2 : ℝ)
      simpa using this
    have hev : ∀ᶠ m in Filter.cofinite, 2 * bj g R m < ε / 2 :=
      h2bj.eventually (eventually_lt_nhds (by positivity))
    rw [Filter.eventually_cofinite] at hev
    exact hev.subset (fun m hm => by simpa using hm)

  have hSbound : ∀ᶠ n in Filter.atTop,
      ∀ m ∈ {m : ℤ | ε / 2 ≤ 2 * bj g R m}, h n m ≤ ε / 2 := by
    rw [Filter.eventually_all_finite hSfin]
    intro m _

    have hcont : Continuous (fun w : ℝ => |g ((m : ℝ) + w) - g ((m : ℝ) + u₀)|) := by
      fun_prop
    have h0 : |g ((m : ℝ) + u₀) - g ((m : ℝ) + u₀)| = 0 := by simp
    have htend0 : Filter.Tendsto (fun n => h n m) Filter.atTop (nhds 0) := by
      have := (hcont.tendsto u₀).comp htend
      rw [h0] at this
      simpa [hh, Function.comp_def] using this
    have : ∀ᶠ n in Filter.atTop, h n m < ε / 2 :=
      htend0.eventually (eventually_lt_nhds (by positivity))
    filter_upwards [this] with n hn using hn.le
  rw [Filter.eventually_atTop] at hSbound
  obtain ⟨N, hN⟩ := hSbound
  refine ⟨N, fun n hn_ge => ?_⟩
  have hn := hN n hn_ge

  show dist (⨆ m : ℤ, h n m) 0 < ε

  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_ciSup_of_le (hBdd n) 0 (hh_nonneg n 0))]
  refine lt_of_le_of_lt (ciSup_le (fun m => ?_)) (by linarith : ε / 2 < ε)
  by_cases hm : ε / 2 ≤ 2 * bj g R m
  ·
    exact hn m hm
  ·
    rw [not_le] at hm
    exact (hdom n m).trans hm.le





theorem uniformCont_columnSum (hg : Continuous g) (hdec : Assembly.HasPolynomialDecay g)
    {R : ℝ} (hR : 0 < R) (u : ℤ → ℕ → ℝ) (u₀ : ℤ → ℝ)
    (hu : ∀ k n, u k n ∈ Set.Icc (-R) R) (hu₀ : ∀ k, u₀ k ∈ Set.Icc (-R) R)
    (htend : ∀ k, Filter.Tendsto (u k) Filter.atTop (nhds (u₀ k))) (l : ℤ) :
    Filter.Tendsto
      (fun n => ∑' k : ℤ, |g ((k : ℝ) - l + u k n) - g ((k : ℝ) - l + u₀ k)|)
      Filter.atTop (nhds 0) := by


  set F : ℕ → ℤ → ℝ :=
    fun n k => |g ((k : ℝ) - l + u k n) - g ((k : ℝ) - l + u₀ k)| with hF
  set bound : ℤ → ℝ := fun k => 2 * bj g R (k - l) with hbound

  have hsum_bound : Summable bound := by
    have hbj : Summable (bj g R) := bj_summable g hg hdec hR
    have hshift : Summable (fun k : ℤ => bj g R (k - l)) := by
      have hinj : Function.Injective (fun k : ℤ => k - l) := fun a b h => by
        simpa using h
      exact hbj.comp_injective hinj
    exact hshift.mul_left 2

  have hterm : ∀ k : ℤ, Filter.Tendsto (fun n => F n k) Filter.atTop (nhds (0 : ℝ)) := by
    intro k
    have hcont : Continuous (fun w : ℝ => |g ((k : ℝ) - l + w) - g ((k : ℝ) - l + u₀ k)|) := by
      fun_prop
    have h0 : |g ((k : ℝ) - l + u₀ k) - g ((k : ℝ) - l + u₀ k)| = 0 := by simp
    have := (hcont.tendsto (u₀ k)).comp (htend k)
    rw [h0] at this
    simpa [hF, Function.comp_def] using this

  have hdom : ∀ n : ℕ, ∀ k : ℤ, ‖F n k‖ ≤ bound k := by
    intro n k
    rw [hF, hbound]
    simp only [Real.norm_eq_abs, abs_abs]

    have hcast : ((k - l : ℤ) : ℝ) = (k : ℝ) - l := by push_cast; ring
    have h1 : |g ((k : ℝ) - l + u k n)| ≤ bj g R (k - l) := by
      have := le_bj g hg (k - l) (v := u k n) (hu k n)
      rwa [hcast] at this
    have h2 : |g ((k : ℝ) - l + u₀ k)| ≤ bj g R (k - l) := by
      have := le_bj g hg (k - l) (v := u₀ k) (hu₀ k)
      rwa [hcast] at this
    have htri : |g ((k : ℝ) - l + u k n) - g ((k : ℝ) - l + u₀ k)|
        ≤ |g ((k : ℝ) - l + u k n)| + |g ((k : ℝ) - l + u₀ k)| := by
      have := abs_sub_le (g ((k : ℝ) - l + u k n)) 0 (g ((k : ℝ) - l + u₀ k))
      simpa using this
    calc |g ((k : ℝ) - l + u k n) - g ((k : ℝ) - l + u₀ k)|
        ≤ |g ((k : ℝ) - l + u k n)| + |g ((k : ℝ) - l + u₀ k)| := htri
      _ ≤ bj g R (k - l) + bj g R (k - l) := by gcongr
      _ = 2 * bj g R (k - l) := by ring

  have := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := F) (g := fun _ : ℤ => (0 : ℝ)) (bound := bound)
    hsum_bound hterm (Filter.Eventually.of_forall hdom)
  simpa [hF] using this

end UniformCont

end Assembly.SelfSim
