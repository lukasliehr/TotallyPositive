import Mathlib.Analysis.Fourier.AddCircle
import LeanCode.Vendor.E5.P10.Part10.Kernels
import LeanCode.Vendor.E5.Defs

open MeasureTheory


noncomputable def chi (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))


noncomputable def cn (g : ℝ → ℝ) (n : ℤ) : ℂ :=
  (1 / 2 : ℂ) * ∫ x in (0 : ℝ)..2, (Halt g x : ℂ) * chi n x


theorem char (g : ℝ → ℝ) (n j : ℤ) (x : ℝ) :
    ‖chi n x‖ = 1 ∧
    chi n (x + j) = (-1 : ℂ) ^ (n * j) * chi n x ∧
    FT g ((n : ℝ) / 2) = ∫ t : ℝ, chi n t * (g t : ℂ) := by
  constructor
  · unfold chi
    rw [Complex.norm_exp]
    have hre : (-(Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    norm_num
  constructor
  · unfold chi
    have hsplit : -(Real.pi : ℂ) * Complex.I * (n : ℂ) * ((x + j : ℝ) : ℂ) =
        (-(Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) +
          (-(Real.pi : ℂ) * Complex.I * (n : ℂ) * (j : ℂ)) := by
      norm_num [Complex.ofReal_add, Complex.ofReal_intCast]
      ring
    rw [hsplit, Complex.exp_add]
    have hfactor : Complex.exp (-(Real.pi : ℂ) * Complex.I * (n : ℂ) * (j : ℂ)) =
        (-1 : ℂ) ^ (n * j) := by
      have harg : -(Real.pi : ℂ) * Complex.I * (n : ℂ) * (j : ℂ) =
          ((-(n * j) : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
        norm_num [Complex.ofReal_intCast]
        ring
      rw [harg, Complex.exp_int_mul, Complex.exp_pi_mul_I]
      rw [show (-1 : ℂ) ^ (-(n * j)) = (-1 : ℂ) ^ (n * j) by
        rw [neg_one_zpow_eq_ite, neg_one_zpow_eq_ite]
        simp [even_neg]]
    rw [hfactor]
    ring
  · unfold FT chi
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    have hhalf : (2 : ℂ) * (((n : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) := by
      norm_num [Complex.ofReal_div, Complex.ofReal_intCast]
      field_simp
    have harg : -2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) / 2 : ℝ) : ℂ) * (t : ℂ) =
        -(Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) := by
      calc
        -2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) / 2 : ℝ) : ℂ) * (t : ℂ)
            = -((Real.pi : ℂ) * Complex.I *
                ((2 : ℂ) * (((n : ℝ) / 2 : ℝ) : ℂ)) * (t : ℂ)) := by ring
        _ = -((Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) := by rw [hhalf]
        _ = -(Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) := by ring
    rw [harg]


theorem g_char_int (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_int : MeasureTheory.Integrable g) (n : ℤ) :
    MeasureTheory.Integrable (fun t : ℝ => chi n t * (g t : ℂ)) ∧
      FT g ((n : ℝ) / 2) = ∫ t : ℝ, chi n t * (g t : ℂ) := by
  have _ : Continuous g := hg_cont
  have hchi_cont : Continuous (fun t : ℝ => chi n t) := by
    unfold chi
    continuity
  have hbound : ∀ᵐ t : ℝ, ‖chi n t‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun t => by
      rw [(char g n 0 t).1]
  constructor
  · exact (hg_int.ofReal).bdd_mul hchi_cont.aestronglyMeasurable hbound
  · exact (char g n 0 0).2.2


theorem unit_partition (h : ℝ → ℂ) (hh : MeasureTheory.Integrable h) (y : ℝ) :
    Summable (fun k : ℤ => ∫ t in (y + k)..(y + k + 1), h t) ∧
      (∑' k : ℤ, ∫ t in (y + k)..(y + k + 1), h t) = ∫ t : ℝ, h t := by
  have hsum : HasSum (fun k : ℤ => ∫ t in (y + k)..(y + k + 1), h t) (∫ t : ℝ, h t) := by
    simpa using hh.hasSum_intervalIntegral y
  exact ⟨hsum.summable, hsum.tsum_eq⟩


theorem width2_partition (h : ℝ → ℂ) (hh : MeasureTheory.Integrable h) :
    Summable (fun m : ℤ => ∫ t in (2 * (m : ℝ))..(2 * (m : ℝ) + 2), h t) ∧
      Summable (fun m : ℤ => ∫ t in (2 * (m : ℝ) + 1)..(2 * (m : ℝ) + 3), h t) ∧
      (∑' m : ℤ, ∫ t in (2 * (m : ℝ))..(2 * (m : ℝ) + 2), h t) =
        ∫ t : ℝ, h t ∧
      (∑' m : ℤ, ∫ t in (2 * (m : ℝ) + 1)..(2 * (m : ℝ) + 3), h t) =
        ∫ t : ℝ, h t := by
  let a : ℤ → ℂ := fun k => ∫ t in (k : ℝ)..((k : ℝ) + 1), h t
  let W0 : ℤ → ℂ := fun m => ∫ t in (2 * (m : ℝ))..(2 * (m : ℝ) + 2), h t
  let W1 : ℤ → ℂ := fun m => ∫ t in (2 * (m : ℝ) + 1)..(2 * (m : ℝ) + 3), h t
  have hunit := unit_partition h hh 0
  have ha : Summable a := by
    simpa [a] using hunit.1
  have ha_tsum : tsum a = ∫ t : ℝ, h t := by
    simpa [a] using hunit.2
  have hpar := parity_split a ha
  have hW0_eq : W0 = fun m : ℤ => a (2 * m) + a (2 * m + 1) := by
    funext m
    have hchasles := intervalIntegral.integral_add_adjacent_intervals
      (hh.intervalIntegrable (a := 2 * (m : ℝ)) (b := 2 * (m : ℝ) + 1))
      (hh.intervalIntegrable (a := 2 * (m : ℝ) + 1) (b := 2 * (m : ℝ) + 2))
    simp [W0, a]
    convert hchasles.symm using 1; ring_nf
  have hW0_sum : Summable W0 := by
    have hsum : Summable (fun m : ℤ => a (2 * m) + a (2 * m + 1)) := hpar.1.add hpar.2.1
    rw [hW0_eq]
    exact hsum
  have hW0_tsum : tsum W0 = ∫ t : ℝ, h t := by
    rw [hW0_eq]
    rw [Summable.tsum_add hpar.1 hpar.2.1]
    rw [← hpar.2.2]
    exact ha_tsum
  let b : ℤ → ℂ := fun k => a (k + 1)
  have hb : Summable b := by
    simpa [b, Function.comp_def, Equiv.addRight] using
      ((Equiv.addRight (1 : ℤ)).summable_iff (f := a)).mpr ha
  have hb_tsum_a : tsum b = tsum a := by
    simpa [b, Function.comp_def, Equiv.addRight] using
      ((Equiv.addRight (1 : ℤ)).tsum_eq a)
  have hb_tsum : tsum b = ∫ t : ℝ, h t := by
    rw [hb_tsum_a, ha_tsum]
  have hparb := parity_split b hb
  have hW1_eq : W1 = fun m : ℤ => b (2 * m) + b (2 * m + 1) := by
    funext m
    have hchasles := intervalIntegral.integral_add_adjacent_intervals
      (hh.intervalIntegrable (a := 2 * (m : ℝ) + 1) (b := 2 * (m : ℝ) + 2))
      (hh.intervalIntegrable (a := 2 * (m : ℝ) + 2) (b := 2 * (m : ℝ) + 3))
    simp [W1, b, a]
    convert hchasles.symm using 1; ring_nf
  have hW1_sum : Summable W1 := by
    have hsum : Summable (fun m : ℤ => b (2 * m) + b (2 * m + 1)) := hparb.1.add hparb.2.1
    rw [hW1_eq]
    exact hsum
  have hW1_tsum : tsum W1 = ∫ t : ℝ, h t := by
    rw [hW1_eq]
    rw [Summable.tsum_add hparb.1 hparb.2.1]
    rw [← hparb.2.2]
    exact hb_tsum
  exact ⟨hW0_sum, hW1_sum, hW0_tsum, hW1_tsum⟩


theorem coeff_termwise (g : ℝ → ℝ) (hg_cont : Continuous g)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg_bound : ∀ t : ℝ, |g t| ≤ C * Real.exp (-c * |t|)) (n : ℤ) :
  let A : ℤ → ℂ := fun k => (-1 : ℂ) ^ k *
    (∫ x in (0 : ℝ)..2, (g (x + k) : ℂ) * chi n x)
  Summable A ∧ cn g n = (1 / 2 : ℂ) * (∑' k : ℤ, A k) := by
  let F : ℤ → ℝ → ℂ := fun k x => (-1 : ℂ) ^ k * ((g (x + k) : ℂ) * chi n x)
  let B : ℤ → ℝ → ℝ := fun k _x => C * Real.exp (c * 2) * Real.exp (-c * |(k : ℝ)|)
  have henv_all := env_decay C c hC hc g hg_bound
  have henv_local : HasLocalLatticeEnvelopes g := henv_all.2
  have henv2 := henv_all.1 2 (by norm_num : (0 : ℝ) ≤ 2)
  have hB_sum : Summable
      (fun k : ℤ => C * Real.exp (c * 2) * Real.exp (-c * |(k : ℝ)|)) :=
    henv2.2
  have hF_meas : ∀ k : ℤ,
      AEStronglyMeasurable (F k) (volume.restrict (Set.uIoc (0 : ℝ) 2)) := by
    intro k
    have hcont : Continuous (F k) := by
      dsimp [F, chi]
      continuity
    exact hcont.aestronglyMeasurable
  have h_bound : ∀ k : ℤ, ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Set.uIoc (0 : ℝ) 2 → ‖F k t‖ ≤ B k t := by
    intro k
    filter_upwards with t ht
    have ht_abs : |t| ≤ (2 : ℝ) := by
      have ht' : 0 < t ∧ t ≤ 2 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hgb := henv2.1 k t ht_abs
    calc
      ‖F k t‖ = |g (t + k)| := by
        simp [F, (char g n 0 t).1]
      _ ≤ C * Real.exp (c * 2) * Real.exp (-c * |(k : ℝ)|) := hgb
      _ = B k t := rfl
  have h_bound_summable : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Set.uIoc (0 : ℝ) 2 → Summable fun k : ℤ => B k t := by
    filter_upwards with t _ht
    simpa [B] using hB_sum
  have h_bound_integrable :
      IntervalIntegrable (fun t : ℝ => tsum (fun k : ℤ => B k t)) volume (0 : ℝ) 2 := by
    have hconst : (fun t : ℝ => tsum (fun k : ℤ => B k t)) =
        fun _t : ℝ =>
          tsum (fun k : ℤ => C * Real.exp (c * 2) * Real.exp (-c * |(k : ℝ)|)) := by
      funext t
      apply tsum_congr
      intro k
      rfl
    rw [hconst]
    exact intervalIntegrable_const
  have h_lim : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 2 →
      HasSum (fun k : ℤ => F k t) ((Halt g t : ℂ) * chi n t) := by
    filter_upwards with t _ht
    have hsum_real : HasSum (fun k : ℤ => (-1 : ℝ) ^ k * g (t + k)) (Halt g t) := by
      exact (H_abs g henv_local t).2.1.hasSum
    have hsum_complex :
        HasSum (fun k : ℤ => (((-1 : ℝ) ^ k * g (t + k) : ℝ) : ℂ))
          ((Halt g t : ℂ)) := by
      exact Complex.hasSum_ofReal.mpr hsum_real
    have hmul := hsum_complex.mul_right (chi n t)
    simpa [F, Complex.ofReal_mul, Complex.ofReal_zpow, mul_assoc] using hmul
  have hhas : HasSum (fun k : ℤ => ∫ x in (0 : ℝ)..2, F k x)
      (∫ x in (0 : ℝ)..2, (Halt g x : ℂ) * chi n x) :=
    intervalIntegral.hasSum_integral_of_dominated_convergence
      B hF_meas h_bound h_bound_summable h_bound_integrable h_lim
  let A : ℤ → ℂ := fun k => (-1 : ℂ) ^ k *
    (∫ x in (0 : ℝ)..2, (g (x + k) : ℂ) * chi n x)
  have hterm : (fun k : ℤ => ∫ x in (0 : ℝ)..2, F k x) = A := by
    funext k
    dsimp [A, F]
    rw [intervalIntegral.integral_const_mul]
  have hA_has : HasSum A (∫ x in (0 : ℝ)..2, (Halt g x : ℂ) * chi n x) := by
    simpa [hterm] using hhas
  constructor
  · exact hA_has.summable
  · unfold cn
    rw [hA_has.tsum_eq]


theorem coeff_shift (g : ℝ → ℝ) (hg_cont : Continuous g) (n j : ℤ) :
    (∫ x in (0 : ℝ)..2, (g (x + j) : ℂ) * chi n x) =
      (-1 : ℂ) ^ (n * j) *
        (∫ t in (j : ℝ)..((j : ℝ) + 2), (g t : ℂ) * chi n t) := by
  have _hcont : Continuous g := hg_cont
  let f : ℝ → ℂ := fun t => (g t : ℂ) * chi n (t - j)
  have htranslate :
      (∫ x in (0 : ℝ)..2, (g (x + j) : ℂ) * chi n x) =
        ∫ t in (j : ℝ)..((j : ℝ) + 2), (g t : ℂ) * chi n (t - j) := by
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 2) f (j : ℝ)
    simpa [f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  rw [htranslate]
  have hpoint : ∀ t : ℝ,
      (g t : ℂ) * chi n (t - j) =
        (-1 : ℂ) ^ (n * j) * ((g t : ℂ) * chi n t) := by
    intro t
    have hchar := (char g n (-j) t).2.1
    have harg : t + ((-j : ℤ) : ℝ) = t - j := by
      norm_num [Int.cast_neg]
      ring
    rw [harg] at hchar
    have hpow : (-1 : ℂ) ^ (n * (-j)) = (-1 : ℂ) ^ (n * j) := by
      rw [show n * (-j) = -(n * j) by ring]
      rw [neg_one_zpow_eq_ite, neg_one_zpow_eq_ite]
      simp [even_neg]
    rw [hchar, hpow]
    ring
  rw [intervalIntegral.integral_congr (fun t _ht => hpoint t)]
  rw [intervalIntegral.integral_const_mul]


theorem coefficients (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_int : MeasureTheory.Integrable g)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg_bound : ∀ t : ℝ, |g t| ≤ C * Real.exp (-c * |t|)) (n : ℤ) :
  cn g n = ((1 - (-1 : ℂ) ^ n) / 2) * FT g ((n : ℝ) / 2) ∧
    (Odd n → cn g n = FT g ((n : ℝ) / 2)) ∧
    (Even n → cn g n = 0) := by
  let A : ℤ → ℂ := fun k => (-1 : ℂ) ^ k *
    (∫ x in (0 : ℝ)..2, (g (x + k) : ℂ) * chi n x)
  let h : ℝ → ℂ := fun t => (g t : ℂ) * chi n t
  have hterm := coeff_termwise g hg_cont C c hC hc hg_bound n
  have hA_sum : Summable A := by
    simpa [A] using hterm.1
  have hcn_term : cn g n = (1 / 2 : ℂ) * tsum A := by
    simpa [A] using hterm.2
  have hpar := parity_split A hA_sum
  have hgchar := g_char_int g hg_cont hg_int n
  have hh_int : MeasureTheory.Integrable h := by
    refine hgchar.1.congr ?_
    filter_upwards with t
    dsimp [h]
    ring_nf
  have hFT_int : (∫ t : ℝ, h t) = FT g ((n : ℝ) / 2) := by
    have hcomm : (∫ t : ℝ, h t) = ∫ t : ℝ, chi n t * (g t : ℂ) := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp [h]
      ring_nf
    rw [hcomm, ← hgchar.2]
  have hwidth := width2_partition h hh_int
  have hA_even_eq : (fun m : ℤ => A (2 * m)) =
      fun m : ℤ => ∫ t in (2 * (m : ℝ))..(2 * (m : ℝ) + 2), h t := by
    funext m
    have hshift := coeff_shift g hg_cont n (2 * m)
    have hp1 : (-1 : ℂ) ^ (2 * m) = 1 := by
      have he : Even (2 * m) := ⟨m, by ring_nf⟩
      exact Even.neg_one_zpow he
    have hp2 : (-1 : ℂ) ^ (n * (2 * m)) = 1 := by
      have he : Even (2 * m) := ⟨m, by ring_nf⟩
      have hprod : Even (n * (2 * m)) := he.mul_left n
      exact Even.neg_one_zpow hprod
    dsimp [A]
    rw [hshift, hp1, hp2]
    simp [h, Int.cast_mul]
  have hA_odd_eq : (fun m : ℤ => A (2 * m + 1)) =
      fun m : ℤ => -((-1 : ℂ) ^ n) *
        (∫ t in (2 * (m : ℝ) + 1)..(2 * (m : ℝ) + 3), h t) := by
    funext m
    have hshift := coeff_shift g hg_cont n (2 * m + 1)
    have hp1 : (-1 : ℂ) ^ (2 * m + 1) = -1 := by
      have ho : Odd (2 * m + 1) := ⟨m, by ring_nf⟩
      exact Odd.neg_one_zpow ho
    have hp2 : (-1 : ℂ) ^ (n * (2 * m + 1)) = (-1 : ℂ) ^ n := by
      rcases Int.even_or_odd n with hn | hn
      · have hprod : Even (n * (2 * m + 1)) := hn.mul_right _
        rw [Even.neg_one_zpow hn, Even.neg_one_zpow hprod]
      · have hodd_factor : Odd (2 * m + 1) := ⟨m, by ring_nf⟩
        have hprod : Odd (n * (2 * m + 1)) := hn.mul hodd_factor
        rw [Odd.neg_one_zpow hn, Odd.neg_one_zpow hprod]
    dsimp [A]
    have hpow_ne : (-1 : ℂ) ^ n ≠ 0 := zpow_ne_zero n (by norm_num)
    rw [hshift, hp1, hp2]
    simp [h, Int.cast_add, Int.cast_mul, hpow_ne]
    ring_nf
  have heven_tsum : tsum (fun m : ℤ => A (2 * m)) = FT g ((n : ℝ) / 2) := by
    rw [hA_even_eq, hwidth.2.2.1, hFT_int]
  have hodd_tsum : tsum (fun m : ℤ => A (2 * m + 1)) =
      -((-1 : ℂ) ^ n) * FT g ((n : ℝ) / 2) := by
    rw [hA_odd_eq]
    rw [tsum_mul_left]
    rw [hwidth.2.2.2, hFT_int]
  have hmain : cn g n = ((1 - (-1 : ℂ) ^ n) / 2) * FT g ((n : ℝ) / 2) := by
    calc
      cn g n = (1 / 2 : ℂ) * tsum A := hcn_term
      _ = (1 / 2 : ℂ) *
          (tsum (fun m : ℤ => A (2 * m)) + tsum (fun m : ℤ => A (2 * m + 1))) := by
        rw [hpar.2.2]
      _ = ((1 - (-1 : ℂ) ^ n) / 2) * FT g ((n : ℝ) / 2) := by
        rw [heven_tsum, hodd_tsum]
        ring
  refine ⟨hmain, ?_, ?_⟩
  · intro hn
    have hp : (-1 : ℂ) ^ n = -1 := Odd.neg_one_zpow hn
    rw [hmain, hp]
    ring
  · intro hn
    have hp : (-1 : ℂ) ^ n = 1 := Even.neg_one_zpow hn
    rw [hmain, hp]
    ring


theorem coeff_bound (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_int : MeasureTheory.Integrable g)
    (C c C₀ γ : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hC₀ : 0 < C₀) (hγ : 0 < γ)
    (hg_bound : ∀ t : ℝ, |g t| ≤ C * Real.exp (-c * |t|))
    (hFT : ∀ ξ : ℝ, ‖FT g ξ‖ ≤ C₀ * Real.exp (-γ * ξ ^ 2)) :
    ∀ n : ℤ, ‖cn g n‖ ≤ C₀ * Real.exp (-γ * (n : ℝ) ^ 2 / 4) := by
  have _ : 0 < γ := hγ
  intro n
  have hcoeff := coefficients g hg_cont hg_int C c hC hc hg_bound n
  by_cases hn_odd : Odd n
  · have hcn : cn g n = FT g ((n : ℝ) / 2) := hcoeff.2.1 hn_odd
    rw [hcn]
    have h := hFT ((n : ℝ) / 2)
    convert h using 2
    ring_nf
  · have hn_even : Even n := (Int.not_odd_iff_even).mp hn_odd
    have hcn : cn g n = 0 := hcoeff.2.2 hn_even
    rw [hcn]
    simpa using
      mul_nonneg (le_of_lt hC₀)
        (le_of_lt (Real.exp_pos (-(γ * (n : ℝ) ^ 2) / 4)))


theorem gauss_summable (C₀ γ R : ℝ) (hC₀ : 0 < C₀) (hγ : 0 < γ)
    (hR : 0 ≤ R) :
  (∀ n : ℤ,
    C₀ * Real.exp (-γ * (n : ℝ) ^ 2 / 4) * Real.exp (Real.pi * |(n : ℝ)| * R) ≤
      C₀ * Real.exp ((Real.pi * R + 1) ^ 2 / γ) * Real.exp (-|(n : ℝ)|)) ∧
  Summable (fun n : ℤ =>
    C₀ * Real.exp (-γ * (n : ℝ) ^ 2 / 4) * Real.exp (Real.pi * |(n : ℝ)| * R)) := by
  have _ : 0 ≤ R := hR
  have hterm : ∀ n : ℤ,
      C₀ * Real.exp (-γ * (n : ℝ) ^ 2 / 4) * Real.exp (Real.pi * |(n : ℝ)| * R) ≤
        C₀ * Real.exp ((Real.pi * R + 1) ^ 2 / γ) * Real.exp (-|(n : ℝ)|) := by
    intro n
    have harg : -γ * (n : ℝ) ^ 2 / 4 + Real.pi * |(n : ℝ)| * R ≤
        (Real.pi * R + 1) ^ 2 / γ - |(n : ℝ)| := by
      have hbase : -γ * |(n : ℝ)| ^ 2 / 4 + Real.pi * |(n : ℝ)| * R ≤
          (Real.pi * R + 1) ^ 2 / γ - |(n : ℝ)| := by
        have hsq : 0 ≤
            (γ / 4) * (|(n : ℝ)| - (2 * (Real.pi * R + 1)) / γ) ^ 2 := by
          positivity
        have hsq_exp : 0 ≤
            γ * |(n : ℝ)| ^ 2 / 4 - (Real.pi * R + 1) * |(n : ℝ)| +
              (Real.pi * R + 1) ^ 2 / γ := by
          convert hsq using 1
          field_simp [ne_of_gt hγ]
          ring
        nlinarith
      have hsquare : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := by rw [sq_abs]
      simpa [hsquare] using hbase
    have hexp : Real.exp (-γ * (n : ℝ) ^ 2 / 4) *
        Real.exp (Real.pi * |(n : ℝ)| * R) ≤
        Real.exp ((Real.pi * R + 1) ^ 2 / γ) * Real.exp (-|(n : ℝ)|) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr harg
    have hmul := mul_le_mul_of_nonneg_left hexp (le_of_lt hC₀)
    simpa [mul_assoc] using hmul
  constructor
  · exact hterm
  · have hbase : Summable (fun n : ℤ => Real.exp (-(1 : ℝ) * |(n : ℝ)|)) :=
      (exp_int_summable 1 (by norm_num)).1
    have hbase_clean : Summable (fun n : ℤ => Real.exp (-|(n : ℝ)|)) := by
      refine hbase.congr ?_
      intro n
      congr 1
      ring
    have hmaj : Summable (fun n : ℤ =>
        C₀ * Real.exp ((Real.pi * R + 1) ^ 2 / γ) * Real.exp (-|(n : ℝ)|)) := by
      simpa [mul_assoc] using
        (hbase_clean.mul_left (C₀ * Real.exp ((Real.pi * R + 1) ^ 2 / γ)))
    refine Summable.of_nonneg_of_le ?hnonneg hterm hmaj
    intro n
    exact mul_nonneg
      (mul_nonneg (le_of_lt hC₀) (le_of_lt (Real.exp_pos (-γ * (n : ℝ) ^ 2 / 4))))
      (le_of_lt (Real.exp_pos (Real.pi * |(n : ℝ)| * R)))


theorem G_entire (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_int : MeasureTheory.Integrable g)
    (C c C₀ γ : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hC₀ : 0 < C₀) (hγ : 0 < γ)
    (hg_bound : ∀ t : ℝ, |g t| ≤ C * Real.exp (-c * |t|))
    (hFT : ∀ ξ : ℝ, ‖FT g ξ‖ ≤ C₀ * Real.exp (-γ * ξ ^ 2)) :
  let G : ℂ → ℂ := fun z =>
    ∑' n : ℤ, cn g n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * z)
  (∀ R : ℝ, 0 ≤ R →
    ∀ z : ℂ, |z.im| ≤ R →
      ∀ n : ℤ,
        ‖cn g n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖ ≤
          C₀ * Real.exp (-γ * (n : ℝ) ^ 2 / 4) *
            Real.exp (Real.pi * |(n : ℝ)| * R)) ∧
    (∀ z : ℂ, Summable (fun n : ℤ =>
      cn g n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * z))) ∧
    Differentiable ℂ G := by
  let term : ℤ → ℂ → ℂ := fun n z =>
    cn g n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * z)
  have hcoeff_bound := coeff_bound g hg_cont hg_int C c C₀ γ hC hc hC₀ hγ hg_bound hFT
  have hterm_bound : ∀ R : ℝ, 0 ≤ R → ∀ z : ℂ, |z.im| ≤ R → ∀ n : ℤ,
      ‖term n z‖ ≤ C₀ * Real.exp (-γ * (n : ℝ) ^ 2 / 4) *
        Real.exp (Real.pi * |(n : ℝ)| * R) := by
    intro R hR z hz n
    have hre : (((Real.pi : ℂ) * Complex.I * (n : ℂ) * z).re) =
        -Real.pi * (n : ℝ) * z.im := by
      simp [Complex.mul_re, Complex.mul_im]
    have hbase : -((n : ℝ) * z.im) ≤ |(n : ℝ)| * |z.im| := by
      calc
        -((n : ℝ) * z.im) ≤ |(n : ℝ) * z.im| := neg_le_abs _
        _ = |(n : ℝ)| * |z.im| := abs_mul _ _
    have him : |(n : ℝ)| * |z.im| ≤ |(n : ℝ)| * R :=
      mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    have hre_le : (((Real.pi : ℂ) * Complex.I * (n : ℂ) * z).re) ≤
        Real.pi * |(n : ℝ)| * R := by
      nlinarith [Real.pi_pos, hbase, him]
    have hexp : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * z)‖ ≤
        Real.exp (Real.pi * |(n : ℝ)| * R) := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr hre_le
    have hmul := mul_le_mul (hcoeff_bound n) hexp (norm_nonneg _) ?_
    · simpa [term, mul_assoc] using hmul
    · exact mul_nonneg (le_of_lt hC₀)
        (le_of_lt (Real.exp_pos (-γ * (n : ℝ) ^ 2 / 4)))
  have hsummable : ∀ z : ℂ, Summable (fun n : ℤ => term n z) := by
    intro z
    have hgs := gauss_summable C₀ γ |z.im| hC₀ hγ (abs_nonneg z.im)
    have hnorm_sum : Summable (fun n : ℤ => ‖term n z‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgs.2
      intro n
      exact hterm_bound |z.im| (abs_nonneg z.im) z le_rfl n
    exact Summable.of_norm hnorm_sum
  constructor
  · simpa [term] using hterm_bound
  constructor
  · simpa [term] using hsummable
  · let G : ℂ → ℂ := fun z => tsum (fun n : ℤ => term n z)
    have hdiff_at : ∀ z : ℂ, DifferentiableAt ℂ G z := by
      intro z
      let R : ℝ := |z.im| + 1
      let U : Set ℂ := {w : ℂ | |w.im| < R}
      have hR_nonneg : 0 ≤ R := by positivity
      have hzU : z ∈ U := by
        dsimp [U, R]
        linarith
      have hUopen : IsOpen U := by
        dsimp [U]
        exact isOpen_lt (Complex.continuous_im.abs) continuous_const
      have hgs := gauss_summable C₀ γ R hC₀ hγ hR_nonneg
      have hdiff_terms : ∀ n : ℤ, DifferentiableOn ℂ (term n) U := by
        intro n
        dsimp [term]
        fun_prop
      have hleU : ∀ (n : ℤ) (w : ℂ), w ∈ U → ‖term n w‖ ≤
          C₀ * Real.exp (-γ * (n : ℝ) ^ 2 / 4) *
            Real.exp (Real.pi * |(n : ℝ)| * R) := by
        intro n w hw
        exact hterm_bound R hR_nonneg w (le_of_lt hw) n
      have hdiff_on : DifferentiableOn ℂ G U := by
        dsimp [G]
        exact Complex.differentiableOn_tsum_of_summable_norm hgs.2 hdiff_terms hUopen hleU
      exact hdiff_on.differentiableAt (hUopen.mem_nhds hzU)
    have hdiffG : Differentiable ℂ G := by
      exact hdiff_at
    simpa [G, term] using hdiffG


theorem G_restrict (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_int : MeasureTheory.Integrable g)
    (C c C₀ γ : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hC₀ : 0 < C₀) (hγ : 0 < γ)
    (hg_bound : ∀ t : ℝ, |g t| ≤ C * Real.exp (-c * |t|))
    (hFT : ∀ ξ : ℝ, ‖FT g ξ‖ ≤ C₀ * Real.exp (-γ * ξ ^ 2)) :
  let G : ℂ → ℂ := fun z =>
    ∑' n : ℤ, cn g n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * z)
  ∀ x : ℝ, G (x : ℂ) = (Halt g x : ℂ) := by
  change ∀ x : ℝ,
    (∑' n : ℤ, cn g n *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))) = (Halt g x : ℂ)
  letI : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
  let hR : ℝ → ℂ := fun x => (Halt g x : ℂ)
  have henv : HasLocalLatticeEnvelopes g :=
    (env_decay C c hC hc g hg_bound).2
  have hHcont : Continuous (Halt g) := H_cont g hg_cont henv
  have hRcont : Continuous hR := by
    exact Complex.continuous_ofReal.comp hHcont
  have hRperiod : Function.Periodic hR (2 : ℝ) := by
    intro x
    dsimp [hR]
    rw [(H_antiper g x).2]
  let h : C(AddCircle (2 : ℝ), ℂ) :=
    ⟨hRperiod.lift, continuous_coinduced_dom.mpr hRcont⟩
  have hcoeff_bound := coeff_bound g hg_cont hg_int C c C₀ γ hC hc hC₀ hγ hg_bound hFT
  have hcoeff : ∀ n : ℤ, fourierCoeff h n = cn g n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral h n 0]
    unfold cn chi
    simp only [zero_add, h, hR, ContinuousMap.coe_mk, Function.Periodic.lift_coe,
      smul_eq_mul]
    norm_num
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [← Complex.exp_conj]
    have hconj :
        (starRingEnd ℂ)
            (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) / 2) =
          -((Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) := by
      rw [starRingEnd_apply]
      simp
      ring
    rw [hconj]
    ring
  have hcn_summable : Summable (fun n : ℤ => cn g n) := by
    have hgs := gauss_summable C₀ γ 0 hC₀ hγ (by norm_num : (0 : ℝ) ≤ 0)
    have hnorm_sum : Summable (fun n : ℤ => ‖cn g n‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgs.2
      intro n
      simpa using hcoeff_bound n
    exact Summable.of_norm hnorm_sum
  have hfourier_summable : Summable (fourierCoeff h) :=
    hcn_summable.congr fun n => (hcoeff n).symm
  intro x
  let G : ℂ → ℂ := fun z =>
    ∑' n : ℤ, cn g n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * z)
  have hpoint :=
    has_pointwise_sum_fourier_series_of_summable (f := h) hfourier_summable
      (x : AddCircle (2 : ℝ))
  calc
    G (x : ℂ) =
        ∑' n : ℤ, fourierCoeff h n • fourier n
          (x : AddCircle (2 : ℝ)) := by
      dsimp [G]
      apply tsum_congr
      intro n
      have hfour_eval :
          (fourier n) (x : AddCircle (2 : ℝ)) =
            Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) := by
        rw [fourier_coe_apply]
        have harg :
          2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) /
              (((2 : ℝ) : ℂ)) =
            (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) := by
          norm_num [Complex.ofReal_intCast]
          ring
        rw [harg]
      rw [hcoeff n]
      change cn g n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) =
        cn g n * (fourier n) (x : AddCircle (2 : ℝ))
      rw [hfour_eval]
    _ = h (x : AddCircle (2 : ℝ)) := hpoint.tsum_eq
    _ = (Halt g x : ℂ) := by
      simp [h, hR]


theorem entire_flat_zero (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (u v : ℝ) (huv : u < v)
    (hflat : ∀ x : ℝ, u < x → x < v → G (x : ℂ) = 0) :
  ∀ z : ℂ, G z = 0 := by
  let w : ℝ := (u + v) / 2
  have hw_left : u < w := by
    dsimp [w]
    linarith
  have hw_right : w < v := by
    dsimp [w]
    linarith
  have hanalytic : AnalyticOnNhd ℂ G Set.univ := by
    exact hG.differentiableOn.analyticOnNhd isOpen_univ
  have hclosure :
      (w : ℂ) ∈ closure ({z : ℂ | G z = 0} \ ({(w : ℂ)} : Set ℂ)) := by
    rw [Metric.mem_closure_iff]
    intro η hη
    let δ : ℝ := min ((v - u) / 4) (η / 2)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact lt_min (by linarith) (by linarith)
    have hδ_le_quarter : δ ≤ (v - u) / 4 := by
      dsimp [δ]
      exact min_le_left _ _
    have hδ_le_eta_half : δ ≤ η / 2 := by
      dsimp [δ]
      exact min_le_right _ _
    refine ⟨((w + δ : ℝ) : ℂ), ?_, ?_⟩
    · constructor
      · have hleft : u < w + δ := by linarith
        have hquarter : w + (v - u) / 4 < v := by
          dsimp [w]
          linarith
        have hright : w + δ < v := by linarith
        exact hflat (w + δ) hleft hright
      · have hne_real : w + δ ≠ w := by linarith
        have hne_complex : ((w + δ : ℝ) : ℂ) ≠ (w : ℂ) := by
          exact_mod_cast hne_real
        simpa using hne_complex
    · have hdist : dist (w : ℂ) ((w + δ : ℝ) : ℂ) = δ := by
        rw [dist_eq_norm]
        simp [abs_of_nonneg hδ_pos.le]
      rw [hdist]
      linarith
  have hzero :=
    hanalytic.eqOn_zero_of_preconnected_of_mem_closure
      isPreconnected_univ (by simp) hclosure
  intro z
  exact hzero (by simp)


theorem case_G (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_int : MeasureTheory.Integrable g)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hg_bound : ∀ t : ℝ, |g t| ≤ C * Real.exp (-c * |t|))
    (C₀ γ : ℝ) (hC₀ : 0 < C₀) (hγ : 0 < γ)
    (hFT : ∀ ξ : ℝ, ‖FT g ξ‖ ≤ C₀ * Real.exp (-γ * ξ ^ 2))
    (hhalf : FT g (1 / 2) ≠ 0)
    (u v : ℝ) (huv : u < v)
    (hflat : ∀ x : ℝ, u < x → x < v → Halt g x = 0) :
    False := by
  let G : ℂ → ℂ := fun z =>
    ∑' n : ℤ, cn g n * Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * z)
  have hGentire := G_entire g hg_cont hg_int C c C₀ γ hC hc hC₀ hγ hg_bound hFT
  have hGdiff : Differentiable ℂ G := by
    simpa [G] using hGentire.2.2
  have hGrestrict : ∀ x : ℝ, G (x : ℂ) = (Halt g x : ℂ) := by
    simpa [G] using G_restrict g hg_cont hg_int C c C₀ γ hC hc hC₀ hγ hg_bound hFT
  have hGflat : ∀ x : ℝ, u < x → x < v → G (x : ℂ) = 0 := by
    intro x hux hxv
    rw [hGrestrict x, hflat x hux hxv]
    norm_num
  have hGzero : ∀ z : ℂ, G z = 0 :=
    entire_flat_zero G hGdiff u v huv hGflat
  have hHzero : ∀ x : ℝ, Halt g x = 0 := by
    intro x
    have hx : (Halt g x : ℂ) = 0 := by
      rw [← hGrestrict x]
      exact hGzero (x : ℂ)
    exact Complex.ofReal_eq_zero.mp hx
  have hcn_zero : cn g 1 = 0 := by
    unfold cn
    simp [hHzero]
  have hcoeff : cn g 1 = FT g (1 / 2) := by
    have h := (coefficients g hg_cont hg_int C c hC hc hg_bound (1 : ℤ)).2.1
      (by norm_num : Odd (1 : ℤ))
    simpa using h
  have hFT_zero : FT g (1 / 2) = 0 := by
    rw [← hcoeff]
    exact hcn_zero
  exact hhalf hFT_zero
