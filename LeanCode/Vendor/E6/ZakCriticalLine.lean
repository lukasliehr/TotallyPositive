import LeanCode.Vendor.E6.Decay

noncomputable section

namespace E6

theorem criticalLine_eq_zak_half (g : ℝ → ℝ)
    (hdecay : HasExponentialDecay g) (t : ℝ) :
    Z g hdecay (t, 1 / 2) = (criticalLineFunction g t : ℂ) := by
  rw [Z, criticalLineFunction]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  have hexp :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((1 / 2 : ℝ) : ℂ)) =
        (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
    have harg :
        2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((1 / 2 : ℝ) : ℂ) =
          (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
      norm_num
      ring
    rw [harg]
    rw [Complex.exp_int_mul]
    rw [Complex.exp_pi_mul_I]
    rw [Complex.ofReal_zpow]
    norm_num
  rw [hexp]
  rw [Complex.ofReal_mul]

theorem zak_half_eq_zero_iff_criticalLine_eq_zero (g : ℝ → ℝ)
    (hdecay : HasExponentialDecay g) (t : ℝ) :
    Z g hdecay (t, 1 / 2) = 0 ↔ criticalLineFunction g t = 0 := by
  rw [criticalLine_eq_zak_half]
  exact Complex.ofReal_eq_zero

theorem continuous_criticalLineFunction (g : ℝ → ℝ)
    (hgcont : Continuous g) (hdecay : HasExponentialDecay g) :
    Continuous (criticalLineFunction g) := by
  change Continuous fun t : ℝ => ∑' m : ℤ, (-1 : ℝ) ^ m * g (t - (m : ℝ))
  rw [continuous_iff_continuousAt]
  intro x
  let T : ℝ := |x| + 1
  have hTpos : 0 < T := by
    dsimp [T]
    positivity
  rcases summable_abs_translate_uniform_envelope g hdecay T hTpos with
    ⟨M, hMsum, hM⟩
  let s : Set ℝ := Metric.closedBall x 1
  have hf_cont : ∀ m : ℤ, ContinuousOn
      (fun y : ℝ => (-1 : ℝ) ^ m * g (y - (m : ℝ))) s := by
    intro m
    have htranslate : Continuous fun y : ℝ => g (y - (m : ℝ)) :=
      hgcont.comp (continuous_id.sub continuous_const)
    exact (htranslate.const_mul ((-1 : ℝ) ^ m)).continuousOn
  have hbound : ∀ (m : ℤ), ∀ y ∈ s,
      ‖(-1 : ℝ) ^ m * g (y - (m : ℝ))‖ ≤ M m := by
    intro m y hy
    have hydist : dist y x ≤ 1 := by
      simpa [s, Metric.mem_closedBall] using hy
    have hyabs_sub : |y - x| ≤ 1 := by
      simpa [Real.dist_eq] using hydist
    have hyabs : |y| ≤ T := by
      have htri : |y| ≤ |y - x| + |x| := by
        have h := abs_add_le (y - x) x
        have h_eq : y - x + x = y := by ring
        rwa [h_eq] at h
      dsimp [T]
      linarith
    calc
      ‖(-1 : ℝ) ^ m * g (y - (m : ℝ))‖ = |g (y - (m : ℝ))| := by
        simp
      _ ≤ M m := (hM m).2 y hyabs
  have hcontOn : ContinuousOn
      (fun y : ℝ => ∑' m : ℤ, (-1 : ℝ) ^ m * g (y - (m : ℝ))) s :=
    continuousOn_tsum hf_cont hMsum hbound
  exact hcontOn.continuousAt (by simpa [s] using Metric.closedBall_mem_nhds x zero_lt_one)

theorem criticalLine_antiperiodic (g : ℝ → ℝ)
    (_hdecay : HasExponentialDecay g) :
    ∀ t : ℝ, criticalLineFunction g (t + 1) = -criticalLineFunction g t := by
  intro t
  rw [criticalLineFunction]
  calc
    (∑' m : ℤ, (-1 : ℝ) ^ m * g (t + 1 - (m : ℝ))) =
        ∑' n : ℤ, -(((-1 : ℝ) ^ n) * g (t - (n : ℝ))) := by
      rw [← (Equiv.addRight (1 : ℤ)).tsum_eq
        (fun m : ℤ => (-1 : ℝ) ^ m * g (t + 1 - (m : ℝ)))]
      apply tsum_congr
      intro n
      have hpow :
          (-1 : ℝ) ^ (((Equiv.addRight (1 : ℤ)) n : ℤ)) =
            -((-1 : ℝ) ^ n) := by
        change (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n)
        rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
        norm_num
      have harg :
          t + 1 - (((Equiv.addRight (1 : ℤ)) n : ℤ) : ℝ) =
            t - (n : ℝ) := by
        change t + 1 - (((n + 1 : ℤ) : ℝ)) = t - (n : ℝ)
        norm_num [Int.cast_add]
      rw [hpow, harg]
      ring
    _ = -∑' n : ℤ, (-1 : ℝ) ^ n * g (t - (n : ℝ)) := by
      rw [tsum_neg]

theorem criticalLine_intShift (g : ℝ → ℝ)
    (hdecay : HasExponentialDecay g) :
    ∀ (t : ℝ) (n : ℤ),
      criticalLineFunction g (t + (n : ℝ)) =
        ((-1 : ℝ) ^ n) * criticalLineFunction g t := by
  intro t n
  revert t
  refine Int.induction_on n ?zero ?succ ?pred
  · intro t
    norm_num
  · intro i ih t
    have hstep := criticalLine_antiperiodic g hdecay (t + ((i : ℤ) : ℝ))
    have hih :
        criticalLineFunction g (t + ((i : ℤ) : ℝ)) =
          ((-1 : ℝ) ^ (i : ℤ)) * criticalLineFunction g t := ih t
    have hpow :
        ((-1 : ℝ) ^ ((i : ℤ) + 1)) = - ((-1 : ℝ) ^ (i : ℤ)) := by
      rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      norm_num
    calc
      criticalLineFunction g (t + (((i : ℤ) + 1 : ℤ) : ℝ)) =
          criticalLineFunction g ((t + ((i : ℤ) : ℝ)) + 1) := by
        norm_num [Int.cast_add]
        ring_nf
      _ = -criticalLineFunction g (t + ((i : ℤ) : ℝ)) := hstep
      _ = -(((-1 : ℝ) ^ (i : ℤ)) * criticalLineFunction g t) := by rw [hih]
      _ = ((-1 : ℝ) ^ ((i : ℤ) + 1)) * criticalLineFunction g t := by
        rw [hpow]
        ring_nf
  · intro i ih t
    let n : ℤ := - (i : ℤ) - 1
    have hstep0 := criticalLine_antiperiodic g hdecay (t + (n : ℝ))
    have hcast : t + ((- (i : ℤ) : ℤ) : ℝ) = (t + (n : ℝ)) + 1 := by
      dsimp [n]
      norm_num [Int.cast_sub, Int.cast_neg]
      ring_nf
    have hback :
        criticalLineFunction g (t + (n : ℝ)) =
          -criticalLineFunction g (t + ((- (i : ℤ) : ℤ) : ℝ)) := by
      calc
        criticalLineFunction g (t + (n : ℝ)) =
            -(-criticalLineFunction g (t + (n : ℝ))) := by
          ring_nf
        _ = -criticalLineFunction g ((t + (n : ℝ)) + 1) := by rw [hstep0]
        _ = -criticalLineFunction g (t + ((- (i : ℤ) : ℤ) : ℝ)) := by
          rw [← hcast]
    have hih :
        criticalLineFunction g (t + ((- (i : ℤ) : ℤ) : ℝ)) =
          ((-1 : ℝ) ^ (- (i : ℤ))) * criticalLineFunction g t := ih t
    have hpow :
        ((-1 : ℝ) ^ ((- (i : ℤ) : ℤ) - 1)) =
          - ((-1 : ℝ) ^ (- (i : ℤ))) := by
      rw [zpow_sub₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      norm_num
      ring_nf
    calc
      criticalLineFunction g (t + (((- (i : ℤ) : ℤ) - 1 : ℤ) : ℝ)) =
          criticalLineFunction g (t + (n : ℝ)) := by
        dsimp [n]
      _ = -criticalLineFunction g (t + ((- (i : ℤ) : ℤ) : ℝ)) := hback
      _ = -(((-1 : ℝ) ^ (- (i : ℤ))) * criticalLineFunction g t) := by
        rw [hih]
      _ =
          ((-1 : ℝ) ^ (((- (i : ℤ) : ℤ) - 1 : ℤ)) *
            criticalLineFunction g t) := by
        rw [hpow]
        ring_nf

end E6
