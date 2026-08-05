import LeanCode.ExternalInputs


















open Real
open MeasureTheory

namespace Assembly




private lemma cube_div_le_exp {s : ℝ} (hs : 0 ≤ s) : (s / 3) ^ 3 ≤ Real.exp s := by
  have h1 : s / 3 ≤ Real.exp (s / 3) := by
    have := Real.add_one_le_exp (s / 3)
    linarith
  have h0 : 0 ≤ s / 3 := by linarith
  have hcube : (s / 3) ^ 3 ≤ (Real.exp (s / 3)) ^ 3 :=
    pow_le_pow_left₀ h0 h1 3
  have hexp : (Real.exp (s / 3)) ^ 3 = Real.exp s := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hcube
  exact hcube



theorem hasExponentialDecay_to_polynomial (g : ℝ → ℝ)
    (h : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)) :
    HasPolynomialDecay g := by
  obtain ⟨C, c, hC, hc, hbound⟩ := h

  set M : ℝ := max 4 (108 / c ^ 3) with hM_def
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C * M, 2, by positivity, by norm_num, ?_⟩
  intro x

  set t : ℝ := |x| with ht_def
  have ht0 : 0 ≤ t := abs_nonneg x
  have hden : 0 < (1 + t) ^ 2 := by positivity
  rw [Real.rpow_two]
  rw [le_div_iff₀ hden]

  have hkey : Real.exp (-c * t) * (1 + t) ^ 2 ≤ M := by
    rcases le_or_gt t 1 with hle | hgt
    ·
      have hexp_le : Real.exp (-c * t) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ c * t := by positivity
        linarith
      have hpoly_le : (1 + t) ^ 2 ≤ 4 := by nlinarith [ht0, hle]
      calc Real.exp (-c * t) * (1 + t) ^ 2
            ≤ 1 * 4 := by
              apply mul_le_mul hexp_le hpoly_le (by positivity) (by norm_num)
        _ = 4 := by ring
        _ ≤ M := le_max_left _ _
    ·

      have ht_pos : 0 < t := lt_trans (by norm_num) hgt
      have hexp_lb : (c * t / 3) ^ 3 ≤ Real.exp (c * t) := by
        apply cube_div_le_exp; positivity
      have hexp_pos : 0 < Real.exp (c * t) := Real.exp_pos _

      have hneg : Real.exp (-c * t) = 1 / Real.exp (c * t) := by
        rw [eq_div_iff (ne_of_gt hexp_pos), ← Real.exp_add]
        rw [show (-c * t + c * t) = 0 by ring, Real.exp_zero]
      rw [hneg]
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hexp_pos]

      have hcubepos : 0 < (c * t / 3) ^ 3 := by positivity
      have hstep : (1 + t) ^ 2 ≤ M * (c * t / 3) ^ 3 := by


        have hMge : 108 / c ^ 3 ≤ M := le_max_right _ _
        have hc3 : 0 < c ^ 3 := by positivity
        have e1 : M * (c * t / 3) ^ 3 = M * c ^ 3 * t ^ 3 / 27 := by ring
        have e2 : (108 / c ^ 3) * c ^ 3 = 108 := by
          field_simp
        have hMc3 : 108 ≤ M * c ^ 3 := by
          have := mul_le_mul_of_nonneg_right hMge (le_of_lt hc3)
          rwa [e2] at this

        rw [e1]
        have hlow : (108 : ℝ) * t ^ 3 / 27 ≤ M * c ^ 3 * t ^ 3 / 27 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          · exact mul_le_mul_of_nonneg_right hMc3 (by positivity)
        have hfac : (0 : ℝ) ≤ (t - 1) * (4 * t ^ 2 + 3 * t + 1) :=
          mul_nonneg (by linarith) (by positivity)
        have hpoly : (1 + t) ^ 2 ≤ 108 * t ^ 3 / 27 := by nlinarith [hfac, hgt, ht_pos]
        linarith
      calc (1 + t) ^ 2 ≤ M * (c * t / 3) ^ 3 := hstep
        _ ≤ M * Real.exp (c * t) := by
            apply mul_le_mul_of_nonneg_left hexp_lb (le_of_lt hMpos)

  have hgx : |g x| ≤ C * Real.exp (-c * t) := by rw [ht_def]; exact hbound x
  calc |g x| * (1 + t) ^ 2
        ≤ (C * Real.exp (-c * t)) * (1 + t) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hgx (by positivity)
    _ = C * (Real.exp (-c * t) * (1 + t) ^ 2) := by ring
    _ ≤ C * M := by apply mul_le_mul_of_nonneg_left hkey (le_of_lt hC)




theorem tpic_hasPolynomialDecay (g : ℝ → ℝ)
    (h : IsTotallyPositiveIntegrableContinuous g) : HasPolynomialDecay g := by
  have hint : IsTotallyPositiveIntegrable g := ⟨h.1, h.2.1⟩
  exact hasExponentialDecay_to_polynomial g (Ext.E1_ExponentialDecay g hint)





theorem hasPolynomialDecay_to_memL2 (g : ℝ → ℝ)
    (hg : Continuous g) (h : HasPolynomialDecay g) :
    MemLp g 2 (volume : Measure ℝ) := by
  obtain ⟨C, η, hC, hη, hbound⟩ := h
  rw [memLp_two_iff_integrable_sq hg.aestronglyMeasurable]

  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * η := by
    rw [Module.finrank_self]; push_cast; linarith
  have hInt0 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 * η))) (volume : Measure ℝ) :=
    integrable_one_add_norm hr
  have hdom : Integrable (fun x : ℝ => C ^ 2 * (1 + ‖x‖) ^ (-(2 * η))) (volume : Measure ℝ) :=
    hInt0.const_mul (C ^ 2)

  refine hdom.mono' (hg.pow 2).aestronglyMeasurable ?_
  · refine Filter.Eventually.of_forall (fun x => ?_)
    have hbx : |g x| ≤ C / (1 + |x|) ^ η := hbound x
    have habs0 : (0 : ℝ) ≤ 1 + |x| := by positivity
    have hpow_pos : 0 < (1 + |x|) ^ η := Real.rpow_pos_of_pos (by positivity) η

    have hnorm : ‖g x ^ 2‖ = |g x| ^ 2 := by
      rw [Real.norm_eq_abs, abs_pow]
    rw [hnorm]

    have hsq : |g x| ^ 2 ≤ (C / (1 + |x|) ^ η) ^ 2 := by
      apply pow_le_pow_left₀ (abs_nonneg _) hbx

    have hupos : (0 : ℝ) < 1 + |x| := by positivity
    have hnormx : (1 + ‖x‖) = (1 + |x|) := by rw [Real.norm_eq_abs]
    have hrhs : (C / (1 + |x|) ^ η) ^ 2 = C ^ 2 * (1 + ‖x‖) ^ (-(2 * η)) := by
      rw [hnormx, div_pow, ← Real.rpow_natCast ((1 + |x|) ^ η) 2,
        ← Real.rpow_mul (le_of_lt hupos), Real.rpow_neg (le_of_lt hupos)]
      have hexp : η * (2 : ℕ) = 2 * η := by push_cast; ring
      rw [hexp, div_eq_mul_inv, mul_comm]
    rw [hrhs] at hsq
    exact hsq

end Assembly
