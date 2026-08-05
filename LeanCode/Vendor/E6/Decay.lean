import LeanCode.Vendor.E6.Defs

noncomputable section

namespace E6

theorem expDecay_bound_by_polynomial (g : ℝ → ℝ)
    (hdecay : HasExponentialDecay g) :
    ∀ n : ℕ, 1 < n →
      ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ, |g t| ≤ C / ((1 : ℝ) + |t|) ^ n := by
  intro n _hn
  rcases hdecay with ⟨A, c, hApos, hcpos, hg⟩
  let B : ℝ := max ((2 : ℝ) ^ n) (((n.factorial : ℝ) * (2 : ℝ) ^ n) / c ^ n)
  have hBpos : 0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) n) (le_max_left _ _)
  refine ⟨A * B, mul_pos hApos hBpos, ?_⟩
  intro t
  let r : ℝ := |t|
  have hrnonneg : 0 ≤ r := by
    dsimp [r]
    exact abs_nonneg t
  have hcore : Real.exp (-c * r) ≤ B / ((1 : ℝ) + r) ^ n := by
    by_cases hr1 : r ≤ 1
    · have hsmall : Real.exp (-c * r) ≤ (2 : ℝ) ^ n / ((1 + r) ^ n) := by
        have h_exp_le_one : Real.exp (-c * r) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith
        have hbase : 1 + r ≤ 2 := by linarith
        have hden_le : (1 + r) ^ n ≤ (2 : ℝ) ^ n := by
          exact pow_le_pow_left₀ (by positivity : 0 ≤ 1 + r) hbase n
        have hden_pos : 0 < (1 + r) ^ n := pow_pos (by positivity : 0 < 1 + r) n
        have hone_le : (1 : ℝ) ≤ (2 : ℝ) ^ n / ((1 + r) ^ n) := by
          rw [one_le_div hden_pos]
          exact hden_le
        exact h_exp_le_one.trans hone_le
      have hnum : (2 : ℝ) ^ n ≤ B := by
        dsimp [B]
        exact le_max_left _ _
      have hden_nonneg : 0 ≤ ((1 : ℝ) + r) ^ n := by positivity
      exact hsmall.trans (div_le_div_of_nonneg_right hnum hden_nonneg)
    · have hrge : 1 ≤ r := le_of_not_ge hr1
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrge
      have htail0 : Real.exp (-c * r) ≤ (n.factorial : ℝ) / ((c * r) ^ n) := by
        have hxnonneg : 0 ≤ c * r := by positivity
        have hpowexp := Real.pow_div_factorial_le_exp (c * r) hxnonneg n
        have hpow_pos : 0 < (c * r) ^ n := pow_pos (mul_pos hcpos hrpos) n
        have hfact_pos : 0 < (n.factorial : ℝ) := by
          exact_mod_cast Nat.factorial_pos n
        have hquot_pos : 0 < (c * r) ^ n / (n.factorial : ℝ) :=
          div_pos hpow_pos hfact_pos
        rw [show -c * r = -(c * r) by ring, Real.exp_neg]
        calc
          (Real.exp (c * r))⁻¹ ≤ (((c * r) ^ n / (n.factorial : ℝ)))⁻¹ := by
            rw [inv_le_inv₀ (Real.exp_pos _) hquot_pos]
            exact hpowexp
          _ = (n.factorial : ℝ) / ((c * r) ^ n) := by rw [inv_div]
      have htail1 : (n.factorial : ℝ) / ((c * r) ^ n) ≤
          (((n.factorial : ℝ) * (2 : ℝ) ^ n) / c ^ n) / ((1 + r) ^ n) := by
        have hbase : 1 + r ≤ 2 * r := by linarith
        have hpowbase : (1 + r) ^ n ≤ (2 * r) ^ n := by
          exact pow_le_pow_left₀ (by positivity : 0 ≤ 1 + r) hbase n
        have hden_le : (1 + r) ^ n ≤ (2 : ℝ) ^ n * r ^ n := by
          simpa [mul_pow] using hpowbase
        have hfact_nonneg : 0 ≤ (n.factorial : ℝ) := by positivity
        have hc_pow_pos : 0 < c ^ n := pow_pos hcpos n
        have hcr_pow_pos : 0 < (c * r) ^ n := pow_pos (mul_pos hcpos hrpos) n
        have h1r_pow_pos : 0 < (1 + r) ^ n := pow_pos (by positivity : 0 < 1 + r) n
        rw [div_le_div_iff₀ hcr_pow_pos h1r_pow_pos]
        rw [mul_pow]
        field_simp [hc_pow_pos.ne']
        nlinarith [hden_le, hfact_nonneg]
      have hnum : (((n.factorial : ℝ) * (2 : ℝ) ^ n) / c ^ n) ≤ B := by
        dsimp [B]
        exact le_max_right _ _
      have hden_nonneg : 0 ≤ ((1 : ℝ) + r) ^ n := by positivity
      exact (htail0.trans htail1).trans (div_le_div_of_nonneg_right hnum hden_nonneg)
  calc
    |g t| ≤ A * Real.exp (-c * |t|) := hg t
    _ = A * Real.exp (-c * r) := by rfl
    _ ≤ A * (B / ((1 : ℝ) + r) ^ n) :=
      mul_le_mul_of_nonneg_left hcore hApos.le
    _ = A * B / ((1 : ℝ) + |t|) ^ n := by
      dsimp [r]
      ring

theorem summable_int_one_add_abs_pow_inv (n : ℕ) (hn : 1 < n) :
    Summable fun k : ℤ => (1 : ℝ) / ((1 : ℝ) + ‖k‖) ^ n := by
  have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnat_rpow :
      Summable fun m : ℕ => (1 : ℝ) / |(m : ℝ) + 1| ^ (n : ℝ) :=
    (Real.summable_one_div_nat_add_rpow 1 (n : ℝ)).2 hnreal
  refine Summable.of_nat_of_neg ?pos ?neg
  · refine hnat_rpow.congr ?_
    intro m
    have hnonneg : 0 ≤ (m : ℝ) + 1 := by positivity
    simp [Real.rpow_natCast, abs_of_nonneg hnonneg, add_comm]
  · refine hnat_rpow.congr ?_
    intro m
    have hnonneg : 0 ≤ (m : ℝ) + 1 := by positivity
    simp [Real.rpow_natCast, abs_of_nonneg hnonneg, add_comm]

theorem summable_abs_translate_uniform_envelope (g : ℝ → ℝ)
    (hdecay : HasExponentialDecay g) :
    ∀ T : ℝ, 0 < T →
      ∃ M : ℤ → ℝ,
        (Summable M) ∧
          ∀ m : ℤ, 0 ≤ M m ∧
            ∀ x : ℝ, |x| ≤ T → |g (x - (m : ℝ))| ≤ M m := by
  intro T hTpos
  rcases expDecay_bound_by_polynomial g hdecay 2 (by norm_num) with
    ⟨C, hCpos, hC⟩
  refine ⟨fun m : ℤ => (C * (1 + T) ^ 2) / ((1 : ℝ) + ‖m‖) ^ 2, ?_, ?_⟩
  · have hp := summable_int_one_add_abs_pow_inv 2 (by norm_num)
    refine (Summable.mul_left (C * (1 + T) ^ 2) hp).congr ?_
    intro m
    ring
  · intro m
    constructor
    · positivity
    · intro x hxT
      let u : ℝ := |x - (m : ℝ)|
      have hm_abs_bound : |(m : ℝ)| ≤ T + u := by
        have htri : |(m : ℝ)| ≤ |x - (m : ℝ)| + |x| := by
          have h := abs_add_le (((m : ℝ) - x)) x
          have h_eq : (m : ℝ) - x + x = (m : ℝ) := by ring
          rw [h_eq] at h
          have habs : |(m : ℝ) - x| = |x - (m : ℝ)| := by
            rw [abs_sub_comm]
          linarith
        dsimp [u]
        linarith
      have hm_norm_bound : ‖m‖ ≤ T + u := by
        rw [Int.norm_eq_abs]
        exact hm_abs_bound
      have hbase : (1 : ℝ) + ‖m‖ ≤ (1 + T) * (1 + u) := by
        have hleft : (1 : ℝ) + ‖m‖ ≤ 1 + T + u := by linarith
        have hright : (1 : ℝ) + T + u ≤ (1 + T) * (1 + u) := by
          nlinarith [hTpos, abs_nonneg (x - (m : ℝ))]
        linarith
      have hden_le :
          ((1 : ℝ) + ‖m‖) ^ 2 ≤ (1 + T) ^ 2 * ((1 : ℝ) + u) ^ 2 := by
        have hsq := pow_le_pow_left₀
          (by positivity : 0 ≤ (1 : ℝ) + ‖m‖) hbase 2
        nlinarith
      have hu_pos : 0 < ((1 : ℝ) + u) ^ 2 := by positivity
      have hm_pos : 0 < ((1 : ℝ) + ‖m‖) ^ 2 := by positivity
      have hfrac : C / ((1 : ℝ) + u) ^ 2 ≤
          (C * (1 + T) ^ 2) / ((1 : ℝ) + ‖m‖) ^ 2 := by
        rw [div_le_div_iff₀ hu_pos hm_pos]
        nlinarith
      calc
        |g (x - (m : ℝ))| ≤ C / ((1 : ℝ) + |x - (m : ℝ)|) ^ 2 :=
          hC (x - (m : ℝ))
        _ = C / ((1 : ℝ) + u) ^ 2 := by rfl
        _ ≤ (C * (1 + T) ^ 2) / ((1 : ℝ) + ‖m‖) ^ 2 := hfrac

theorem summable_abs_translate_of_hasExponentialDecay (g : ℝ → ℝ)
    (hdecay : HasExponentialDecay g) :
    ∀ x : ℝ, Summable fun m : ℤ => |g (x - (m : ℝ))| := by
  intro x
  let T : ℝ := |x| + 1
  have hTpos : 0 < T := by
    dsimp [T]
    positivity
  have hxT : |x| ≤ T := by
    dsimp [T]
    linarith [abs_nonneg x]
  rcases summable_abs_translate_uniform_envelope g hdecay T hTpos with
    ⟨M, hMsum, hM⟩
  exact Summable.of_nonneg_of_le
    (fun m : ℤ => abs_nonneg (g (x - (m : ℝ))))
    (fun m : ℤ => (hM m).2 x hxT)
    hMsum

end E6
