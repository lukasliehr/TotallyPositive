import Mathlib
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open scoped BigOperators






namespace Part6







noncomputable def E (w : ℂ) : ℂ := (1 + w) * Complex.exp (-w)


noncomputable def Qn (β : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (n + 1), (n.choose m : ℂ) * (β m : ℂ) * z ^ m


noncomputable def Pn (β : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (β 0 : ℂ)⁻¹ * Qn β n (z / (n : ℂ))


noncomputable def delta (β : ℕ → ℝ) : ℝ := β 1 / β 0


noncomputable def Bconst (β : ℕ → ℝ) : ℝ := (delta β) ^ 2 - β 2 / β 0


noncomputable def Mconst (β : ℕ → ℝ) : ℝ := (delta β) ^ 2 + |β 2| / β 0


noncomputable def Kbound (A M R : ℝ) : ℝ := Real.exp (R * A + 6 * R ^ 2 * M)


noncomputable def epsN (R M : ℝ) (N : ℕ) : ℝ := 2 * R ^ 3 * M * Real.sqrt (M / (N : ℝ))



def HypH (β : ℕ → ℝ) : Prop := 0 < β 0 ∧ ∀ n : ℕ, RealRooted (jensenPoly β n)










theorem E_series :
    (∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ‖E w - (1 - w ^ 2 / 2)‖ ≤ (5 / 12) * ‖w‖ ^ 3) ∧
    (∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ‖E w - 1‖ ≤ (3 / 4) * ‖w‖ ^ 2) ∧
    (∀ w : ℂ, ‖E w - 1‖ ≤ (1 + ‖w‖) * Real.exp ‖w‖ + 1) ∧
    (∀ t : ℝ, 0 ≤ t → (1 - t) * Real.exp t ≤ 1) := by
  have part1 : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ‖E w - (1 - w ^ 2 / 2)‖ ≤ (5 / 12) * ‖w‖ ^ 3 := by
    intro w hw
    have hx : ‖(-w : ℂ)‖ ≤ 1 := by rw [norm_neg]; linarith
    have hb := Complex.exp_bound hx (n := 5) (by norm_num)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one] at hb
    simp only [Nat.factorial] at hb
    norm_num at hb
    have hr : ‖Complex.exp (-w) - (1 - w + w ^ 2 / 2 - w ^ 3 / 6 + w ^ 4 / 24)‖ ≤ ‖w‖ ^ 5 / 100 := by
      have e1 : (1 - w + w ^ 2 / 2 - w ^ 3 / 6 + w ^ 4 / 24 : ℂ)
          = (1 + -w + w ^ 2 / 2 + (-w) ^ 3 / 6 + w ^ 4 / 24) := by ring
      rw [e1]
      calc ‖Complex.exp (-w) - (1 + -w + w ^ 2 / 2 + (-w) ^ 3 / 6 + w ^ 4 / 24)‖
          ≤ ‖w‖ ^ 5 * (1 / 100) := hb
        _ = ‖w‖ ^ 5 / 100 := by ring
    set r : ℂ := Complex.exp (-w) - (1 - w + w ^ 2 / 2 - w ^ 3 / 6 + w ^ 4 / 24) with hrdef
    have hE : E w - (1 - w ^ 2 / 2) = (w ^ 3 / 3 - w ^ 4 / 8 + w ^ 5 / 24) + (1 + w) * r := by
      rw [E, hrdef]; ring
    rw [hE]
    have hpoly : ‖(w ^ 3 / 3 - w ^ 4 / 8 + w ^ 5 / 24 : ℂ)‖
        ≤ ‖w‖ ^ 3 / 3 + ‖w‖ ^ 4 / 8 + ‖w‖ ^ 5 / 24 := by
      have t1 : ‖(w ^ 3 / 3 - w ^ 4 / 8 + w ^ 5 / 24 : ℂ)‖
          ≤ ‖(w ^ 3 / 3 - w ^ 4 / 8 : ℂ)‖ + ‖(w ^ 5 / 24 : ℂ)‖ := norm_add_le _ _
      have t2 : ‖(w ^ 3 / 3 - w ^ 4 / 8 : ℂ)‖
          ≤ ‖(w ^ 3 / 3 : ℂ)‖ + ‖(w ^ 4 / 8 : ℂ)‖ := norm_sub_le _ _
      have n3 : ‖(w ^ 3 / 3 : ℂ)‖ = ‖w‖ ^ 3 / 3 := by rw [norm_div, norm_pow]; norm_num
      have n4 : ‖(w ^ 4 / 8 : ℂ)‖ = ‖w‖ ^ 4 / 8 := by rw [norm_div, norm_pow]; norm_num
      have n5 : ‖(w ^ 5 / 24 : ℂ)‖ = ‖w‖ ^ 5 / 24 := by rw [norm_div, norm_pow]; norm_num
      rw [n5] at t1; rw [n3, n4] at t2; linarith
    have hmulr : ‖(1 + w) * r‖ ≤ (1 + ‖w‖) * (‖w‖ ^ 5 / 100) := by
      rw [norm_mul]
      apply mul_le_mul _ hr (norm_nonneg _) (by positivity)
      have := norm_add_le (1 : ℂ) w; rwa [norm_one] at this
    have htri : ‖(w ^ 3 / 3 - w ^ 4 / 8 + w ^ 5 / 24) + (1 + w) * r‖
        ≤ ‖(w ^ 3 / 3 - w ^ 4 / 8 + w ^ 5 / 24 : ℂ)‖ + ‖(1 + w) * r‖ := norm_add_le _ _
    have hn0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
    nlinarith [htri, hpoly, hmulr, pow_nonneg hn0 3, pow_nonneg hn0 4, pow_nonneg hn0 5,
               mul_le_mul_of_nonneg_left hw (pow_nonneg hn0 3),
               sq_nonneg ‖w‖, mul_nonneg hn0 (pow_nonneg hn0 4), mul_nonneg hn0 (pow_nonneg hn0 3)]
  refine ⟨part1, ?_, ?_, ?_⟩
  · intro w hw
    have p1 := part1 w hw
    have hsplit : ‖E w - 1‖ ≤ ‖E w - (1 - w ^ 2 / 2)‖ + ‖(w ^ 2 / 2 : ℂ)‖ := by
      have he : E w - 1 = (E w - (1 - w ^ 2 / 2)) - (w ^ 2 / 2) := by ring
      rw [he]; exact norm_sub_le _ _
    have hw2 : ‖(w ^ 2 / 2 : ℂ)‖ = ‖w‖ ^ 2 / 2 := by rw [norm_div, norm_pow]; norm_num
    rw [hw2] at hsplit
    have hn0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
    have hcube : (5 / 12) * ‖w‖ ^ 3 ≤ (5 / 24) * ‖w‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hw (sq_nonneg ‖w‖), sq_nonneg ‖w‖]
    nlinarith [p1, hsplit, hcube, sq_nonneg ‖w‖]
  · intro w
    have h1 : ‖E w - 1‖ ≤ ‖E w‖ + 1 := by
      have := norm_sub_le (E w) 1; rwa [norm_one] at this
    have h2 : ‖E w‖ = ‖1 + w‖ * Real.exp (-w.re) := by
      rw [E, norm_mul, Complex.norm_exp, Complex.neg_re]
    have h3 : ‖1 + w‖ ≤ 1 + ‖w‖ := by
      have := norm_add_le (1 : ℂ) w; rwa [norm_one] at this
    have h4 : Real.exp (-w.re) ≤ Real.exp ‖w‖ := by
      apply Real.exp_le_exp.mpr
      have hb : -w.re ≤ |w.re| := neg_le_abs w.re
      have hc : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
      linarith
    have h5 : ‖E w‖ ≤ (1 + ‖w‖) * Real.exp ‖w‖ := by
      rw [h2]; apply mul_le_mul h3 h4 (Real.exp_pos _).le; positivity
    linarith
  · intro t ht
    have hexp : -t + 1 ≤ Real.exp (-t) := Real.add_one_le_exp (-t)
    have hpos : 0 < Real.exp t := Real.exp_pos t
    have hmul : (-t + 1) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
      mul_le_mul_of_nonneg_right hexp hpos.le
    have hkey : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    rw [hkey] at hmul
    nlinarith [hmul]


theorem exp_lower : ∀ x : ℝ, 1 + x ≤ Real.exp x := by
  intro x
  have := Real.add_one_le_exp x
  linarith


private lemma exp_sub_one_le (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.add_one_le_exp (-t)
  have hpos := Real.exp_pos t
  have hmul : (-t + 1) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
    mul_le_mul_of_nonneg_right h (le_of_lt hpos)
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
  nlinarith [hmul]




theorem exp_diff :
    (∀ t : ℝ, 0 ≤ t → Real.exp t - 1 ≤ t * Real.exp t) ∧
    (∀ u : ℂ, ‖Complex.exp u - 1‖ ≤ Real.exp ‖u‖ - 1 ∧
              Real.exp ‖u‖ - 1 ≤ ‖u‖ * Real.exp ‖u‖) := by
  refine ⟨fun t _ => exp_sub_one_le t, fun u => ⟨?_, exp_sub_one_le ‖u‖⟩⟩
  have hsc : HasSum (fun n : ℕ => u ^ n / (n.factorial : ℂ)) (Complex.exp u) := by
    have := NormedSpace.expSeries_div_hasSum_exp u
    rwa [← Complex.exp_eq_exp_ℂ] at this
  have hsr : HasSum (fun n : ℕ => ‖u‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖u‖) := by
    have := NormedSpace.expSeries_div_hasSum_exp ‖u‖
    rwa [← Real.exp_eq_exp_ℝ] at this
  have hsc1 : HasSum (fun n : ℕ => u ^ (n + 1) / ((n + 1).factorial : ℂ)) (Complex.exp u - 1) :=
    (hasSum_nat_add_iff (f := fun n : ℕ => u ^ n / (n.factorial : ℂ)) 1).mpr (by simpa using hsc)
  have hsr1 : HasSum (fun n : ℕ => ‖u‖ ^ (n + 1) / ((n + 1).factorial : ℝ)) (Real.exp ‖u‖ - 1) :=
    (hasSum_nat_add_iff (f := fun n : ℕ => ‖u‖ ^ n / (n.factorial : ℝ)) 1).mpr (by simpa using hsr)
  have hnormeq : ∀ n : ℕ,
      ‖u ^ (n + 1) / ((n + 1).factorial : ℂ)‖ = ‖u‖ ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    intro n; rw [norm_div, norm_pow, Complex.norm_natCast]
  have hsummc : Summable (fun n : ℕ => ‖u ^ (n + 1) / ((n + 1).factorial : ℂ)‖) := by
    simpa only [hnormeq] using hsr1.summable
  calc ‖Complex.exp u - 1‖
      = ‖∑' n : ℕ, u ^ (n + 1) / ((n + 1).factorial : ℂ)‖ := by rw [hsc1.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖u ^ (n + 1) / ((n + 1).factorial : ℂ)‖ := norm_tsum_le_tsum_norm hsummc
    _ = ∑' n : ℕ, ‖u‖ ^ (n + 1) / ((n + 1).factorial : ℝ) := by simp_rw [hnormeq]
    _ = Real.exp ‖u‖ - 1 := hsr1.tsum_eq



theorem log_abs : ∀ w : ℂ, 1 + w ≠ 0 →
    Real.log ‖1 + w‖ ≤ w.re + (1 / 2) * ‖w‖ ^ 2 ∧
    Real.log ‖1 + w‖ ≤ w.re + 2 * ‖w‖ ^ 2 := by
  intro w hw
  have hnorm_pos : 0 < ‖1 + w‖ := by rw [norm_pos_iff]; exact hw

  have hsq : ‖1 + w‖ ^ 2 = 1 + (2 * w.re + ‖w‖ ^ 2) := by
    have h1 : ‖(1 : ℂ) + w‖ ^ 2 = Complex.normSq (1 + w) :=
      (Complex.normSq_eq_norm_sq (1 + w)).symm
    have h2 : ‖w‖ ^ 2 = Complex.normSq w := (Complex.normSq_eq_norm_sq w).symm
    rw [h1, h2, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring

  have hpos2 : (0 : ℝ) < 1 + (2 * w.re + ‖w‖ ^ 2) := by rw [← hsq]; positivity
  have hexp : (1 : ℝ) + (2 * w.re + ‖w‖ ^ 2) ≤ Real.exp (2 * w.re + ‖w‖ ^ 2) :=
    exp_lower _
  have hlog : Real.log (‖1 + w‖ ^ 2) ≤ 2 * w.re + ‖w‖ ^ 2 := by
    rw [hsq]
    calc Real.log (1 + (2 * w.re + ‖w‖ ^ 2))
        ≤ Real.log (Real.exp (2 * w.re + ‖w‖ ^ 2)) :=
          Real.log_le_log hpos2 hexp
      _ = 2 * w.re + ‖w‖ ^ 2 := Real.log_exp _
  rw [Real.log_pow] at hlog
  push_cast at hlog
  refine ⟨by nlinarith [hlog], by nlinarith [hlog, sq_nonneg ‖w‖]⟩



theorem small_log : ∀ η : ℂ, ‖η‖ ≤ 1 / 8 →
    ∃ r : ℂ, Complex.exp r = 1 + η ∧ ‖r‖ ≤ 2 * ‖η‖ ∧ |r.im| < Real.pi / 2 := by
  intro η hη
  have hle : (7 : ℝ) / 8 ≤ ‖1 + η‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-η)
    simp only [sub_neg_eq_add, norm_neg, norm_one] at h
    linarith
  have hne : (1 : ℂ) + η ≠ 0 := by
    rw [← norm_pos_iff]; linarith
  refine ⟨Complex.log (1 + η), Complex.exp_log hne, ?_, ?_⟩
  · have hb : ‖Complex.log (1 + η)‖ ≤ (3 / 2) * ‖η‖ :=
      Complex.norm_log_one_add_half_le_self (by linarith)
    nlinarith [norm_nonneg η]
  · have hb : ‖Complex.log (1 + η)‖ ≤ (3 / 2) * ‖η‖ :=
      Complex.norm_log_one_add_half_le_self (by linarith)
    have him : |(Complex.log (1 + η)).im| ≤ ‖Complex.log (1 + η)‖ :=
      Complex.abs_im_le_norm _
    have hpi : (1 : ℝ) < Real.pi := by
      have := Real.pi_gt_three; linarith
    nlinarith [norm_nonneg η, him, hb]



theorem logE : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 →
    ∃ ρ : ℂ, E w = Complex.exp (-(w ^ 2) / 2 + ρ) ∧ ‖ρ‖ ≤ (3 / 2) * ‖w‖ ^ 3 := by
  intro w hw
  have hlt : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hne : (1 : ℂ) + w ≠ 0 := by
    have hge : ‖(1:ℂ) + w‖ ≥ 1 - ‖w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-w)
      rw [sub_neg_eq_add, norm_neg, norm_one] at this
      exact this
    have hpos : ‖(1:ℂ) + w‖ > 0 := lt_of_lt_of_le (by linarith) hge
    exact (norm_pos_iff.mp hpos)
  have htaylor : Complex.logTaylor 3 w = w - w^2/2 := by
    simp [Complex.logTaylor, Finset.sum_range_succ]
    ring
  refine ⟨Complex.log (1 + w) - Complex.logTaylor 3 w, ?_, ?_⟩
  · rw [htaylor, E]
    rw [show -(w ^ 2) / 2 + (Complex.log (1 + w) - (w - w ^ 2 / 2))
          = Complex.log (1 + w) + (-w) by ring]
    rw [Complex.exp_add, Complex.exp_log hne]
  · have hbound := Complex.norm_log_sub_logTaylor_le 2 hlt
    have hw3 : (0:ℝ) ≤ ‖w‖^3 := pow_nonneg (norm_nonneg w) 3
    have hposden : (0:ℝ) < 1 - ‖w‖ := by linarith
    have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ hposden]; linarith
    have hinvpos : (0:ℝ) ≤ (1 - ‖w‖)⁻¹ := le_of_lt (inv_pos.mpr hposden)
    calc ‖Complex.log (1 + w) - Complex.logTaylor 3 w‖
        ≤ ‖w‖ ^ (2 + 1) * (1 - ‖w‖)⁻¹ / (↑(2:ℕ) + 1) := hbound
      _ ≤ (3/2) * ‖w‖ ^ 3 := by
          push_cast
          rw [show (2:ℝ)+1 = 3 by norm_num]
          nlinarith [hw3, hinv, mul_nonneg hw3 hinvpos]

end Part6
