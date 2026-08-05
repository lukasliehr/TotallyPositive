import LeanCode.Vendor.E5.P6.Part6.Basic
import LeanCode.Vendor.E5.P6.Part6.PolyTools
import LeanCode.Vendor.E5.Defs

open scoped BigOperators

namespace Part6




def IsLambdaFamily (β : ℕ → ℝ) (Λ : ℕ → ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ j : ℕ, n ≤ j → Λ n j = 0) ∧
    (∀ i j : ℕ, i ≤ j → |Λ n j| ≤ |Λ n i|) ∧
    (∀ J : ℕ, n ≤ J → ∀ z : ℂ, Pn β n z = ∏ j ∈ Finset.range J, (1 + (Λ n j : ℂ) * z))







theorem reversal_identity : ∀ (β : ℕ → ℝ) (n : ℕ) (z : ℂ), z ≠ 0 →
    Qn β n z = z ^ n * Polynomial.aeval (z⁻¹) (jensenPoly β n) := by
  intro β n z hz
  rw [Qn, jensenPoly, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hpow : z ^ n * (z⁻¹) ^ (n - m) = z ^ m := by
    have hsplit : z ^ n = z ^ m * z ^ (n - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmn]
    rw [hsplit, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hz), mul_one]
  have haeval : z ^ n * Polynomial.aeval (z⁻¹)
        (Polynomial.C ((n.choose m : ℝ) * β m) * Polynomial.X ^ (n - m))
      = ((n.choose m : ℝ) * β m : ℂ) * (z ^ n * (z⁻¹) ^ (n - m)) := by
    rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Complex.coe_algebraMap]
    push_cast; ring
  rw [haeval, hpow]
  push_cast
  ring



theorem reversal : ∀ (β : ℕ → ℝ), HypH β → ∀ (n : ℕ),
    Qn β n 0 = (β 0 : ℂ) ∧ ∀ z : ℂ, Qn β n z = 0 → z.im = 0 ∧ z ≠ 0 := by
  intro β hβ n
  obtain ⟨hβ0, hrr⟩ := hβ
  have hQ0 : Qn β n 0 = (β 0 : ℂ) := by
    rw [Qn, Finset.sum_eq_single 0]
    · simp
    · intro m _ hm0; rw [zero_pow hm0, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  refine ⟨hQ0, fun z hz => ?_⟩
  have hzne : z ≠ 0 := by
    rintro rfl
    rw [hQ0] at hz
    exact hβ0.ne' (by exact_mod_cast hz)
  refine ⟨?_, hzne⟩
  rw [reversal_identity β n z hzne] at hz
  have haeval : Polynomial.aeval z⁻¹ (jensenPoly β n) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hzne)
  have hinv : (z⁻¹).im = 0 := hrr n z⁻¹ haeval
  rw [Complex.inv_im] at hinv
  have hns : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hzne).ne'
  have : -z.im = 0 := (div_eq_zero_iff.mp hinv).resolve_right hns
  linarith




theorem Pn_basic : ∀ (β : ℕ → ℝ), HypH β → ∀ (n : ℕ), 1 ≤ n →
    (∀ z : ℂ, Pn β n z
        = ∑ m ∈ Finset.range (n + 1),
            ((β m / β 0 * (n.choose m : ℝ) / (n : ℝ) ^ m : ℝ) : ℂ) * z ^ m) ∧
    Pn β n 0 = 1 ∧
    (∀ z : ℂ, Pn β n z = 0 → z.im = 0 ∧ z ≠ 0) := by
  intro β hβ n hn
  obtain ⟨hβ0, hrr⟩ := hβ
  have hβ0c : (β 0 : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have hQ0 : Qn β n 0 = (β 0 : ℂ) := (reversal β ⟨hβ0, hrr⟩ n).1
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rw [Pn, Qn, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [div_pow]
    push_cast
    ring
  · rw [Pn, show (0 : ℂ) / (n : ℂ) = 0 by simp, hQ0, inv_mul_cancel₀ hβ0c]
  · intro z hz
    have hqn : Qn β n (z / (n : ℂ)) = 0 := by
      rw [Pn] at hz
      exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hβ0c)
    obtain ⟨hw_im, hw_ne⟩ := (reversal β ⟨hβ0, hrr⟩ n).2 (z / (n : ℂ)) hqn
    have hz_ne : z ≠ 0 := fun h => hw_ne (by rw [h]; simp)
    refine ⟨?_, hz_ne⟩
    have hz_eq : z = (n : ℂ) * (z / (n : ℂ)) := by field_simp
    rw [hz_eq, Complex.mul_im]
    simp [hw_im, Complex.natCast_im]


theorem Lambda_family : ∀ (β : ℕ → ℝ), HypH β → ∃ Λ : ℕ → ℕ → ℝ, IsLambdaFamily β Λ := by
  intro β hβ
  have key : ∀ n : ℕ, 1 ≤ n → ∃ g : ℕ → ℝ,
      (∀ j : ℕ, n ≤ j → g j = 0) ∧
      (∀ i j : ℕ, i ≤ j → |g j| ≤ |g i|) ∧
      (∀ J : ℕ, n ≤ J → ∀ z : ℂ, Pn β n z = ∏ j ∈ Finset.range J, (1 + (g j : ℂ) * z)) := by
    intro n hn
    set a : ℕ → ℝ := fun m => β m / β 0 * (n.choose m : ℝ) / (n : ℝ) ^ m with ha_def
    have hβ0 : 0 < β 0 := hβ.1
    have hPn := Pn_basic β hβ n hn
    have hPnsum : ∀ z : ℂ, Pn β n z = ∑ m ∈ Finset.range (n + 1), (a m : ℂ) * z ^ m := by
      intro z; rw [hPn.1 z]
    have ha0 : a 0 = 1 := by
      simp only [ha_def, Nat.choose_zero_right, pow_zero, Nat.cast_one, mul_one, div_one]
      field_simp
    have hatail : ∀ m : ℕ, n < m → a m = 0 := by
      intro m hm
      simp only [ha_def, Nat.choose_eq_zero_of_lt hm, Nat.cast_zero, mul_zero, zero_div]
    have harr : ∀ z : ℂ, (∑ m ∈ Finset.range (n + 1), (a m : ℂ) * z ^ m) = 0 → z.im = 0 := by
      intro z hz
      rw [← hPnsum z] at hz
      exact (hPn.2.2 z hz).1
    obtain ⟨D, lam, hDn, hlne, hfac⟩ := factorization n a ha0 hatail harr
    have hPnfac : ∀ z : ℂ, Pn β n z = ∏ j ∈ Finset.range D, (1 + (lam j : ℂ) * z) := by
      intro z; rw [hPnsum z, hfac z]
    obtain ⟨⟨π, hsmono, hsprod, _, _⟩, _⟩ := sorting D (fun i : Fin D => lam (i : ℕ))
    have hPnperm : ∀ z : ℂ, Pn β n z = ∏ j : Fin D, (1 + (lam (π j) : ℂ) * z) := by
      intro z
      rw [hPnfac z]
      rw [← Fin.prod_univ_eq_prod_range (fun j => 1 + (lam j : ℂ) * z) D]
      exact (hsprod z).symm
    set g : ℕ → ℝ := fun j => if h : j < D then lam (π ⟨j, h⟩) else 0 with hg_def
    have hgval : ∀ (j : Fin D), g (j : ℕ) = lam (π j) := by
      intro j
      simp only [hg_def, Fin.is_lt, dif_pos]
    refine ⟨g, ?_, ?_, ?_⟩
    · intro j hj
      have hjD : ¬ j < D := by omega
      simp only [hg_def, hjD, dif_neg, not_false_iff]
    · intro i j hij
      by_cases hjD : j < D
      · have hiD : i < D := lt_of_le_of_lt hij hjD
        simp only [hg_def, hjD, hiD, dif_pos]
        have : (⟨i, hiD⟩ : Fin D) ≤ ⟨j, hjD⟩ := hij
        exact hsmono ⟨i, hiD⟩ ⟨j, hjD⟩ this
      · have : g j = 0 := by simp only [hg_def, hjD, dif_neg, not_false_iff]
        rw [this, abs_zero]
        exact abs_nonneg _
    · intro J hJ z
      have hDJ : D ≤ J := le_trans hDn hJ
      have hstep1 : (∏ j ∈ Finset.range J, (1 + (g j : ℂ) * z))
          = ∏ j ∈ Finset.range D, (1 + (g j : ℂ) * z) := by
        symm
        apply Finset.prod_subset (Finset.range_mono hDJ)
        intro x hxJ hxD
        rw [Finset.mem_range] at hxJ hxD
        have hxD' : ¬ x < D := hxD
        have hgx : g x = 0 := by simp only [hg_def, hxD', dif_neg, not_false_iff]
        rw [hgx]; push_cast; ring
      have hstep2 : (∏ j ∈ Finset.range D, (1 + (g j : ℂ) * z))
          = ∏ j : Fin D, (1 + (lam (π j) : ℂ) * z) := by
        rw [← Fin.prod_univ_eq_prod_range (fun j => 1 + (g j : ℂ) * z) D]
        apply Finset.prod_congr rfl
        intro j _
        rw [hgval j]
      rw [hstep1, hstep2, ← hPnperm z]
  classical
  refine ⟨fun n => if h : 1 ≤ n then (key n h).choose else fun _ => 0, ?_⟩
  intro n hn
  simp only [dif_pos hn]
  exact (key n hn).choose_spec





theorem symmetric : ∀ (β : ℕ → ℝ), HypH β → ∀ (n : ℕ), 1 ≤ n →
    ∀ (J : ℕ) (lam : ℕ → ℝ),
      (∀ z : ℂ, (∏ j ∈ Finset.range J, (1 + (lam j : ℂ) * z)) = Pn β n z) →
      (∑ j ∈ Finset.range J, lam j = delta β) ∧
      (∑ S ∈ Finset.powersetCard 2 (Finset.range J), ∏ i ∈ S, lam i
          = ((n : ℝ) - 1) / (2 * n) * (β 2 / β 0)) ∧
      (∑ j ∈ Finset.range J, (lam j) ^ 2
          = (delta β) ^ 2 - ((n : ℝ) - 1) / n * (β 2 / β 0)) ∧
      (0 ≤ ∑ j ∈ Finset.range J, (lam j) ^ 2 ∧
        ∑ j ∈ Finset.range J, (lam j) ^ 2 ≤ Mconst β) := by
  intro β hβ n hn J lam h
  obtain ⟨hβ0, hrr⟩ := hβ
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  set d := max (max J n) 2 with hd
  have hJd : J ≤ d := le_trans (le_max_left J n) (le_max_left _ 2)
  have hnd : n ≤ d := le_trans (le_max_right J n) (le_max_left _ 2)
  have h2d : 2 ≤ d := le_max_right _ 2
  set E : ℕ → ℝ := fun k => ∑ S ∈ Finset.powersetCard k (Finset.range J), ∏ i ∈ S, lam i with hE
  set c : ℕ → ℝ := fun k => β k / β 0 * (n.choose k : ℝ) / (n : ℝ) ^ k with hc
  set a : ℕ → ℂ := fun k => ((E k : ℝ) : ℂ) with ha
  set b : ℕ → ℂ := fun k => ((c k : ℝ) : ℂ) with hb
  have hAB : ∀ z : ℂ, (∑ k ∈ Finset.range (d + 1), a k * z ^ k)
      = ∑ k ∈ Finset.range (d + 1), b k * z ^ k := by
    intro z
    have hRHS : (∑ k ∈ Finset.range (d + 1), b k * z ^ k) = Pn β n z := by
      have hdrop : (∑ k ∈ Finset.range (d + 1), b k * z ^ k)
          = ∑ k ∈ Finset.range (n + 1), b k * z ^ k := by
        symm
        apply Finset.sum_subset
        · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
        · intro k _ hknot
          rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hknot
          have : n.choose k = 0 := Nat.choose_eq_zero_of_lt hknot
          simp [hb, hc, this]
      rw [hdrop, (Pn_basic β ⟨hβ0, hrr⟩ n hn).1 z]
    have hLHS : (∑ k ∈ Finset.range (d + 1), a k * z ^ k)
        = ∏ j ∈ Finset.range J, (1 + (lam j : ℂ) * z) := by
      rw [vieta J (fun i => (lam i : ℂ)) z]
      have hcoeff : ∀ k, (∑ S ∈ Finset.powersetCard k (Finset.range J),
            ∏ i ∈ S, (lam i : ℂ)) = a k := by
        intro k
        rw [ha]; simp only
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl (fun S _ => by rw [Complex.ofReal_prod])
      have hshrink : (∑ k ∈ Finset.range (d + 1), a k * z ^ k)
          = ∑ k ∈ Finset.range (J + 1), a k * z ^ k := by
        symm
        apply Finset.sum_subset
        · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
        · intro k _ hknot
          rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hknot
          have hemp : Finset.powersetCard k (Finset.range J) = ∅ := by
            rw [Finset.powersetCard_eq_empty, Finset.card_range]; exact hknot
          simp [ha, hE, hemp]
      rw [hshrink]
      exact Finset.sum_congr rfl (fun k _ => by rw [hcoeff k])
    rw [hLHS, hRHS, h z]
  have hcoeffeq : ∀ k, k ≤ d → E k = c k := by
    intro k hk
    have := poly_ext d a b hAB k hk
    rw [ha, hb] at this; simp only at this
    exact Complex.ofReal_inj.mp this
  have hE1 : E 1 = ∑ j ∈ Finset.range J, lam j := by
    rw [hE]; simp only
    rw [Finset.powersetCard_one, Finset.sum_map]
    exact Finset.sum_congr rfl (fun i _ => by simp)
  have hc1 : c 1 = β 1 / β 0 := by
    rw [hc]; simp only; rw [Nat.choose_one_right]; field_simp
  have hpart1 : ∑ j ∈ Finset.range J, lam j = delta β := by
    rw [← hE1, hcoeffeq 1 (le_trans hn hnd), hc1, delta]
  have hc2 : c 2 = ((n : ℝ) - 1) / (2 * n) * (β 2 / β 0) := by
    rw [hc]; simp only; rw [Nat.cast_choose_two]; field_simp; try ring
  have hE2eq : E 2 = c 2 := hcoeffeq 2 h2d
  have hpart2 : ∑ S ∈ Finset.powersetCard 2 (Finset.range J), ∏ i ∈ S, lam i
      = ((n : ℝ) - 1) / (2 * n) * (β 2 / β 0) := by
    have : E 2 = ∑ S ∈ Finset.powersetCard 2 (Finset.range J), ∏ i ∈ S, lam i := by rw [hE]
    rw [← this, hE2eq, hc2]
  have hpart3 : ∑ j ∈ Finset.range J, (lam j) ^ 2
      = (delta β) ^ 2 - ((n : ℝ) - 1) / n * (β 2 / β 0) := by
    have hnewt := newton J lam
    rw [hpart1] at hnewt; rw [hpart2] at hnewt
    have : ∑ j ∈ Finset.range J, (lam j) ^ 2
        = (delta β) ^ 2 - 2 * (((n : ℝ) - 1) / (2 * n) * (β 2 / β 0)) := by linarith [hnewt]
    rw [this]; field_simp; try ring
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range J, (lam j) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hub : ∑ j ∈ Finset.range J, (lam j) ^ 2 ≤ Mconst β := by
    rw [hpart3, Mconst]
    have hfrac_le : ((n : ℝ) - 1) / n ≤ 1 := by rw [div_le_one hnpos]; linarith
    have hfrac_nonneg : (0 : ℝ) ≤ ((n : ℝ) - 1) / n := by
      apply div_nonneg _ (le_of_lt hnpos)
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hb0 : (0 : ℝ) < β 0 := hβ0
    have hkey : -(((n : ℝ) - 1) / n) * (β 2) ≤ |β 2| := by
      calc -(((n : ℝ) - 1) / n) * (β 2) = (((n : ℝ) - 1) / n) * (-(β 2)) := by ring
        _ ≤ (((n : ℝ) - 1) / n) * |β 2| :=
              mul_le_mul_of_nonneg_left (neg_le_abs (β 2)) hfrac_nonneg
        _ ≤ 1 * |β 2| := mul_le_mul_of_nonneg_right hfrac_le (abs_nonneg (β 2))
        _ = |β 2| := by ring
    have hkey2 : (-(((n : ℝ) - 1) / n) * (β 2)) / β 0 ≤ |β 2| / β 0 :=
      div_le_div_of_nonneg_right hkey (le_of_lt hb0)
    have heq : (-(((n : ℝ) - 1) / n) * (β 2)) / β 0
        = -(((n : ℝ) - 1) / n) * (β 2 / β 0) := by ring
    rw [heq] at hkey2
    linarith [hkey2]
  exact ⟨hpart1, hpart2, hpart3, hnonneg, hub⟩



theorem B_limit : ∀ (β : ℕ → ℝ), HypH β →
    Filter.Tendsto (fun n : ℕ => (delta β) ^ 2 - ((n : ℝ) - 1) / n * (β 2 / β 0))
        Filter.atTop (nhds (Bconst β)) ∧
    0 ≤ Bconst β ∧ Bconst β ≤ Mconst β := by
  intro β hβ
  obtain ⟨hβ0, hrr⟩ := hβ
  have htend : Filter.Tendsto (fun n : ℕ => (delta β) ^ 2 - ((n : ℝ) - 1) / n * (β 2 / β 0))
      Filter.atTop (nhds (Bconst β)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) - 1) / n) Filter.atTop (nhds 1) := by
      have hcong : (fun n : ℕ => ((n : ℝ) - 1) / n) =ᶠ[Filter.atTop] (fun n => 1 - 1 / (n : ℝ)) := by
        filter_upwards [Filter.eventually_gt_atTop 0] with n hn
        have hnn : (n : ℝ) ≠ 0 := by
          have : (0 : ℝ) < n := by exact_mod_cast hn
          exact ne_of_gt this
        field_simp
      rw [Filter.tendsto_congr' hcong]
      have h0 : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat 1
      have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
      simpa using hh
    have hBc : Bconst β = (delta β) ^ 2 - 1 * (β 2 / β 0) := by rw [Bconst]; ring
    rw [hBc]
    have h2 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) - 1) / n * (β 2 / β 0)) Filter.atTop
        (nhds (1 * (β 2 / β 0))) := h1.mul_const (β 2 / β 0)
    exact h2.const_sub ((delta β) ^ 2)
  refine ⟨htend, ?_, ?_⟩
  · obtain ⟨Λ, hΛ⟩ := Lambda_family β ⟨hβ0, hrr⟩
    apply ge_of_tendsto htend
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    obtain ⟨_, _, hprod⟩ := hΛ n hn
    have hsym := (symmetric β ⟨hβ0, hrr⟩ n hn n (Λ n) (fun z => (hprod n (le_refl n) z).symm)).2.2.1
    rw [← hsym]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · rw [Bconst, Mconst]
    have hdiv : -(β 2 / β 0) ≤ |β 2| / β 0 := by
      rw [← neg_div]
      exact (div_le_div_iff_of_pos_right hβ0).mpr (neg_le_abs _)
    linarith




theorem lambda_decay : ∀ (β : ℕ → ℝ), HypH β → ∀ (Λ : ℕ → ℕ → ℝ), IsLambdaFamily β Λ →
    ∀ n : ℕ, 1 ≤ n →
      (∀ J : ℕ, ∑ i ∈ Finset.range J, (Λ n i) ^ 2 ≤ Mconst β) ∧
      (∀ j : ℕ, |Λ n j| ≤ Real.sqrt (Mconst β / ((j : ℝ) + 1))) := by
  intro β hβ Λ hΛ n hn
  obtain ⟨hzero, hmono, hprod⟩ := hΛ n hn
  have hsumM : ∀ J : ℕ, ∑ i ∈ Finset.range J, (Λ n i) ^ 2 ≤ Mconst β := by
    intro J
    have hJJ' : J ≤ max J n := le_max_left _ _
    have hnJ' : n ≤ max J n := le_max_right _ _
    have hsym := (symmetric β hβ n hn (max J n) (Λ n) (fun z => (hprod (max J n) hnJ' z).symm)).2.2.2.2
    calc ∑ i ∈ Finset.range J, (Λ n i) ^ 2
        ≤ ∑ i ∈ Finset.range (max J n), (Λ n i) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hJJ')
          intro i _ _; positivity
      _ ≤ Mconst β := hsym
  refine ⟨hsumM, fun j => ?_⟩
  have hpart : ((j : ℝ) + 1) * (Λ n j) ^ 2 ≤ Mconst β := by
    have hterm : ∀ i ∈ Finset.range (j + 1), (Λ n j) ^ 2 ≤ (Λ n i) ^ 2 := by
      intro i hi
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      have hm := hmono i j hi
      nlinarith [sq_abs (Λ n j), sq_abs (Λ n i), abs_nonneg (Λ n i), abs_nonneg (Λ n j), hm]
    have hconst : ((j : ℝ) + 1) * (Λ n j) ^ 2 = ∑ _i ∈ Finset.range (j + 1), (Λ n j) ^ 2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    rw [hconst]
    calc ∑ _i ∈ Finset.range (j + 1), (Λ n j) ^ 2
        ≤ ∑ i ∈ Finset.range (j + 1), (Λ n i) ^ 2 := Finset.sum_le_sum hterm
      _ ≤ Mconst β := hsumM (j + 1)
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hsq : (Λ n j) ^ 2 ≤ Mconst β / ((j : ℝ) + 1) := by
    rw [le_div_iff₀ hj1]; nlinarith [hpart]
  calc |Λ n j| = Real.sqrt ((Λ n j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Mconst β / ((j : ℝ) + 1)) := Real.sqrt_le_sqrt hsq




theorem E_product : ∀ (β : ℕ → ℝ), HypH β → ∀ (Λ : ℕ → ℕ → ℝ), IsLambdaFamily β Λ →
    ∀ n : ℕ, 1 ≤ n → ∀ J : ℕ, n ≤ J → ∀ z : ℂ,
      Pn β n z = Complex.exp ((delta β : ℂ) * z) * ∏ j ∈ Finset.range J, E ((Λ n j : ℂ) * z) := by
  intro β hβ Λ hΛ n hn J hJ z
  obtain ⟨hzero, hmono, hprod⟩ := hΛ n hn
  have hsum : (∑ j ∈ Finset.range J, (Λ n j : ℂ)) = (delta β : ℂ) := by
    have hs := (symmetric β hβ n hn J (Λ n) (fun z => (hprod J hJ z).symm)).1
    rw [← hs]; push_cast; ring
  have hEprod : ∏ j ∈ Finset.range J, E ((Λ n j : ℂ) * z)
      = (∏ j ∈ Finset.range J, (1 + (Λ n j : ℂ) * z))
        * Complex.exp (-(∑ j ∈ Finset.range J, (Λ n j : ℂ)) * z) := by
    simp only [E]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [← Complex.exp_sum]
    congr 1
    simp only [← mul_neg]
    rw [← Finset.sum_mul]
    ring
  rw [hEprod, hsum, ← hprod J hJ z,
      show Complex.exp ((delta β : ℂ) * z) * (Pn β n z * Complex.exp (-(delta β : ℂ) * z))
        = Pn β n z * (Complex.exp ((delta β : ℂ) * z) * Complex.exp (-(delta β : ℂ) * z)) by ring,
      ← Complex.exp_add,
      show (delta β : ℂ) * z + -(delta β : ℂ) * z = 0 by ring,
      Complex.exp_zero, mul_one]

end Part6
