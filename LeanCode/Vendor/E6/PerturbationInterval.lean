import LeanCode.Vendor.E6.External
import LeanCode.Vendor.E6.ZakCriticalLine

noncomputable section

namespace E6

theorem perturbationInterval_nonempty {x₀ ε : ℝ}
    (_hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (_hε₀ : 0 < ε) (hε₁ : ε < 1 / 2) :
    (PerturbationInterval x₀ ε).Nonempty := by
  rw [PerturbationInterval, Set.nonempty_Icc]
  linarith

theorem perturbationInterval_isCompact {x₀ ε : ℝ} :
    IsCompact (PerturbationInterval x₀ ε) := by
  simpa [PerturbationInterval] using isCompact_Icc

theorem perturbationInterval_subset_open {x₀ ε : ℝ}
    (_hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hε₀ : 0 < ε) (_hε₁ : ε < 1 / 2) :
    PerturbationInterval x₀ ε ⊆ Set.Ioo (x₀ - 1) x₀ := by
  intro t ht
  rw [PerturbationInterval] at ht
  rcases ht with ⟨hlo, hhi⟩
  constructor
  · linarith
  · linarith

theorem perturbationInterval_abs_le_one {x₀ ε t : ℝ}
    (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hε₀ : 0 < ε) (_hε₁ : ε < 1 / 2)
    (ht : t ∈ PerturbationInterval x₀ ε) :
    |t| ≤ 1 := by
  rw [PerturbationInterval] at ht
  rw [abs_le]
  constructor <;> linarith [hx₀.1, hx₀.2, hε₀, ht.1, ht.2]

theorem integer_translate_not_mem_gap {x₀ : ℝ}
    (_hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ n : ℤ, x₀ + (n : ℝ) ∉ Set.Ioo (x₀ - 1) x₀ := by
  intro n hn
  rw [Set.mem_Ioo] at hn
  have hn_lt_zero_real : (n : ℝ) < 0 := by linarith
  have hneg_one_lt_n_real : (-1 : ℝ) < n := by linarith
  have hn_lt_zero : n < 0 := by exact_mod_cast hn_lt_zero_real
  have hneg_one_lt_n : (-1 : ℤ) < n := by exact_mod_cast hneg_one_lt_n_real
  omega

theorem criticalLine_ne_zero_on_perturbationInterval (g : ℝ → ℝ)
    (hg₀ : g ≠ 0) (hg : IsTotallyPositiveIntegrableContinuous g)
    (hdecay : HasExponentialDecay g)
    {x₀ ε : ℝ}
    (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hx₀zero : Z g hdecay (x₀, 1 / 2) = 0)
    (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2) :
    ∀ ⦃t : ℝ⦄, t ∈ PerturbationInterval x₀ ε →
      criticalLineFunction g t ≠ 0 := by
  intro t ht htzero
  rcases VinogradovUlitskaya g hg₀ hg with ⟨xuniq, _hxuniq, huniq⟩
  have hx₀zero_ext :
      Z g (ExponentialDecay g ⟨hg.1, hg.2.1⟩) (x₀, 1 / 2) = 0 := by
    simpa [Z] using hx₀zero
  have hx₀_eq : x₀ = xuniq := huniq x₀ ⟨hx₀, hx₀zero_ext⟩
  rcases perturbationInterval_subset_open hx₀ hε₀ hε₁ ht with ⟨ht_lower, ht_upper⟩
  by_cases ht_nonneg : 0 ≤ t
  · have htIco : t ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · exact ht_nonneg
      · exact lt_trans ht_upper hx₀.2
    have htZ :
        Z g (ExponentialDecay g ⟨hg.1, hg.2.1⟩) (t, 1 / 2) = 0 := by
      have hzt := (zak_half_eq_zero_iff_criticalLine_eq_zero g hdecay t).mpr htzero
      simpa [Z] using hzt
    have ht_eq : t = x₀ := by
      exact (huniq t ⟨htIco, htZ⟩).trans hx₀_eq.symm
    linarith
  · have ht_neg : t < 0 := lt_of_not_ge ht_nonneg
    have ht1zero : criticalLineFunction g (t + 1) = 0 := by
      have hshift := criticalLine_intShift g hdecay t (1 : ℤ)
      simpa [htzero] using hshift
    have ht1Ico : t + 1 ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · linarith [ht_lower, hx₀.1]
      · linarith
    have ht1Z :
        Z g (ExponentialDecay g ⟨hg.1, hg.2.1⟩) (t + 1, 1 / 2) = 0 := by
      have hzt :=
        (zak_half_eq_zero_iff_criticalLine_eq_zero g hdecay (t + 1)).mpr ht1zero
      simpa [Z] using hzt
    have ht1_eq : t + 1 = x₀ := by
      exact (huniq (t + 1) ⟨ht1Ico, ht1Z⟩).trans hx₀_eq.symm
    linarith

theorem criticalLine_uniform_sign_on_perturbationInterval (g : ℝ → ℝ)
    (hg₀ : g ≠ 0) (hg : IsTotallyPositiveIntegrableContinuous g)
    (hdecay : HasExponentialDecay g)
    {x₀ ε : ℝ}
    (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hx₀zero : Z g hdecay (x₀, 1 / 2) = 0)
    (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2) :
    ∃ m σ : ℝ, 0 < m ∧ (σ = 1 ∨ σ = -1) ∧
      ∀ ⦃t : ℝ⦄, t ∈ PerturbationInterval x₀ ε →
        m ≤ σ * criticalLineFunction g t := by
  let K : Set ℝ := PerturbationInterval x₀ ε
  let f : ℝ → ℝ := criticalLineFunction g
  have hKcompact : IsCompact K := by
    simpa [K] using (perturbationInterval_isCompact (x₀ := x₀) (ε := ε))
  have hKnonempty : K.Nonempty := by
    simpa [K] using perturbationInterval_nonempty hx₀ hε₀ hε₁
  have hfcont : ContinuousOn f K := by
    simpa [f, K] using (continuous_criticalLineFunction g hg.2.2 hdecay).continuousOn
  have hne : ∀ ⦃t : ℝ⦄, t ∈ K → f t ≠ 0 := by
    intro t ht
    simpa [f, K] using
      criticalLine_ne_zero_on_perturbationInterval
        g hg₀ hg hdecay hx₀ hx₀zero hε₀ hε₁ ht
  have hconn : IsPreconnected K := by
    simpa [K, PerturbationInterval] using
      (isPreconnected_Icc : IsPreconnected (Set.Icc (x₀ - 1 + ε) (x₀ - ε)))
  rcases hKcompact.exists_isMinOn hKnonempty hfcont.abs with ⟨t₀, ht₀, hmin⟩
  have ht₀_ne : f t₀ ≠ 0 := hne ht₀
  have hmpos : 0 < |f t₀| := abs_pos.mpr ht₀_ne
  have hpos_all (ht₀pos : 0 < f t₀) :
      ∀ ⦃t : ℝ⦄, t ∈ K → 0 < f t := by
    intro t ht
    by_contra hnot
    have ht_le : f t ≤ 0 := le_of_not_gt hnot
    have ht_neg : f t < 0 := lt_of_le_of_ne ht_le (hne ht)
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (f t) (f t₀) :=
      ⟨ht_neg.le, ht₀pos.le⟩
    rcases hconn.intermediate_value ht ht₀ hfcont hzero_mem with ⟨z, hzK, hz⟩
    exact (hne hzK) hz
  have hneg_all (ht₀neg : f t₀ < 0) :
      ∀ ⦃t : ℝ⦄, t ∈ K → f t < 0 := by
    intro t ht
    by_contra hnot
    have ht_ge : 0 ≤ f t := le_of_not_gt hnot
    have ht_pos : 0 < f t := lt_of_le_of_ne ht_ge (hne ht).symm
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (f t₀) (f t) :=
      ⟨ht₀neg.le, ht_pos.le⟩
    rcases hconn.intermediate_value ht₀ ht hfcont hzero_mem with ⟨z, hzK, hz⟩
    exact (hne hzK) hz
  rcases lt_or_gt_of_ne ht₀_ne with ht₀neg | ht₀pos
  · refine ⟨|f t₀|, -1, hmpos, Or.inr rfl, ?_⟩
    intro t ht
    have htneg := hneg_all ht₀neg (by simpa [K] using ht)
    have hmin_t := hmin (by simpa [K] using ht)
    simpa [f, abs_of_neg htneg] using hmin_t
  · refine ⟨|f t₀|, 1, hmpos, Or.inl rfl, ?_⟩
    intro t ht
    have htpos := hpos_all ht₀pos (by simpa [K] using ht)
    have hmin_t := hmin (by simpa [K] using ht)
    simpa [f, abs_of_pos htpos] using hmin_t

end E6
