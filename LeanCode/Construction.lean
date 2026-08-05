import LeanCode.Vocab





















open Set

namespace Assembly

namespace Construction




noncomputable def sawtooth : ℝ → ℝ := fun t => (⌈t⌉ : ℝ) - t


theorem sawtooth_periodic : ∀ t : ℝ, sawtooth (t + 1) = sawtooth t := by
  intro t
  unfold sawtooth
  rw [Int.ceil_add_one]
  push_cast
  ring


theorem sawtooth_mem_Ioo :
    ∀ t : ℝ, ¬ (∃ z : ℤ, (z : ℝ) = t) → 0 < sawtooth t ∧ sawtooth t < 1 := by
  intro t h
  unfold sawtooth
  refine ⟨?_, ?_⟩
  ·
    have hlt : (t : ℝ) < ⌈t⌉ := by
      rcases lt_or_eq_of_le (Int.le_ceil t) with hlt | heq
      · exact hlt
      · exact absurd ⟨⌈t⌉, heq.symm⟩ h
    linarith
  · have := Int.ceil_lt_add_one t
    linarith




def badSet (x α : ℝ) : Set ℝ :=
  (fun p : ℤ × ℤ => x + α * (p.1 : ℝ) - (p.2 : ℝ)) '' (Set.univ : Set (ℤ × ℤ))

theorem badSet_countable (x α : ℝ) : (badSet x α).Countable :=
  Set.countable_univ.image _





theorem choose_a (x₀ ε x α : ℝ) (hα : 0 < α) (hε : 0 < ε) (hsum : 2 * ε + α < 1) :
    ∃ a : ℝ, a ∈ Set.Icc (x₀ - 1 + ε) (x₀ - ε - α) ∧ a ∉ badSet x α := by


  have hlt : x₀ - 1 + ε < x₀ - ε - α := by linarith

  have hJ_unc : ¬ (Set.Icc (x₀ - 1 + ε) (x₀ - ε - α)).Countable := by
    rw [Cardinal.Real.Icc_countable_iff]
    exact not_le.mpr hlt

  have hne : (Set.Icc (x₀ - 1 + ε) (x₀ - ε - α) \ badSet x α).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
    exact hJ_unc ((badSet_countable x α).mono hemp)
  obtain ⟨a, ha_mem, ha_notin⟩ := hne
  exact ⟨a, ha_mem, ha_notin⟩









def I (x₀ ε : ℝ) : Set ℝ := Set.Icc (x₀ - 1 + ε) (x₀ - ε)


noncomputable def deltaSeq (x α a : ℝ) : ℤ → ℝ :=
  fun k => a + α * sawtooth (((k : ℝ) + a - x) / α)


noncomputable def nu (x α a : ℝ) : ℤ → ℤ :=
  fun k => ⌈((k : ℝ) + a - x) / α⌉




theorem tk_not_int (x α a : ℝ) (hα : 0 < α) (ha : a ∉ badSet x α) :
    ∀ k : ℤ, ¬ ∃ z : ℤ, (z : ℝ) = ((k : ℝ) + a - x) / α := by
  intro k ⟨z, hz⟩
  apply ha

  have hα' : α ≠ 0 := ne_of_gt hα
  have hzeq : (z : ℝ) * α = (k : ℝ) + a - x := by
    field_simp at hz
    linarith [hz]
  refine ⟨(z, k), Set.mem_univ _, ?_⟩
  simp only
  linarith [hzeq]



theorem deltaSeq_mem_Ioo (x α a : ℝ) (hα : 0 < α) (ha : a ∉ badSet x α) :
    ∀ k : ℤ, a < deltaSeq x α a k ∧ deltaSeq x α a k < a + α := by
  intro k
  have hF := sawtooth_mem_Ioo (((k : ℝ) + a - x) / α) (tk_not_int x α a hα ha k)
  obtain ⟨hF0, hF1⟩ := hF
  unfold deltaSeq
  constructor
  · nlinarith [mul_pos hα hF0]
  · nlinarith [mul_lt_of_lt_one_right hα hF1]




theorem deltaSeq_mem_I (x₀ ε x α a : ℝ) (hα : 0 < α) (ha : a ∉ badSet x α)
    (hsub : Set.Ico a (a + α) ⊆ I x₀ ε) :
    ∀ k : ℤ, deltaSeq x α a k ∈ I x₀ ε := by
  intro k
  obtain ⟨h0, h1⟩ := deltaSeq_mem_Ioo x α a hα ha k
  exact hsub ⟨le_of_lt h0, h1⟩



theorem deltaSeq_lattice (x α a : ℝ) (hα : 0 < α) :
    ∀ k : ℤ, (k : ℝ) + deltaSeq x α a k = x + α * (nu x α a k : ℝ) := by
  intro k
  unfold deltaSeq nu sawtooth
  have hα' : α ≠ 0 := ne_of_gt hα
  field_simp
  ring





theorem nu_injective (x α a : ℝ) (hα : 0 < α) (hα1 : α < 1) (ha : a ∉ badSet x α) :
    Function.Injective (nu x α a) := by
  intro k1 k2 hnu

  have l1 := deltaSeq_lattice x α a hα k1
  have l2 := deltaSeq_lattice x α a hα k2
  have hlat : (k1 : ℝ) + deltaSeq x α a k1 = (k2 : ℝ) + deltaSeq x α a k2 := by
    rw [l1, l2, hnu]

  obtain ⟨h1a, h1b⟩ := deltaSeq_mem_Ioo x α a hα ha k1
  obtain ⟨h2a, h2b⟩ := deltaSeq_mem_Ioo x α a hα ha k2

  have hd : |(k1 : ℝ) - k2| < 1 := by
    have hsub : (k1 : ℝ) - k2 = deltaSeq x α a k2 - deltaSeq x α a k1 := by linarith
    rw [hsub, abs_lt]
    constructor <;> linarith
  have hcast : |((k1 - k2 : ℤ) : ℝ)| < 1 := by push_cast; exact hd
  have hint : |k1 - k2| < (1 : ℤ) := by exact_mod_cast hcast
  have : k1 - k2 = 0 := Int.abs_lt_one_iff.mp hint
  omega






theorem gaborSubmatrix_offDiagonalDecay (g : ℝ → ℝ) (δ : ℤ → ℝ)
    (hg : HasPolynomialDecay g) (hδ : ∃ R : ℝ, ∀ k : ℤ, |δ k| ≤ R) :
    HasPolynomialOffDiagonalDecayR (GaborSubmatrixR g δ) := by
  obtain ⟨C, η, hC, hη, hbound⟩ := hg
  obtain ⟨R, hR⟩ := hδ

  have hRnonneg : 0 ≤ R := le_trans (abs_nonneg _) (hR 0)
  refine ⟨C * (1 + R) ^ η, η, ?_, hη, ?_⟩
  · have : (0 : ℝ) < (1 + R) ^ η := Real.rpow_pos_of_pos (by positivity) η
    positivity
  intro n m

  set dk : ℝ := (n : ℝ) + δ n - (m : ℝ) with hdk_def
  set kl : ℝ := (n : ℝ) - (m : ℝ) with hkl_def

  have hgbound : ‖GaborSubmatrixR g δ n m‖ ≤ C / (1 + |dk|) ^ η := by
    have := hbound dk
    rw [Real.norm_eq_abs]
    simpa [GaborSubmatrixR, hdk_def, sub_eq_add_neg] using this

  have htri : 1 + |kl| ≤ (1 + R) * (1 + |dk|) := by
    have hlink : kl = dk - δ n := by rw [hkl_def, hdk_def]; ring
    have h1 : |kl| ≤ |dk| + |δ n| := by rw [hlink]; exact abs_sub _ _
    have h2 : |δ n| ≤ R := hR n
    have hdknn : 0 ≤ |dk| := abs_nonneg _
    nlinarith [mul_nonneg hRnonneg hdknn]

  have hpos_dk : (0 : ℝ) < 1 + |dk| := by positivity
  have hpos_kl : (0 : ℝ) < 1 + |kl| := by positivity
  have hpos_R : (0 : ℝ) < 1 + R := by positivity
  have hmono : (1 + |kl|) ^ η ≤ ((1 + R) * (1 + |dk|)) ^ η :=
    Real.rpow_le_rpow (le_of_lt hpos_kl) htri (le_of_lt (by linarith : (0 : ℝ) < η))
  have hmul : ((1 + R) * (1 + |dk|)) ^ η = (1 + R) ^ η * (1 + |dk|) ^ η :=
    Real.mul_rpow (le_of_lt hpos_R) (le_of_lt hpos_dk)
  rw [hmul] at hmono
  have hdkpow : (0 : ℝ) < (1 + |dk|) ^ η := Real.rpow_pos_of_pos hpos_dk η
  have hklpow : (0 : ℝ) < (1 + |kl|) ^ η := Real.rpow_pos_of_pos hpos_kl η
  have hchain : C / (1 + |dk|) ^ η ≤ (C * (1 + R) ^ η) / (1 + |kl|) ^ η := by
    rw [div_le_div_iff₀ hdkpow hklpow]
    calc C * (1 + |kl|) ^ η
        ≤ C * ((1 + R) ^ η * (1 + |dk|) ^ η) :=
          mul_le_mul_of_nonneg_left hmono (le_of_lt hC)
      _ = C * (1 + R) ^ η * (1 + |dk|) ^ η := by ring

  have hgoal : ‖GaborSubmatrixR g δ n m‖ ≤ (C * (1 + R) ^ η) / (1 + |kl|) ^ η :=
    le_trans hgbound hchain
  simpa [hkl_def] using hgoal

end Construction

end Assembly
