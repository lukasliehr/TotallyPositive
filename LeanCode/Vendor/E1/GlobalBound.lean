import LeanCode.Vendor.E1.IntegralEstimates

noncomputable section

namespace ExpDecay

theorem global_bound {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, g x ≤ M := by
  classical
  by_cases htwo : ∃ a b : ℝ, a ∈ positivitySet g ∧ b ∈ positivitySet g ∧ a < b
  · rcases htwo with ⟨a, b, ha, hb, hab⟩
    let δ : ℝ := (b - a) / 2
    let L : ℝ := (totalMass g) ^ 2 / (g b * δ ^ 2)
    let R : ℝ := (totalMass g) ^ 2 / (g a * δ ^ 2)
    let M : ℝ := max 1 (max L R)
    have ha_pos : 0 < g a := by simpa [positivitySet] using ha
    have hb_pos : 0 < g b := by simpa [positivitySet] using hb
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left 1 (max L R))
    refine ⟨M, hM, ?_⟩
    intro x
    by_cases hxle : x ≤ (a + b) / 2
    · have hxb : x < b := by linarith
      have hleft := endpointLeft_bound hg hxb hb_pos
      have hδle : δ ≤ b - x := by
        dsimp [δ]
        nlinarith
      have hbx_nonneg : 0 ≤ b - x := sub_nonneg.mpr hxb.le
      have hδsq_le : δ ^ 2 ≤ (b - x) ^ 2 :=
        (sq_le_sq₀ hδ.le hbx_nonneg).2 hδle
      have hden_pos : 0 < g b * δ ^ 2 := mul_pos hb_pos (sq_pos_of_pos hδ)
      have hden_le : g b * δ ^ 2 ≤ g b * (b - x) ^ 2 :=
        mul_le_mul_of_nonneg_left hδsq_le hb_pos.le
      have hquot :
          (totalMass g) ^ 2 / (g b * (b - x) ^ 2) ≤ L := by
        dsimp [L]
        exact div_le_div_of_nonneg_left (sq_nonneg (totalMass g)) hden_pos hden_le
      exact (hleft.trans hquot).trans
        ((le_max_left L R).trans (le_max_right 1 (max L R)))
    · have hxgt : (a + b) / 2 < x := lt_of_not_ge hxle
      have hax : a < x := by linarith
      have hright := endpointRight_bound hg hax ha_pos
      have hδle : δ ≤ x - a := by
        dsimp [δ]
        nlinarith
      have hxa_nonneg : 0 ≤ x - a := sub_nonneg.mpr hax.le
      have hδsq_le : δ ^ 2 ≤ (x - a) ^ 2 :=
        (sq_le_sq₀ hδ.le hxa_nonneg).2 hδle
      have hden_pos : 0 < g a * δ ^ 2 := mul_pos ha_pos (sq_pos_of_pos hδ)
      have hden_le : g a * δ ^ 2 ≤ g a * (x - a) ^ 2 :=
        mul_le_mul_of_nonneg_left hδsq_le ha_pos.le
      have hquot :
          (totalMass g) ^ 2 / (g a * (x - a) ^ 2) ≤ R := by
        dsimp [R]
        exact div_le_div_of_nonneg_left (sq_nonneg (totalMass g)) hden_pos hden_le
      exact (hright.trans hquot).trans
        ((le_max_right L R).trans (le_max_right 1 (max L R)))
  · by_cases hex : ∃ u : ℝ, u ∈ positivitySet g
    · rcases hex with ⟨u, hu⟩
      let M : ℝ := max 1 (g u)
      have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left 1 (g u))
      refine ⟨M, hM, ?_⟩
      intro x
      by_cases hxpos : x ∈ positivitySet g
      · have hxu : x = u := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact htwo ⟨x, u, hxpos, hu, hlt⟩
          · exact htwo ⟨u, x, hu, hxpos, hgt⟩
        rw [hxu]
        exact le_max_right 1 (g u)
      · have hxle : g x ≤ 0 := by
          dsimp [positivitySet] at hxpos
          exact le_of_not_gt hxpos
        exact hxle.trans (le_trans zero_le_one (le_max_left 1 (g u)))
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x
      have hxnot : ¬ x ∈ positivitySet g := fun hx => hex ⟨x, hx⟩
      have hxle : g x ≤ 0 := by
        dsimp [positivitySet] at hxnot
        exact le_of_not_gt hxnot
      exact hxle.trans zero_le_one

end ExpDecay
