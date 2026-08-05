import LeanCode.Vendor.E5.P12.Part12.Columns
import LeanCode.Vendor.E5.Defs
open VendorE5

open MeasureTheory
















namespace Part12



theorem ratio_cont (g : ℝ → ℝ) (hg : Continuous g) (hdec : HasExponentialDecay g)
    (hB : ∀ x : ℝ, 0 < Bcol g x) :
    Continuous (fun x : ℝ => Acol g x / Bcol g x) := by
  obtain ⟨hcA, hcB⟩ := cont g hg hdec
  exact hcA.div hcB (fun x => (hB x).ne')


theorem ratio_pos (g : ℝ → ℝ) (hA : ∀ x : ℝ, 0 < Acol g x)
    (hB : ∀ x : ℝ, 0 < Bcol g x) :
    ∀ x : ℝ, 0 < Acol g x / Bcol g x :=
  fun x => div_pos (hA x) (hB x)



theorem ratio_inv (g : ℝ → ℝ) (_hA : ∀ x : ℝ, 0 < Acol g x)
    (_hB : ∀ x : ℝ, 0 < Bcol g x) :
    ∀ x : ℝ, Acol g (x + 1) / Bcol g (x + 1) = (Acol g x / Bcol g x)⁻¹ := by
  intro x
  obtain ⟨h1, h2⟩ := shift g x
  rw [h1, h2, inv_div]




theorem sign_transfer (g : ℝ → ℝ) (c : ℝ) (hB : ∀ x : ℝ, 0 < Bcol g x)
    (hcyc : CyclicAlt4 (fun x : ℝ => Acol g x / Bcol g x - c)) :
    CyclicAlt4 (fun x : ℝ => Acol g x - c * Bcol g x) := by
  obtain ⟨t, hmono, hwin, ε, hε, hpos⟩ := hcyc
  refine ⟨t, hmono, hwin, ε, hε, fun i => ?_⟩
  have hb := hB (t i)
  have hbne : Bcol g (t i) ≠ 0 := hb.ne'
  have hpi : 0 < ε * (-1 : ℝ) ^ (i : ℕ) * (Acol g (t i) / Bcol g (t i) - c) := hpos i
  show 0 < ε * (-1 : ℝ) ^ (i : ℕ) * (Acol g (t i) - c * Bcol g (t i))
  have hkey : ε * (-1 : ℝ) ^ (i : ℕ) * (Acol g (t i) - c * Bcol g (t i))
      = (ε * (-1 : ℝ) ^ (i : ℕ) * (Acol g (t i) / Bcol g (t i) - c)) * Bcol g (t i) := by
    field_simp
  rw [hkey]
  exact mul_pos hpi hb



theorem zeros (g : ℝ → ℝ) (hdec : HasExponentialDecay g)
    (hB : ∀ x : ℝ, 0 < Bcol g x) :
    ∀ x : ℝ, Halt g x = 0 ↔ Acol g x / Bcol g x = 1 := by
  intro x
  rw [split g hdec x, sub_eq_zero, div_eq_one_iff_eq (hB x).ne']



theorem noflat (g : ℝ → ℝ) (hdec : HasExponentialDecay g)
    (hB : ∀ x : ℝ, 0 < Bcol g x)
    (hnf : ∀ u v : ℝ, u < v → ∃ x : ℝ, u < x ∧ x < v ∧ Halt g x ≠ 0) :
    ∀ u v : ℝ, u < v → ∃ x : ℝ, u < x ∧ x < v ∧ Acol g x / Bcol g x ≠ 1 := by
  intro u v huv
  obtain ⟨x, hux, hxv, hHx⟩ := hnf u v huv
  exact ⟨x, hux, hxv, fun h => hHx ((zeros g hdec hB x).mpr h)⟩

end Part12
