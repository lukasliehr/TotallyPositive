import LeanCode.Vendor.E5.P12.Part12.Ratio
import LeanCode.Vendor.E5.P12.Part12.Existence
import LeanCode.Vendor.E5.Defs
open VendorE5

open MeasureTheory














namespace Part12





theorem uniqueness (g : ℝ → ℝ) (hg : Continuous g) (hdec : HasExponentialDecay g)
    (hA : ∀ x : ℝ, 0 < Acol g x) (hB : ∀ x : ℝ, 0 < Bcol g x)
    (hcyc : ∀ c : ℝ, 0 < c →
      ¬ CyclicAlt4 (fun x : ℝ => Acol g x - c * Bcol g x))
    (hnf : ∀ u v : ℝ, u < v → ∃ x : ℝ, u < x ∧ x < v ∧ Halt g x ≠ 0)
    (h11 : Statement_Part_11) :
    ∀ x y : ℝ, 0 ≤ x → x < 1 → 0 ≤ y → y < 1 →
      Halt g x = 0 → Halt g y = 0 → x = y := by
  intro x y hx0 hx1 hy0 hy1 hHx hHy
  exact h11 (fun x => Acol g x / Bcol g x)
    (ratio_cont g hg hdec hB)
    (ratio_pos g hA hB)
    (ratio_inv g hA hB)
    (fun c hc hcon => hcyc c hc (sign_transfer g c hB hcon))
    (noflat g hdec hB hnf)
    x y
    (Set.mem_Ico.mpr ⟨hx0, hx1⟩)
    (Set.mem_Ico.mpr ⟨hy0, hy1⟩)
    ((zeros g hdec hB x).mp hHx)
    ((zeros g hdec hB y).mp hHy)




theorem bridge (g : ℝ → ℝ) (hg : Continuous g) (hdec : HasExponentialDecay g)
    (h2 : Statement_Part_2) :
    Continuous (Halt g) ∧
    (∀ x : ℝ, Halt g (x + 1) = - Halt g x) ∧
    (∀ x : ℝ, Zak g (x, 1 / 2) = 0 ↔ Halt g x = 0) := by
  obtain ⟨hcont, hanti, hzak⟩ := h2 g hg hdec
  refine ⟨hcont, hanti, fun x => ?_⟩
  rw [hzak x]
  exact Complex.ofReal_eq_zero

end Part12





theorem Part_12_main
    (h1 : Statement_Part_1) (h2 : Statement_Part_2)
    (h7 : Statement_Part_7) (h8 : Statement_Part_8)
    (h9 : Statement_Part_9) (h10 : Statement_Part_10)
    (h11 : Statement_Part_11) : Statement_Part_12 := by
  intro g hg0 htpic

  have hcont : Continuous g := htpic.2.2
  have hint : MeasureTheory.Integrable g := htpic.2.1

  have hdec : HasExponentialDecay g := h1 g htpic
  have hSP := h7 g htpic hg0 hdec
  have hreal := h8 g htpic hg0 hdec hSP
  have hApos : ∀ x : ℝ, 0 < Acol g x := hreal.1
  have hBpos : ∀ x : ℝ, 0 < Bcol g x := hreal.2.1
  have hcyc := h9 g htpic hdec
  have hnf := h10 g hcont hint hdec hreal

  obtain ⟨hHcont, hHanti, hHzak⟩ := Part12.bridge g hcont hdec h2

  obtain ⟨x0, hx0nonneg, hx0lt1, hHx0⟩ := Part12.existence (Halt g) hHcont hHanti
  refine ⟨x0, ⟨Set.mem_Ico.mpr ⟨hx0nonneg, hx0lt1⟩, (hHzak x0).mpr hHx0⟩, ?_⟩

  rintro y ⟨hyIco, hyZak⟩
  obtain ⟨hy0, hy1⟩ := Set.mem_Ico.mp hyIco
  exact Part12.uniqueness g hcont hdec hApos hBpos hcyc hnf h11 y x0 hy0 hy1
    hx0nonneg hx0lt1 ((hHzak y).mp hyZak) hHx0
