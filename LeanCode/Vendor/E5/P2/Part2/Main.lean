import LeanCode.Vendor.E5.P2.Part2.Continuity
import LeanCode.Vendor.E5.P2.Part2.Algebra
import LeanCode.Vendor.E5.Defs

open MeasureTheory











namespace Part2





theorem ofreal_tsum (a : ℤ → ℝ) (_ha : Summable a) :
    ∑' k : ℤ, ((a k : ℝ) : ℂ) = (((∑' k : ℤ, a k) : ℝ) : ℂ) :=
  (Complex.ofReal_tsum a).symm





theorem antiperiodic (f : ℝ → ℝ) (C c : ℝ) (_hC : 0 < C) (_hc : 0 < c)
    (_hb : ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|)) (x : ℝ) :
    Halt f (x + 1) = - Halt f x := by
  simp only [Halt]
  rw [← tsum_neg, ← Equiv.tsum_eq (Equiv.subRight (1 : ℤ))
        (fun k : ℤ => (-1 : ℝ) ^ k * f ((x + 1) + k))]
  refine tsum_congr (fun k => ?_)
  simp only [Equiv.subRight_apply]
  rw [(sign_succ k).2, show ((k - 1 : ℤ) : ℝ) = (k : ℝ) - 1 from by push_cast; ring,
     show (x + 1) + ((k : ℝ) - 1) = x + (k : ℝ) from by ring]
  ring





theorem zak (f : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hb : ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|)) (x : ℝ) :
    Zak f (x, 1 / 2) = ((Halt f x : ℝ) : ℂ) := by
  have hsum := (abs_summable f C c hC hc hb x).2
  simp only [Zak, Halt]

  rw [tsum_congr (fun k : ℤ => coe_bridge k (f (x - (k : ℝ))))]

  rw [← tsum_comp_neg (fun k : ℤ => (((-1 : ℝ) ^ k * f (x - (k : ℝ)) : ℝ) : ℂ))]

  rw [tsum_congr (fun k : ℤ =>
    show ((((-1 : ℝ) ^ (-k) * f (x - ((-k : ℤ) : ℝ))) : ℝ) : ℂ)
        = ((((-1 : ℝ) ^ k * f (x + (k : ℝ))) : ℝ) : ℂ) from by
      rw [sign_neg, show x - ((-k : ℤ) : ℝ) = x + (k : ℝ) from by push_cast; ring])]
  exact ofreal_tsum (fun k : ℤ => (-1 : ℝ) ^ k * f (x + (k : ℝ))) hsum

end Part2




theorem Part_2_main : Statement_Part_2 := by
  intro f hf hdecay
  obtain ⟨C, c, hC, hc, hb⟩ := hdecay
  exact ⟨Part2.cont f C c hC hc hf hb,
    fun x => Part2.antiperiodic f C c hC hc hb x,
    fun x => Part2.zak f C c hC hc hb x⟩
