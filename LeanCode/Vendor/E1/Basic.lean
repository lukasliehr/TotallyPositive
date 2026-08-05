import LeanCode.Vendor.E1.Defs

noncomputable section

namespace ExpDecay

theorem isTotallyPositive_nonneg {g : ℝ → ℝ}
    (hg : IsTotallyPositive g) (t : ℝ) :
    0 ≤ g t := by
  have hdet := hg 1 (fun _ : Fin 1 => t) (fun _ : Fin 1 => 0)
    (by intro i j hij; fin_cases i; fin_cases j; simp at hij)
    (by intro i j hij; fin_cases i; fin_cases j; simp at hij)
  simpa [IsTotallyPositive_n, Matrix.det_fin_one] using hdet

theorem isTotallyPositive_fourPoint {g : ℝ → ℝ}
    (hg : IsTotallyPositive g) (x h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    g (x + h) * g (x + k) ≥ g x * g (x + h + k) := by
  let a : Fin 2 → ℝ := fun i => if i = 0 then x + h else x + h + k
  let b : Fin 2 → ℝ := fun i => if i = 0 then 0 else h
  have ha : StrictMono a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [a] at hij ⊢
    linarith
  have hb : StrictMono b := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [b] at hij ⊢
    linarith
  have hdet := hg 2 a b ha hb
  simp [Matrix.det_fin_two, a, b] at hdet
  have hx : x + h + k - h = x + k := by ring
  simpa [hx] using hdet

theorem positivitySet_convex {g : ℝ → ℝ}
    (hg : IsTotallyPositive g) {a b c : ℝ}
    (ha : a ∈ positivitySet g) (hc : c ∈ positivitySet g)
    (hab : a < b) (hbc : b < c) :
    b ∈ positivitySet g := by
  dsimp [positivitySet] at ha hc ⊢
  have hh : 0 < b - a := sub_pos.mpr hab
  have hk : 0 < c - b := sub_pos.mpr hbc
  have hineq := isTotallyPositive_fourPoint hg a (b - a) (c - b) hh hk
  have hineq' : g b * g (a + c - b) ≥ g a * g c := by
    convert hineq using 2 <;> ring_nf
  have hprod_pos : 0 < g b * g (a + c - b) :=
    lt_of_lt_of_le (mul_pos ha hc) hineq'
  have hb_nonneg : 0 ≤ g b := isTotallyPositive_nonneg hg b
  by_contra hb_not_pos
  have hb_le_zero : g b ≤ 0 := le_of_not_gt hb_not_pos
  have hb_zero : g b = 0 := le_antisymm hb_le_zero hb_nonneg
  simp [hb_zero] at hprod_pos

theorem positivitySet_rightHalfLine {g : ℝ → ℝ}
    (hg : IsTotallyPositive g)
    (hunbounded : ∀ B : ℝ, ∃ p ∈ positivitySet g, B < p)
    {u x : ℝ} (hu : u ∈ positivitySet g) (hux : u < x) :
    x ∈ positivitySet g := by
  rcases hunbounded x with ⟨w, hw, hxw⟩
  exact positivitySet_convex hg hu hw hux hxw

end ExpDecay
