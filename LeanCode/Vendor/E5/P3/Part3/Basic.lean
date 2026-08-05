import Mathlib
import LeanCode.Vendor.E5.Defs

open MeasureTheory
















namespace Part3



def minorSel {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (r : Fin k → Fin m) (c : Fin k → Fin n) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of (fun i j => A (r i) (c j))


theorem sign_ne_zero {n s : ℕ} (v : Fin n → ℝ) (h : SignChangesGE v s) : v ≠ 0 := by
  obtain ⟨idx, _hmono, ε, _hε, hpos⟩ := h
  intro hv
  have h0 := hpos 0
  rw [hv] at h0
  simp at h0


theorem sign_s0 {n : ℕ} (v : Fin n → ℝ) (h : v ≠ 0) : SignChangesGE v 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  rw [Pi.zero_apply] at hj
  refine ⟨fun _ => j, ?_, (if 0 < v j then (1 : ℝ) else -1), ?_, ?_⟩
  · intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    exact absurd (Fin.lt_def.mp hab) (by omega)
  · by_cases hpos : 0 < v j <;> simp [hpos]
  · intro i
    have hi : (i : ℕ) = 0 := by have := i.isLt; omega
    simp only [hi, pow_zero, mul_one]
    by_cases hpos : 0 < v j
    · simp only [if_pos hpos, one_mul]; exact hpos
    · simp only [if_neg hpos, neg_one_mul]
      exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hpos) hj)


theorem sign_mono {n s s' : ℕ} (v : Fin n → ℝ)
    (h : SignChangesGE v s) (hle : s' ≤ s) : SignChangesGE v s' := by
  obtain ⟨idx, hmono, ε, hε, hpos⟩ := h
  have hle1 : s' + 1 ≤ s + 1 := by omega
  refine ⟨idx ∘ Fin.castLE hle1, hmono.comp (Fin.strictMono_castLE hle1), ε, hε, ?_⟩
  intro i
  simpa using hpos (Fin.castLE hle1 i)

end Part3
