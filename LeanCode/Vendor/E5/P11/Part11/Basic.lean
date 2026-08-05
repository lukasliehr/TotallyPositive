import Mathlib
import LeanCode.Vendor.E5.Defs

















theorem witness (F : ℝ → ℝ) (t₀ t₁ t₂ t₃ : ℝ)
    (h01 : t₀ < t₁) (h12 : t₁ < t₂) (h23 : t₂ < t₃) (hwin : t₃ < t₀ + 2)
    (s0 : 0 < F t₀) (s1 : F t₁ < 0) (s2 : 0 < F t₂) (s3 : F t₃ < 0) :
    CyclicAlt4 F := by
  refine ⟨![t₀, t₁, t₂, t₃], ?_, ?_, 1, Or.inl rfl, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · simpa using h01
    · simpa using h12
    · simpa using h23
  · simpa using hwin
  · intro i
    fin_cases i <;> simp <;> linarith
