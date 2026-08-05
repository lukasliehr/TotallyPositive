import LeanCode.Vendor.E5.P3.Part3.DetTools
import LeanCode.Vendor.E5.Defs

open MeasureTheory








namespace Part3


private theorem column_space_aux :
    ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (B : Matrix (Fin m) (Fin r) ℝ), TotallyNonneg B →
      ∀ (a : Fin r → ℝ), ¬ SignChangesGE (B.mulVec a) r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r IH =>
    intro hr m B hB a hsc
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    ·
      interval_cases r
      obtain ⟨idx, hidx, ε, hε, hpos⟩ := hsc
      have hz : ∀ i : Fin m, (B.mulVec a) i = B i 0 * a 0 := fun i => by
        simp [Matrix.mulVec, dotProduct]
      have hBnn : ∀ i : Fin m, 0 ≤ B i 0 := by
        intro i
        have hsm1 : StrictMono (fun _ : Fin 1 => i) := by
          intro a b hab
          exact absurd (Fin.lt_def.mp hab) (by have := a.isLt; have := b.isLt; omega)
        have hsm2 : StrictMono (fun _ : Fin 1 => (0 : Fin 1)) := by
          intro a b hab
          exact absurd (Fin.lt_def.mp hab) (by have := a.isLt; have := b.isLt; omega)
        have h := hB 1 (fun _ => i) (fun _ => 0) hsm1 hsm2
        rwa [Matrix.det_fin_one, Matrix.of_apply] at h
      have h0 := hpos 0
      have h1 := hpos 1
      rw [hz (idx 0)] at h0
      rw [hz (idx 1)] at h1
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at h0 h1
      have hp0 : 0 < ε * a 0 := by nlinarith [h0, hBnn (idx 0)]
      have hp1 : ε * a 0 < 0 := by nlinarith [h1, hBnn (idx 1)]
      linarith
    ·
      obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
      have ht1 : 1 ≤ t := by omega
      obtain ⟨idx, hidx, ε, hε, hpos⟩ := hsc
      set C : Matrix (Fin (t + 2)) (Fin (t + 1)) ℝ :=
        Matrix.of (fun ℓ j => B (idx ℓ) j) with hC
      have hCTN : TotallyNonneg C := by
        rw [hC]; exact reselect hB hidx strictMono_id
      have hw : ∀ ℓ, (C.mulVec a) ℓ = (B.mulVec a) (idx ℓ) := by
        intro ℓ; simp only [hC, Matrix.mulVec, dotProduct, Matrix.of_apply]
      have hwpos : ∀ ℓ : Fin (t + 2), 0 < ε * (-1 : ℝ) ^ (ℓ : ℕ) * (C.mulVec a) ℓ := by
        intro ℓ; rw [hw ℓ]; exact hpos ℓ
      have hdetnn : ∀ ℓ : Fin (t + 2), 0 ≤ (rowDeleted C ℓ).det := by
        intro ℓ
        have := hCTN (t + 1) ℓ.succAbove id (Fin.strictMono_succAbove ℓ) strictMono_id
        simpa [rowDeleted, id_eq] using this
      by_cases hcase : ∃ ℓ0, 0 < (rowDeleted C ℓ0).det
      ·
        obtain ⟨ℓ0, hℓ0⟩ := hcase
        have hterm : ∀ ℓ : Fin (t + 2), 0 ≤ ε * (cofactorCoeff C ℓ * (C.mulVec a) ℓ) := by
          intro ℓ
          have h1 := hdetnn ℓ
          have h2 := hwpos ℓ
          rw [cofactorCoeff]; nlinarith [h1, h2]
        have hpos0 : 0 < ε * (cofactorCoeff C ℓ0 * (C.mulVec a) ℓ0) := by
          have h2 := hwpos ℓ0
          rw [cofactorCoeff]; nlinarith [hℓ0, h2]
        have hsum : 0 < ∑ ℓ, ε * (cofactorCoeff C ℓ * (C.mulVec a) ℓ) :=
          Finset.sum_pos' (fun ℓ _ => hterm ℓ) ⟨ℓ0, Finset.mem_univ ℓ0, hpos0⟩
        rw [← Finset.mul_sum, cofactor_vec C a, mul_zero] at hsum
        exact lt_irrefl 0 hsum
      ·
        push Not at hcase
        have hdet0 : ∀ ℓ : Fin (t + 2), (rowDeleted C ℓ).det = 0 :=
          fun ℓ => le_antisymm (hcase ℓ) (hdetnn ℓ)
        have hvanish : ∀ ρ : Fin (t + 1) → Fin (t + 2), StrictMono ρ →
            (Matrix.of (fun u j => C (ρ u) j)).det = 0 := by
          intro ρ hρ
          obtain ⟨ℓ, hℓ, -⟩ := skip_classify hρ
          have heq : (Matrix.of (fun u j => C (ρ u) j)) = rowDeleted C ℓ := by
            rw [hℓ]; rfl
          rw [heq]; exact hdet0 ℓ
        obtain ⟨x, hx0, hCx⟩ := dependency (by omega : 1 ≤ t + 1) C hvanish
        obtain ⟨j0, hj0⟩ : ∃ j0, x j0 ≠ 0 := by
          by_contra h; push Not at h; exact hx0 (funext h)
        set a' : Fin (t + 1) → ℝ := a - (a j0 / x j0) • x with ha'
        have hCa' : C.mulVec a' = C.mulVec a := by
          rw [ha', Matrix.mulVec_sub, Matrix.mulVec_smul, hCx, smul_zero, sub_zero]
        have ha'j0 : a' j0 = 0 := by
          have hx : a j0 / x j0 * x j0 = a j0 := by field_simp
          simp only [ha', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hx, sub_self]
        have hC''b : (Matrix.of (fun i s => C i (j0.succAbove s))).mulVec
            (fun s => a' (j0.succAbove s)) = C.mulVec a := by
          rw [← hCa']
          funext i
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
          rw [Fin.sum_univ_succAbove (fun j => C i j * a' j) j0, ha'j0, mul_zero, zero_add]
        have hC''TN : TotallyNonneg (Matrix.of (fun i s => C i (j0.succAbove s))) :=
          colselect hCTN (Fin.strictMono_succAbove j0)
        have hwsc : SignChangesGE (C.mulVec a) (t + 1) :=
          ⟨id, strictMono_id, ε, hε, fun ℓ => by simpa using hwpos ℓ⟩
        have hbsc : SignChangesGE ((Matrix.of (fun i s => C i (j0.succAbove s))).mulVec
            (fun s => a' (j0.succAbove s))) t := by
          rw [hC''b]; exact sign_mono _ hwsc (by omega)
        exact IH t (by omega) ht1 (t + 2)
          (Matrix.of (fun i s => C i (j0.succAbove s))) hC''TN
          (fun s => a' (j0.succAbove s)) hbsc



theorem column_space {r m : ℕ} (hr : 1 ≤ r) {B : Matrix (Fin m) (Fin r) ℝ}
    (hB : TotallyNonneg B) (a : Fin r → ℝ) : ¬ SignChangesGE (B.mulVec a) r :=
  column_space_aux r hr m B hB a

end Part3
