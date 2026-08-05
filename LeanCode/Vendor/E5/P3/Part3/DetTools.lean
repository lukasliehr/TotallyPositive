import LeanCode.Vendor.E5.P3.Part3.Fin
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open scoped Matrix













namespace Part3


theorem det_col_sum {q : ℕ} (t : Fin q) {ι : Type*} (S : Finset ι)
    (v : ι → (Fin q → ℝ)) (N : Matrix (Fin q) (Fin q) ℝ) :
    (N.updateCol t (∑ j ∈ S, v j)).det = ∑ j ∈ S, (N.updateCol t (v j)).det := by
  classical
  refine Finset.induction_on S ?_ (fun a s ha ih => ?_)
  · simp only [Finset.sum_empty]
    apply Matrix.det_eq_zero_of_column_eq_zero t
    intro i; simp [Matrix.updateCol_self]
  · rw [Finset.sum_insert ha, Matrix.det_updateCol_add, ih, Finset.sum_insert ha]







theorem multilin {q : ℕ} {ι : Type*} (S : Fin q → Finset ι)
    (w : Fin q → ι → ℝ) (f : Fin q → ι → (Fin q → ℝ))
    (G : Matrix (Fin q) (Fin q) ℝ)
    (hG : ∀ i t, G i t = ∑ j ∈ S t, w t j * f t j i) :
    G.det = ∑ j ∈ Fintype.piFinset S,
      (∏ t, w t (j t)) * (Matrix.of (fun i t => f t (j t) i)).det := by
  classical

  have hGT : Gᵀ = fun t => ∑ j ∈ S t, w t j • f t j := by
    funext t i
    simp only [Matrix.transpose_apply, hG i t, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.det_transpose G, hGT]

  change Matrix.detRowAlternating.toMultilinearMap
      (fun t => ∑ j ∈ S t, w t j • f t j) = _
  rw [Matrix.detRowAlternating.toMultilinearMap.map_sum_finset
        (fun t j => w t j • f t j) S]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Matrix.detRowAlternating.toMultilinearMap.map_smul_univ
        (fun t => w t (r t)) (fun t => f t (r t)), smul_eq_mul]
  congr 1
  rw [show Matrix.detRowAlternating.toMultilinearMap (fun t => f t (r t))
        = (Matrix.of (fun t i => f t (r t) i)).det from rfl,
      show (Matrix.of (fun t i => f t (r t) i) : Matrix (Fin q) (Fin q) ℝ)
        = (Matrix.of (fun i t => f t (r t) i))ᵀ from by
          ext a b; simp [Matrix.transpose_apply, Matrix.of_apply],
      Matrix.det_transpose]


def rowDeleted {r : ℕ} (C : Matrix (Fin (r + 1)) (Fin r) ℝ) (ℓ : Fin (r + 1)) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of (fun i j => C (ℓ.succAbove i) j)


def cofactorCoeff {r : ℕ} (C : Matrix (Fin (r + 1)) (Fin r) ℝ)
    (ℓ : Fin (r + 1)) : ℝ :=
  (-1 : ℝ) ^ (ℓ : ℕ) * (rowDeleted C ℓ).det





theorem cofactor {r : ℕ} (C : Matrix (Fin (r + 1)) (Fin r) ℝ) (t : Fin r) :
    ∑ ℓ, cofactorCoeff C ℓ * C ℓ t = 0 := by
  classical
  set D : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    Matrix.of (fun ℓ j => Fin.cases (C ℓ t) (fun v => C ℓ v) j) with hD
  have hdet0 : D.det = 0 := by
    refine Matrix.det_zero_of_column_eq (i := (0 : Fin (r + 1))) (j := t.succ)
      ((Fin.succ_ne_zero t).symm) ?_
    intro ℓ
    simp only [hD, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
  have hlap : D.det = ∑ ℓ, cofactorCoeff C ℓ * C ℓ t := by
    rw [Matrix.det_succ_column_zero]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    have hsub : D.submatrix ℓ.succAbove Fin.succ = rowDeleted C ℓ := by
      ext u v
      simp only [hD, Matrix.submatrix_apply, Matrix.of_apply, Fin.cases_succ, rowDeleted]
    have h0 : D ℓ 0 = C ℓ t := by
      simp only [hD, Matrix.of_apply, Fin.cases_zero]
    rw [hsub, h0, cofactorCoeff]; ring
  rw [← hlap]; exact hdet0



theorem cofactor_vec {r : ℕ} (C : Matrix (Fin (r + 1)) (Fin r) ℝ) (a : Fin r → ℝ) :
    ∑ ℓ, cofactorCoeff C ℓ * (C.mulVec a) ℓ = 0 := by
  have hmv : ∀ ℓ, (C.mulVec a) ℓ = ∑ t, C ℓ t * a t := by
    intro ℓ; simp [Matrix.mulVec, dotProduct]
  calc ∑ ℓ, cofactorCoeff C ℓ * (C.mulVec a) ℓ
      = ∑ ℓ, ∑ t, cofactorCoeff C ℓ * (C ℓ t * a t) := by
        refine Finset.sum_congr rfl (fun ℓ _ => ?_)
        rw [hmv ℓ, Finset.mul_sum]
    _ = ∑ t, ∑ ℓ, cofactorCoeff C ℓ * (C ℓ t * a t) := Finset.sum_comm
    _ = ∑ t, a t * ∑ ℓ, cofactorCoeff C ℓ * C ℓ t := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ℓ _ => ?_); ring
    _ = 0 := by simp [cofactor C]




private theorem det_inj_rows_zero {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (hvanish : ∀ ρ : Fin q → Fin p, StrictMono ρ →
      (Matrix.of (fun u j => M (ρ u) j)).det = 0)
    (ι : Fin q → Fin p) (hι : Function.Injective ι) :
    (Matrix.of (fun u j => M (ι u) j)).det = 0 := by
  set σ := Tuple.sort ι with hσ
  have hsm : StrictMono (ι ∘ σ) :=
    (Tuple.monotone_sort ι).strictMono_of_injective (hι.comp σ.injective)
  have hmat : (Matrix.of (fun u j => M (ι u) j))
      = (Matrix.of (fun u j => M ((ι ∘ σ) u) j)).submatrix σ.symm id := by
    ext u j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq, Function.comp_apply,
      Equiv.apply_symm_apply]
  rw [hmat, Matrix.det_permute, hvanish (ι ∘ σ) hsm, mul_zero]


private theorem dependency_aux :
    ∀ (n p : ℕ) (M : Matrix (Fin p) (Fin (n + 1)) ℝ),
      (∀ ρ : Fin (n + 1) → Fin p, StrictMono ρ →
        (Matrix.of (fun u j => M (ρ u) j)).det = 0) →
      ∃ x : Fin (n + 1) → ℝ, x ≠ 0 ∧ M.mulVec x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    obtain _ | m := n
    ·
      intro p M hvanish
      refine ⟨fun _ => 1, ?_, ?_⟩
      · intro hx; simpa using congrFun hx 0
      · funext i
        have hMi : M i 0 = 0 := by
          have hsm : StrictMono (fun _ : Fin 1 => i) := by
            intro a b hab
            exact absurd (Fin.lt_def.mp hab) (by have := a.isLt; have := b.isLt; omega)
          have h := hvanish (fun _ => i) hsm
          rwa [Matrix.det_fin_one, Matrix.of_apply] at h
        simp [Matrix.mulVec, dotProduct, hMi]
    ·
      intro p M hvanish
      by_cases hA : ∀ ρ' : Fin (m + 1) → Fin p, StrictMono ρ' →
          (Matrix.of (fun u j => M (ρ' u) (Fin.castSucc j))).det = 0
      ·
        obtain ⟨y, hy0, hMy⟩ := IH m (Nat.lt_succ_self m) p
          (Matrix.of (fun i j => M i (Fin.castSucc j)))
          (fun ρ' hρ' => by simpa [Matrix.of_apply] using hA ρ' hρ')
        refine ⟨Fin.snoc y 0, ?_, ?_⟩
        · intro hx
          apply hy0
          funext t
          have := congrFun hx (Fin.castSucc t)
          rwa [Fin.snoc_castSucc, Pi.zero_apply] at this
        · funext i
          have hMyi : ∑ t, M i (Fin.castSucc t) * y t = 0 := by
            have h2 := congrFun hMy i
            simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using h2
          simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]
          exact hMyi
      ·
        push Not at hA
        obtain ⟨π, hπsm, hd⟩ := hA
        set x : Fin (m + 2) → ℝ := fun t => (-1 : ℝ) ^ (t : ℕ) *
            (Matrix.of (fun u v : Fin (m + 1) => M (π u) (t.succAbove v))).det with hxdef
        have hxval : ∀ t, x t = (-1 : ℝ) ^ (t : ℕ) *
            (Matrix.of (fun u v : Fin (m + 1) => M (π u) (t.succAbove v))).det :=
          fun t => by rw [hxdef]
        refine ⟨x, ?_, ?_⟩
        · intro hx0
          have hlast := congrFun hx0 (Fin.last (m + 1))
          rw [hxval, Pi.zero_apply, Fin.succAbove_last] at hlast
          rcases mul_eq_zero.mp hlast with h1 | h2
          · exact (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)) h1
          · exact hd h2
        · funext i
          rw [Pi.zero_apply]
          have hlap : (M.mulVec x) i
              = (Matrix.of (Fin.cons (M i) (fun u' : Fin (m + 1) => M (π u')))).det := by
            rw [Matrix.det_succ_row_zero]
            simp only [Matrix.mulVec, dotProduct]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            have hrow0 : (Matrix.of (Fin.cons (M i) (fun u' => M (π u')))) 0 j = M i j := by
              simp [Fin.cons_zero]
            have hsub : (Matrix.of (Fin.cons (M i) (fun u' => M (π u')))).submatrix
                Fin.succ j.succAbove
                = Matrix.of (fun u v : Fin (m + 1) => M (π u) (j.succAbove v)) := by
              ext u v; simp [Matrix.submatrix_apply, Matrix.of_apply, Fin.cons_succ]
            rw [hxval j, hrow0, hsub]; ring
          rw [hlap]
          by_cases hi : i ∈ Set.range π
          · obtain ⟨u0, hu0⟩ := hi
            refine Matrix.det_zero_of_row_eq (i := 0) (j := Fin.succ u0)
              ((Fin.succ_ne_zero u0).symm) ?_
            funext j; simp [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, hu0]
          · have hιinj : Function.Injective
                (Fin.cons i π : Fin (m + 2) → Fin p) :=
              Fin.cons_injective_iff.mpr ⟨hi, hπsm.injective⟩
            have hzero := det_inj_rows_zero M hvanish (Fin.cons i π) hιinj
            rw [show (Matrix.of (Fin.cons (M i) (fun u' : Fin (m + 1) => M (π u'))))
                = Matrix.of (fun u j => M ((Fin.cons i π : Fin (m + 2) → Fin p) u) j)
                from by
                  ext u j
                  refine Fin.cases ?_ (fun u' => ?_) u <;>
                    simp [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]]
            exact hzero




theorem dependency {p q : ℕ} (hq : 1 ≤ q) (M : Matrix (Fin p) (Fin q) ℝ)
    (hvanish : ∀ ρ : Fin q → Fin p, StrictMono ρ →
      (Matrix.of (fun u j => M (ρ u) j)).det = 0) :
    ∃ x : Fin q → ℝ, x ≠ 0 ∧ M.mulVec x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  exact dependency_aux n p M hvanish

end Part3
