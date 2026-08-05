import LeanCode.Vendor.E5.P3.Part3.ColumnSpace
import LeanCode.Vendor.E5.P3.Part3.Blocks
import LeanCode.Vendor.E5.Defs

open MeasureTheory








namespace Part3







theorem block_matrix_tn {m n K : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonneg A) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (J : Fin (K + 1) → Finset (Fin n))
    (hcross : ∀ ν ν' : Fin (K + 1), ν < ν' → ∀ j ∈ J ν, ∀ j' ∈ J ν', j < j') :
    TotallyNonneg
      (Matrix.of (fun (i : Fin m) (ν : Fin (K + 1)) => ∑ j ∈ J ν, w j * A i j)) := by
  intro k μ η hμ hη
  rw [multilin (fun t => J (η t)) (fun _ j => w j) (fun _ j u => A (μ u) j)
      (Matrix.of (fun i j =>
        (Matrix.of (fun (i : Fin m) (ν : Fin (K + 1)) => ∑ j ∈ J ν, w j * A i j)) (μ i) (η j)))
      (fun _ _ => rfl)]
  apply Finset.sum_nonneg
  intro jt hjt
  rw [Fintype.mem_piFinset] at hjt
  apply mul_nonneg (Finset.prod_nonneg (fun t _ => hw (jt t)))
  have hγ : StrictMono jt := fun t t' htt' =>
    hcross (η t) (η t') (hη htt') (jt t) (hjt t) (jt t') (hjt t')
  exact hA k μ jt hμ hγ

end Part3

open Part3









theorem Part_3_main : Statement_Part_3 := by
  intro m n A hA c s hsc
  by_contra hcon

  have hc0 : c ≠ 0 := by
    intro h
    rw [h, show A.mulVec (0 : Fin n → ℝ) = 0 from by simp] at hsc
    exact sign_ne_zero 0 hsc rfl

  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; exact absurd (sign_s0 c hc0) hcon
    · exact h

  obtain ⟨k, ε, J, hε, hne, hunion, hcross, hsign, hdisj⟩ := blocks c hc0
  have hks : k + 1 ≤ s := by
    have := blocks_bound hs1 c ε hε J hne hcross hsign hcon
    omega

  set B : Matrix (Fin m) (Fin (k + 1)) ℝ :=
    Matrix.of (fun i ν => ∑ j ∈ J ν, |c j| * A i j) with hB
  set a : Fin (k + 1) → ℝ := fun ν => ε * (-1 : ℝ) ^ (ν : ℕ) with hadef
  have mem_supp : ∀ j, j ∈ supp c ↔ c j ≠ 0 := fun j => by simp [supp]

  have hsignid : ∀ (ν : Fin (k + 1)) (j : Fin n), j ∈ J ν →
      c j = ε * (-1 : ℝ) ^ (ν : ℕ) * |c j| := by
    intro ν j hj
    have hs := hsign ν j hj
    have hp : (-1 : ℝ) ^ (ν : ℕ) = 1 ∨ (-1 : ℝ) ^ (ν : ℕ) = -1 := by
      rcases Nat.even_or_odd (ν : ℕ) with he | ho
      · exact Or.inl he.neg_one_pow
      · exact Or.inr ho.neg_one_pow
    have hτ : ε * (-1 : ℝ) ^ (ν : ℕ) = 1 ∨ ε * (-1 : ℝ) ^ (ν : ℕ) = -1 := by
      rcases hε with h | h <;> rcases hp with hp | hp <;> rw [h, hp] <;> norm_num
    rcases hτ with h | h
    · rw [h, one_mul] at hs ⊢; rw [abs_of_pos hs]
    · rw [h] at hs ⊢
      have hneg : c j < 0 := by nlinarith [hs]
      rw [abs_of_neg hneg]; ring

  have hBa : ∀ i, (A.mulVec c) i = (B.mulVec a) i := by
    intro i
    have hI : (A.mulVec c) i = ∑ j ∈ supp c, A i j * c j := by
      rw [show (A.mulVec c) i = ∑ j, A i j * c j from by simp [Matrix.mulVec, dotProduct]]
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro j _ hj
      rw [show c j = 0 from by by_contra hh; exact hj ((mem_supp j).mpr hh), mul_zero]
    have hmv : (B.mulVec a) i
        = ∑ ν : Fin (k + 1), (ε * (-1 : ℝ) ^ (ν : ℕ)) * (∑ j ∈ J ν, |c j| * A i j) := by
      simp only [hB, hadef, Matrix.mulVec, dotProduct, Matrix.of_apply]
      exact Finset.sum_congr rfl (fun ν _ => by ring)
    rw [hmv, hI, ← hunion, Finset.sum_biUnion (fun ν _ ν' _ hne => hdisj ν ν' hne)]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    nth_rewrite 1 [hsignid ν j hj]; ring

  have hBTN : TotallyNonneg B := by
    rw [hB]; exact block_matrix_tn hA (fun j => |c j|) (fun j => abs_nonneg _) J hcross

  apply column_space (by omega : 1 ≤ k + 1) hBTN a
  rw [show B.mulVec a = A.mulVec c from funext (fun i => (hBa i).symm)]
  exact sign_mono _ hsc hks
