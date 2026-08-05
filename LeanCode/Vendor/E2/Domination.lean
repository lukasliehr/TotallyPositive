import LeanCode.Vendor.E2.MatrixDefs

open scoped ENNReal

namespace VendorE2.Lean_Code


def transposeMatrix (A : ℤ → ℤ → ℂ) : ℤ → ℤ → ℂ :=
  fun k l => A l k


def reflectedKernel (a : ℤ → ℝ) : ℤ → ℝ :=
  fun n => a (-n)


def EvenKernel (a : ℤ → ℝ) : Prop :=
  ∀ n : ℤ, a n = a (-n)


def MatrixDominatedBy (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) : Prop :=
  (∀ n : ℤ, 0 ≤ a n) ∧
    Summable (fun n : ℤ => ‖a n‖) ∧
      ∀ k l : ℤ, ‖A k l‖ ≤ a (k - l)


def shiftSeq (n : ℤ) (x : ℤ → ℂ) : ℤ → ℂ :=
  fun k => x (k - n)

lemma memℓp_comp_equiv
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : ℤ ≃ ℤ) (x : ellp p) :
    Memℓp (fun k : ℤ => x (σ k)) p := by
  by_cases hp_top : p = ∞
  · subst p
    apply memℓp_infty
    rcases (lp.memℓp x).bddAbove with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hC ⟨σ k, rfl⟩
  · have hp_ne_zero : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    apply memℓp_gen
    have hs := (lp.memℓp x).summable hp_pos
    simpa [Function.comp_def] using σ.summable_iff.mpr hs

noncomputable def reindexLinearIsometryEquiv
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : ℤ ≃ ℤ) :
    ellp p ≃ₗᵢ[ℂ] ellp p where
  toLinearEquiv :=
    { toFun := fun x => ⟨fun k : ℤ => x (σ k), memℓp_comp_equiv p σ x⟩
      invFun := fun x => ⟨fun k : ℤ => x (σ.symm k), memℓp_comp_equiv p σ.symm x⟩
      left_inv := by
        intro x
        ext k
        simp
      right_inv := by
        intro x
        ext k
        simp
      map_add' := by
        intro x y
        ext k
        simp
      map_smul' := by
        intro c x
        ext k
        simp }
  norm_map' := by
    intro x
    by_cases hp_top : p = ∞
    · subst p
      rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
      exact σ.iSup_congr fun _ => rfl
    · have hp_ne_zero : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
      have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
      rw [lp.norm_eq_tsum_rpow hp_pos, lp.norm_eq_tsum_rpow hp_pos]
      congr 1
      exact σ.tsum_eq (fun k : ℤ => ‖x k‖ ^ p.toReal)


def shiftEquiv (n : ℤ) : ℤ ≃ ℤ where
  toFun k := k - n
  invFun k := k + n
  left_inv k := by simp
  right_inv k := by simp

noncomputable def reindexOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : ℤ ≃ ℤ) :
    ellp p →L[ℂ] ellp p :=
  (reindexLinearIsometryEquiv p σ).toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def shiftOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    ellp p →L[ℂ] ellp p :=
  reindexOperator p (shiftEquiv n)

noncomputable def coordCLM
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : ellp p →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x n
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
    1
    (by
      intro x
      simpa using
        lp.norm_apply_le_norm (p := p) (f := x) (i := n)
          (zero_lt_one.trans_le Fact.out).ne')

noncomputable def diagonalShiftOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) (d : ℤ) : ellp p →L[ℂ] ellp p :=
  (lp.mapCLM p
    (fun k : ℤ => (ContinuousLinearMap.lsmul ℂ ℂ (A k (k - d)) : ℂ →L[ℂ] ℂ))
    (hA.1 d)
    (fun k => by
      have hbound := hA.2.2 k (k - d)
      simpa using hbound)).comp (shiftOperator p d)

lemma diagonalShiftOperator_apply
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) (d : ℤ) (x : ellp p) (n : ℤ) :
    diagonalShiftOperator p A a hA d x n = A n (n - d) * x (n - d) := by
  change A n (n - d) * (shiftOperator p d x) n = A n (n - d) * x (n - d)
  simp [shiftOperator, reindexOperator, reindexLinearIsometryEquiv, shiftEquiv]

lemma diagonalShiftOperator_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) (d : ℤ) :
    ‖diagonalShiftOperator p A a hA d‖ ≤ a d := by
  have hshift_norm : ‖shiftOperator p d‖ ≤ (1 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound (shiftOperator p d) (M := (1 : ℝ)) zero_le_one
    intro x
    simp [shiftOperator, reindexOperator, (reindexLinearIsometryEquiv p (shiftEquiv d)).norm_map x]
  unfold diagonalShiftOperator
  calc
    ‖(lp.mapCLM p
        (fun k : ℤ => (ContinuousLinearMap.lsmul ℂ ℂ (A k (k - d)) : ℂ →L[ℂ] ℂ))
        (hA.1 d)
        (fun k => by
          have hbound := hA.2.2 k (k - d)
          simpa using hbound)).comp (shiftOperator p d)‖
        ≤ ‖lp.mapCLM p
          (fun k : ℤ => (ContinuousLinearMap.lsmul ℂ ℂ (A k (k - d)) : ℂ →L[ℂ] ℂ))
          (hA.1 d)
          (fun k => by
            have hbound := hA.2.2 k (k - d)
            simpa using hbound)‖ * ‖shiftOperator p d‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ a d * ‖shiftOperator p d‖ := by
      exact mul_le_mul_of_nonneg_right
        (lp.norm_mapCLM_le p
          (fun k : ℤ => (ContinuousLinearMap.lsmul ℂ ℂ (A k (k - d)) : ℂ →L[ℂ] ℂ))
          (hA.1 d)
          (fun k => by
            have hbound := hA.2.2 k (k - d)
            simpa using hbound))
        (norm_nonneg _)
    _ ≤ a d * 1 := mul_le_mul_of_nonneg_left hshift_norm (hA.1 d)
    _ = a d := by ring

lemma diagonalShiftOperator_summable
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) :
    Summable (fun d : ℤ => diagonalShiftOperator p A a hA d) := by
  apply Summable.of_norm_bounded hA.2.1
  intro d
  calc
    ‖diagonalShiftOperator p A a hA d‖ ≤ a d :=
      diagonalShiftOperator_norm_le p A a hA d
    _ = ‖a d‖ := (Real.norm_of_nonneg (hA.1 d)).symm

lemma diagonalShiftOperator_summable_norm
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) :
    Summable (fun d : ℤ => ‖diagonalShiftOperator p A a hA d‖) := by
  exact hA.2.1.of_nonneg_of_le (fun d => norm_nonneg _) (fun d => by
    calc
      ‖diagonalShiftOperator p A a hA d‖ ≤ a d :=
        diagonalShiftOperator_norm_le p A a hA d
      _ = ‖a d‖ := (Real.norm_of_nonneg (hA.1 d)).symm)

noncomputable def dominatedMatrixOperatorSeries
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) : ellp p →L[ℂ] ellp p :=
  ∑' d : ℤ, diagonalShiftOperator p A a hA d

lemma dominatedMatrixOperatorSeries_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) :
    ‖dominatedMatrixOperatorSeries p A a hA‖ ≤ ∑' n : ℤ, ‖a n‖ := by
  unfold dominatedMatrixOperatorSeries
  calc
    ‖∑' d : ℤ, diagonalShiftOperator p A a hA d‖ ≤
        ∑' d : ℤ, ‖diagonalShiftOperator p A a hA d‖ :=
      norm_tsum_le_tsum_norm (diagonalShiftOperator_summable_norm p A a hA)
    _ ≤ ∑' d : ℤ, ‖a d‖ := by
      exact Summable.tsum_le_tsum
        (fun d => by
          calc
            ‖diagonalShiftOperator p A a hA d‖ ≤ a d :=
              diagonalShiftOperator_norm_le p A a hA d
            _ = ‖a d‖ := (Real.norm_of_nonneg (hA.1 d)).symm)
        (diagonalShiftOperator_summable_norm p A a hA) hA.2.1

lemma dominatedMatrixOperatorSeries_apply_diagonal_sum
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) (x : ellp p) (n : ℤ) :
    dominatedMatrixOperatorSeries p A a hA x n =
      ∑' d : ℤ, A n (n - d) * x (n - d) := by
  let evalX : (ellp p →L[ℂ] ellp p) →L[ℂ] ellp p :=
    ContinuousLinearMap.apply ℂ (ellp p) x
  have hsum_ops := diagonalShiftOperator_summable p A a hA
  have hsum_x : HasSum (fun d : ℤ => diagonalShiftOperator p A a hA d x)
      (dominatedMatrixOperatorSeries p A a hA x) := by
    simpa [dominatedMatrixOperatorSeries, evalX, Function.comp_def] using
      hsum_ops.hasSum.map evalX evalX.continuous
  have hsum_coord : HasSum
      (fun d : ℤ => (diagonalShiftOperator p A a hA d x) n)
      (dominatedMatrixOperatorSeries p A a hA x n) := by
    simpa [coordCLM, Function.comp_def] using
      hsum_x.map (coordCLM p n) (coordCLM p n).continuous
  rw [← hsum_coord.tsum_eq]
  exact tsum_congr (fun d => diagonalShiftOperator_apply p A a hA d x n)

lemma dominatedMatrixOperatorSeries_isMatrixOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) :
    IsMatrixOperator p A (dominatedMatrixOperatorSeries p A a hA) := by
  intro x n
  have hdiag_summ : Summable (fun d : ℤ => A n (n - d) * x (n - d)) := by
    let evalX : (ellp p →L[ℂ] ellp p) →L[ℂ] ellp p :=
      ContinuousLinearMap.apply ℂ (ellp p) x
    have hsum_ops := diagonalShiftOperator_summable p A a hA
    have hsum_x : HasSum (fun d : ℤ => diagonalShiftOperator p A a hA d x)
        (dominatedMatrixOperatorSeries p A a hA x) := by
      simpa [dominatedMatrixOperatorSeries, evalX, Function.comp_def] using
        hsum_ops.hasSum.map evalX evalX.continuous
    have hsum_coord : Summable
        (fun d : ℤ => (diagonalShiftOperator p A a hA d x) n) :=
      ((hsum_x.map (coordCLM p n) (coordCLM p n).continuous).summable)
    simpa [diagonalShiftOperator_apply p A a hA] using hsum_coord
  have hrow_summ : Summable (fun m : ℤ => A n m * x m) := by
    exact ((Equiv.subLeft n).summable_iff (f := fun m : ℤ => A n m * x m)).mp
      (by simpa [Function.comp_def] using hdiag_summ)
  refine ⟨hrow_summ, ?_⟩
  calc
    dominatedMatrixOperatorSeries p A a hA x n =
        ∑' d : ℤ, A n (n - d) * x (n - d) :=
      dominatedMatrixOperatorSeries_apply_diagonal_sum p A a hA x n
    _ = ∑' m : ℤ, A n m * x m := by
      simpa [Function.comp_def] using
        (Equiv.subLeft n).tsum_eq (fun m : ℤ => A n m * x m)

theorem exists_dominatedMatrixOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) :
    ∃ T : ellp p →L[ℂ] ellp p,
      IsMatrixOperator p A T ∧ ‖T‖ ≤ ∑' n : ℤ, ‖a n‖ := by
  exact ⟨dominatedMatrixOperatorSeries p A a hA,
    dominatedMatrixOperatorSeries_isMatrixOperator p A a hA,
    dominatedMatrixOperatorSeries_norm_le p A a hA⟩

noncomputable def dominatedMatrixOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) :
    ellp p →L[ℂ] ellp p :=
  Classical.choose (exists_dominatedMatrixOperator p A a hA)

theorem dominatedMatrixOperator_isMatrixOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) :
    IsMatrixOperator p A (dominatedMatrixOperator p A a hA) :=
  (Classical.choose_spec (exists_dominatedMatrixOperator p A a hA)).1

theorem dominatedMatrixOperator_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) :
    ‖dominatedMatrixOperator p A a hA‖ ≤ ∑' n : ℤ, ‖a n‖ :=
  (Classical.choose_spec (exists_dominatedMatrixOperator p A a hA)).2


def convolutionMatrix (a : ℤ → ℝ) : ℤ → ℤ → ℂ :=
  fun k l => (a (k - l) : ℂ)

lemma convolutionMatrix_dominated
    (a : ℤ → ℝ)
    (ha_nonneg : ∀ n : ℤ, 0 ≤ a n)
    (ha_sum : Summable (fun n : ℤ => ‖a n‖)) :
    MatrixDominatedBy (convolutionMatrix a) a := by
  refine ⟨ha_nonneg, ha_sum, ?_⟩
  intro k l
  unfold convolutionMatrix
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha_nonneg (k - l))]

noncomputable def convolutionVector
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℤ → ℝ) (x : ellp p) :
    ellp p := by
  classical
  exact
    if h : (∀ n : ℤ, 0 ≤ a n) ∧ Summable (fun n : ℤ => ‖a n‖) then
      dominatedMatrixOperator p (convolutionMatrix a) a
        (convolutionMatrix_dominated a h.1 h.2) x
    else 0

theorem MatrixDominatedBy.transpose_reflect
    {A : ℤ → ℤ → ℂ} {a : ℤ → ℝ} :
    MatrixDominatedBy A a →
      MatrixDominatedBy (transposeMatrix A) (reflectedKernel a) := by
  intro hA
  rcases hA with ⟨ha_nonneg, ha_sum, hA_bound⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ha_nonneg (-n)
  · simpa [reflectedKernel, Function.comp_def] using
      ((Equiv.neg ℤ).summable_iff.mpr ha_sum)
  · intro k l
    have hdiff : l - k = -(k - l) := by ring
    change ‖A l k‖ ≤ a (-(k - l))
    rw [← hdiff]
    exact hA_bound l k

theorem MatrixDominatedBy.transpose_of_even
    {A : ℤ → ℤ → ℂ} {a : ℤ → ℝ} :
    MatrixDominatedBy A a → EvenKernel a →
      MatrixDominatedBy (transposeMatrix A) a := by
  intro hA ha_even
  rcases hA with ⟨ha_nonneg, ha_sum, hA_bound⟩
  refine ⟨ha_nonneg, ha_sum, ?_⟩
  intro k l
  have hdiff : l - k = -(k - l) := by ring
  have ha_eq : a (l - k) = a (k - l) := by
    rw [hdiff]
    exact (ha_even (k - l)).symm
  change ‖A l k‖ ≤ a (k - l)
  rw [← ha_eq]
  exact hA_bound l k

theorem ellp_norm_comp_equiv
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : ℤ ≃ ℤ) (x : ellp p) :
    ‖reindexOperator p σ x‖ = ‖x‖ := by
  simp [reindexOperator, (reindexLinearIsometryEquiv p σ).norm_map x]

theorem ellp_shift_isometry
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) (x : ellp p) :
    ‖shiftOperator p n x‖ = ‖x‖ := by
  exact ellp_norm_comp_equiv p (shiftEquiv n) x

theorem ellp_convolution_bound
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℤ → ℝ) (x : ellp p)
    (ha_nonneg : ∀ n : ℤ, 0 ≤ a n)
    (ha_sum : Summable (fun n : ℤ => ‖a n‖)) :
    ‖convolutionVector p a x‖ ≤ (∑' n : ℤ, ‖a n‖) * ‖x‖ := by
  have h : (∀ n : ℤ, 0 ≤ a n) ∧ Summable (fun n : ℤ => ‖a n‖) :=
    ⟨ha_nonneg, ha_sum⟩
  unfold convolutionVector
  rw [dif_pos h]
  calc
    ‖dominatedMatrixOperator p (convolutionMatrix a) a
        (convolutionMatrix_dominated a h.1 h.2) x‖ ≤
        ‖dominatedMatrixOperator p (convolutionMatrix a) a
          (convolutionMatrix_dominated a h.1 h.2)‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (∑' n : ℤ, ‖a n‖) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right
        (dominatedMatrixOperator_norm_le p (convolutionMatrix a) a
          (convolutionMatrix_dominated a h.1 h.2))
        (norm_nonneg x)

theorem isMatrixOperator_unique
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ)
    (T S : ellp p →L[ℂ] ellp p)
    (hT : IsMatrixOperator p A T) (hS : IsMatrixOperator p A S) :
    T = S := by
  ext x n
  exact (hT x n).2.trans (hS x n).2.symm

theorem isMatrixOperator_sub
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A B : ℤ → ℤ → ℂ)
    (TA TB : ellp p →L[ℂ] ellp p)
    (hTA : IsMatrixOperator p A TA) (hTB : IsMatrixOperator p B TB) :
    IsMatrixOperator p (fun k l : ℤ => B k l - A k l) (TB - TA) := by
  intro x n
  have hB := hTB x n
  have hA := hTA x n
  constructor
  · have hsum_sub : Summable fun m : ℤ => B n m * x m - A n m * x m :=
      hB.1.sub hA.1
    simpa [sub_mul] using hsum_sub
  · change (TB x) n - (TA x) n =
      tsum (fun m : ℤ => (B n m - A n m) * x m)
    rw [hB.2, hA.2]
    rw [← Summable.tsum_sub hB.1 hA.1]
    apply tsum_congr
    intro m
    ring

theorem dominatedMatrixOperator_sub_eq
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A B : ℤ → ℤ → ℂ) (a b c : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) (hB : MatrixDominatedBy B b)
    (hsub : MatrixDominatedBy (fun k l : ℤ => B k l - A k l) c) :
    dominatedMatrixOperator p (fun k l : ℤ => B k l - A k l) c hsub =
      dominatedMatrixOperator p B b hB - dominatedMatrixOperator p A a hA := by
  exact isMatrixOperator_unique p (fun k l : ℤ => B k l - A k l)
    (dominatedMatrixOperator p (fun k l : ℤ => B k l - A k l) c hsub)
    (dominatedMatrixOperator p B b hB - dominatedMatrixOperator p A a hA)
    (dominatedMatrixOperator_isMatrixOperator p
      (fun k l : ℤ => B k l - A k l) c hsub)
    (isMatrixOperator_sub p A B
      (dominatedMatrixOperator p A a hA)
      (dominatedMatrixOperator p B b hB)
      (dominatedMatrixOperator_isMatrixOperator p A a hA)
      (dominatedMatrixOperator_isMatrixOperator p B b hB))

theorem dominatedMatrixOperator_sub_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A B : ℤ → ℤ → ℂ) (a b c : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) (hB : MatrixDominatedBy B b)
    (hsub : MatrixDominatedBy (fun k l : ℤ => B k l - A k l) c) :
    ‖dominatedMatrixOperator p B b hB - dominatedMatrixOperator p A a hA‖ ≤
      tsum (fun n : ℤ => ‖c n‖) := by
  rw [← dominatedMatrixOperator_sub_eq p A B a b c hA hB hsub]
  exact dominatedMatrixOperator_norm_le p (fun k l : ℤ => B k l - A k l) c hsub

end VendorE2.Lean_Code
