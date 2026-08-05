import LeanCode.Vendor.E6.LinftySurjectivity

noncomputable section

namespace E6

theorem schur_bounds_of_polynomialOffDiagonalDecay (A : ℤ → ℤ → ℂ)
    (hdecay : HasPolynomialOffDiagonalDecay A) :
    (∀ k : ℤ, Summable fun l : ℤ => ‖A k l‖) ∧
      (∀ l : ℤ, Summable fun k : ℤ => ‖A k l‖) := by
  rcases hdecay with ⟨C, n, _hCpos, hn, hbound⟩
  constructor
  · intro k
    have hinj : Function.Injective fun l : ℤ => k - l := by
      intro a b h
      linarith
    have hbase := summable_int_one_add_abs_pow_inv n hn
    have hshift :
        Summable fun l : ℤ =>
          (1 : ℝ) / ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ n :=
      hbase.comp_injective hinj
    have hupper :
        Summable fun l : ℤ => C / ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ n := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hshift.mul_left C
    refine Summable.of_nonneg_of_le (fun l => norm_nonneg (A k l)) ?_ hupper
    intro l
    exact hbound k l
  · intro l
    have hinj : Function.Injective fun k : ℤ => k - l := by
      intro a b h
      linarith
    have hbase := summable_int_one_add_abs_pow_inv n hn
    have hshift :
        Summable fun k : ℤ =>
          (1 : ℝ) / ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ n :=
      hbase.comp_injective hinj
    have hupper :
        Summable fun k : ℤ => C / ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ n := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hshift.mul_left C
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg (A k l)) ?_ hupper
    intro k
    exact hbound k l

theorem matrixOperator_realization_l1_linf_of_decay (A : ℤ → ℤ → ℂ)
    (hdecay : HasPolynomialOffDiagonalDecay A) :
    IsMatrixOperator A SequenceSpace.one ∧
      IsMatrixOperator A SequenceSpace.infinity := by
  rcases hdecay with ⟨C, n, hCpos, hn, hbound⟩
  have hdecay' : HasPolynomialOffDiagonalDecay A := ⟨C, n, hCpos, hn, hbound⟩
  have hschur := schur_bounds_of_polynomialOffDiagonalDecay A hdecay'
  have hentry_bound : ∀ k l : ℤ, ‖A k l‖ ≤ C := by
    intro k l
    have hbase : (1 : ℝ) ≤ (1 : ℝ) + ‖(k - l : ℤ)‖ := by
      have hnorm := norm_nonneg (k - l : ℤ)
      linarith
    have hden_ge_one :
        (1 : ℝ) ≤ ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ n :=
      one_le_pow₀ hbase
    have hden_pos :
        0 < ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ n := by
      positivity
    have hfrac_le :
        C / ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ n ≤ C := by
      rw [div_le_iff₀ hden_pos]
      nlinarith [mul_le_mul_of_nonneg_left hden_ge_one hCpos.le]
    exact (hbound k l).trans hfrac_le
  constructor
  · intro x hx k
    have hxsum : Summable fun l : ℤ => ‖x l‖ := by
      simpa [InComplexSequenceSpace, IsSummableSequence] using hx
    refine Summable.of_norm_bounded (hxsum.mul_left C) ?_
    intro l
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hentry_bound k l) (norm_nonneg (x l))
  · intro x hx k
    rcases (by simpa [InComplexSequenceSpace, IsBoundedSequence] using hx) with ⟨M, hM⟩
    refine Summable.of_norm_bounded ((hschur.1 k).mul_left M) ?_
    intro l
    rw [norm_mul]
    calc
      ‖A k l‖ * ‖x l‖ ≤ ‖A k l‖ * M :=
        mul_le_mul_of_nonneg_left (hM l) (norm_nonneg (A k l))
      _ = M * ‖A k l‖ := by ring

theorem realSequenceSurjectivity_complexifies (A : ℤ → ℤ → ℝ)
    (hdecay : HasPolynomialOffDiagonalDecay A)
    (hsurj : ∀ x : ℤ → ℝ, IsBoundedSequence x →
      ∃ y : ℤ → ℝ, IsBoundedSequence y ∧ MatVec A y = x) :
    MatrixSurjectiveOn (ComplexifyMatrix A) SequenceSpace.infinity := by
  rcases hdecay with ⟨C, n, hC, hn, hbound⟩
  have hdecayC : HasPolynomialOffDiagonalDecay (ComplexifyMatrix A) := by
    refine ⟨C, n, hC, hn, ?_⟩
    intro k l
    simpa [ComplexifyMatrix] using hbound k l
  have hoper :=
    (matrixOperator_realization_l1_linf_of_decay (ComplexifyMatrix A) hdecayC).2
  intro v hv
  have hv_re : IsBoundedSequence fun k : ℤ => (v k).re := by
    rcases hv with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro k
    exact (by
      simpa [Real.norm_eq_abs] using (Complex.abs_re_le_norm (v k)).trans (hM k))
  have hv_im : IsBoundedSequence fun k : ℤ => (v k).im := by
    rcases hv with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro k
    exact (by
      simpa [Real.norm_eq_abs] using (Complex.abs_im_le_norm (v k)).trans (hM k))
  rcases hsurj (fun k : ℤ => (v k).re) hv_re with ⟨yr, hyr_bdd, hyr_eq⟩
  rcases hsurj (fun k : ℤ => (v k).im) hv_im with ⟨yi, hyi_bdd, hyi_eq⟩
  let y : ℤ → ℂ := fun k => (yr k : ℂ) + Complex.I * (yi k : ℂ)
  have hy_bdd : IsBoundedSequence y := by
    rcases hyr_bdd with ⟨MR, hMR⟩
    rcases hyi_bdd with ⟨MI, hMI⟩
    refine ⟨MR + MI, ?_⟩
    intro k
    calc
      ‖y k‖ ≤ ‖(yr k : ℂ)‖ + ‖Complex.I * (yi k : ℂ)‖ := by
        dsimp [y]
        exact norm_add_le _ _
      _ = ‖yr k‖ + ‖yi k‖ := by simp
      _ ≤ MR + MI := add_le_add (hMR k) (hMI k)
  refine ⟨y, hy_bdd, ?_⟩
  funext k
  apply Complex.ext
  · have hsum := hoper y hy_bdd k
    calc
      (CMatVec (ComplexifyMatrix A) y k).re =
          ∑' l : ℤ, (ComplexifyMatrix A k l * y l).re := by
        simpa [CMatVec] using (Complex.reCLM.map_tsum hsum)
      _ = ∑' l : ℤ, A k l * yr l := by
        apply tsum_congr
        intro l
        simp [ComplexifyMatrix, y]
      _ = (v k).re := by
        simpa [MatVec] using congrFun hyr_eq k
  · have hsum := hoper y hy_bdd k
    calc
      (CMatVec (ComplexifyMatrix A) y k).im =
          ∑' l : ℤ, (ComplexifyMatrix A k l * y l).im := by
        simpa [CMatVec] using (Complex.imCLM.map_tsum hsum)
      _ = ∑' l : ℤ, A k l * yi l := by
        apply tsum_congr
        intro l
        simp [ComplexifyMatrix, y]
      _ = (v k).im := by
        simpa [MatVec] using congrFun hyi_eq k

theorem real_l1_preimage_of_complex_l1_surjective (A : ℤ → ℤ → ℝ)
    (hdecay : HasPolynomialOffDiagonalDecay A)
    (hsurj : MatrixSurjectiveOn (ComplexifyMatrix A) SequenceSpace.one) :
    ∀ v : ℤ → ℝ, IsSummableSequence v →
      ∃ y : ℤ → ℝ, IsSummableSequence y ∧ MatVec A y = v := by
  rcases hdecay with ⟨C, n, hC, hn, hbound⟩
  have hdecayC : HasPolynomialOffDiagonalDecay (ComplexifyMatrix A) := by
    refine ⟨C, n, hC, hn, ?_⟩
    intro k l
    simpa [ComplexifyMatrix] using hbound k l
  have hoper :=
    (matrixOperator_realization_l1_linf_of_decay (ComplexifyMatrix A) hdecayC).1
  intro v hv
  have hvC : InComplexSequenceSpace SequenceSpace.one (fun k : ℤ => (v k : ℂ)) := by
    simpa [InComplexSequenceSpace, IsSummableSequence] using hv
  rcases hsurj (fun k : ℤ => (v k : ℂ)) hvC with ⟨yc, hyc_space, hyc_eq⟩
  have hyc_sum : Summable fun k : ℤ => ‖yc k‖ := by
    simpa [InComplexSequenceSpace, IsSummableSequence] using hyc_space
  let y : ℤ → ℝ := fun k => (yc k).re
  have hy_sum : IsSummableSequence y := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg (y k)) ?_ hyc_sum
    intro k
    dsimp [y]
    simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (yc k)
  refine ⟨y, hy_sum, ?_⟩
  funext k
  have hsum := hoper yc hyc_space k
  have hre :
      (CMatVec (ComplexifyMatrix A) yc k).re =
        ∑' l : ℤ, A k l * (yc l).re := by
    calc
      (CMatVec (ComplexifyMatrix A) yc k).re =
          ∑' l : ℤ, (ComplexifyMatrix A k l * yc l).re := by
        simpa [CMatVec] using (Complex.reCLM.map_tsum hsum)
      _ = ∑' l : ℤ, A k l * (yc l).re := by
        apply tsum_congr
        intro l
        simp [ComplexifyMatrix]
  calc
    MatVec A y k = ∑' l : ℤ, A k l * (yc l).re := by rfl
    _ = (CMatVec (ComplexifyMatrix A) yc k).re := hre.symm
    _ = ((v k : ℂ)).re := by rw [congrFun hyc_eq k]
    _ = v k := by simp

end E6
