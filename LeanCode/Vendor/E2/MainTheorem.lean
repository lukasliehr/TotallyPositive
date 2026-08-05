import LeanCode.Vendor.E2.Decay
import LeanCode.Vendor.E2.Surjective

open scoped ENNReal

namespace VendorE2.Lean_Code

theorem matrixSurjectiveOn_of_matrixInvertibleOn
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) :
    MatrixInvertibleOn p A → MatrixSurjectiveOn p A := by
  rintro ⟨T, hT, hT_unit⟩
  exact ⟨T, hT, (ContinuousLinearMap.isUnit_iff_bijective.mp hT_unit).2⟩

theorem matrixBoundedBelowOn_of_matrixInvertibleOn
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) :
    MatrixInvertibleOn p A → MatrixBoundedBelowOn p A := by
  rintro ⟨T, hT, hT_unit⟩
  rcases isUnit_iff_exists.mp hT_unit with ⟨R, _hTR, hRT⟩
  let C : ℝ := max ‖R‖ 1
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨T, hT, C⁻¹, inv_pos.mpr hC_pos, ?_⟩
  intro x
  have hRx : R (T x) = x := by
    have happ := congrArg (fun S : ellp p →L[ℂ] ellp p => S x) hRT
    simpa using happ
  have hx_le : ‖x‖ ≤ C * ‖T x‖ := by
    calc
      ‖x‖ = ‖R (T x)‖ := by rw [hRx]
      _ ≤ ‖R‖ * ‖T x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖T x‖ := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  calc
    C⁻¹ * ‖x‖ ≤ C⁻¹ * (C * ‖T x‖) := by
      exact mul_le_mul_of_nonneg_left hx_le (inv_nonneg.mpr hC_pos.le)
    _ = ‖T x‖ := by
      field_simp [hC_pos.ne']

theorem matrixInvertibleOn_of_matrixSurjectiveOn_of_matrixBoundedBelowOn
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ)
    (hsurj : MatrixSurjectiveOn p A) (hbelow : MatrixBoundedBelowOn p A) :
    MatrixInvertibleOn p A := by
  rcases hsurj with ⟨T, hT, hT_surj⟩
  rcases hbelow with ⟨S, hS, hS_below⟩
  have hTS : T = S := isMatrixOperator_unique p A T S hT hS
  have hT_below : OperatorBoundedBelow T := by
    simpa [hTS] using hS_below
  have hT_inj : Function.Injective T :=
    boundedBelow_injective p T hT_below
  exact ⟨T, hT,
    continuousLinearMap_isUnit_of_bijective p T ⟨hT_inj, hT_surj⟩⟩

lemma one_le_conjugateExponent
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    1 ≤ conjugateExponent p := by
  haveI hpq : ENNReal.HolderConjugate p (conjugateExponent p) := by
    dsimp [conjugateExponent]
    infer_instance
  exact ENNReal.HolderConjugate.one_le (conjugateExponent p) p

theorem matrixInvertibleOn_finite_of_lower_bounds
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hdomA : MatrixDominatedBy A a)
    (hdomAt : MatrixDominatedBy (transposeMatrix A) a)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq_ne_top : q ≠ ∞)
    [Fact (1 ≤ conjugateExponent q)]
    (hbelowA : MatrixBoundedBelowOn q A)
    (hbelowAt : MatrixBoundedBelowOn (conjugateExponent q) (transposeMatrix A)) :
    MatrixInvertibleOn q A := by
  have hsurj : MatrixSurjectiveOn q A :=
    surjective_of_transpose_lower_bound A a hdomA hdomAt
      q (conjugateExponent q) hq_ne_top rfl hbelowAt
  exact matrixInvertibleOn_of_matrixSurjectiveOn_of_matrixBoundedBelowOn
    q A hsurj hbelowA

theorem matrixInvertibleOn_top_of_lower_bounds
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hdomA : MatrixDominatedBy A a)
    (hdomAt : MatrixDominatedBy (transposeMatrix A) a)
    (hbelowA_all :
      ∀ p : ℝ≥0∞, [Fact (1 ≤ p)] → MatrixBoundedBelowOn p A)
    (hbelowAt_all :
      ∀ p : ℝ≥0∞, [Fact (1 ≤ p)] →
        MatrixBoundedBelowOn p (transposeMatrix A)) :
    MatrixInvertibleOn (∞ : ℝ≥0∞) A := by
  have hdouble : transposeMatrix (transposeMatrix A) = A := by
    funext k l
    rfl
  have hdomAtt : MatrixDominatedBy (transposeMatrix (transposeMatrix A)) a := by
    simpa [hdouble] using hdomA
  have hAtt_below_top :
      MatrixBoundedBelowOn (∞ : ℝ≥0∞)
        (transposeMatrix (transposeMatrix A)) := by
    simpa [hdouble] using hbelowA_all (∞ : ℝ≥0∞)
  have hAt_surj_one : MatrixSurjectiveOn (1 : ℝ≥0∞) (transposeMatrix A) :=
    surjective_of_transpose_lower_bound (transposeMatrix A) a hdomAt hdomAtt
      (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (by simp)
      conjugateExponent_one_eq_top hAtt_below_top
  have hAt_below_one : MatrixBoundedBelowOn (1 : ℝ≥0∞) (transposeMatrix A) :=
    hbelowAt_all (1 : ℝ≥0∞)
  have hAt_inv_one : MatrixInvertibleOn (1 : ℝ≥0∞) (transposeMatrix A) :=
    matrixInvertibleOn_of_matrixSurjectiveOn_of_matrixBoundedBelowOn
      (1 : ℝ≥0∞) (transposeMatrix A) hAt_surj_one hAt_below_one
  exact invertible_infinity_of_transpose_invertible_one A hAt_inv_one


theorem SpectralInvariance
    (A : ℤ → ℤ → ℂ)
    (hA : HasPolynomialOffDiagonalDecay A)
    (p₀ : ℝ≥0∞) [Fact (1 ≤ p₀)]
    (h_inv : MatrixInvertibleOn p₀ A) :
    ∀ q : ℝ≥0∞, [Fact (1 ≤ q)] → MatrixInvertibleOn q A := by
  rcases polynomialDecay_to_even_ellOne_domination A hA with
    ⟨a, _ha_even, hdomA, hdomAt⟩
  have hsurj_p₀ : MatrixSurjectiveOn p₀ A :=
    matrixSurjectiveOn_of_matrixInvertibleOn p₀ A h_inv
  have hbelow_p₀ : MatrixBoundedBelowOn p₀ A :=
    matrixBoundedBelowOn_of_matrixInvertibleOn p₀ A h_inv
  have hbelowA_all :
      ∀ p : ℝ≥0∞, [Fact (1 ≤ p)] → MatrixBoundedBelowOn p A :=
    propagate_lower_bound A a hdomA p₀ hbelow_p₀
  let p₀' : ℝ≥0∞ := conjugateExponent p₀
  letI : Fact (1 ≤ p₀') := ⟨one_le_conjugateExponent p₀⟩
  have hAt_below_p₀' : MatrixBoundedBelowOn p₀' (transposeMatrix A) :=
    transpose_lower_bound_of_surjective A a hdomA hdomAt
      p₀ p₀' rfl hsurj_p₀
  have hbelowAt_all :
      ∀ p : ℝ≥0∞, [Fact (1 ≤ p)] →
        MatrixBoundedBelowOn p (transposeMatrix A) :=
    propagate_lower_bound (transposeMatrix A) a hdomAt p₀' hAt_below_p₀'
  intro q hq
  letI : Fact (1 ≤ q) := hq
  by_cases hq_top : q = ∞
  · subst q
    exact matrixInvertibleOn_top_of_lower_bounds
      A a hdomA hdomAt hbelowA_all hbelowAt_all
  · letI : Fact (1 ≤ conjugateExponent q) :=
      ⟨one_le_conjugateExponent q⟩
    exact matrixInvertibleOn_finite_of_lower_bounds
      A a hdomA hdomAt q hq_top
      (hbelowA_all q) (hbelowAt_all (conjugateExponent q))

end VendorE2.Lean_Code
