import LeanCode.Vendor.E2.Localization
import LeanCode.Vendor.E2.BanachFacts
import LeanCode.Vendor.E2.Duality

open scoped ENNReal

namespace VendorE2.Lean_Code

theorem transpose_lower_bound_of_surjective
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (_hA : MatrixDominatedBy A a)
    (hAt : MatrixDominatedBy (transposeMatrix A) a)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hconj : q = conjugateExponent p)
    (hsurj : MatrixSurjectiveOn p A) :
    MatrixBoundedBelowOn q (transposeMatrix A) := by
  rcases hsurj with ⟨T, hT, hT_surj⟩
  let Tt : ellp q →L[ℂ] ellp q :=
    dominatedMatrixOperator q (transposeMatrix A) a hAt
  have hTt : IsMatrixOperator q (transposeMatrix A) Tt :=
    dominatedMatrixOperator_isMatrixOperator q (transposeMatrix A) a hAt
  rcases surjective_maps_ball_onto_ball p T hT_surj with
    ⟨δ, hδ_pos, hδ_ball⟩
  refine ⟨Tt, hTt, δ, hδ_pos, ?_⟩
  intro z
  have hnorm_le : ‖z‖ ≤ δ⁻¹ * ‖Tt z‖ := by
    rw [ellp_norm_eq_iSup_pairing p q hconj z]
    refine csSup_le ?_ ?_
    · refine ⟨0, ?_⟩
      refine ⟨0, by simp, ?_⟩
      simp [lpPairing]
    · rintro r ⟨x, hx, rfl⟩
      have hδ_norm : ‖(δ : ℂ)‖ = δ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
      have hscaled_norm : ‖(δ : ℂ) • x‖ ≤ δ := by
        calc
          ‖(δ : ℂ) • x‖ = ‖(δ : ℂ)‖ * ‖x‖ := norm_smul _ _
          _ = δ * ‖x‖ := by rw [hδ_norm]
          _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hx hδ_pos.le
          _ = δ := mul_one δ
      rcases hδ_ball ((δ : ℂ) • x) hscaled_norm with ⟨y, hy, hTy⟩
      have hscale_pair_norm :
          ‖lpPairing p q ((δ : ℂ) • x) z‖ =
            δ * ‖lpPairing p q x z‖ := by
        rw [lpPairing_smul_left p q hconj (δ : ℂ) x z, norm_mul, hδ_norm]
      have hpair_eq :
          lpPairing p q ((δ : ℂ) • x) z =
            lpPairing p q y (Tt z) := by
        rw [← hTy]
        exact lpPairing_matrixOperator_eq_transpose p q hconj A T Tt hT hTt y z
      have hδ_pair_le :
          δ * ‖lpPairing p q x z‖ ≤ ‖Tt z‖ := by
        rw [← hscale_pair_norm, hpair_eq]
        calc
          ‖lpPairing p q y (Tt z)‖ ≤ ‖y‖ * ‖Tt z‖ :=
            lpPairing_bound p q hconj y (Tt z)
          _ ≤ 1 * ‖Tt z‖ :=
            mul_le_mul_of_nonneg_right hy (norm_nonneg _)
          _ = ‖Tt z‖ := one_mul _
      calc
        ‖lpPairing p q x z‖ = δ⁻¹ * (δ * ‖lpPairing p q x z‖) := by
          field_simp [hδ_pos.ne']
        _ ≤ δ⁻¹ * ‖Tt z‖ :=
          mul_le_mul_of_nonneg_left hδ_pair_le (inv_nonneg.mpr hδ_pos.le)
  calc
    δ * ‖z‖ ≤ δ * (δ⁻¹ * ‖Tt z‖) :=
      mul_le_mul_of_nonneg_left hnorm_le hδ_pos.le
    _ = ‖Tt z‖ := by
      field_simp [hδ_pos.ne']

theorem closedBall_subset_closure_image_of_transpose_lower_bound
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_finite : p ≠ ∞)
    (hconj : q = conjugateExponent p)
    (T : ellp p →L[ℂ] ellp p) (Tt : ellp q →L[ℂ] ellp q)
    (hpair : ∀ x y, lpPairing p q (T x) y = lpPairing p q x (Tt y))
    (c R : ℝ) (_hc : 0 < c) (hR : 0 < R)
    (hbelow : ∀ y : ellp q, c * ‖y‖ ≤ ‖Tt y‖) :
    Metric.closedBall (0 : ellp p) (c * R) ⊆
      closure (Set.image (fun x => T x) (Metric.closedBall (0 : ellp p) R)) := by
  intro z hz_ball
  have hz_norm : ‖z‖ ≤ c * R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz_ball
  let C : Set (ellp p) :=
    closure (Set.image (fun x => T x) (Metric.closedBall (0 : ellp p) R))
  by_contra hzC
  have hclosed : IsClosed C := by
    dsimp [C]
    exact closure_image_closedBall_zero_isClosed p T R
  have hconvex : Convex ℝ C := by
    dsimp [C]
    exact closure_image_closedBall_zero_convex p T R
  rcases exists_continuousLinearFunctional_separating_point_closed_convex p C z
      hclosed hconvex hzC with
    ⟨f, α, hαz, hαC⟩
  have hzeroC : (0 : ellp p) ∈ C := by
    dsimp [C]
    apply subset_closure
    refine ⟨0, ?_, by simp⟩
    simp [Metric.mem_closedBall, hR.le]
  rcases ellp_dual_isometry_surjective p q hp_finite hconj f with ⟨y, hy_repr⟩
  have hTf_norm_bound : ∀ x : ellp p, ‖x‖ ≤ R → ‖f (T x)‖ ≤ α := by
    intro x hxR
    apply complex_norm_le_of_forall_norm_one_re_mul_le
    intro θ hθ
    have hxθ : ‖θ • x‖ ≤ R := by
      calc
        ‖θ • x‖ = ‖θ‖ * ‖x‖ := norm_smul θ x
        _ = 1 * ‖x‖ := by rw [hθ]
        _ ≤ R := by simpa using hxR
    have hmem_image : T (θ • x) ∈ Set.image (fun x => T x)
        (Metric.closedBall (0 : ellp p) R) := by
      refine ⟨θ • x, ?_, rfl⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxθ
    have hmemC : T (θ • x) ∈ C := by
      dsimp [C]
      exact subset_closure hmem_image
    have hle := hαC (T (θ • x)) hmemC
    have hmap : f (T (θ • x)) = θ * f (T x) := by
      simp
    simpa [hmap] using hle
  have hTt_norm_le : ‖Tt y‖ ≤ α / R := by
    rw [ellp_norm_eq_iSup_pairing p q hconj (Tt y)]
    refine csSup_le ?_ ?_
    · refine ⟨0, ?_⟩
      refine ⟨0, by simp, ?_⟩
      simp [lpPairing]
    · rintro r ⟨x, hx, rfl⟩
      have hscaled_norm : ‖(R : ℂ) • x‖ ≤ R := by
        have hRnorm : ‖(R : ℂ)‖ = R := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
        calc
          ‖(R : ℂ) • x‖ = ‖(R : ℂ)‖ * ‖x‖ := norm_smul _ _
          _ = R * ‖x‖ := by rw [hRnorm]
          _ ≤ R * 1 := mul_le_mul_of_nonneg_left hx hR.le
          _ = R := mul_one R
      have hscaled_bound := hTf_norm_bound ((R : ℂ) • x) hscaled_norm
      have hscaled_pair : f (T ((R : ℂ) • x)) =
          (R : ℂ) * lpPairing p q x (Tt y) := by
        rw [hy_repr (T ((R : ℂ) • x))]
        rw [hpair ((R : ℂ) • x) y]
        rw [lpPairing_smul_left p q hconj]
      have hmul_le : R * ‖lpPairing p q x (Tt y)‖ ≤ α := by
        have hRnorm : ‖(R : ℂ)‖ = R := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
        rw [hscaled_pair, norm_mul, hRnorm] at hscaled_bound
        exact hscaled_bound
      calc
        ‖lpPairing p q x (Tt y)‖ =
            R⁻¹ * (R * ‖lpPairing p q x (Tt y)‖) := by
          field_simp [hR.ne']
        _ ≤ R⁻¹ * α :=
          mul_le_mul_of_nonneg_left hmul_le (inv_nonneg.mpr hR.le)
        _ = α / R := by ring
  have hcy_le : c * ‖y‖ ≤ α / R := (hbelow y).trans hTt_norm_le
  have hRcy_le : R * (c * ‖y‖) ≤ α := by
    have := mul_le_mul_of_nonneg_left hcy_le hR.le
    calc
      R * (c * ‖y‖) ≤ R * (α / R) := this
      _ = α := by field_simp [hR.ne']
  have hfz_norm_le : ‖f z‖ ≤ α := by
    rw [hy_repr z]
    calc
      ‖lpPairing p q z y‖ ≤ ‖z‖ * ‖y‖ := lpPairing_bound p q hconj z y
      _ ≤ (c * R) * ‖y‖ := mul_le_mul_of_nonneg_right hz_norm (norm_nonneg y)
      _ = R * (c * ‖y‖) := by ring
      _ ≤ α := hRcy_le
  have hrez_le : (f z).re ≤ α := (RCLike.re_le_norm (f z)).trans hfz_norm_le
  exact not_lt_of_ge hrez_le hαz

theorem matrixOperator_range_closed_of_transpose_lower_bound
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a)
    (_hAt : MatrixDominatedBy (transposeMatrix A) a)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_finite : p ≠ ∞)
    (hconj : q = conjugateExponent p)
    (hbelow : MatrixBoundedBelowOn q (transposeMatrix A)) :
    IsClosed (Set.range (dominatedMatrixOperator p A a hA)) := by
  let T : ellp p →L[ℂ] ellp p := dominatedMatrixOperator p A a hA
  have hT : IsMatrixOperator p A T :=
    dominatedMatrixOperator_isMatrixOperator p A a hA
  rcases hbelow with ⟨Tt, hTt, c, hc_pos, hbound⟩
  have hsurj : Function.Surjective T :=
    surjective_of_closedBall_subset_closure_image p T c hc_pos
      (fun R hR =>
        closedBall_subset_closure_image_of_transpose_lower_bound p q hp_finite
          hconj T Tt
          (fun x y =>
            lpPairing_matrixOperator_eq_transpose p q hconj A T Tt hT hTt x y)
          c R hc_pos hR hbound)
  have hrange_univ : Set.range T = Set.univ := Set.range_eq_univ.mpr hsurj
  simp [T, hrange_univ]

theorem dense_range_of_transpose_lower_bound
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a)
    (_hAt : MatrixDominatedBy (transposeMatrix A) a)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_finite : p ≠ ∞)
    (hconj : q = conjugateExponent p)
    (hbelow : MatrixBoundedBelowOn q (transposeMatrix A)) :
    Dense (Set.range (dominatedMatrixOperator p A a hA)) := by
  let T : ellp p →L[ℂ] ellp p := dominatedMatrixOperator p A a hA
  have hT : IsMatrixOperator p A T :=
    dominatedMatrixOperator_isMatrixOperator p A a hA
  rcases hbelow with ⟨Tt, hTt, hTt_below⟩
  have hdense_submodule : Dense ((T.range : Set (ellp p))) := by
    apply dense_of_trivial_annihilator p q hp_finite hconj T.range
    intro y hy_ann
    have hTt_y_zero : Tt y = 0 := by
      have hpair_zero : ∀ x : ellp p, lpPairing p q x (Tt y) = 0 := by
        intro x
        have hx_range : T x ∈ T.range := ⟨x, rfl⟩
        have hann := hy_ann (T x) hx_range
        have hpair_eq :=
          lpPairing_matrixOperator_eq_transpose p q hconj A T Tt hT hTt x y
        rw [← hpair_eq]
        exact hann
      have hnorm_le_zero : ‖Tt y‖ ≤ 0 := by
        rw [ellp_norm_eq_iSup_pairing p q hconj (Tt y)]
        refine csSup_le ?_ ?_
        · refine ⟨0, ?_⟩
          refine ⟨0, by simp, ?_⟩
          simp [lpPairing]
        · rintro r ⟨x, _hx, rfl⟩
          simp [hpair_zero x]
      have hnorm_zero : ‖Tt y‖ = 0 :=
        le_antisymm hnorm_le_zero (norm_nonneg _)
      exact norm_eq_zero.mp hnorm_zero
    rcases hTt_below with ⟨c, hc_pos, hbound⟩
    have hle := hbound y
    rw [hTt_y_zero, norm_zero] at hle
    have hnorm_zero : ‖y‖ = 0 := by
      have hnonneg : 0 ≤ ‖y‖ := norm_nonneg _
      nlinarith
    exact norm_eq_zero.mp hnorm_zero
  have hrange_set : (T.range : Set (ellp p)) = Set.range T := by
    ext y
    simp [LinearMap.mem_range]
  rw [← hrange_set]
  exact hdense_submodule

theorem surjective_of_transpose_lower_bound
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a)
    (hAt : MatrixDominatedBy (transposeMatrix A) a)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_finite : p ≠ ∞)
    (hconj : q = conjugateExponent p)
    (hbelow : MatrixBoundedBelowOn q (transposeMatrix A)) :
    MatrixSurjectiveOn p A := by
  let T : ellp p →L[ℂ] ellp p := dominatedMatrixOperator p A a hA
  have hT : IsMatrixOperator p A T :=
    dominatedMatrixOperator_isMatrixOperator p A a hA
  have hdense : Dense (Set.range T) := by
    simpa [T] using
      dense_range_of_transpose_lower_bound A a hA hAt p q hp_finite hconj hbelow
  have hclosed : IsClosed (Set.range T) := by
    simpa [T] using
      matrixOperator_range_closed_of_transpose_lower_bound A a hA hAt p q hp_finite
        hconj hbelow
  have hrange_univ : Set.range T = Set.univ := by
    calc
      Set.range T = closure (Set.range T) := hclosed.closure_eq.symm
      _ = Set.univ := hdense.closure_eq
  refine ⟨T, hT, ?_⟩
  intro y
  have hy : y ∈ Set.range T := by
    rw [hrange_univ]
    trivial
  exact hy

theorem invertible_infinity_of_transpose_invertible_one
    (A : ℤ → ℤ → ℂ) :
    MatrixInvertibleOn (1 : ℝ≥0∞) (transposeMatrix A) →
      MatrixInvertibleOn (∞ : ℝ≥0∞) A := by
  rintro ⟨Tt, hTt, hTt_unit⟩
  exact ⟨preadjointOnEllOne Tt,
    preadjoint_transpose_isMatrixOperator_infinity A Tt hTt,
    preadjointOnEllOne_isUnit Tt hTt_unit⟩

end VendorE2.Lean_Code
