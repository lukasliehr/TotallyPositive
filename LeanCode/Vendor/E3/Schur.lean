import LeanCode.Vendor.E3.Summability

open scoped ENNReal

namespace VendorE3
noncomputable section








structure SchurBounds (A : ℤ → ℤ → ℂ) (R S : ℝ) : Prop where
  R_nonneg : 0 ≤ R
  S_nonneg : 0 ≤ S
  row_summable : ∀ j : ℤ, Summable (fun k : ℤ => ‖A j k‖)
  row_bound : ∀ j : ℤ, (∑' k : ℤ, ‖A j k‖) ≤ R
  col_summable : ∀ k : ℤ, Summable (fun j : ℤ => ‖A j k‖)
  col_bound : ∀ k : ℤ, (∑' j : ℤ, ‖A j k‖) ≤ S



theorem schur_row_pairing_summable
    {A : ℤ → ℤ → ℂ} {R S : ℝ} (hA : SchurBounds A R S)
    (c : ellp (2 : ℝ≥0∞)) (j : ℤ) :
    Summable (fun k : ℤ => A j k * c k) ∧
      (∑' k : ℤ, ‖A j k * c k‖) ≤ R * ‖c‖ := by
  have hrow : Summable (fun k : ℤ => ‖A j k‖) := hA.row_summable j
  have hmajor : Summable (fun k : ℤ => ‖A j k‖ * ‖c‖) :=
    hrow.mul_right ‖c‖
  have hle : ∀ k : ℤ, ‖A j k * c k‖ ≤ ‖A j k‖ * ‖c‖ := by
    intro k
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (lp_norm_apply_le_norm_int c k) (norm_nonneg _)
  have hnormsummable : Summable (fun k : ℤ => ‖A j k * c k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hmajor
  constructor
  · exact Summable.of_norm hnormsummable
  · calc
      (∑' k : ℤ, ‖A j k * c k‖) ≤ ∑' k : ℤ, ‖A j k‖ * ‖c‖ := by
        exact Summable.tsum_le_tsum hle hnormsummable hmajor
      _ = (∑' k : ℤ, ‖A j k‖) * ‖c‖ := by
        exact hrow.tsum_mul_right ‖c‖
      _ ≤ R * ‖c‖ := by
        exact mul_le_mul_of_nonneg_right (hA.row_bound j) (norm_nonneg c)


theorem schur_square_sum_bound
    {A : ℤ → ℤ → ℂ} {R S : ℝ} (hA : SchurBounds A R S)
    (c : ellp (2 : ℝ≥0∞)) :
    Summable (fun j : ℤ => ‖∑' k : ℤ, A j k * c k‖ ^ 2) ∧
      (∑' j : ℤ, ‖∑' k : ℤ, A j k * c k‖ ^ 2) ≤ R * S * ‖c‖ ^ 2 := by
  let f : ℤ → ℝ := fun j => ‖∑' k : ℤ, A j k * c k‖ ^ 2
  have hf_nonneg : 0 ≤ f := by
    intro j
    exact sq_nonneg _
  have hc_sq_summable : Summable (fun k : ℤ => ‖c k‖ ^ 2) := by
    simpa using (lp.memℓp c).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hc_tsum_sq : (∑' k : ℤ, ‖c k‖ ^ 2) = ‖c‖ ^ 2 := by
    have hnorm :
        ‖c‖ ^ 2 = ∑' k : ℤ, ‖c k‖ ^ 2 := by
      simpa using
        (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ)
          (by norm_num) c)
    exact hnorm.symm
  have hfinite :
      ∀ s : Finset ℤ, ∑ j ∈ s, f j ≤ R * S * ‖c‖ ^ 2 := by
    intro s
    have hw_summable :
        ∀ j ∈ s, Summable (fun k : ℤ => ‖A j k‖ * ‖c k‖ ^ 2) := by
      intro j _hj
      have hmajor : Summable (fun k : ℤ => ‖A j k‖ * ‖c‖ ^ 2) :=
        (hA.row_summable j).mul_right (‖c‖ ^ 2)
      refine Summable.of_nonneg_of_le
        (fun k => mul_nonneg (norm_nonneg _) (sq_nonneg _)) ?_ hmajor
      intro k
      have hc_le : ‖c k‖ ≤ ‖c‖ := lp_norm_apply_le_norm_int c k
      have hc_sq_le : ‖c k‖ ^ 2 ≤ ‖c‖ ^ 2 := by
        nlinarith [norm_nonneg (c k), norm_nonneg c]
      exact mul_le_mul_of_nonneg_left hc_sq_le (norm_nonneg _)
    have hcolumn_point :
        ∀ k : ℤ,
          (∑ j ∈ s, ‖A j k‖ * ‖c k‖ ^ 2) ≤ S * ‖c k‖ ^ 2 := by
      intro k
      have hcol_fin : (∑ j ∈ s, ‖A j k‖) ≤ S := by
        calc
          (∑ j ∈ s, ‖A j k‖)
              ≤ ∑' j : ℤ, ‖A j k‖ :=
                (hA.col_summable k).sum_le_tsum s
                  (fun _j _hj => norm_nonneg _)
          _ ≤ S := hA.col_bound k
      calc
        (∑ j ∈ s, ‖A j k‖ * ‖c k‖ ^ 2)
            = (∑ j ∈ s, ‖A j k‖) * ‖c k‖ ^ 2 := by
              rw [Finset.sum_mul]
        _ ≤ S * ‖c k‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hcol_fin (sq_nonneg _)
    have hcolumn_major :
        Summable (fun k : ℤ => S * ‖c k‖ ^ 2) :=
      hc_sq_summable.mul_left S
    have hcolumn_sum_summable :
        Summable (fun k : ℤ =>
          ∑ j ∈ s, ‖A j k‖ * ‖c k‖ ^ 2) := by
      refine Summable.of_nonneg_of_le
        (fun k => Finset.sum_nonneg
          (fun j _hj => mul_nonneg (norm_nonneg _) (sq_nonneg _)))
        hcolumn_point hcolumn_major
    have hcolumn :
        (∑ j ∈ s, ∑' k : ℤ, ‖A j k‖ * ‖c k‖ ^ 2) ≤
          S * ‖c‖ ^ 2 := by
      have hcomm :
          (∑' k : ℤ, ∑ j ∈ s, ‖A j k‖ * ‖c k‖ ^ 2) =
            ∑ j ∈ s, ∑' k : ℤ, ‖A j k‖ * ‖c k‖ ^ 2 :=
        Summable.tsum_finsetSum hw_summable
      calc
        (∑ j ∈ s, ∑' k : ℤ, ‖A j k‖ * ‖c k‖ ^ 2)
            = ∑' k : ℤ, ∑ j ∈ s, ‖A j k‖ * ‖c k‖ ^ 2 :=
              hcomm.symm
        _ ≤ ∑' k : ℤ, S * ‖c k‖ ^ 2 :=
              Summable.tsum_le_tsum hcolumn_point hcolumn_sum_summable
                hcolumn_major
        _ = S * (∑' k : ℤ, ‖c k‖ ^ 2) := by
              rw [tsum_mul_left]
        _ = S * ‖c‖ ^ 2 := by
              rw [hc_tsum_sq]
    have hrow_point :
        ∀ j : ℤ,
          f j ≤ R * (∑' k : ℤ, ‖A j k‖ * ‖c k‖ ^ 2) := by
      intro j
      have hcs :=
        weighted_cauchy_schwarz_tsum
          (b := fun k : ℤ => A j k) (z := fun k : ℤ => c k)
          (hA.row_summable j)
          ⟨‖c‖, fun k => lp_norm_apply_le_norm_int c k⟩
      have hsecond_nonneg :
          0 ≤ (∑' k : ℤ, ‖A j k‖ * ‖c k‖ ^ 2) := by
        exact tsum_nonneg
          (fun k => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      calc
        f j ≤ (∑' k : ℤ, ‖A j k‖) *
            (∑' k : ℤ, ‖A j k‖ * ‖c k‖ ^ 2) := hcs
        _ ≤ R * (∑' k : ℤ, ‖A j k‖ * ‖c k‖ ^ 2) :=
              mul_le_mul_of_nonneg_right (hA.row_bound j) hsecond_nonneg
    calc
      (∑ j ∈ s, f j)
          ≤ ∑ j ∈ s, R * (∑' k : ℤ, ‖A j k‖ * ‖c k‖ ^ 2) := by
            exact Finset.sum_le_sum (fun j _hj => hrow_point j)
      _ = R * (∑ j ∈ s, ∑' k : ℤ, ‖A j k‖ * ‖c k‖ ^ 2) := by
            rw [Finset.mul_sum]
      _ ≤ R * (S * ‖c‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hcolumn hA.R_nonneg
      _ = R * S * ‖c‖ ^ 2 := by ring
  have hf_summable : Summable f := summable_of_sum_le hf_nonneg hfinite
  constructor
  · simpa [f] using hf_summable
  · have hle : (∑' j : ℤ, f j) ≤ R * S * ‖c‖ ^ 2 :=
      Real.tsum_le_of_sum_le hf_nonneg hfinite
    simpa [f] using hle


def schurOperator
    (A : ℤ → ℤ → ℂ) (R S : ℝ) (hA : SchurBounds A R S) :
    ellp (2 : ℝ≥0∞) →L[ℂ] ellp (2 : ℝ≥0∞) := by
  let L : ellp (2 : ℝ≥0∞) →ₗ[ℂ] ellp (2 : ℝ≥0∞) :=
    { toFun c := by
        refine ⟨fun j : ℤ => ∑' k : ℤ, A j k * c k, ?_⟩
        exact memℓp_gen (by simpa using (schur_square_sum_bound hA c).1)
      map_add' c d := by
        ext j
        have hc := (schur_row_pairing_summable hA c j).1
        have hd := (schur_row_pairing_summable hA d j).1
        calc
          (∑' k : ℤ, A j k * (c + d) k)
              = ∑' k : ℤ, (A j k * c k + A j k * d k) := by
                apply tsum_congr
                intro k
                simp [mul_add]
          _ = (∑' k : ℤ, A j k * c k) +
                (∑' k : ℤ, A j k * d k) :=
              hc.tsum_add hd
      map_smul' a c := by
        ext j
        have hc := (schur_row_pairing_summable hA c j).1
        calc
          (∑' k : ℤ, A j k * (a • c) k)
              = ∑' k : ℤ, a • (A j k * c k) := by
                apply tsum_congr
                intro k
                simp [mul_left_comm]
          _ = a • (∑' k : ℤ, A j k * c k) :=
              Summable.tsum_const_smul a hc }
  refine L.mkContinuous (Real.sqrt (R * S)) ?_
  intro c
  have hRS_nonneg : 0 ≤ R * S := mul_nonneg hA.R_nonneg hA.S_nonneg
  have hright_nonneg : 0 ≤ Real.sqrt (R * S) * ‖c‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsum :
      (∑' j : ℤ, ‖(L c) j‖ ^ 2) ≤
        (Real.sqrt (R * S) * ‖c‖) ^ 2 := by
    calc
      (∑' j : ℤ, ‖(L c) j‖ ^ 2)
          = ∑' j : ℤ, ‖∑' k : ℤ, A j k * c k‖ ^ 2 := rfl
      _ ≤ R * S * ‖c‖ ^ 2 := (schur_square_sum_bound hA c).2
      _ = (Real.sqrt (R * S) * ‖c‖) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hRS_nonneg]
  exact lp.norm_le_of_tsum_le (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ)
    (by norm_num) hright_nonneg (by simpa using hsum)


theorem schurOperator_isMatrixOperator
    (A : ℤ → ℤ → ℂ) (R S : ℝ) (hA : SchurBounds A R S) :
    IsMatrixOperator (2 : ℝ≥0∞) A (schurOperator A R S hA) := by
  intro c j
  constructor
  · exact (schur_row_pairing_summable hA c j).1
  · rfl


theorem schurOperator_norm_le
    (A : ℤ → ℤ → ℂ) (R S : ℝ) (hA : SchurBounds A R S) :
    ‖schurOperator A R S hA‖ ≤ Real.sqrt (R * S) := by
  refine (schurOperator A R S hA).opNorm_le_bound (Real.sqrt_nonneg _) ?_
  intro c
  have hcoord :
      ∀ j : ℤ,
        (schurOperator A R S hA c) j =
          ∑' k : ℤ, A j k * c k := by
    intro j
    exact (schurOperator_isMatrixOperator A R S hA c j).2
  have hnormsq :
      ‖schurOperator A R S hA c‖ ^ 2 =
        ∑' j : ℤ, ‖∑' k : ℤ, A j k * c k‖ ^ 2 := by
    have hnorm :
        ‖schurOperator A R S hA c‖ ^ 2 =
          ∑' j : ℤ, ‖(schurOperator A R S hA c) j‖ ^ 2 := by
      simpa using
        (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ)
          (by norm_num) (schurOperator A R S hA c))
    rw [hnorm]
    apply tsum_congr
    intro j
    rw [hcoord j]
  have hschur := (schur_square_sum_bound hA c).2
  have hRS_nonneg : 0 ≤ R * S := mul_nonneg hA.R_nonneg hA.S_nonneg
  have hsq :
      ‖schurOperator A R S hA c‖ ^ 2 ≤
        (Real.sqrt (R * S) * ‖c‖) ^ 2 := by
    calc
      ‖schurOperator A R S hA c‖ ^ 2
          = ∑' j : ℤ, ‖∑' k : ℤ, A j k * c k‖ ^ 2 := hnormsq
      _ ≤ R * S * ‖c‖ ^ 2 := hschur
      _ = (Real.sqrt (R * S) * ‖c‖) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hRS_nonneg]
  have hright_nonneg : 0 ≤ Real.sqrt (R * S) * ‖c‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have h := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hright_nonneg] using h



theorem lower_bound_of_left_inverse
    (T U : ellp (2 : ℝ≥0∞) →L[ℂ] ellp (2 : ℝ≥0∞))
    (hUT : ∀ c : ellp (2 : ℝ≥0∞), U (T c) = c) :
    ∀ c : ellp (2 : ℝ≥0∞),
      (1 / (1 + ‖U‖)) * ‖c‖ ≤ ‖T c‖ := by
  intro c
  have hpos : 0 < 1 + ‖U‖ := by positivity
  have hnorm : ‖c‖ ≤ (1 + ‖U‖) * ‖T c‖ := by
    calc
      ‖c‖ = ‖U (T c)‖ := by rw [hUT c]
      _ ≤ ‖U‖ * ‖T c‖ := U.le_opNorm (T c)
      _ ≤ (1 + ‖U‖) * ‖T c‖ := by
        exact mul_le_mul_of_nonneg_right
          (by linarith [norm_nonneg U]) (norm_nonneg (T c))
  have hnorm' : ‖c‖ ≤ ‖T c‖ * (1 + ‖U‖) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnorm
  calc
    (1 / (1 + ‖U‖)) * ‖c‖ = ‖c‖ / (1 + ‖U‖) := by ring
    _ ≤ ‖T c‖ := (div_le_iff₀ hpos).2 hnorm'

end

end VendorE3
