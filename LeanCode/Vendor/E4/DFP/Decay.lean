import LeanCode.Vendor.E4.DFP.SequenceSpaces

open scoped BigOperators

noncomputable section

namespace VendorE4


private theorem summable_decay_kernel {eta : Real} (heta : 1 < eta) :
    Summable (fun d : Int => 1 / (1 + |(d : Real)|) ^ eta) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact ((Real.summable_one_div_nat_add_rpow 1 eta).2 heta).congr (fun n => by
      have hn : 0 <= (n : Real) := Nat.cast_nonneg n
      have hn1 : 0 <= (n : Real) + 1 := by positivity
      simp [abs_of_nonneg hn, abs_of_nonneg hn1, add_comm])
  · exact ((Real.summable_one_div_nat_add_rpow 1 eta).2 heta).congr (fun n => by
      have hn : 0 <= (n : Real) := Nat.cast_nonneg n
      have hn1 : 0 <= (n : Real) + 1 := by positivity
      simp [abs_of_nonneg hn, abs_of_nonneg hn1, add_comm])



theorem uniformlySummableRows_of_polynomialOffDiagonalDecay :
  forall {G : Int -> Int -> Real},
    HasPolynomialOffDiagonalDecay G -> UniformlySummableRows G := by
  intro G hdecay
  rcases hdecay with ⟨C, eta, hCpos, heta, hbound⟩
  let base : Int -> Real := fun d => C / (1 + |(d : Real)|) ^ eta
  have hbaseNoC : Summable (fun d : Int => 1 / (1 + |(d : Real)|) ^ eta) :=
    summable_decay_kernel heta
  have hbase : Summable base := by
    simpa [base, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hbaseNoC.mul_left C
  refine ⟨max 1 (∑' d : Int, base d),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro i
  have hshiftSummable : Summable (fun j : Int => base (i - j)) :=
    hbase.comp_injective
      (show Function.Injective (fun j : Int => i - j) from sub_right_injective)
  have hrowSummable : Summable (fun j : Int => |G i j|) := by
    exact hshiftSummable.of_nonneg_of_le
      (fun j => abs_nonneg (G i j))
      (fun j => by
        simpa [base, Real.norm_eq_abs] using hbound i j)
  constructor
  · exact hrowSummable
  · have hleShift : (∑' j : Int, |G i j|) <= ∑' j : Int, base (i - j) := by
      exact Summable.tsum_le_tsum
        (fun j => by simpa [base, Real.norm_eq_abs] using hbound i j)
        hrowSummable hshiftSummable
    let e : Int ≃ Int :=
      { toFun := fun j => i - j
        invFun := fun d => i - d
        left_inv := by intro j; simp
        right_inv := by intro d; simp }
    have htsumShift : (∑' j : Int, base (i - j)) = ∑' d : Int, base d := by
      simpa [e] using e.tsum_eq base
    exact hleShift.trans (by
      rw [htsumShift]
      exact le_max_right _ _)

end VendorE4
