import LeanCode.Vendor.E2.Bridges

open scoped ENNReal

namespace VendorE2.Lean_Code


noncomputable def polynomialDecayKernel (C η : ℝ) (n : ℤ) : ℝ :=
  C * |(n : ℝ)| ^ (-η) + if n = 0 then C else 0

lemma polynomialDecayKernel_nonneg {C η : ℝ} (hC : 0 ≤ C) (n : ℤ) :
    0 ≤ polynomialDecayKernel C η n := by
  unfold polynomialDecayKernel
  exact add_nonneg
    (mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _))
    (by split <;> positivity)

lemma polynomialDecayKernel_even (C η : ℝ) :
    EvenKernel (polynomialDecayKernel C η) := by
  intro n
  unfold polynomialDecayKernel
  by_cases hn : n = 0
  · subst n
    simp
  · have hneg : -n ≠ 0 := by
      intro h
      exact hn (neg_eq_zero.mp h)
    simp [hn, hneg, abs_neg]

lemma polynomialDecayKernel_summable {C η : ℝ} (hC : 0 ≤ C) (hη : 1 < η) :
    Summable (fun n : ℤ => ‖polynomialDecayKernel C η n‖) := by
  have hs_base : Summable (fun n : ℤ => C * |(n : ℝ)| ^ (-η)) :=
    (Real.summable_abs_int_rpow hη).mul_left C
  have hs_single : Summable (fun n : ℤ => if n = 0 then C else 0) := by
    refine summable_of_hasFiniteSupport ((Set.finite_singleton 0).subset ?_)
    intro n hn
    by_contra hn0_mem
    have hn0 : n ≠ 0 := by simpa using hn0_mem
    have hzero : (if n = 0 then C else 0) = 0 := by simp [hn0]
    exact hn hzero
  refine (hs_base.add hs_single).congr ?_
  intro n
  rw [Real.norm_of_nonneg (polynomialDecayKernel_nonneg hC n)]
  simp [polynomialDecayKernel]

lemma polynomialDecay_bound_le_kernel {C η : ℝ} (hC : 0 ≤ C) (hη_pos : 0 < η)
    (d : ℤ) :
    C / (1 + |(d : ℝ)|) ^ η ≤ polynomialDecayKernel C η d := by
  by_cases hd : d = 0
  · subst d
    have hterm_nonneg : 0 ≤ C * (0 : ℝ) ^ (-η) :=
      mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
    calc
      C / (1 + |((0 : ℤ) : ℝ)|) ^ η = C := by simp
      _ ≤ polynomialDecayKernel C η 0 := by
        unfold polynomialDecayKernel
        simpa using add_le_add_right hterm_nonneg C
  · have hd_pos : 0 < |(d : ℝ)| := by
      exact abs_pos.mpr (by exact_mod_cast hd)
    have hle : |(d : ℝ)| ≤ 1 + |(d : ℝ)| := by
      linarith [abs_nonneg (d : ℝ)]
    have hrpow :
        (1 + |(d : ℝ)|) ^ (-η) ≤ |(d : ℝ)| ^ (-η) := by
      exact Real.rpow_le_rpow_of_nonpos hd_pos hle (by linarith)
    calc
      C / (1 + |(d : ℝ)|) ^ η =
          C * (1 + |(d : ℝ)|) ^ (-η) := by
        rw [div_eq_mul_inv, Real.rpow_neg (by positivity)]
      _ ≤ C * |(d : ℝ)| ^ (-η) :=
        mul_le_mul_of_nonneg_left hrpow hC
      _ ≤ polynomialDecayKernel C η d := by
        unfold polynomialDecayKernel
        simp [hd]

theorem polynomialDecay_to_even_ellOne_domination
    (A : ℤ → ℤ → ℂ)
    (hA : HasPolynomialOffDiagonalDecay A) :
    ∃ a : ℤ → ℝ,
      EvenKernel a ∧
        MatrixDominatedBy A a ∧ MatrixDominatedBy (transposeMatrix A) a := by
  rcases hA with ⟨C, η, hC_pos, hη, hbound⟩
  refine ⟨polynomialDecayKernel C η, polynomialDecayKernel_even C η, ?_, ?_⟩
  · refine ⟨polynomialDecayKernel_nonneg hC_pos.le,
      polynomialDecayKernel_summable hC_pos.le hη, ?_⟩
    intro k l
    have hcast : ((k - l : ℤ) : ℝ) = (k : ℝ) - (l : ℝ) := by
      norm_num [Int.cast_sub]
    calc
      ‖A k l‖ ≤ C / (1 + |(k : ℝ) - (l : ℝ)|) ^ η := hbound k l
      _ = C / (1 + |((k - l : ℤ) : ℝ)|) ^ η := by
        rw [hcast]
      _ ≤ polynomialDecayKernel C η (k - l) :=
        polynomialDecay_bound_le_kernel hC_pos.le (zero_lt_one.trans hη) (k - l)
  · refine ⟨polynomialDecayKernel_nonneg hC_pos.le,
      polynomialDecayKernel_summable hC_pos.le hη, ?_⟩
    intro k l
    have hdiff : (l : ℝ) - (k : ℝ) = -((k - l : ℤ) : ℝ) := by
      norm_num [Int.cast_sub]
    calc
      ‖transposeMatrix A k l‖ = ‖A l k‖ := rfl
      _ ≤ C / (1 + |(l : ℝ) - (k : ℝ)|) ^ η := hbound l k
      _ = C / (1 + |((k - l : ℤ) : ℝ)|) ^ η := by
        rw [hdiff, abs_neg]
      _ ≤ polynomialDecayKernel C η (k - l) :=
        polynomialDecay_bound_le_kernel hC_pos.le (zero_lt_one.trans hη) (k - l)

end VendorE2.Lean_Code
