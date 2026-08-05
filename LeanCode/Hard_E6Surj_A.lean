import LeanCode.Vendor.E6.Defs
import LeanCode.Vendor.E2

open scoped ENNReal

noncomputable section

namespace Assembly.HardE6SurjA

open VendorE2.Lean_Code


theorem memℓp_one_iff {f : ℤ → ℂ} : Memℓp f 1 ↔ Summable (fun k : ℤ => ‖f k‖) := by
  have hp : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp]
  simp only [ENNReal.toReal_one, Real.rpow_one]



theorem e6Decay_to_e2Decay
    (A : ℤ → ℤ → ℂ) (h : E6.HasPolynomialOffDiagonalDecay A) :
    VendorE2.Lean_Code.HasPolynomialOffDiagonalDecay A := by
  rcases h with ⟨C, n, hCpos, hn, hbound⟩
  refine ⟨C, (n : ℝ), hCpos, by exact_mod_cast hn, ?_⟩
  intro k l
  have hcast : ‖(k - l : ℤ)‖ = |(k : ℝ) - (l : ℝ)| := by
    rw [Int.norm_eq_abs]
    push_cast
    rfl
  have hpow : ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ n = (1 + |(k : ℝ) - (l : ℝ)|) ^ (n : ℝ) := by
    rw [hcast, Real.rpow_natCast]
  calc
    ‖A k l‖ ≤ C / ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ n := hbound k l
    _ = C / (1 + |(k : ℝ) - (l : ℝ)|) ^ (n : ℝ) := by rw [hpow]



theorem surjSpectralInvariance_proof
    (A : ℤ → ℤ → ℂ) (hdecay : E6.HasPolynomialOffDiagonalDecay A) :
    E6.MatrixSurjectiveOn A E6.SequenceSpace.infinity →
      E6.MatrixSurjectiveOn A E6.SequenceSpace.one := by
  intro hInf

  have hA2 : VendorE2.Lean_Code.HasPolynomialOffDiagonalDecay A :=
    e6Decay_to_e2Decay A hdecay

  obtain ⟨a, _hae, hdomA, _hdomAt⟩ :=
    VendorE2.Lean_Code.polynomialDecay_to_even_ellOne_domination A hA2

  set Tinf : ellp (∞ : ℝ≥0∞) →L[ℂ] ellp (∞ : ℝ≥0∞) :=
    VendorE2.Lean_Code.dominatedMatrixOperator (∞ : ℝ≥0∞) A a hdomA with hTinf
  have hTinf_op : VendorE2.Lean_Code.IsMatrixOperator (∞ : ℝ≥0∞) A Tinf :=
    VendorE2.Lean_Code.dominatedMatrixOperator_isMatrixOperator (∞ : ℝ≥0∞) A a hdomA

  have hTinf_surj : Function.Surjective Tinf := by
    intro x

    have hxbdd : E6.IsBoundedSequence (fun k : ℤ => (x : ℤ → ℂ) k) := by
      refine ⟨‖x‖, ?_⟩
      intro k
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero x k

    obtain ⟨y, hy_bdd, hCMatVec⟩ := hInf (fun k : ℤ => (x : ℤ → ℂ) k) hxbdd

    have hy_mem : Memℓp y (∞ : ℝ≥0∞) := by
      rw [memℓp_infty_iff]
      obtain ⟨M, hM⟩ := hy_bdd
      exact ⟨M, by rintro _ ⟨k, rfl⟩; exact hM k⟩
    let ylp : ellp (∞ : ℝ≥0∞) := ⟨y, hy_mem⟩
    refine ⟨ylp, ?_⟩

    apply lp.ext
    funext n
    have hcoe : ((ylp : ellp (∞ : ℝ≥0∞)) : ℤ → ℂ) = y := rfl
    have hop := (hTinf_op ylp n).2

    rw [hop]
    have hrw : (fun m : ℤ => A n m * ((ylp : ellp (∞ : ℝ≥0∞)) : ℤ → ℂ) m)
        = (fun m : ℤ => A n m * y m) := by
      funext m; rw [hcoe]
    rw [hrw]
    have : E6.CMatVec A y n = (fun k : ℤ => (x : ℤ → ℂ) k) n := by
      rw [hCMatVec]
    simpa [E6.CMatVec] using this

  have hSurjInf2 : VendorE2.Lean_Code.MatrixSurjectiveOn (∞ : ℝ≥0∞) A :=
    ⟨Tinf, hTinf_op, hTinf_surj⟩

  have hSurj12 : VendorE2.Lean_Code.MatrixSurjectiveOn (1 : ℝ≥0∞) A :=
    VendorE2.Lean_Code.SurjSpectralInvariance A hA2 hSurjInf2

  obtain ⟨T1, hT1_op, hT1_surj⟩ := hSurj12
  intro v hv_summable

  have hv_mem : Memℓp v (1 : ℝ≥0∞) := memℓp_one_iff.mpr hv_summable
  let vlp : ellp (1 : ℝ≥0∞) := ⟨v, hv_mem⟩
  obtain ⟨z, hz⟩ := hT1_surj vlp
  refine ⟨fun k : ℤ => (z : ℤ → ℂ) k, ?_, ?_⟩
  ·
    exact memℓp_one_iff.mp (lp.memℓp z)
  ·
    funext n
    have hop := (hT1_op z n).2
    have hzn : (T1 z) n = ∑' m : ℤ, A n m * (z : ℤ → ℂ) m := hop
    have hvcoe : ((vlp : ellp (1 : ℝ≥0∞)) : ℤ → ℂ) = v := rfl
    have : (T1 z) n = ((vlp : ellp (1 : ℝ≥0∞)) : ℤ → ℂ) n := by
      rw [hz]
    rw [hvcoe] at this

    have : (∑' m : ℤ, A n m * (z : ℤ → ℂ) m) = v n := by
      rw [← hzn]; exact this
    simpa [E6.CMatVec] using this

end Assembly.HardE6SurjA
