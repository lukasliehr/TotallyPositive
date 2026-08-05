import LeanCode.Vendor.E2.Domination

open scoped ENNReal NNReal

namespace VendorE2.Lean_Code


noncomputable def conjugateExponent (p : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.conjExponent p


noncomputable def lpPairing
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (x : ellp p) (y : ellp q) : ℂ :=
  ∑' k : ℤ, x k * y k

noncomputable def lpPairingCLM
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hconj : q = conjugateExponent p) :
    ellp p →L[ℂ] ellp q →L[ℂ] ℂ := by
  subst q
  haveI : ENNReal.HolderConjugate p (conjugateExponent p) := by
    dsimp [conjugateExponent]
    infer_instance
  let B : (k : ℤ) → ℂ →L[ℂ] ℂ →L[ℂ] ℂ :=
    fun _ => ContinuousLinearMap.mul ℂ ℂ
  have hB : ∀ k : ℤ, ‖B k‖ ≤ (1 : ℝ≥0) := by
    intro k
    simp [B]
  exact lp.dualPairing p (conjugateExponent p) B hB

lemma lpPairingCLM_apply
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hconj : q = conjugateExponent p)
    (x : ellp p) (y : ellp q) :
    lpPairingCLM p q hconj x y = lpPairing p q x y := by
  subst q
  simp [lpPairingCLM, lp.dualPairing_apply, lpPairing]

lemma lpPairing_smul_left
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hconj : q = conjugateExponent p)
    (c : ℂ) (x : ellp p) (y : ellp q) :
    lpPairing p q (c • x) y = c * lpPairing p q x y := by
  rw [← lpPairingCLM_apply p q hconj (c • x) y,
    ← lpPairingCLM_apply p q hconj x y]
  exact congrArg (fun F : ellp q →L[ℂ] ℂ => F y)
    (ContinuousLinearMap.map_smul (lpPairingCLM p q hconj) c x)

theorem lpPairing_bound
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hconj : q = conjugateExponent p)
    (x : ellp p) (y : ellp q) :
    ‖lpPairing p q x y‖ ≤ ‖x‖ * ‖y‖ := by
  subst q
  haveI : ENNReal.HolderConjugate p (conjugateExponent p) := by
    dsimp [conjugateExponent]
    infer_instance
  let B : (k : ℤ) → ℂ →L[ℂ] ℂ →L[ℂ] ℂ :=
    fun _ => ContinuousLinearMap.mul ℂ ℂ
  have hB : ∀ k : ℤ, ‖B k‖ ≤ (1 : ℝ≥0) := by
    intro k
    simp [B]
  let D := lp.dualPairing p (conjugateExponent p) B hB
  have hD_norm : ‖D‖ ≤ (1 : ℝ≥0) := by
    simpa [D] using
      (lp.norm_dualPairing (p := p) (q := conjugateExponent p) B hB)
  have hD_apply : D x y = lpPairing p (conjugateExponent p) x y := by
    simp [D, B, lp.dualPairing_apply, lpPairing]
  rw [← hD_apply]
  calc
    ‖D x y‖ ≤ ‖D x‖ * ‖y‖ :=
      ContinuousLinearMap.le_opNorm (D x) y
    _ ≤ (‖D‖ * ‖x‖) * ‖y‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.le_opNorm D x) (norm_nonneg y)
    _ ≤ (1 * ‖x‖) * ‖y‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg y)
      exact mul_le_mul_of_nonneg_right hD_norm (norm_nonneg x)
    _ = ‖x‖ * ‖y‖ := by ring

lemma lpPairing_single_left
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (n : ℤ) (c : ℂ) (b : ellp q) :
    lpPairing p q (lp.single (E := fun _ : ℤ => ℂ) p n c) b = c * b n := by
  rw [lpPairing]
  rw [tsum_eq_single n]
  · simp [Pi.single_eq_same]
  · intro m hm
    simp [Pi.single_eq_of_ne hm]

lemma lpPairing_single_one_left
    (n : ℤ) (b : ellp (∞ : ℝ≥0∞)) :
    lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
      (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n 1) b = b n := by
  rw [lpPairing]
  rw [tsum_eq_single n]
  · simp [Pi.single_eq_same]
  · intro m hm
    simp [Pi.single_eq_of_ne hm]

lemma lpPairing_single_one_left_smul
    (n : ℤ) (c : ℂ) (b : ellp (∞ : ℝ≥0∞)) :
    lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
      (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c) b = c * b n := by
  rw [lpPairing]
  rw [tsum_eq_single n]
  · simp [Pi.single_eq_same]
  · intro m hm
    simp [Pi.single_eq_of_ne hm]

lemma lpPairing_single_one_right
    (x : ellp (∞ : ℝ≥0∞)) (n : ℤ) (c : ℂ) :
    lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) x
      (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c) = x n * c := by
  rw [lpPairing]
  rw [tsum_eq_single n]
  · simp [Pi.single_eq_same]
  · intro m hm
    simp [Pi.single_eq_of_ne hm]

theorem ellInfinity_norm_eq_iSup_pairing
    (z : ellp (∞ : ℝ≥0∞)) :
    ‖z‖ =
      sSup {r : ℝ | ∃ x : ellp (1 : ℝ≥0∞), ‖x‖ ≤ 1 ∧
        r = ‖lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x z‖} := by
  let S : Set ℝ := {r : ℝ | ∃ x : ellp (1 : ℝ≥0∞), ‖x‖ ≤ 1 ∧
    r = ‖lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x z‖}
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨0, by simp, by simp [lpPairing]⟩
  have hS_bdd : BddAbove S := by
    refine ⟨‖z‖, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    have hconj : (∞ : ℝ≥0∞) = conjugateExponent (1 : ℝ≥0∞) :=
      (ENNReal.HolderConjugate.one_top.conjExponent_eq).symm
    calc
      ‖lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x z‖ ≤ ‖x‖ * ‖z‖ :=
        lpPairing_bound (1 : ℝ≥0∞) (∞ : ℝ≥0∞) hconj x z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
      _ = ‖z‖ := one_mul _
  change ‖z‖ = sSup S
  apply le_antisymm
  · rw [lp.norm_eq_ciSup]
    refine ciSup_le ?_
    intro n
    refine le_csSup hS_bdd ?_
    refine ⟨lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n 1, ?_, ?_⟩
    · rw [lp.norm_single]
      · simp
      · exact zero_lt_one
    · simp [lpPairing_single_one_left]
  · refine csSup_le hS_nonempty ?_
    rintro r ⟨x, hx, rfl⟩
    have hconj : (∞ : ℝ≥0∞) = conjugateExponent (1 : ℝ≥0∞) :=
      (ENNReal.HolderConjugate.one_top.conjExponent_eq).symm
    calc
      ‖lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x z‖ ≤ ‖x‖ * ‖z‖ :=
        lpPairing_bound (1 : ℝ≥0∞) (∞ : ℝ≥0∞) hconj x z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
      _ = ‖z‖ := one_mul _

noncomputable def ellOneNormingVector
    (z : ellp (1 : ℝ≥0∞)) : ellp (∞ : ℝ≥0∞) :=
  ⟨fun k : ℤ => if z k = 0 then 0 else ((‖z k‖ : ℝ) : ℂ) / z k, by
    change Memℓp
      (fun k : ℤ => if z k = 0 then 0 else ((‖z k‖ : ℝ) : ℂ) / z k)
      (∞ : ℝ≥0∞)
    rw [memℓp_infty_iff]
    refine ⟨1, ?_⟩
    rintro r ⟨k, rfl⟩
    by_cases hz : z k = 0
    · simp [hz]
    · have hnorm_pos : 0 < ‖z k‖ := norm_pos_iff.mpr hz
      calc
        ‖(if z k = 0 then 0 else ((‖z k‖ : ℝ) : ℂ) / z k)‖ =
            ‖((‖z k‖ : ℝ) : ℂ) / z k‖ := by simp [hz]
        _ = ‖((‖z k‖ : ℝ) : ℂ)‖ / ‖z k‖ := norm_div _ _
        _ = ‖z k‖ / ‖z k‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        _ = 1 := by field_simp [hnorm_pos.ne']
        _ ≤ 1 := le_rfl⟩

lemma ellOneNormingVector_norm_le
    (z : ellp (1 : ℝ≥0∞)) :
    ‖ellOneNormingVector z‖ ≤ 1 := by
  rw [lp.norm_eq_ciSup]
  refine ciSup_le ?_
  intro k
  by_cases hz : z k = 0
  · simp [ellOneNormingVector, hz]
  · have hnorm_pos : 0 < ‖z k‖ := norm_pos_iff.mpr hz
    calc
      ‖ellOneNormingVector z k‖ =
          ‖((‖z k‖ : ℝ) : ℂ) / z k‖ := by
        simp [ellOneNormingVector, hz]
      _ = ‖((‖z k‖ : ℝ) : ℂ)‖ / ‖z k‖ := norm_div _ _
      _ = ‖z k‖ / ‖z k‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = 1 := by field_simp [hnorm_pos.ne']
      _ ≤ 1 := le_rfl

lemma ellOneNormingVector_mul
    (z : ellp (1 : ℝ≥0∞)) (k : ℤ) :
    ellOneNormingVector z k * z k = ((‖z k‖ : ℝ) : ℂ) := by
  by_cases hz : z k = 0
  · simp [ellOneNormingVector, hz]
  · simp [ellOneNormingVector, hz]

lemma ellOne_norm_eq_tsum_norm
    (z : ellp (1 : ℝ≥0∞)) :
    ‖z‖ = ∑' k : ℤ, ‖z k‖ := by
  simpa using (lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (by norm_num) z)

lemma lpPairing_ellOne_normingVector
    (z : ellp (1 : ℝ≥0∞)) :
    lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) (ellOneNormingVector z) z =
      (‖z‖ : ℂ) := by
  unfold lpPairing
  calc
    ∑' k : ℤ, ellOneNormingVector z k * z k =
        ∑' k : ℤ, ((‖z k‖ : ℝ) : ℂ) := by
      exact tsum_congr (ellOneNormingVector_mul z)
    _ = (‖z‖ : ℂ) := by
      rw [← Complex.ofReal_tsum]
      exact congrArg (fun t : ℝ => (t : ℂ)) (ellOne_norm_eq_tsum_norm z).symm

theorem ellOne_norm_eq_iSup_pairing
    (z : ellp (1 : ℝ≥0∞)) :
    ‖z‖ =
      sSup {r : ℝ | ∃ x : ellp (∞ : ℝ≥0∞), ‖x‖ ≤ 1 ∧
        r = ‖lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) x z‖} := by
  let S : Set ℝ := {r : ℝ | ∃ x : ellp (∞ : ℝ≥0∞), ‖x‖ ≤ 1 ∧
    r = ‖lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) x z‖}
  have hconj : (1 : ℝ≥0∞) = conjugateExponent (∞ : ℝ≥0∞) :=
    (ENNReal.HolderConjugate.top_one.conjExponent_eq).symm
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨0, by simp, by simp [lpPairing]⟩
  have hS_bdd : BddAbove S := by
    refine ⟨‖z‖, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    calc
      ‖lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) x z‖ ≤ ‖x‖ * ‖z‖ :=
        lpPairing_bound (∞ : ℝ≥0∞) (1 : ℝ≥0∞) hconj x z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
      _ = ‖z‖ := one_mul _
  change ‖z‖ = sSup S
  apply le_antisymm
  · refine le_csSup hS_bdd ?_
    refine ⟨ellOneNormingVector z, ellOneNormingVector_norm_le z, ?_⟩
    rw [lpPairing_ellOne_normingVector]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  · refine csSup_le hS_nonempty ?_
    rintro r ⟨x, hx, rfl⟩
    calc
      ‖lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) x z‖ ≤ ‖x‖ * ‖z‖ :=
        lpPairing_bound (∞ : ℝ≥0∞) (1 : ℝ≥0∞) hconj x z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
      _ = ‖z‖ := one_mul _

lemma matrixOperator_single_apply
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ)
    (T : ellp p →L[ℂ] ellp p)
    (hT : IsMatrixOperator p A T)
    (n m : ℤ) (c : ℂ) :
    (T (lp.single (E := fun _ : ℤ => ℂ) p n c)) m = A m n * c := by
  let e : ellp p := lp.single (E := fun _ : ℤ => ℂ) p n c
  have hsum : (∑' l : ℤ, A m l * e l) = A m n * c := by
    rw [tsum_eq_single n]
    · simp [e, Pi.single_eq_same]
    · intro l hl
      simp [e, Pi.single_eq_of_ne hl]
  have hmat := (hT e m).2
  change (T e) m = A m n * c
  rw [hmat, hsum]

lemma matrixOperator_single_apply_one
    (A : ℤ → ℤ → ℂ)
    (T : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (hT : IsMatrixOperator (1 : ℝ≥0∞) A T)
    (n m : ℤ) (c : ℂ) :
    (T (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c)) m = A m n * c := by
  let e : ellp (1 : ℝ≥0∞) :=
    lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c
  have hsum : (∑' l : ℤ, A m l * e l) = A m n * c := by
    rw [tsum_eq_single n]
    · simp [e, Pi.single_eq_same]
    · intro l hl
      simp [e, Pi.single_eq_of_ne hl]
  have hmat := (hT e m).2
  change (T e) m = A m n * c
  rw [hmat, hsum]

lemma transposeMatrixOperator_single_apply_one
    (A : ℤ → ℤ → ℂ)
    (Tt : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (hTt : IsMatrixOperator (1 : ℝ≥0∞) (transposeMatrix A) Tt)
    (n m : ℤ) (c : ℂ) :
    (Tt (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c)) m = A n m * c := by
  let e : ellp (1 : ℝ≥0∞) :=
    lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c
  have hsum : (∑' l : ℤ, transposeMatrix A m l * e l) = A n m * c := by
    rw [tsum_eq_single n]
    · simp [e, transposeMatrix, Pi.single_eq_same]
    · intro l hl
      simp [e, transposeMatrix, Pi.single_eq_of_ne hl]
  have hmat := (hTt e m).2
  change (Tt e) m = A n m * c
  rw [hmat, hsum]

lemma lpPairing_matrixOperator_eq_transpose_single_top_one
    (A : ℤ → ℤ → ℂ)
    (T : ellp (∞ : ℝ≥0∞) →L[ℂ] ellp (∞ : ℝ≥0∞))
    (Tt : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (hT : IsMatrixOperator (∞ : ℝ≥0∞) A T)
    (hTt : IsMatrixOperator (1 : ℝ≥0∞) (transposeMatrix A) Tt)
    (x : ellp (∞ : ℝ≥0∞)) (n : ℤ) (c : ℂ) :
    lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) (T x)
      (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c) =
    lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) x
      (Tt (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c)) := by
  have hTx := (hT x n).2
  have hsumm := (hT x n).1
  calc
    lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) (T x)
        (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c)
        = (T x) n * c := lpPairing_single_one_right (T x) n c
    _ = (∑' m : ℤ, A n m * x m) * c := by rw [hTx]
    _ = ∑' m : ℤ, (A n m * x m) * c := by
      exact (Summable.tsum_mul_right c hsumm).symm
    _ = ∑' m : ℤ, x m * (A n m * c) := by
      exact tsum_congr (fun m => by ring)
    _ = lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) x
        (Tt (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c)) := by
      rw [lpPairing]
      exact tsum_congr (fun m =>
        by rw [transposeMatrixOperator_single_apply_one A Tt hTt n m c])

theorem lpPairing_matrixOperator_eq_transpose_top_one
    (A : ℤ → ℤ → ℂ)
    (T : ellp (∞ : ℝ≥0∞) →L[ℂ] ellp (∞ : ℝ≥0∞))
    (Tt : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (hT : IsMatrixOperator (∞ : ℝ≥0∞) A T)
    (hTt : IsMatrixOperator (1 : ℝ≥0∞) (transposeMatrix A) Tt)
    (x : ellp (∞ : ℝ≥0∞)) (y : ellp (1 : ℝ≥0∞)) :
    lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) (T x) y =
      lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) x (Tt y) := by
  have hconj : (1 : ℝ≥0∞) = conjugateExponent (∞ : ℝ≥0∞) :=
    (ENNReal.HolderConjugate.top_one.conjExponent_eq).symm
  let F : ellp (1 : ℝ≥0∞) →L[ℂ] ℂ :=
    lpPairingCLM (∞ : ℝ≥0∞) (1 : ℝ≥0∞) hconj (T x)
  let G : ellp (1 : ℝ≥0∞) →L[ℂ] ℂ :=
    (lpPairingCLM (∞ : ℝ≥0∞) (1 : ℝ≥0∞) hconj x).comp Tt
  have hFG : F = G := by
    apply lp.ext_continuousLinearMap
      (𝕜 := ℂ) (E := fun _ : ℤ => ℂ) (p := (1 : ℝ≥0∞)) (hp := by simp)
    intro n
    apply ContinuousLinearMap.ext
    intro c
    change F (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c) =
      G (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c)
    simpa [F, G, lpPairingCLM_apply] using
      lpPairing_matrixOperator_eq_transpose_single_top_one A T Tt hT hTt x n c
  have happ := congrArg (fun H : ellp (1 : ℝ≥0∞) →L[ℂ] ℂ => H y) hFG
  simpa [F, G, lpPairingCLM_apply] using happ

lemma lpPairing_matrixOperator_eq_transpose_single_one_top
    (A : ℤ → ℤ → ℂ)
    (T : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (Tt : ellp (∞ : ℝ≥0∞) →L[ℂ] ellp (∞ : ℝ≥0∞))
    (hT : IsMatrixOperator (1 : ℝ≥0∞) A T)
    (hTt : IsMatrixOperator (∞ : ℝ≥0∞) (transposeMatrix A) Tt)
    (n : ℤ) (c : ℂ) (y : ellp (∞ : ℝ≥0∞)) :
    lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
      (T (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c)) y =
    lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
      (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c) (Tt y) := by
  have hTt_coord := (hTt y n).2
  have hsumm := (hTt y n).1
  change Summable (fun m : ℤ => A m n * y m) at hsumm
  calc
    lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
        (T (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c)) y
        = ∑' m : ℤ, (A m n * c) * y m := by
      rw [lpPairing]
      exact tsum_congr (fun m => by rw [matrixOperator_single_apply_one A T hT n m c])
    _ = ∑' m : ℤ, c * (A m n * y m) := by
      exact tsum_congr (fun m => by ring)
    _ = c * (∑' m : ℤ, A m n * y m) := by
      exact Summable.tsum_mul_left c hsumm
    _ = c * (Tt y) n := by
      rw [hTt_coord]
      simp [transposeMatrix]
    _ = lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
        (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c) (Tt y) := by
      exact (lpPairing_single_one_left_smul n c (Tt y)).symm

theorem lpPairing_matrixOperator_eq_transpose_one_top
    (A : ℤ → ℤ → ℂ)
    (T : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (Tt : ellp (∞ : ℝ≥0∞) →L[ℂ] ellp (∞ : ℝ≥0∞))
    (hT : IsMatrixOperator (1 : ℝ≥0∞) A T)
    (hTt : IsMatrixOperator (∞ : ℝ≥0∞) (transposeMatrix A) Tt)
    (x : ellp (1 : ℝ≥0∞)) (y : ellp (∞ : ℝ≥0∞)) :
    lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (T x) y =
      lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x (Tt y) := by
  have hconj : (∞ : ℝ≥0∞) = conjugateExponent (1 : ℝ≥0∞) :=
    (ENNReal.HolderConjugate.one_top.conjExponent_eq).symm
  let D : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (∞ : ℝ≥0∞) →L[ℂ] ℂ :=
    lpPairingCLM (1 : ℝ≥0∞) (∞ : ℝ≥0∞) hconj
  let F : ellp (1 : ℝ≥0∞) →L[ℂ] ℂ := (D.flip y).comp T
  let G : ellp (1 : ℝ≥0∞) →L[ℂ] ℂ := D.flip (Tt y)
  have hFG : F = G := by
    apply lp.ext_continuousLinearMap
      (𝕜 := ℂ) (E := fun _ : ℤ => ℂ) (p := (1 : ℝ≥0∞)) (hp := by simp)
    intro n
    apply ContinuousLinearMap.ext
    intro c
    change F (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c) =
      G (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n c)
    simpa [F, G, D, lpPairingCLM_apply] using
      lpPairing_matrixOperator_eq_transpose_single_one_top A T Tt hT hTt n c y
  have happ := congrArg (fun H : ellp (1 : ℝ≥0∞) →L[ℂ] ℂ => H x) hFG
  simpa [F, G, D, lpPairingCLM_apply] using happ

lemma lpPairing_matrixOperator_eq_transpose_single_left
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : ℤ → ℤ → ℂ)
    (T : ellp p →L[ℂ] ellp p)
    (Tt : ellp q →L[ℂ] ellp q)
    (hT : IsMatrixOperator p A T)
    (hTt : IsMatrixOperator q (transposeMatrix A) Tt)
    (n : ℤ) (c : ℂ) (y : ellp q) :
    lpPairing p q (T (lp.single (E := fun _ : ℤ => ℂ) p n c)) y =
      lpPairing p q (lp.single (E := fun _ : ℤ => ℂ) p n c) (Tt y) := by
  have hTt_coord := (hTt y n).2
  have hsumm := (hTt y n).1
  change Summable (fun m : ℤ => A m n * y m) at hsumm
  calc
    lpPairing p q (T (lp.single (E := fun _ : ℤ => ℂ) p n c)) y
        = ∑' m : ℤ, (A m n * c) * y m := by
      rw [lpPairing]
      exact tsum_congr (fun m => by rw [matrixOperator_single_apply p A T hT n m c])
    _ = ∑' m : ℤ, c * (A m n * y m) := by
      exact tsum_congr (fun m => by ring)
    _ = c * (∑' m : ℤ, A m n * y m) := by
      exact Summable.tsum_mul_left c hsumm
    _ = c * (Tt y) n := by
      rw [hTt_coord]
      simp [transposeMatrix]
    _ = lpPairing p q (lp.single (E := fun _ : ℤ => ℂ) p n c) (Tt y) := by
      exact (lpPairing_single_left p q n c (Tt y)).symm

theorem lpPairing_matrixOperator_eq_transpose_of_finite_left
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_finite : p ≠ ∞)
    (hconj : q = conjugateExponent p)
    (A : ℤ → ℤ → ℂ)
    (T : ellp p →L[ℂ] ellp p)
    (Tt : ellp q →L[ℂ] ellp q)
    (hT : IsMatrixOperator p A T)
    (hTt : IsMatrixOperator q (transposeMatrix A) Tt)
    (x : ellp p) (y : ellp q) :
    lpPairing p q (T x) y = lpPairing p q x (Tt y) := by
  let D : ellp p →L[ℂ] ellp q →L[ℂ] ℂ := lpPairingCLM p q hconj
  let F : ellp p →L[ℂ] ℂ := (D.flip y).comp T
  let G : ellp p →L[ℂ] ℂ := D.flip (Tt y)
  have hFG : F = G := by
    apply lp.ext_continuousLinearMap
      (𝕜 := ℂ) (E := fun _ : ℤ => ℂ) (p := p) (hp := hp_finite)
    intro n
    apply ContinuousLinearMap.ext
    intro c
    change F (lp.single (E := fun _ : ℤ => ℂ) p n c) =
      G (lp.single (E := fun _ : ℤ => ℂ) p n c)
    simpa [F, G, D, lpPairingCLM_apply] using
      lpPairing_matrixOperator_eq_transpose_single_left p q A T Tt hT hTt n c y
  have happ := congrArg (fun H : ellp p →L[ℂ] ℂ => H x) hFG
  simpa [F, G, D, lpPairingCLM_apply] using happ

theorem lpPairing_matrixOperator_eq_transpose
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hconj : q = conjugateExponent p)
    (A : ℤ → ℤ → ℂ)
    (T : ellp p →L[ℂ] ellp p)
    (Tt : ellp q →L[ℂ] ellp q)
    (hT : IsMatrixOperator p A T)
    (hTt : IsMatrixOperator q (transposeMatrix A) Tt)
    (x : ellp p) (y : ellp q) :
    lpPairing p q (T x) y = lpPairing p q x (Tt y) := by
  by_cases hp_top : p = ∞
  · subst p
    have hq : q = 1 := by
      have hone : (1 : ℝ≥0∞) = conjugateExponent (∞ : ℝ≥0∞) :=
        (ENNReal.HolderConjugate.top_one.conjExponent_eq).symm
      exact hconj.trans hone.symm
    cases hq
    exact lpPairing_matrixOperator_eq_transpose_top_one A T Tt hT hTt x y
  · exact lpPairing_matrixOperator_eq_transpose_of_finite_left
      p q hp_top hconj A T Tt hT hTt x y

end VendorE2.Lean_Code
