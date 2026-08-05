import LeanCode.Vendor.E2.Pairing
import LeanCode.Vendor.E2.BanachFacts

open scoped ENNReal NNReal

namespace VendorE2.Lean_Code

noncomputable def ellOneDualVector
    (f : ellp (1 : ℝ≥0∞) →L[ℂ] ℂ) : ellp (∞ : ℝ≥0∞) :=
  ⟨fun n : ℤ => f (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n 1), by
    change Memℓp
      (fun n : ℤ => f (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n 1))
      (∞ : ℝ≥0∞)
    rw [memℓp_infty_iff]
    refine ⟨‖f‖, ?_⟩
    rintro r ⟨n, rfl⟩
    calc
      ‖f (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n 1)‖ ≤
          ‖f‖ * ‖lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n (1 : ℂ)‖ :=
        ContinuousLinearMap.le_opNorm f _
      _ = ‖f‖ * 1 := by
        rw [lp.norm_single]
        · norm_num
        · norm_num
      _ = ‖f‖ := mul_one _⟩

lemma ellOne_single_smul
    (x : ellp (1 : ℝ≥0∞)) (n : ℤ) :
    lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n (x n) =
      (x n) • lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n 1 := by
  ext k
  by_cases hk : k = n
  · subst k
    simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne hk]

lemma ellOneDualVector_apply_single
    (f : ellp (1 : ℝ≥0∞) →L[ℂ] ℂ)
    (x : ellp (1 : ℝ≥0∞)) (n : ℤ) :
    f (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n (x n)) =
      x n * ellOneDualVector f n := by
  rw [ellOne_single_smul x n]
  simp [ellOneDualVector]

theorem ellp_dual_isometry_surjective_one_top
    (f : ellp (1 : ℝ≥0∞) →L[ℂ] ℂ) :
    ∃ y : ellp (∞ : ℝ≥0∞),
      ∀ x : ellp (1 : ℝ≥0∞),
        f x = lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x y := by
  refine ⟨ellOneDualVector f, ?_⟩
  intro x
  have hsum :=
    lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (1 : ℝ≥0∞)) (by simp) x
  have hmap := hsum.map f f.continuous
  have hfx :
      f x =
        ∑' n : ℤ,
          f (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n (x n)) := by
    exact hmap.tsum_eq.symm
  rw [hfx]
  unfold lpPairing
  exact tsum_congr (fun n => ellOneDualVector_apply_single f x n)

noncomputable def ellpDualVectorInterior
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : ellp p →L[ℂ] ℂ)
    (hmem : Memℓp (fun n : ℤ =>
      f (lp.single (E := fun _ : ℤ => ℂ) p n 1)) q) : ellp q :=
  ⟨fun n : ℤ => f (lp.single (E := fun _ : ℤ => ℂ) p n 1), hmem⟩

lemma ellpDualVectorInterior_apply_single
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : ellp p →L[ℂ] ℂ)
    (x : ellp p) (n : ℤ) :
    f (lp.single (E := fun _ : ℤ => ℂ) p n (x n)) =
      x n * f (lp.single (E := fun _ : ℤ => ℂ) p n 1) := by
  rw [show lp.single (E := fun _ : ℤ => ℂ) p n (x n) =
      (x n) • lp.single (E := fun _ : ℤ => ℂ) p n 1 by
    ext k
    by_cases hk : k = n
    · subst k
      simp [Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne hk]]
  simp

noncomputable def dualNormingCoeff (q : ℝ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else ((‖z‖ ^ q : ℝ) : ℂ) / z

lemma dualNormingCoeff_mul (z : ℂ) (q : ℝ) (hq_pos : 0 < q) :
    dualNormingCoeff q z * z = ((‖z‖ ^ q : ℝ) : ℂ) := by
  by_cases hz : z = 0
  · simp [dualNormingCoeff, hz, Real.zero_rpow hq_pos.ne']
  · simp [dualNormingCoeff, hz]

lemma dualNormingCoeff_norm_rpow
    (z : ℂ) (p q : ℝ) (hp_pos : 0 < p) (hq_pos : 0 < q)
    (hpow : (q - 1) * p = q) :
    ‖dualNormingCoeff q z‖ ^ p = ‖z‖ ^ q := by
  by_cases hz : z = 0
  · simp [dualNormingCoeff, hz, Real.zero_rpow hp_pos.ne',
      Real.zero_rpow hq_pos.ne']
  · have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    calc
      ‖dualNormingCoeff q z‖ ^ p =
          (‖((‖z‖ ^ q : ℝ) : ℂ) / z‖) ^ p := by
        simp [dualNormingCoeff, hz]
      _ = ((‖z‖ ^ q) / ‖z‖) ^ p := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) q)]
      _ = (‖z‖ ^ (q - 1)) ^ p := by
        rw [Real.rpow_sub hnorm_pos q 1]
        simp
      _ = ‖z‖ ^ ((q - 1) * p) := by
        rw [← Real.rpow_mul (norm_nonneg _) (q - 1) p]
      _ = ‖z‖ ^ q := by rw [hpow]

lemma lp_single_smul_one
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) (c : ℂ) :
    lp.single (E := fun _ : ℤ => ℂ) p n c =
      c • lp.single (E := fun _ : ℤ => ℂ) p n 1 := by
  ext k
  by_cases hk : k = n
  · subst k
    simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne hk]

theorem ellp_dual_coordinate_partial_sum_bound_interior
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_finite : p ≠ ∞)
    (hp_ne_one : p ≠ 1)
    (hconj : q = conjugateExponent p)
    (f : ellp p →L[ℂ] ℂ) :
    ∀ s : Finset ℤ,
      ∑ n ∈ s, ‖f (lp.single (E := fun _ : ℤ => ℂ) p n 1)‖ ^ q.toReal ≤
        ‖f‖ ^ q.toReal := by
  intro s
  haveI hpq : ENNReal.HolderConjugate p q := by
    subst q
    dsimp [conjugateExponent]
    infer_instance
  have hp_gt_one_en : 1 < p := lt_of_le_of_ne Fact.out (Ne.symm hp_ne_one)
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp_finite
  have hp_gt_one : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_finite).2 hp_gt_one_en
  have hq_ne_top : q ≠ ∞ := by
    haveI hqp : ENNReal.HolderConjugate q p := hpq.symm
    have hlt : q < ∞ :=
      (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp_gt_one_en
    exact ne_of_lt hlt
  have hq_pos : 0 < q.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq_ne_top
  have hpq_real : p.toReal.HolderConjugate q.toReal :=
    ENNReal.HolderConjugate.toReal hp_gt_one
  have hqp_real : q.toReal.HolderConjugate p.toReal := hpq_real.symm
  let y : ℤ → ℂ := fun n =>
    f (lp.single (E := fun _ : ℤ => ℂ) p n 1)
  let coeff : ℤ → ℂ := fun n => dualNormingCoeff q.toReal (y n)
  let x : ellp p := ∑ n ∈ s, lp.single (E := fun _ : ℤ => ℂ) p n (coeff n)
  let S : ℝ := ∑ n ∈ s, ‖y n‖ ^ q.toReal
  have hcoeff_mul : ∀ n, coeff n * y n = ((‖y n‖ ^ q.toReal : ℝ) : ℂ) := by
    intro n
    exact dualNormingCoeff_mul (y n) q.toReal hq_pos
  have hcoeff_norm : ∀ n, ‖coeff n‖ ^ p.toReal = ‖y n‖ ^ q.toReal := by
    intro n
    exact dualNormingCoeff_norm_rpow (y n) p.toReal q.toReal
      hp_pos hq_pos hqp_real.sub_one_mul_conj
  have hx_pow : ‖x‖ ^ p.toReal = S := by
    calc
      ‖x‖ ^ p.toReal = ∑ n ∈ s, ‖coeff n‖ ^ p.toReal := by
        simpa [x] using
          lp.norm_sum_single (p := p) (E := fun _ : ℤ => ℂ) hp_pos coeff s
      _ = S := by
        simp [S, hcoeff_norm]
  have hfx : f x = (S : ℂ) := by
    calc
      f x = ∑ n ∈ s, f (lp.single (E := fun _ : ℤ => ℂ) p n (coeff n)) := by
        simp [x]
      _ = ∑ n ∈ s, coeff n * y n := by
        refine Finset.sum_congr rfl ?_
        intro n _hn
        rw [lp_single_smul_one p n (coeff n)]
        simp [y]
      _ = ∑ n ∈ s, ((‖y n‖ ^ q.toReal : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro n _hn
        rw [hcoeff_mul n]
      _ = (S : ℂ) := by
        simp [S]
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg (fun n _hn => Real.rpow_nonneg (norm_nonneg _) _)
  have hS_le_op : S ≤ ‖f‖ * ‖x‖ := by
    have hop := ContinuousLinearMap.le_opNorm f x
    rw [hfx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS_nonneg] at hop
    exact hop
  by_cases hx_zero : ‖x‖ = 0
  · have hS_zero : S = 0 := by
      rw [← hx_pow, hx_zero]
      exact Real.zero_rpow hp_pos.ne'
    rw [show ∑ n ∈ s, ‖f (lp.single (E := fun _ : ℤ => ℂ) p n 1)‖ ^ q.toReal =
      S by rfl]
    rw [hS_zero]
    exact Real.rpow_nonneg (norm_nonneg _) _
  · have hx_pos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx_zero)
    have hx_sub_le : ‖x‖ ^ (p.toReal - 1) ≤ ‖f‖ := by
      calc
        ‖x‖ ^ (p.toReal - 1) = ‖x‖ ^ p.toReal / ‖x‖ := by
          rw [Real.rpow_sub hx_pos p.toReal 1]
          simp
        _ = S / ‖x‖ := by rw [hx_pow]
        _ ≤ (‖f‖ * ‖x‖) / ‖x‖ := by
          exact div_le_div_of_nonneg_right hS_le_op hx_pos.le
        _ = ‖f‖ := by field_simp [hx_pos.ne']
    have hraised := Real.rpow_le_rpow
      (Real.rpow_nonneg (norm_nonneg _) (p.toReal - 1)) hx_sub_le hq_pos.le
    rw [← Real.rpow_mul (norm_nonneg _) (p.toReal - 1) q.toReal,
      hpq_real.sub_one_mul_conj] at hraised
    rw [show ∑ n ∈ s, ‖f (lp.single (E := fun _ : ℤ => ℂ) p n 1)‖ ^ q.toReal =
      S by rfl]
    rw [← hx_pow]
    exact hraised

theorem ellp_dual_vector_mem_norm_le_interior
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_finite : p ≠ ∞)
    (hp_ne_one : p ≠ 1)
    (hconj : q = conjugateExponent p)
    (f : ellp p →L[ℂ] ℂ) :
    ∃ hmem : Memℓp (fun n : ℤ =>
      f (lp.single (E := fun _ : ℤ => ℂ) p n 1)) q,
      ‖ellpDualVectorInterior p q f hmem‖ ≤ ‖f‖ := by
  haveI hpq : ENNReal.HolderConjugate p q := by
    subst q
    dsimp [conjugateExponent]
    infer_instance
  have hq_ne_top : q ≠ ∞ := by
    haveI hqp : ENNReal.HolderConjugate q p := hpq.symm
    have hp_gt_one : 1 < p := lt_of_le_of_ne Fact.out (Ne.symm hp_ne_one)
    have hlt : q < ∞ :=
      (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp_gt_one
    exact ne_of_lt hlt
  have hq_ne_zero : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq_ne_zero hq_ne_top
  let yfun : ℤ → ℂ := fun n =>
    f (lp.single (E := fun _ : ℤ => ℂ) p n 1)
  have hpartial : ∀ s : Finset ℤ,
      ∑ n ∈ s, ‖yfun n‖ ^ q.toReal ≤ ‖f‖ ^ q.toReal := by
    intro s
    simpa [yfun] using
      ellp_dual_coordinate_partial_sum_bound_interior
        p q hp_finite hp_ne_one hconj f s
  have hsumm : Summable (fun n : ℤ => ‖yfun n‖ ^ q.toReal) :=
    summable_of_sum_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) hpartial
  have hmem : Memℓp yfun q := memℓp_gen hsumm
  refine ⟨hmem, ?_⟩
  have htsum_le : ∑' n : ℤ, ‖yfun n‖ ^ q.toReal ≤ ‖f‖ ^ q.toReal :=
    Real.tsum_le_of_sum_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) hpartial
  have hnorm_le : ‖(⟨yfun, hmem⟩ : ellp q)‖ ≤ ‖f‖ :=
    lp.norm_le_of_tsum_le hq_pos (norm_nonneg f) htsum_le
  simpa [ellpDualVectorInterior, yfun] using hnorm_le

theorem ellp_dual_isometry_surjective_interior
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_finite : p ≠ ∞)
    (hp_ne_one : p ≠ 1)
    (hconj : q = conjugateExponent p)
    (f : ellp p →L[ℂ] ℂ) :
    ∃ y : ellp q, ‖y‖ ≤ ‖f‖ ∧ ∀ x : ellp p, f x = lpPairing p q x y := by
  rcases ellp_dual_vector_mem_norm_le_interior p q hp_finite hp_ne_one hconj f with
    ⟨hmem, hnorm⟩
  let y : ellp q := ellpDualVectorInterior p q f hmem
  refine ⟨y, hnorm, ?_⟩
  intro x
  have hsum := lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := p) hp_finite x
  have hmap := hsum.map f f.continuous
  have hfx : f x =
      ∑' n : ℤ, f (lp.single (E := fun _ : ℤ => ℂ) p n (x n)) := by
    exact hmap.tsum_eq.symm
  rw [hfx]
  unfold lpPairing
  exact tsum_congr (fun n => ellpDualVectorInterior_apply_single p f x n)

theorem ellp_dual_isometry_surjective
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_finite : p ≠ ∞)
    (hconj : q = conjugateExponent p)
    (f : ellp p →L[ℂ] ℂ) :
    ∃ y : ellp q, ∀ x : ellp p, f x = lpPairing p q x y := by
  by_cases hp_one : p = 1
  · subst p
    have hq : q = ∞ := by
      have htop : (∞ : ℝ≥0∞) = conjugateExponent (1 : ℝ≥0∞) :=
        (ENNReal.HolderConjugate.one_top.conjExponent_eq).symm
      exact hconj.trans htop.symm
    cases hq
    exact ellp_dual_isometry_surjective_one_top f
  · rcases ellp_dual_isometry_surjective_interior p q hp_finite hp_one hconj f with
      ⟨y, _hy_norm, hy_repr⟩
    exact ⟨y, hy_repr⟩

theorem dense_of_trivial_annihilator
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_finite : p ≠ ∞)
    (hconj : q = conjugateExponent p)
    (M : Submodule ℂ (ellp p))
    (h_ann : ∀ y : ellp q,
      (∀ x : ellp p, x ∈ M → lpPairing p q x y = 0) → y = 0) :
    Dense ((M : Set (ellp p))) := by
  subst q
  by_contra h_dense
  rw [Submodule.dense_iff_topologicalClosure_eq_top] at h_dense
  let C : Submodule ℂ (ellp p) := M.topologicalClosure
  have hC_closed : IsClosed (C : Set (ellp p)) := by
    simp [C]
  haveI : IsClosed (C : Set (ellp p)) := hC_closed
  letI : NormedAddCommGroup (ellp p ⧸ C) :=
    Submodule.Quotient.normedAddCommGroup C
  have hC_ne_top : C ≠ ⊤ := by
    simpa [C] using h_dense
  have hnot_forall : ¬ ∀ x : ellp p, x ∈ C := by
    intro hmem
    apply hC_ne_top
    ext x
    exact ⟨fun _ => trivial, fun _ => hmem x⟩
  push Not at hnot_forall
  rcases hnot_forall with ⟨x₀, hx₀C⟩
  let qx₀ : ellp p ⧸ C := Submodule.Quotient.mk x₀
  have hqx₀_ne : qx₀ ≠ 0 := by
    intro hq
    exact hx₀C ((Submodule.Quotient.mk_eq_zero (p := C)).mp hq)
  have hqx₀_norm_ne : ‖qx₀‖ ≠ 0 := by
    intro hnorm
    exact hx₀C ((QuotientAddGroup.norm_mk_eq_zero (S := C.toAddSubgroup) (m := x₀)).mp hnorm)
  obtain ⟨g, _hg_norm, hgx₀⟩ := exists_dual_vector ℂ qx₀ hqx₀_norm_ne
  let f : ellp p →L[ℂ] ℂ := g.comp C.mkQL
  have hf_ann : ∀ x : ellp p, x ∈ M → f x = 0 := by
    intro x hxM
    have hxC : x ∈ C := M.le_topologicalClosure hxM
    simp [f, C, Submodule.mkQL_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero (p := M.topologicalClosure)).mpr hxC]
  rcases ellp_dual_isometry_surjective p (conjugateExponent p) hp_finite rfl f with
    ⟨y, hy⟩
  have hy_zero : y = 0 := by
    apply h_ann y
    intro x hxM
    rw [← hy x, hf_ann x hxM]
  have hf_x₀_zero : f x₀ = 0 := by
    rw [hy x₀, hy_zero]
    simp [lpPairing]
  have hf_x₀_ne : f x₀ ≠ 0 := by
    have hgx₀_ne : g qx₀ ≠ 0 := by
      rw [hgx₀]
      intro hzero
      exact hqx₀_norm_ne (Complex.ofReal_eq_zero.mp hzero)
    simpa [f, qx₀, C, Submodule.mkQL_apply, Submodule.mkQ_apply] using hgx₀_ne
  exact hf_x₀_ne hf_x₀_zero

noncomputable def ellOneInfinityPairingCLM :
    ellp (1 : ℝ≥0∞) →L[ℂ] ellp (∞ : ℝ≥0∞) →L[ℂ] ℂ := by
  let B : (k : ℤ) → ℂ →L[ℂ] ℂ →L[ℂ] ℂ :=
    fun _ => ContinuousLinearMap.mul ℂ ℂ
  have hB : ∀ k : ℤ, ‖B k‖ ≤ (1 : ℝ≥0) := by
    intro k
    simp [B]
  exact lp.dualPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) B hB

lemma ellOneInfinityPairingCLM_apply
    (x : ellp (1 : ℝ≥0∞)) (b : ellp (∞ : ℝ≥0∞)) :
    ellOneInfinityPairingCLM x b =
      lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x b := by
  simp [ellOneInfinityPairingCLM, lp.dualPairing_apply, lpPairing]

lemma conjugateExponent_one_eq_top :
    (∞ : ℝ≥0∞) = conjugateExponent (1 : ℝ≥0∞) := by
  exact (ENNReal.HolderConjugate.one_top.conjExponent_eq).symm

lemma conjugateExponent_top_eq_one :
    (1 : ℝ≥0∞) = conjugateExponent (∞ : ℝ≥0∞) := by
  exact (ENNReal.HolderConjugate.top_one.conjExponent_eq).symm

lemma lpPairing_comm
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (x : ellp p) (y : ellp q) :
    lpPairing p q x y = lpPairing q p y x := by
  simp [lpPairing, mul_comm]

theorem ellp_norm_eq_iSup_pairing
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hconj : q = conjugateExponent p)
    (z : ellp q) :
    ‖z‖ =
      sSup {r : ℝ | ∃ x : ellp p, ‖x‖ ≤ 1 ∧ r = ‖lpPairing p q x z‖} := by
  by_cases hp_one : p = 1
  · subst p
    have hq : q = ∞ := by
      have htop : (∞ : ℝ≥0∞) = conjugateExponent (1 : ℝ≥0∞) :=
        (ENNReal.HolderConjugate.one_top.conjExponent_eq).symm
      exact hconj.trans htop.symm
    cases hq
    exact ellInfinity_norm_eq_iSup_pairing z
  · by_cases hp_top : p = ∞
    · subst p
      have hq : q = 1 := by
        have hone : (1 : ℝ≥0∞) = conjugateExponent (∞ : ℝ≥0∞) :=
          (ENNReal.HolderConjugate.top_one.conjExponent_eq).symm
        exact hconj.trans hone.symm
      cases hq
      exact ellOne_norm_eq_iSup_pairing z
    · let S : Set ℝ := {r : ℝ | ∃ x : ellp p, ‖x‖ ≤ 1 ∧
        r = ‖lpPairing p q x z‖}
      have hS_nonempty : S.Nonempty := by
        refine ⟨0, ?_⟩
        exact ⟨0, by simp, by simp [lpPairing]⟩
      have hzero_mem : 0 ∈ S := by
        exact ⟨0, by simp, by simp [lpPairing]⟩
      have hS_bdd : BddAbove S := by
        refine ⟨‖z‖, ?_⟩
        rintro r ⟨x, hx, rfl⟩
        calc
          ‖lpPairing p q x z‖ ≤ ‖x‖ * ‖z‖ :=
            lpPairing_bound p q hconj x z
          _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
          _ = ‖z‖ := one_mul _
      change ‖z‖ = sSup S
      apply le_antisymm
      · by_cases hz : ‖z‖ = 0
        · rw [hz]
          exact le_csSup hS_bdd hzero_mem
        · rcases exists_dual_vector ℂ z hz with ⟨f, hf_norm, hfz⟩
          haveI hpq : ENNReal.HolderConjugate p q := by
            subst q
            dsimp [conjugateExponent]
            infer_instance
          have hq_finite : q ≠ ∞ := by
            haveI hqp : ENNReal.HolderConjugate q p := hpq.symm
            have hlt : q < ∞ :=
              (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2
                (lt_of_le_of_ne Fact.out (Ne.symm hp_one))
            exact ne_of_lt hlt
          have hq_ne_one : q ≠ 1 := by
            intro hq_one
            have hpq_symm : ENNReal.HolderConjugate q p := hpq.symm
            have h_one_p : ENNReal.HolderConjugate (1 : ℝ≥0∞) p := by
              simpa [hq_one] using hpq_symm
            have hp_top' : p = ∞ := by
              exact @ENNReal.HolderConjugate.unique
                (1 : ℝ≥0∞) p h_one_p ∞ ENNReal.HolderConjugate.one_top
            exact hp_top hp_top'
          have hsymm : p = conjugateExponent q := by
            haveI hqp : ENNReal.HolderConjugate q p := hpq.symm
            exact (ENNReal.HolderConjugate.conjExponent_eq (p := q) (q := p)).symm
          rcases ellp_dual_isometry_surjective_interior
              q p hq_finite hq_ne_one hsymm f with
            ⟨x, hx_norm, hx_repr⟩
          have hx_unit : ‖x‖ ≤ 1 := by
            simpa [hf_norm] using hx_norm
          refine le_csSup hS_bdd ?_
          refine ⟨x, hx_unit, ?_⟩
          have hpair_eq : lpPairing p q x z = (‖z‖ : ℂ) := by
            rw [lpPairing_comm p q x z]
            rw [← hx_repr z]
            exact hfz
          have hnorm_pair : ‖lpPairing p q x z‖ = ‖z‖ := by
            rw [hpair_eq, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (norm_nonneg z)]
          exact hnorm_pair.symm
      · refine csSup_le hS_nonempty ?_
        rintro r ⟨x, hx, rfl⟩
        calc
          ‖lpPairing p q x z‖ ≤ ‖x‖ * ‖z‖ :=
            lpPairing_bound p q hconj x z
          _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
          _ = ‖z‖ := one_mul _

noncomputable def fixedEllInfinityPairingFunctional
    (b : ellp (∞ : ℝ≥0∞)) :
    ellp (1 : ℝ≥0∞) →L[ℂ] ℂ :=
  ellOneInfinityPairingCLM.flip b

lemma fixedEllInfinityPairingFunctional_apply
    (b : ellp (∞ : ℝ≥0∞)) (x : ellp (1 : ℝ≥0∞)) :
    fixedEllInfinityPairingFunctional b x =
      lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x b := by
  simp [fixedEllInfinityPairingFunctional, ellOneInfinityPairingCLM_apply]

noncomputable def preadjointVector
    (S : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (b : ellp (∞ : ℝ≥0∞)) : ellp (∞ : ℝ≥0∞) :=
  Classical.choose <|
    ellp_dual_isometry_surjective (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
      (by simp) conjugateExponent_one_eq_top
      ((fixedEllInfinityPairingFunctional b).comp S)

lemma preadjointVector_pairing
    (S : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (y : ellp (1 : ℝ≥0∞)) (b : ellp (∞ : ℝ≥0∞)) :
    lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (S y) b =
      lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y (preadjointVector S b) := by
  have hspec :=
    Classical.choose_spec <|
      ellp_dual_isometry_surjective (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
        (by simp) conjugateExponent_one_eq_top
        ((fixedEllInfinityPairingFunctional b).comp S)
  specialize hspec y
  simpa [preadjointVector, fixedEllInfinityPairingFunctional_apply] using hspec

lemma ellInfinity_norm_le_of_pairing_bound
    (z : ellp (∞ : ℝ≥0∞)) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ x : ellp (1 : ℝ≥0∞), ‖x‖ ≤ 1 →
      ‖lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x z‖ ≤ C) :
    ‖z‖ ≤ C := by
  rw [ellInfinity_norm_eq_iSup_pairing z]
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    refine ⟨0, by simp, ?_⟩
    simp [lpPairing]
  · rintro r ⟨x, hx, rfl⟩
    exact hbound x hx

lemma ellInfinity_ext_pairing
    {u v : ellp (∞ : ℝ≥0∞)}
    (h : ∀ x : ellp (1 : ℝ≥0∞),
      lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x u =
        lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x v) :
    u = v := by
  suffices ‖u - v‖ = 0 by
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  refine le_antisymm ?_ (norm_nonneg _)
  apply ellInfinity_norm_le_of_pairing_bound (z := u - v) (C := 0) (by positivity)
  intro x _hx
  have hx_pair : lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) x (u - v) = 0 := by
    have hlin : ellOneInfinityPairingCLM x (u - v) = 0 := by
      rw [map_sub]
      simp [ellOneInfinityPairingCLM_apply, h x]
    simpa [ellOneInfinityPairingCLM_apply] using hlin
  simp [hx_pair]

lemma preadjointVector_norm_le
    (S : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (b : ellp (∞ : ℝ≥0∞)) :
    ‖preadjointVector S b‖ ≤ ‖S‖ * ‖b‖ := by
  apply ellInfinity_norm_le_of_pairing_bound
    (z := preadjointVector S b) (C := ‖S‖ * ‖b‖)
  · positivity
  intro x hx
  rw [← preadjointVector_pairing S x b]
  calc
    ‖lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (S x) b‖ ≤ ‖S x‖ * ‖b‖ :=
      lpPairing_bound (1 : ℝ≥0∞) (∞ : ℝ≥0∞)
        conjugateExponent_one_eq_top (S x) b
    _ ≤ (‖S‖ * ‖x‖) * ‖b‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.le_opNorm S x) (norm_nonneg b)
    _ ≤ (‖S‖ * 1) * ‖b‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg b)
      exact mul_le_mul_of_nonneg_left hx (norm_nonneg S)
    _ = ‖S‖ * ‖b‖ := by ring

noncomputable def preadjointOnEllOne
    (S : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞)) :
    ellp (∞ : ℝ≥0∞) →L[ℂ] ellp (∞ : ℝ≥0∞) :=
  LinearMap.mkContinuous
    { toFun := preadjointVector S
      map_add' := by
        intro b c
        apply ellInfinity_ext_pairing
        intro y
        have hleft :
            lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y
                (preadjointVector S (b + c)) =
              lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (S y) (b + c) :=
          (preadjointVector_pairing S y (b + c)).symm
        have hright :
            lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y
                (preadjointVector S b + preadjointVector S c) =
              lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y (preadjointVector S b) +
                lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y (preadjointVector S c) := by
          have hlin :
              ellOneInfinityPairingCLM y (preadjointVector S b + preadjointVector S c) =
                ellOneInfinityPairingCLM y (preadjointVector S b) +
                  ellOneInfinityPairingCLM y (preadjointVector S c) :=
            map_add (ellOneInfinityPairingCLM y) _ _
          simpa [ellOneInfinityPairingCLM_apply] using hlin
        rw [hleft, hright, ← preadjointVector_pairing S y b,
          ← preadjointVector_pairing S y c]
        have hlin :
            lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (S y) (b + c) =
              lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (S y) b +
                lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (S y) c := by
          have hlin' :
              ellOneInfinityPairingCLM (S y) (b + c) =
                ellOneInfinityPairingCLM (S y) b +
                  ellOneInfinityPairingCLM (S y) c :=
            map_add (ellOneInfinityPairingCLM (S y)) _ _
          simpa [ellOneInfinityPairingCLM_apply] using hlin'
        exact hlin
      map_smul' := by
        intro c b
        apply ellInfinity_ext_pairing
        intro y
        calc
          lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y
              (preadjointVector S (c • b)) =
              lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (S y) (c • b) :=
            (preadjointVector_pairing S y (c • b)).symm
          _ = c • lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (S y) b := by
            rw [← ellOneInfinityPairingCLM_apply, ← ellOneInfinityPairingCLM_apply]
            exact map_smul (ellOneInfinityPairingCLM (S y)) c b
          _ = c • lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y
              (preadjointVector S b) := by
            rw [preadjointVector_pairing S y b]
          _ = lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y
              (c • preadjointVector S b) := by
            rw [← ellOneInfinityPairingCLM_apply, ← ellOneInfinityPairingCLM_apply]
            exact (map_smul (ellOneInfinityPairingCLM y) c
              (preadjointVector S b)).symm
        }
    ‖S‖
    (preadjointVector_norm_le S)

theorem preadjointOnEllOne_pairing
    (S : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (y : ellp (1 : ℝ≥0∞)) (b : ellp (∞ : ℝ≥0∞)) :
    lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (S y) b =
      lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y (preadjointOnEllOne S b) := by
  exact preadjointVector_pairing S y b

theorem preadjointOnEllOne_comp
    (S T : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞)) :
    preadjointOnEllOne (S.comp T) =
      (preadjointOnEllOne T).comp (preadjointOnEllOne S) := by
  apply ContinuousLinearMap.ext
  intro b
  apply ellInfinity_ext_pairing
  intro y
  calc
    lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y
        (preadjointOnEllOne (S.comp T) b) =
        lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) ((S.comp T) y) b :=
      (preadjointOnEllOne_pairing (S.comp T) y b).symm
    _ = lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (T y)
        (preadjointOnEllOne S b) := by
      simpa using preadjointOnEllOne_pairing S (T y) b
    _ = lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y
        ((preadjointOnEllOne T).comp (preadjointOnEllOne S) b) := by
      simpa using
        preadjointOnEllOne_pairing T y (preadjointOnEllOne S b)

theorem preadjointOnEllOne_id :
    preadjointOnEllOne (ContinuousLinearMap.id ℂ (ellp (1 : ℝ≥0∞))) =
      ContinuousLinearMap.id ℂ (ellp (∞ : ℝ≥0∞)) := by
  apply ContinuousLinearMap.ext
  intro b
  apply ellInfinity_ext_pairing
  intro y
  simpa using
    (preadjointOnEllOne_pairing
      (ContinuousLinearMap.id ℂ (ellp (1 : ℝ≥0∞))) y b).symm

theorem preadjointOnEllOne_isUnit
    (S : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (hS : IsUnit S) :
    IsUnit (preadjointOnEllOne S) := by
  rcases isUnit_iff_exists.mp hS with ⟨R, hSR, hRS⟩
  refine isUnit_iff_exists.mpr ?_
  refine ⟨preadjointOnEllOne R, ?_, ?_⟩
  · rw [show preadjointOnEllOne S * preadjointOnEllOne R =
        (preadjointOnEllOne S).comp (preadjointOnEllOne R) by rfl]
    rw [← preadjointOnEllOne_comp]
    change preadjointOnEllOne (R * S) = 1
    rw [hRS]
    exact preadjointOnEllOne_id
  · rw [show preadjointOnEllOne R * preadjointOnEllOne S =
        (preadjointOnEllOne R).comp (preadjointOnEllOne S) by rfl]
    rw [← preadjointOnEllOne_comp]
    change preadjointOnEllOne (S * R) = 1
    rw [hSR]
    exact preadjointOnEllOne_id

lemma summable_mul_ellOne_ellInfinity
    (u : ellp (1 : ℝ≥0∞)) (b : ellp (∞ : ℝ≥0∞)) :
    Summable (fun m : ℤ => u m * b m) := by
  have hu_mem : Memℓp (fun m : ℤ => u m) (1 : ℝ≥0∞) := lp.memℓp u
  have hb_mem : Memℓp (fun m : ℤ => b m) (∞ : ℝ≥0∞) := lp.memℓp b
  rcases hb_mem.bddAbove with ⟨C, hC⟩
  let Cmax : ℝ := max C 0
  have hb_bound : ∀ m : ℤ, ‖b m‖ ≤ Cmax := by
    intro m
    exact (hC ⟨m, rfl⟩).trans (le_max_left C 0)
  have hscaled_mem :
      Memℓp (fun m : ℤ => (Cmax : ℝ) * ‖u m‖) (1 : ℝ≥0∞) := by
    have hnorm_mem : Memℓp (fun m : ℤ => ‖u m‖) (1 : ℝ≥0∞) :=
      hu_mem.norm
    simpa using hnorm_mem.const_mul Cmax
  have hprod_mem : Memℓp (fun m : ℤ => u m * b m) (1 : ℝ≥0∞) := by
    exact hscaled_mem.mono (fun m => by
      calc
        ‖u m * b m‖ = ‖u m‖ * ‖b m‖ := norm_mul _ _
        _ ≤ ‖u m‖ * Cmax :=
          mul_le_mul_of_nonneg_left (hb_bound m) (norm_nonneg _)
        _ = Cmax * ‖u m‖ := by ring)
  exact Memℓp.summable_of_one hprod_mem

lemma transpose_single_coordinate
    (A : ℤ → ℤ → ℂ)
    (Tt : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (hTt : IsMatrixOperator (1 : ℝ≥0∞) (transposeMatrix A) Tt)
    (n m : ℤ) :
    (Tt (lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n 1)) m = A n m := by
  let e : ellp (1 : ℝ≥0∞) :=
    lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n 1
  have hsum : (∑' l : ℤ, transposeMatrix A m l * e l) = A n m := by
    rw [tsum_eq_single n]
    · simp [e, transposeMatrix, Pi.single_eq_same]
    · intro l hl
      simp [e, transposeMatrix, Pi.single_eq_of_ne hl]
  have hmat := (hTt e m).2
  change (Tt e) m = A n m
  rw [hmat, hsum]

theorem preadjoint_transpose_isMatrixOperator_infinity
    (A : ℤ → ℤ → ℂ)
    (Tt : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (hTt : IsMatrixOperator (1 : ℝ≥0∞) (transposeMatrix A) Tt) :
    IsMatrixOperator (∞ : ℝ≥0∞) A (preadjointOnEllOne Tt) := by
  intro b n
  let e : ellp (1 : ℝ≥0∞) :=
    lp.single (E := fun _ : ℤ => ℂ) (1 : ℝ≥0∞) n 1
  have hcoord : ∀ m : ℤ, (Tt e) m = A n m := by
    intro m
    exact transpose_single_coordinate A Tt hTt n m
  have hsumm_T : Summable (fun m : ℤ => (Tt e) m * b m) :=
    summable_mul_ellOne_ellInfinity (Tt e) b
  have hsumm_A : Summable (fun m : ℤ => A n m * b m) := by
    simpa [hcoord] using hsumm_T
  refine ⟨hsumm_A, ?_⟩
  calc
    (preadjointOnEllOne Tt b) n =
        lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) e (preadjointOnEllOne Tt b) := by
      simpa [e] using (lpPairing_single_one_left n (preadjointOnEllOne Tt b)).symm
    _ = lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (Tt e) b := by
      simpa using (preadjointOnEllOne_pairing Tt e b).symm
    _ = ∑' m : ℤ, (Tt e) m * b m := by
      rfl
    _ = ∑' m : ℤ, A n m * b m := by
      exact tsum_congr (fun m => by rw [hcoord m])

theorem transpose_preadjoint_eq_operator
    (A : ℤ → ℤ → ℂ)
    (Tt : ellp (1 : ℝ≥0∞) →L[ℂ] ellp (1 : ℝ≥0∞))
    (Tinf : ellp (∞ : ℝ≥0∞) →L[ℂ] ellp (∞ : ℝ≥0∞))
    (hTt : IsMatrixOperator (1 : ℝ≥0∞) (transposeMatrix A) Tt)
    (hTinf : IsMatrixOperator (∞ : ℝ≥0∞) A Tinf) :
    preadjointOnEllOne Tt = Tinf := by
  apply ContinuousLinearMap.ext
  intro b
  apply ellInfinity_ext_pairing
  intro y
  calc
    lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y (preadjointOnEllOne Tt b) =
        lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (Tt y) b :=
      (preadjointOnEllOne_pairing Tt y b).symm
    _ = lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) b (Tt y) :=
      lpPairing_comm (1 : ℝ≥0∞) (∞ : ℝ≥0∞) (Tt y) b
    _ = lpPairing (∞ : ℝ≥0∞) (1 : ℝ≥0∞) (Tinf b) y := by
      exact (lpPairing_matrixOperator_eq_transpose
        (∞ : ℝ≥0∞) (1 : ℝ≥0∞) conjugateExponent_top_eq_one
        A Tinf Tt hTinf hTt b y).symm
    _ = lpPairing (1 : ℝ≥0∞) (∞ : ℝ≥0∞) y (Tinf b) :=
      lpPairing_comm (∞ : ℝ≥0∞) (1 : ℝ≥0∞) (Tinf b) y

end VendorE2.Lean_Code
