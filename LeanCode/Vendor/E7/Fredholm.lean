import LeanCode.Vendor.E7.Defs
import LeanCode.Vendor.E7.SchurBound
import LeanCode.Vendor.E7.BanachFacts
import LeanCode.Vendor.E7.LimitOperators





















noncomputable section
namespace LimitOps









theorem surjective_opOfMatrix (A : ℤ → ℤ → ℂ)
    (hdecay : HasPolynomialOffDiagonalDecay A) (hsurj : MatrixSurjectiveOnEllOne A) :
    Function.Surjective (opOfMatrix A) := by
  intro v

  obtain ⟨y, hy_mem, hy_eq⟩ := hsurj (v : ℤ → ℂ) (memℓp_one_iff.mp (lp.memℓp v))

  refine ⟨⟨y, memℓp_one_iff.mpr hy_mem⟩, ?_⟩

  apply lp.ext
  funext k
  rw [opOfMatrix_apply hdecay]

  exact congrFun hy_eq k






theorem isClosed_range_opOfMatrix (A : ℤ → ℤ → ℂ)
    (hsurj : Function.Surjective (opOfMatrix A)) :
    IsClosed (Set.range (opOfMatrix A)) := by
  rw [Set.range_eq_univ.mpr hsurj]
  exact isClosed_univ



theorem finiteDimensional_coker_opOfMatrix (A : ℤ → ℤ → ℂ)
    (hsurj : Function.Surjective (opOfMatrix A)) :
    FiniteDimensional ℂ (ℓ1 ⧸ LinearMap.range (opOfMatrix A).toLinearMap) := by
  have hrange_top : LinearMap.range (opOfMatrix A).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  haveI : Subsingleton (ℓ1 ⧸ LinearMap.range (opOfMatrix A).toLinearMap) :=
    Submodule.Quotient.subsingleton_iff.mpr hrange_top

  exact Module.Finite.of_finite













theorem opNorm_opOfMatrix_le {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A)
    {M : ℝ} (hM0 : 0 ≤ M) (hMbound : ∀ l : ℤ, ∑' k : ℤ, ‖A k l‖ ≤ M) :
    ‖opOfMatrix A‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 (fun c => ?_)
  rw [norm_eq_tsum]

  have hcongr : (∑' k : ℤ, ‖(opOfMatrix A c : ℤ → ℂ) k‖)
      = ∑' k : ℤ, ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖ :=
    tsum_congr (fun k => by rw [opOfMatrix_apply h])
  rw [hcongr]

  have hsummable : Summable (fun k : ℤ => ‖∑' l : ℤ, A k l * (c : ℤ → ℂ) l‖) :=
    memℓp_one_iff.mp (memℓp_matVec h c)
  have hkey := tsum_ofReal_norm_matVec_le h hMbound c
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => norm_nonneg _) hsummable] at hkey
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM0 (norm_nonneg _))).mp hkey



def truncation (A : ℤ → ℤ → ℂ) (N : ℕ) : ℤ → ℤ → ℂ :=
  fun i j => if |i - j| ≤ (N : ℤ) then A i j else 0


def truncationTail (A : ℤ → ℤ → ℂ) (N : ℕ) : ℤ → ℤ → ℂ :=
  fun i j => if |i - j| ≤ (N : ℤ) then 0 else A i j

@[simp] theorem truncation_add_tail (A : ℤ → ℤ → ℂ) (N : ℕ) (i j : ℤ) :
    truncation A N i j + truncationTail A N i j = A i j := by
  unfold truncation truncationTail
  by_cases h : |i - j| ≤ (N : ℤ) <;> simp [h]


theorem norm_truncation_le (A : ℤ → ℤ → ℂ) (N : ℕ) (i j : ℤ) :
    ‖truncation A N i j‖ ≤ ‖A i j‖ := by
  unfold truncation
  by_cases h : |i - j| ≤ (N : ℤ) <;> simp [h]

theorem norm_truncationTail_le (A : ℤ → ℤ → ℂ) (N : ℕ) (i j : ℤ) :
    ‖truncationTail A N i j‖ ≤ ‖A i j‖ := by
  unfold truncationTail
  by_cases h : |i - j| ≤ (N : ℤ) <;> simp [h]


theorem hasDecay_of_norm_le {A B : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A)
    (hle : ∀ i j : ℤ, ‖B i j‖ ≤ ‖A i j‖) : HasPolynomialOffDiagonalDecay B := by
  obtain ⟨C, η, hC, hη, hbound⟩ := h
  exact ⟨C, η, hC, hη, fun k l => (hle k l).trans (hbound k l)⟩

theorem hasDecay_truncation {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) (N : ℕ) :
    HasPolynomialOffDiagonalDecay (truncation A N) :=
  hasDecay_of_norm_le h (norm_truncation_le A N)

theorem hasDecay_truncationTail {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A) (N : ℕ) :
    HasPolynomialOffDiagonalDecay (truncationTail A N) :=
  hasDecay_of_norm_le h (norm_truncationTail_le A N)



theorem sub_opOfMatrix_truncation_apply {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A)
    (N : ℕ) (c : ℓ1) (k : ℤ) :
    ((opOfMatrix A - opOfMatrix (truncation A N)) c : ℤ → ℂ) k
      = ∑' l : ℤ, truncationTail A N k l * (c : ℤ → ℂ) l := by
  rw [sub_apply]
  show (opOfMatrix A c : ℤ → ℂ) k - (opOfMatrix (truncation A N) c : ℤ → ℂ) k = _
  rw [opOfMatrix_apply h, opOfMatrix_apply (hasDecay_truncation h N)]
  rw [← (summable_row_matVec h c k).tsum_sub (summable_row_matVec (hasDecay_truncation h N) c k)]
  refine tsum_congr (fun l => ?_)

  rw [← sub_mul]

  have hsplit : A k l - truncation A N k l = truncationTail A N k l := by
    have h1 := truncation_add_tail A N k l
    rw [← h1]; ring
  rw [hsplit]




theorem norm_sub_opOfMatrix_truncation_le {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A)
    (N : ℕ) {M : ℝ} (hM0 : 0 ≤ M)
    (hMbound : ∀ l : ℤ, ∑' k : ℤ, ‖truncationTail A N k l‖ ≤ M) :
    ‖opOfMatrix A - opOfMatrix (truncation A N)‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 (fun c => ?_)
  rw [norm_eq_tsum]

  have hcongr : (∑' k : ℤ, ‖((opOfMatrix A - opOfMatrix (truncation A N)) c : ℤ → ℂ) k‖)
      = ∑' k : ℤ, ‖∑' l : ℤ, truncationTail A N k l * (c : ℤ → ℂ) l‖ :=
    tsum_congr (fun k => by rw [sub_opOfMatrix_truncation_apply h])
  rw [hcongr]

  have hsummable : Summable (fun k : ℤ => ‖∑' l : ℤ, truncationTail A N k l * (c : ℤ → ℂ) l‖) :=
    memℓp_one_iff.mp (memℓp_matVec (hasDecay_truncationTail h N) c)
  have hkey := tsum_ofReal_norm_matVec_le (hasDecay_truncationTail h N) hMbound c
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => norm_nonneg _) hsummable] at hkey
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM0 (norm_nonneg _))).mp hkey


theorem exists_Icc_superset (s : Finset ℤ) : ∃ N : ℕ, s ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  set N : ℕ := s.sup Int.natAbs with hNdef
  refine ⟨N, fun n hn => ?_⟩
  rw [Finset.mem_Icc]
  have hle : n.natAbs ≤ N := Finset.le_sup (f := Int.natAbs) hn
  have hbound : |n| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hle
  refine ⟨?_, ?_⟩
  · linarith [neg_abs_le n]
  · linarith [le_abs_self n]




theorem exists_tail_rpow_le {g : ℤ → ℝ} (_hg0 : ∀ n, 0 ≤ g n) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∑' n : ℤ, (if (N : ℤ) < |n| then g n else 0) ≤ ε := by

  have htail := tendsto_tsum_compl_atTop_zero g
  rw [tendsto_order] at htail
  have hev := htail.2 ε hε
  rw [Filter.eventually_atTop] at hev
  obtain ⟨s₀, hs₀⟩ := hev
  obtain ⟨N, hN⟩ := exists_Icc_superset s₀
  refine ⟨N, ?_⟩

  have hmem : ∀ n : ℤ, (n ∈ (↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ) ↔ (N : ℤ) < |n| := by
    intro n
    rw [Set.mem_compl_iff, Finset.coe_Icc, Set.mem_Icc, ← abs_le, not_le]

  have hset : (fun n : ℤ => if (N : ℤ) < |n| then g n else 0)
      = (↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ.indicator g := by
    funext n
    rw [Set.indicator_apply]
    congr 1
    exact propext (by rw [hmem])
  rw [hset, ← tsum_subtype]
  exact (hs₀ _ hN).le



theorem exists_truncationTail_col_bound {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ l : ℤ, ∑' k : ℤ, ‖truncationTail A N k l‖ ≤ ε := by
  obtain ⟨C, η, hC, hη, hbound⟩ := h
  set g : ℤ → ℝ := fun n => C * (1 + |(n : ℝ)|) ^ (-η) with hg_def
  have hg0 : ∀ n, 0 ≤ g n := fun n => mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)

  obtain ⟨N, hN⟩ := exists_tail_rpow_le hg0 hε
  refine ⟨N, fun l => ?_⟩
  have hdecay : HasPolynomialOffDiagonalDecay A := ⟨C, η, hC, hη, hbound⟩

  set F : ℤ → ℝ := fun k => if (N : ℤ) < |k - l| then C * (1 + |(k : ℝ) - (l : ℝ)|) ^ (-η) else 0
    with hF_def

  have hGsummable : Summable (fun n : ℤ => if (N : ℤ) < |n| then g n else 0) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (summable_one_add_abs_rpow hη |>.mul_left C)
    · split <;> [exact hg0 n; rfl]
    · split
      · exact le_refl _
      · exact mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
  have hFsummable : Summable F := by
    have hre := (Equiv.subRight l).summable_iff (f := fun n : ℤ => if (N : ℤ) < |n| then g n else 0)
    rw [← hre] at hGsummable
    refine hGsummable.congr (fun k => ?_)
    simp only [hF_def, hg_def, Equiv.subRight_apply, Function.comp]
    push_cast
    ring_nf

  have hpt : ∀ k : ℤ, ‖truncationTail A N k l‖ ≤ F k := by
    intro k
    unfold truncationTail
    simp only [hF_def]
    by_cases hkl : |k - l| ≤ (N : ℤ)
    · rw [if_pos hkl, norm_zero, if_neg (by omega)]
    · rw [if_neg hkl, if_pos (by omega)]
      exact hbound k l

  calc ∑' k : ℤ, ‖truncationTail A N k l‖
      ≤ ∑' k : ℤ, F k :=
        (summable_col (hasDecay_truncationTail hdecay N) l).tsum_le_tsum hpt hFsummable
    _ = ∑' n : ℤ, (if (N : ℤ) < |n| then g n else 0) := by
        rw [← (Equiv.subRight l).tsum_eq (fun n : ℤ => if (N : ℤ) < |n| then g n else 0)]
        refine tsum_congr (fun k => ?_)
        simp only [hF_def, hg_def, Equiv.subRight_apply]
        push_cast
        ring_nf
    _ ≤ ε := hN




theorem exists_truncation_norm_le {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ‖opOfMatrix A - opOfMatrix (truncation A N)‖ ≤ ε := by
  obtain ⟨N, hN⟩ := exists_truncationTail_col_bound h hε
  exact ⟨N, norm_sub_opOfMatrix_truncation_le h N hε.le hN⟩










theorem finiteDimensional_ker_of_perturbation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T T_N B : E →L[ℂ] E) (hTB : T ∘L B = 1)
    (hnorm : ‖T - T_N‖ * ‖B‖ < 1 / 2)
    (hTN_fin : ∀ R : E →L[ℂ] E, T_N ∘L R = 1 →
      FiniteDimensional ℂ (LinearMap.ker T_N.toLinearMap)) :
    FiniteDimensional ℂ (LinearMap.ker T.toLinearMap) := by

  set Er : E →L[ℂ] E := T - T_N with hEr
  set r : ℝ := ‖Er‖ * ‖B‖ with hr
  have hr_lt : r < 1 / 2 := hnorm
  have hr0 : 0 ≤ r := mul_nonneg (norm_nonneg _) (norm_nonneg _)

  have hErB_le : ‖Er * B‖ ≤ r := norm_mul_le Er B
  have hErB_lt : ‖Er * B‖ < 1 := lt_of_le_of_lt hErB_le (by linarith)

  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one (Er * B) hErB_lt
  have hu_norm : ‖(↑u⁻¹ : E →L[ℂ] E)‖ ≤ (1 - ‖Er * B‖)⁻¹ :=
    norm_inverse_one_sub_le (Er * B) hErB_lt u hu

  have hTB' : T * B = 1 := hTB
  have hErB_eq : Er * B = 1 - T_N * B := by
    rw [hEr, sub_mul, hTB']
  have hTNB : T_N * B = (↑u : E →L[ℂ] E) := by
    rw [hu, hErB_eq]; abel

  set R : E →L[ℂ] E := B * (↑u⁻¹ : E →L[ℂ] E) with hR
  have hTNR : T_N * R = 1 := by
    rw [hR, ← mul_assoc, hTNB, Units.mul_inv]

  have hRE_lt : ‖R * Er‖ < 1 := by
    have hstep : ‖R * Er‖ ≤ ‖B‖ * ‖(↑u⁻¹ : E →L[ℂ] E)‖ * ‖Er‖ := by
      calc ‖R * Er‖ ≤ ‖R‖ * ‖Er‖ := norm_mul_le _ _
        _ ≤ (‖B‖ * ‖(↑u⁻¹ : E →L[ℂ] E)‖) * ‖Er‖ := by
              gcongr; exact norm_mul_le _ _
        _ = ‖B‖ * ‖(↑u⁻¹ : E →L[ℂ] E)‖ * ‖Er‖ := by ring

    have hden_pos : 0 < 1 - ‖Er * B‖ := by linarith
    have h1 : ‖B‖ * ‖(↑u⁻¹ : E →L[ℂ] E)‖ * ‖Er‖ ≤ ‖B‖ * (1 - ‖Er * B‖)⁻¹ * ‖Er‖ := by
      gcongr
    have h2 : ‖B‖ * (1 - ‖Er * B‖)⁻¹ * ‖Er‖ ≤ r * (1 - r)⁻¹ := by
      rw [hr]
      have hle_inv : (1 - ‖Er * B‖)⁻¹ ≤ (1 - r)⁻¹ :=
        inv_anti₀ (by linarith) (by linarith)
      calc ‖B‖ * (1 - ‖Er * B‖)⁻¹ * ‖Er‖
          = (‖Er‖ * ‖B‖) * (1 - ‖Er * B‖)⁻¹ := by ring
        _ ≤ (‖Er‖ * ‖B‖) * (1 - r)⁻¹ := by
              gcongr
        _ = ‖Er‖ * ‖B‖ * (1 - r)⁻¹ := by ring
    have h3 : r * (1 - r)⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ (by linarith)]; linarith
    calc ‖R * Er‖ ≤ ‖B‖ * ‖(↑u⁻¹ : E →L[ℂ] E)‖ * ‖Er‖ := hstep
      _ ≤ ‖B‖ * (1 - ‖Er * B‖)⁻¹ * ‖Er‖ := h1
      _ ≤ r * (1 - r)⁻¹ := h2
      _ < 1 := h3

  set G : E →L[ℂ] E := 1 + R * Er with hG
  have hG_unit : IsUnit G := by
    have hneg : ‖-(R * Er)‖ < 1 := by rwa [norm_neg]
    have := isUnit_one_sub_of_norm_lt_one (-(R * Er)) hneg
    rwa [sub_neg_eq_add] at this
  have hG_inj : Function.Injective G :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hG_unit).injective

  have hmaps : ∀ x ∈ LinearMap.ker T.toLinearMap, G x ∈ LinearMap.ker T_N.toLinearMap := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢

    simp only [ContinuousLinearMap.coe_coe] at hx ⊢

    have hTx : (T : E → E) x = 0 := hx
    have hErx : (Er : E → E) x = - ((T_N : E → E) x) := by
      rw [hEr]; simp only [sub_apply, hTx, zero_sub]

    have hTNR_app : (T_N : E → E) ((R : E → E) ((Er : E → E) x)) = (Er : E → E) x := by
      have hcomp := congrArg (fun (f : E →L[ℂ] E) => (f : E → E) ((Er : E → E) x)) hTNR
      rw [mul_apply_eq_comp, one_apply_eq_self] at hcomp
      exact hcomp

    show (T_N : E → E) ((G : E → E) x) = 0
    rw [hG, add_apply, one_apply_eq_self, mul_apply_eq_comp, map_add, hTNR_app, hErx]
    abel

  haveI hTN_findim : FiniteDimensional ℂ (LinearMap.ker T_N.toLinearMap) := hTN_fin R hTNR

  set Φ : LinearMap.ker T.toLinearMap →ₗ[ℂ] LinearMap.ker T_N.toLinearMap :=
    (G : E →ₗ[ℂ] E).restrict hmaps with hΦ
  have hΦ_inj : Function.Injective Φ := by
    intro a b hab
    have : (G : E → E) (a : E) = (G : E → E) (b : E) := by
      have h := congrArg (Subtype.val) hab
      rwa [hΦ, LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply] at h
    exact Subtype.ext (hG_inj this)
  exact FiniteDimensional.of_injective Φ hΦ_inj









theorem exists_rightInverse_opOfMatrix {A : ℤ → ℤ → ℂ}
    (_hdecay : HasPolynomialOffDiagonalDecay A) (hsurj : Function.Surjective (opOfMatrix A)) :
    ∃ B : ℓ1 →L[ℂ] ℓ1, opOfMatrix A ∘L B = 1 := by
  classical
  set T : ℓ1 →L[ℂ] ℓ1 := opOfMatrix A with hT

  obtain ⟨C, hC0, hC⟩ := T.exists_preimage_norm_le hsurj

  set e : ℤ → ℓ1 := fun j => (lp.single 1 j (1 : ℂ) : ℓ1) with he
  have he_norm : ∀ j, ‖e j‖ = 1 := fun j => by rw [he, lp.norm_single (by norm_num)]; simp

  set b : ℤ → ℓ1 := fun j => (hC (e j)).choose with hb
  have hb_eq : ∀ j, T (b j) = e j := fun j => (hC (e j)).choose_spec.1
  have hb_norm : ∀ j, ‖b j‖ ≤ C := fun j => by
    have h := (hC (e j)).choose_spec.2
    calc ‖b j‖ ≤ C * ‖e j‖ := h
      _ = C := by rw [he_norm j, mul_one]

  have hterm : ∀ (y : ℓ1) (j : ℤ), ‖(y : ℤ → ℂ) j • b j‖ ≤ C * ‖(y : ℤ → ℂ) j‖ := by
    intro y j
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hb_norm j) (norm_nonneg _)

  have hsummable : ∀ y : ℓ1, Summable (fun j : ℤ => (y : ℤ → ℂ) j • b j) := by
    intro y
    have hy : Summable (fun j : ℤ => ‖(y : ℤ → ℂ) j‖) := memℓp_one_iff.mp (lp.memℓp y)
    exact Summable.of_norm_bounded (g := fun j : ℤ => C * ‖(y : ℤ → ℂ) j‖)
      (hy.mul_left C) (fun j => hterm y j)

  have hBbound : ∀ y : ℓ1, ‖∑' j : ℤ, (y : ℤ → ℂ) j • b j‖ ≤ C * ‖y‖ := by
    intro y
    have hy : Summable (fun j : ℤ => ‖(y : ℤ → ℂ) j‖) := memℓp_one_iff.mp (lp.memℓp y)
    have hsn : Summable (fun j : ℤ => ‖(y : ℤ → ℂ) j • b j‖) :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hterm y j) (hy.mul_left C)
    calc ‖∑' j : ℤ, (y : ℤ → ℂ) j • b j‖
        ≤ ∑' j : ℤ, ‖(y : ℤ → ℂ) j • b j‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' j : ℤ, C * ‖(y : ℤ → ℂ) j‖ := hsn.tsum_le_tsum (fun j => hterm y j) (hy.mul_left C)
      _ = C * ∑' j : ℤ, ‖(y : ℤ → ℂ) j‖ := tsum_mul_left
      _ = C * ‖y‖ := by rw [← norm_eq_tsum]

  set Bfun : ℓ1 →ₗ[ℂ] ℓ1 :=
    { toFun := fun y => ∑' j : ℤ, (y : ℤ → ℂ) j • b j
      map_add' := fun y z => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (hsummable y).tsum_add (hsummable z)
      map_smul' := fun c y => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul]
        exact (hsummable y).tsum_const_smul c } with hBfun

  set B : ℓ1 →L[ℂ] ℓ1 := Bfun.mkContinuous C hBbound with hBdef
  refine ⟨B, ?_⟩

  refine ContinuousLinearMap.ext (fun y => ?_)
  show T (B y) = y
  have hBy : (B y : ℓ1) = ∑' j : ℤ, (y : ℤ → ℂ) j • b j := rfl
  rw [hBy]
  rw [ContinuousLinearMap.map_tsum T (hsummable y)]

  have hstep : ∀ j : ℤ, T ((y : ℤ → ℂ) j • b j) = (lp.single 1 j ((y : ℤ → ℂ) j) : ℓ1) := by
    intro j
    rw [map_smul, hb_eq, he]
    rw [← lp.single_smul]
    congr 1
    simp
  rw [tsum_congr hstep]
  exact (lp.hasSum_single (by norm_num) y).tsum_eq














theorem row_truncation_eq_windowSum {A : ℤ → ℤ → ℂ}
    (hdecay : HasPolynomialOffDiagonalDecay A) (N : ℕ) (M : ℕ)
    (x : ℓ1) (i : ℤ) (hi : i ∈ Finset.Icc (-(M:ℤ)) (M:ℤ)) :
    (∑ l ∈ Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N), truncation A N i l * (x : ℤ → ℂ) l)
      = (opOfMatrix (truncation A N) x : ℤ → ℂ) i := by
  have hd := hasDecay_truncation hdecay N
  rw [opOfMatrix_apply hd]
  symm
  apply tsum_eq_sum
  intro l hl
  rw [Finset.mem_Icc] at hi
  rw [Finset.mem_Icc] at hl
  push_neg at hl
  unfold truncation
  have hnle : ¬ |i - l| ≤ (N:ℤ) := by
    rw [abs_le]; push_neg
    by_cases hcase : l < -(M:ℤ) - N
    · intro _; omega
    · intro _
      have : (M:ℤ) + N < l := hl (by omega)
      omega
  rw [if_neg hnle, zero_mul]



def finSection (A : ℤ → ℤ → ℂ) (N M : ℕ) :
    ({j : ℤ // j ∈ Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N)} → ℂ) →ₗ[ℂ]
    ({i : ℤ // i ∈ Finset.Icc (-(M:ℤ)) (M:ℤ)} → ℂ) where
  toFun z := fun i => ∑ j : {j : ℤ // j ∈ Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N)},
    truncation A N (i : ℤ) (j : ℤ) * z j
  map_add' z w := by
    funext i; simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  map_smul' c z := by
    funext i; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring

theorem finSection_apply (A : ℤ → ℤ → ℂ) (N M : ℕ)
    (z : {j : ℤ // j ∈ Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N)} → ℂ)
    (i : {i : ℤ // i ∈ Finset.Icc (-(M:ℤ)) (M:ℤ)}) :
    finSection A N M z i = ∑ j : {j : ℤ // j ∈ Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N)},
      truncation A N (i : ℤ) (j : ℤ) * z j := rfl


def resLM (N M : ℕ) : ℓ1 →ₗ[ℂ]
    ({j : ℤ // j ∈ Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N)} → ℂ) where
  toFun x := fun j => (x : ℤ → ℂ) (j : ℤ)
  map_add' x y := by funext j; simp
  map_smul' c x := by funext j; simp

theorem resLM_apply (N M : ℕ) (x : ℓ1)
    (j : {j : ℤ // j ∈ Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N)}) :
    resLM N M x j = (x : ℤ → ℂ) (j : ℤ) := rfl



theorem finSection_resLM_apply {A : ℤ → ℤ → ℂ} (hdecay : HasPolynomialOffDiagonalDecay A)
    (N M : ℕ) (x : ℓ1) (i : {i : ℤ // i ∈ Finset.Icc (-(M:ℤ)) (M:ℤ)}) :
    finSection A N M (resLM N M x) i = (opOfMatrix (truncation A N) x : ℤ → ℂ) (i : ℤ) := by
  rw [finSection_apply]
  rw [← row_truncation_eq_windowSum hdecay N M x (i : ℤ) i.2]
  rw [← Finset.sum_attach (Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N))
      (fun l => truncation A N (i:ℤ) l * (x : ℤ → ℂ) l)]
  rfl



def extLM (M : ℕ) (y : {i : ℤ // i ∈ Finset.Icc (-(M:ℤ)) (M:ℤ)} → ℂ) : ℓ1 :=
  ⟨fun k => if h : k ∈ Finset.Icc (-(M:ℤ)) (M:ℤ) then y ⟨k, h⟩ else 0, by
    refine memℓp_one_iff.mpr ?_
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(M:ℤ)) (M:ℤ))
    intro k hk
    rw [dif_neg hk, norm_zero]⟩

theorem extLM_apply_mem (M : ℕ) (y : {i : ℤ // i ∈ Finset.Icc (-(M:ℤ)) (M:ℤ)} → ℂ)
    (i : {i : ℤ // i ∈ Finset.Icc (-(M:ℤ)) (M:ℤ)}) :
    (extLM M y : ℤ → ℂ) (i : ℤ) = y i := by
  show (if h : (i:ℤ) ∈ Finset.Icc (-(M:ℤ)) (M:ℤ) then y ⟨(i:ℤ), h⟩ else 0) = y i
  rw [dif_pos i.2]




theorem finSection_surjective {A : ℤ → ℤ → ℂ} (hdecay : HasPolynomialOffDiagonalDecay A)
    (N M : ℕ) (R : ℓ1 →L[ℂ] ℓ1) (hR : opOfMatrix (truncation A N) ∘L R = 1) :
    Function.Surjective (finSection A N M) := by
  intro y
  set yext : ℓ1 := extLM M y with hyext
  set x : ℓ1 := R yext with hx
  refine ⟨resLM N M x, ?_⟩
  funext i
  rw [finSection_resLM_apply hdecay N M x i]
  have hTRx : opOfMatrix (truncation A N) x = yext := by
    have := ContinuousLinearMap.ext_iff.mp hR yext
    simpa [hx] using this
  rw [hTRx, hyext, extLM_apply_mem]





theorem exists_resLM_injOn (N : ℕ) (U : Submodule ℂ ℓ1) [FiniteDimensional ℂ U] :
    ∃ M : ℕ, ∀ x : ℓ1, x ∈ U → resLM N M x = 0 → x = 0 := by
  obtain ⟨M, hM⟩ := LimitOps.finiteDim_tail_small U (ε := 1/2) (by norm_num)
  refine ⟨M, fun x hxU hres => ?_⟩
  have hproj : projCLM M x = 0 := by
    apply lp.ext
    funext k
    rw [projCLM_apply]
    by_cases hk : |k| ≤ (M:ℤ)
    · rw [if_pos hk]
      have hkmem : k ∈ Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N) := by
        rw [Finset.mem_Icc]; rw [abs_le] at hk; omega
      have := congrFun hres ⟨k, hkmem⟩
      rw [resLM_apply] at this
      simpa using this
    · rw [if_neg hk]; rfl
  have hxq : x = QCLM M x := by
    have : QCLM M x = x - projCLM M x := by simp [QCLM]
    rw [this, hproj, sub_zero]
  have hnorm : ‖x‖ ≤ (1/2) * ‖x‖ := by
    conv_lhs => rw [hxq]
    exact hM x hxU
  rw [← norm_le_zero_iff]
  linarith [norm_nonneg x]


theorem card_windows (N M : ℕ) :
    Fintype.card {j : ℤ // j ∈ Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N)}
      = Fintype.card {i : ℤ // i ∈ Finset.Icc (-(M:ℤ)) (M:ℤ)} + 2 * N := by
  rw [Fintype.card_coe, Fintype.card_coe]
  have h1 : ((Finset.Icc (-(M:ℤ) - N) ((M:ℤ) + N)).card : ℤ) = 2*M + 2*N + 1 := by
    have := Int.card_Icc_of_le (-(M:ℤ) - N) ((M:ℤ) + N) (by omega)
    rw [this]; ring
  have h2 : ((Finset.Icc (-(M:ℤ)) (M:ℤ)).card : ℤ) = 2*M + 1 := by
    have := Int.card_Icc_of_le (-(M:ℤ)) (M:ℤ) (by omega)
    rw [this]; ring
  omega



theorem finrank_ker_finSection_le {A : ℤ → ℤ → ℂ} (hdecay : HasPolynomialOffDiagonalDecay A)
    (N M : ℕ) (R : ℓ1 →L[ℂ] ℓ1) (hR : opOfMatrix (truncation A N) ∘L R = 1) :
    Module.finrank ℂ (LinearMap.ker (finSection A N M)) ≤ 2 * N := by
  have hsurj := finSection_surjective hdecay N M R hR
  have hrn := (finSection A N M).finrank_range_add_finrank_ker
  have hrange : LinearMap.range (finSection A N M) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  rw [hrange, finrank_top] at hrn
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hrn
  have hcard := card_windows N M
  omega











theorem card_le_of_linearIndependent_ker_truncation {A : ℤ → ℤ → ℂ}
    (hdecay : HasPolynomialOffDiagonalDecay A) (N : ℕ)
    (R : ℓ1 →L[ℂ] ℓ1) (hR : opOfMatrix (truncation A N) ∘L R = 1)
    (s : Finset (LinearMap.ker (opOfMatrix (truncation A N)).toLinearMap))
    (hs : LinearIndependent ℂ (fun i : s => (i : LinearMap.ker
      (opOfMatrix (truncation A N)).toLinearMap))) :
    s.card ≤ 2 * N := by

  let K := LinearMap.ker (opOfMatrix (truncation A N)).toLinearMap
  let v : s → K := fun i => (i : K)
  have hspanfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range v)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  let U : Submodule ℂ ℓ1 := Submodule.map K.subtype (Submodule.span ℂ (Set.range v))
  haveI : FiniteDimensional ℂ U := inferInstanceAs
    (FiniteDimensional ℂ (Submodule.map K.subtype (Submodule.span ℂ (Set.range v))))
  obtain ⟨M, hMinj⟩ := exists_resLM_injOn N U

  have hmaps : ∀ x : K, resLM N M (x : ℓ1) ∈ LinearMap.ker (finSection A N M) := by
    intro x
    rw [LinearMap.mem_ker]
    funext i
    rw [finSection_resLM_apply hdecay N M (x : ℓ1) i]
    have hx0 : opOfMatrix (truncation A N) (x : ℓ1) = 0 := by
      have hxk : (opOfMatrix (truncation A N)).toLinearMap (x : ℓ1) = 0 :=
        LinearMap.mem_ker.mp x.2
      exact hxk
    rw [hx0]; rfl
  let Ψ : K →ₗ[ℂ] LinearMap.ker (finSection A N M) :=
    LinearMap.codRestrict _ ((resLM N M).comp K.subtype) hmaps

  have hindep : LinearIndependent ℂ (Ψ ∘ v) := by
    apply hs.map (f := Ψ)
    rw [Submodule.disjoint_def]
    intro w hw hwker
    have hres0 : resLM N M (w : ℓ1) = 0 := by
      have h2 := congrArg (Subtype.val) (LinearMap.mem_ker.mp hwker)
      rw [LinearMap.codRestrict_apply] at h2
      simpa using h2
    have hwU : (w : ℓ1) ∈ U := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
    exact Subtype.ext (hMinj (w : ℓ1) hwU hres0)

  have hcard : Fintype.card s ≤ Module.finrank ℂ (LinearMap.ker (finSection A N M)) :=
    hindep.fintype_card_le_finrank
  have hle := finrank_ker_finSection_le hdecay N M R hR
  rw [Fintype.card_coe] at hcard
  omega





theorem finiteDimensional_ker_truncation {A : ℤ → ℤ → ℂ}
    (hdecay : HasPolynomialOffDiagonalDecay A) (N : ℕ)
    (R : ℓ1 →L[ℂ] ℓ1) (hR : opOfMatrix (truncation A N) ∘L R = 1) :
    FiniteDimensional ℂ (LinearMap.ker (opOfMatrix (truncation A N)).toLinearMap) := by

  have hrank : Module.rank ℂ (LinearMap.ker (opOfMatrix (truncation A N)).toLinearMap)
      ≤ ((2 * N : ℕ) : Cardinal) :=
    rank_le (fun s hs => card_le_of_linearIndependent_ker_truncation hdecay N R hR s hs)
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  exact lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0 ..)



theorem thm_surjectivity_implies_Fredholm (A : ℤ → ℤ → ℂ)
    (hdecay : HasPolynomialOffDiagonalDecay A) (hsurj : MatrixSurjectiveOnEllOne A) :
    Fredholm (opOfMatrix A) := by
  have hsurj_op : Function.Surjective (opOfMatrix A) :=
    surjective_opOfMatrix A hdecay hsurj
  refine
    { isClosed_range := isClosed_range_opOfMatrix A hsurj_op
      finiteDimensional_ker := ?_
      finiteDimensional_coker := finiteDimensional_coker_opOfMatrix A hsurj_op }


  obtain ⟨B, hB⟩ := exists_rightInverse_opOfMatrix hdecay hsurj_op

  have hεpos : (0 : ℝ) < 1 / (2 * (‖B‖ + 1)) := by positivity
  obtain ⟨N, hN⟩ := exists_truncation_norm_le hdecay hεpos
  have hnorm : ‖opOfMatrix A - opOfMatrix (truncation A N)‖ * ‖B‖ < 1 / 2 := by
    have hBnn : (0 : ℝ) ≤ ‖B‖ := norm_nonneg _
    calc ‖opOfMatrix A - opOfMatrix (truncation A N)‖ * ‖B‖
        ≤ (1 / (2 * (‖B‖ + 1))) * ‖B‖ := by gcongr
      _ < 1 / 2 := by
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
          ring_nf
          nlinarith [hBnn]

  exact finiteDimensional_ker_of_perturbation (opOfMatrix A) (opOfMatrix (truncation A N)) B hB
    hnorm (fun R hR => finiteDimensional_ker_truncation hdecay N R hR)

end LimitOps