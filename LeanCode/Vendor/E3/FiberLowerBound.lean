import LeanCode.Vendor.E3.PreGramian

open scoped ENNReal

namespace VendorE3
noncomputable section









theorem preGramian_apply_selected_eq_submatrix_apply
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ)
    {x : ℝ} {δ : ℤ → ℝ} {ν : ℤ → ℤ}
    (hsel : ∀ k : ℤ, x + α * (ν k : ℝ) = (k : ℝ) + δ k)
    (T : ellp (2 : ℝ≥0∞) →L[ℂ] ellp (2 : ℝ≥0∞))
    (hT : IsMatrixOperator (2 : ℝ≥0∞) (GaborSubmatrix g δ) T)
    (c : ellp (2 : ℝ≥0∞)) (k : ℤ) :
    (preGramianOperator g α C σ hα hdec x c) (ν k) = (T c) k := by
  have hP :=
    preGramianOperator_isMatrixOperator g α C σ hα hdec x c (ν k)
  have hTk := hT c k
  rw [hP.2, hTk.2]
  apply tsum_congr
  intro l
  dsimp [preGramianMatrix, GaborSubmatrix]
  rw [hsel k]


theorem preGramian_lower_bound_at
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ)
    {x : ℝ} {δ : ℤ → ℝ} {ν : ℤ → ℤ}
    (hν : Function.Injective ν)
    (hsel : ∀ k : ℤ, x + α * (ν k : ℝ) = (k : ℝ) + δ k)
    (hinv : MatrixInvertibleOn (2 : ℝ≥0∞) (GaborSubmatrix g δ)) :
    ∃ a : ℝ, 0 < a ∧
      ∀ c : ellp (2 : ℝ≥0∞),
        a * ‖c‖ ≤ ‖preGramianOperator g α C σ hα hdec x c‖ := by
  rcases hinv with ⟨T, hT, hunit⟩
  rcases hunit.exists_left_inv with ⟨U, hUTmul⟩
  have hUT : ∀ c : ellp (2 : ℝ≥0∞), U (T c) = c := by
    intro c
    have h := congrArg
      (fun L : ellp (2 : ℝ≥0∞) →L[ℂ] ellp (2 : ℝ≥0∞) => L c) hUTmul
    simpa using h
  let a0 : ℝ := 1 / (1 + ‖U‖)
  have ha0 : 0 < a0 := by
    dsimp [a0]
    positivity
  refine ⟨a0, ha0, ?_⟩
  intro c
  let P := preGramianOperator g α C σ hα hdec x
  have hlowerT := lower_bound_of_left_inverse T U hUT c
  have hcoord : ∀ k : ℤ, (T c) k = (P c) (ν k) := by
    intro k
    have hselk :=
      preGramian_apply_selected_eq_submatrix_apply
        g α C σ hα hdec hsel T hT c k
    exact hselk.symm
  have hsummP : Summable (fun j : ℤ => ‖(P c) j‖ ^ 2) := by
    simpa using (lp.memℓp (P c)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hsubseries :=
    tsum_comp_le_tsum_of_injective_nonneg
      (b := fun j : ℤ => ‖(P c) j‖ ^ 2)
      (fun _j => sq_nonneg _) hsummP hν
  have htsum_le :
      (∑' k : ℤ, ‖(T c) k‖ ^ 2) ≤
        ∑' j : ℤ, ‖(P c) j‖ ^ 2 := by
    calc
      (∑' k : ℤ, ‖(T c) k‖ ^ 2)
          = ∑' k : ℤ, ‖(P c) (ν k)‖ ^ 2 := by
            apply tsum_congr
            intro k
            rw [hcoord k]
      _ ≤ ∑' j : ℤ, ‖(P c) j‖ ^ 2 := hsubseries.2
  have hnormsq_le : ‖T c‖ ^ 2 ≤ ‖P c‖ ^ 2 := by
    have hTnorm :
        ‖T c‖ ^ 2 = ∑' k : ℤ, ‖(T c) k‖ ^ 2 := by
      simpa using
        (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ)
          (by norm_num) (T c))
    have hPnorm :
        ‖P c‖ ^ 2 = ∑' j : ℤ, ‖(P c) j‖ ^ 2 := by
      simpa using
        (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ)
          (by norm_num) (P c))
    rw [hTnorm, hPnorm]
    exact htsum_le
  have hnorm_le : ‖T c‖ ≤ ‖P c‖ := by
    have h := sq_le_sq.mp hnormsq_le
    simpa [abs_of_nonneg (norm_nonneg _)] using h
  exact hlowerT.trans hnorm_le


theorem preGramian_uniform_lower_bound_Icc
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hgc : Continuous g) (hα : 0 < α)
    (hdec : HasDecayWithConstants g C σ)
    (hsub : SubmatrixCondition g α) :
    ∃ a : ℝ, 0 < a ∧
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
        ∀ c : ellp (2 : ℝ≥0∞),
          a * ‖c‖ ≤ ‖preGramianOperator g α C σ hα hdec x c‖ := by
  classical
  let P : ℝ → ellp (2 : ℝ≥0∞) →L[ℂ] ellp (2 : ℝ≥0∞) :=
    fun x => preGramianOperator g α C σ hα hdec x
  have hpoint : ∀ x : ℝ, ∃ a : ℝ, 0 < a ∧
      ∀ c : ellp (2 : ℝ≥0∞), a * ‖c‖ ≤ ‖P x c‖ := by
    intro x
    rcases hsub x with ⟨δ, ν, hν, hsel, hinv⟩
    simpa [P] using
      preGramian_lower_bound_at g α C σ hα hdec hν hsel hinv
  let lowerConst : ℝ → ℝ := fun x => Classical.choose (hpoint x)
  have lowerConst_pos : ∀ x : ℝ, 0 < lowerConst x := by
    intro x
    exact (Classical.choose_spec (hpoint x)).1
  have lowerConst_bound :
      ∀ x : ℝ, ∀ c : ellp (2 : ℝ≥0∞),
        lowerConst x * ‖c‖ ≤ ‖P x c‖ := by
    intro x
    exact (Classical.choose_spec (hpoint x)).2
  let radius : ℝ → ℝ := fun x =>
    Classical.choose
      (preGramian_norm_continuous_uniform g α C σ hgc hα hdec
        (lowerConst x / 2) (half_pos (lowerConst_pos x)))
  have radius_spec :
      ∀ x : ℝ, 0 < radius x ∧
        ∀ y h : ℝ, |h| ≤ radius x →
          ‖P (y + h) - P y‖ ≤ lowerConst x / 2 := by
    intro x
    simpa [radius, P] using
      Classical.choose_spec
        (preGramian_norm_continuous_uniform g α C σ hgc hα hdec
          (lowerConst x / 2) (half_pos (lowerConst_pos x)))
  have radius_pos : ∀ x : ℝ, 0 < radius x := fun x => (radius_spec x).1
  obtain ⟨t, ht_subset, hcover⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).elim_nhds_subcover
      (fun x : ℝ => Metric.ball x (radius x))
      (by
        intro x _hx
        exact Metric.ball_mem_nhds x (radius_pos x))
  have ht_nonempty : t.Nonempty := by
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    have hzcover := hcover hzero
    rcases Set.mem_iUnion.mp hzcover with ⟨x0, hx0⟩
    rcases Set.mem_iUnion.mp hx0 with ⟨hx0t, _hxball⟩
    exact ⟨x0, hx0t⟩
  let a : ℝ := t.inf' ht_nonempty (fun x => lowerConst x / 2)
  have ha : 0 < a := by
    dsimp [a]
    rw [Finset.lt_inf'_iff]
    intro x _hx
    exact half_pos (lowerConst_pos x)
  refine ⟨a, ha, ?_⟩
  intro x hx c
  have hxcover := hcover hx
  rcases Set.mem_iUnion.mp hxcover with ⟨x0, hx0⟩
  rcases Set.mem_iUnion.mp hx0 with ⟨hx0t, hxball⟩
  have ha_le_local : a ≤ lowerConst x0 / 2 := by
    dsimp [a]
    exact Finset.inf'_le (fun x => lowerConst x / 2) hx0t
  have hdist_lt : dist x x0 < radius x0 := by
    simpa [Metric.mem_ball] using hxball
  have habs_le : |x - x0| ≤ radius x0 := by
    simpa [Real.dist_eq] using hdist_lt.le
  have hcont_yx : ‖P x - P x0‖ ≤ lowerConst x0 / 2 := by
    have hcont := (radius_spec x0).2 x0 (x - x0) habs_le
    simpa [P, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcont
  have hcont_xy : ‖P x0 - P x‖ ≤ lowerConst x0 / 2 := by
    have hneg : P x0 - P x = -(P x - P x0) := by
      ext c j
      simp
    rw [hneg, norm_neg]
    exact hcont_yx
  have hdecomp : P x0 c = P x c + ((P x0 - P x) c) := by
    simp [P]
  have hPx0_le :
      ‖P x0 c‖ ≤ ‖P x c‖ + (lowerConst x0 / 2) * ‖c‖ := by
    calc
      ‖P x0 c‖ = ‖P x c + ((P x0 - P x) c)‖ := by rw [hdecomp]
      _ ≤ ‖P x c‖ + ‖((P x0 - P x) c)‖ := norm_add_le _ _
      _ ≤ ‖P x c‖ + ‖P x0 - P x‖ * ‖c‖ := by
            have hop := (P x0 - P x).le_opNorm c
            nlinarith
      _ ≤ ‖P x c‖ + (lowerConst x0 / 2) * ‖c‖ := by
            have hmul := mul_le_mul_of_nonneg_right hcont_xy (norm_nonneg c)
            nlinarith
  have hlocal_lower : (lowerConst x0 / 2) * ‖c‖ ≤ ‖P x c‖ := by
    have hlow := lowerConst_bound x0 c
    have hmain : lowerConst x0 * ‖c‖ ≤
        ‖P x c‖ + (lowerConst x0 / 2) * ‖c‖ :=
      hlow.trans hPx0_le
    nlinarith [lowerConst_pos x0, norm_nonneg c, norm_nonneg (P x c)]
  calc
    a * ‖c‖ ≤ (lowerConst x0 / 2) * ‖c‖ := by
      exact mul_le_mul_of_nonneg_right ha_le_local (norm_nonneg c)
    _ ≤ ‖P x c‖ := hlocal_lower


theorem preGramian_two_sided_bound_Icc
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hgc : Continuous g) (hα : 0 < α)
    (hdec : HasDecayWithConstants g C σ)
    (hsub : SubmatrixCondition g α) :
    ∃ a : ℝ, 0 < a ∧ a ≤ preGramianNormBound C σ α ∧
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
        ∀ c : ellp (2 : ℝ≥0∞),
          a ^ 2 * ‖c‖ ^ 2 ≤
              ‖preGramianOperator g α C σ hα hdec x c‖ ^ 2 ∧
            ‖preGramianOperator g α C σ hα hdec x c‖ ^ 2 ≤
              preGramianBesselBound C σ α * ‖c‖ ^ 2 := by
  obtain ⟨a0, ha0, hlow0⟩ :=
    preGramian_uniform_lower_bound_Icc g α C σ hgc hα hdec hsub
  have hC : 0 < C := hdec.1
  have hσ : 1 < σ := hdec.2.1
  have hrow_pos : 0 < preGramianRowBound C σ := by
    dsimp [preGramianRowBound]
    have hone : 1 ≤ masterSeries 1 σ := one_le_masterSeries (by norm_num) hσ
    nlinarith [hC, hone]
  have hcol_pos : 0 < preGramianColBound C σ α := by
    dsimp [preGramianColBound]
    have hone : 1 ≤ masterSeries α σ := one_le_masterSeries hα hσ
    nlinarith [hC, hone]
  let M := preGramianNormBound C σ α
  have hMpos : 0 < M := by
    dsimp [M, preGramianNormBound]
    exact Real.sqrt_pos.2 (mul_pos hrow_pos hcol_pos)
  refine ⟨min a0 M, lt_min ha0 hMpos, min_le_right _ _, ?_⟩
  intro x hx c
  constructor
  · have hlow : min a0 M * ‖c‖ ≤
        ‖preGramianOperator g α C σ hα hdec x c‖ := by
      calc
        min a0 M * ‖c‖ ≤ a0 * ‖c‖ := by
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg c)
        _ ≤ ‖preGramianOperator g α C σ hα hdec x c‖ := hlow0 x hx c
    have hleft_nonneg : 0 ≤ min a0 M * ‖c‖ := by
      exact mul_nonneg (le_of_lt (lt_min ha0 hMpos)) (norm_nonneg c)
    have hright_nonneg :
        0 ≤ ‖preGramianOperator g α C σ hα hdec x c‖ := norm_nonneg _
    calc
      (min a0 M) ^ 2 * ‖c‖ ^ 2 = (min a0 M * ‖c‖) ^ 2 := by ring
      _ ≤ ‖preGramianOperator g α C σ hα hdec x c‖ ^ 2 := by
        nlinarith
  · exact preGramian_norm_sq_le g α C σ hα hdec x c

end

end VendorE3
