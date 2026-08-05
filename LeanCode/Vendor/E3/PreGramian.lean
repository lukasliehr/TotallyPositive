import LeanCode.Vendor.E3.Schur

open scoped ENNReal

namespace VendorE3
noncomputable section








def preGramianMatrix (g : ℝ → ℝ) (α x : ℝ) : ℤ → ℤ → ℂ :=
  fun j l => (g (x + α * (j : ℝ) - (l : ℝ)) : ℂ)


def preGramianRowBound (C σ : ℝ) : ℝ :=
  2 * C * masterSeries 1 σ


def preGramianColBound (C σ α : ℝ) : ℝ :=
  2 * C * masterSeries α σ


def preGramianNormBound (C σ α : ℝ) : ℝ :=
  Real.sqrt (preGramianRowBound C σ * preGramianColBound C σ α)


def preGramianBesselBound (C σ α : ℝ) : ℝ :=
  preGramianNormBound C σ α ^ 2



theorem preGramian_row_col_bounds
    {g : ℝ → ℝ} {C σ α x : ℝ}
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ) :
    SchurBounds (preGramianMatrix g α x)
      (preGramianRowBound C σ) (preGramianColBound C σ α) := by
  have hC : 0 < C := hdec.1
  have hσ : 1 < σ := hdec.2.1
  refine
    { R_nonneg := ?_
      S_nonneg := ?_
      row_summable := ?_
      row_bound := ?_
      col_summable := ?_
      col_bound := ?_ }
  · dsimp [preGramianRowBound]
    have hone : 1 ≤ masterSeries 1 σ := one_le_masterSeries (by norm_num) hσ
    nlinarith
  · dsimp [preGramianColBound]
    have hone : 1 ≤ masterSeries α σ := one_le_masterSeries hα hσ
    nlinarith
  · intro j
    obtain ⟨hrow, _hcol, _hsq⟩ :=
      window_lattice_row_sums (g := g) (C := C) (σ := σ) (α := α)
        (y := x + α * (j : ℝ)) hα hdec
    simpa [preGramianMatrix] using hrow.1
  · intro j
    obtain ⟨hrow, _hcol, _hsq⟩ :=
      window_lattice_row_sums (g := g) (C := C) (σ := σ) (α := α)
        (y := x + α * (j : ℝ)) hα hdec
    simpa [preGramianMatrix, preGramianRowBound] using hrow.2
  · intro k
    obtain ⟨_hrow, hcol, _hsq⟩ :=
      window_lattice_row_sums (g := g) (C := C) (σ := σ) (α := α)
        (y := x - (k : ℝ)) hα hdec
    have hfun :
        (fun j : ℤ => ‖preGramianMatrix g α x j k‖) =
          fun j : ℤ => |g ((x - (k : ℝ)) + α * (j : ℝ))| := by
      funext j
      have harg :
          x + α * (j : ℝ) - (k : ℝ) =
            (x - (k : ℝ)) + α * (j : ℝ) := by ring
      simp [preGramianMatrix, harg]
    rw [hfun]
    exact hcol.1
  · intro k
    obtain ⟨_hrow, hcol, _hsq⟩ :=
      window_lattice_row_sums (g := g) (C := C) (σ := σ) (α := α)
        (y := x - (k : ℝ)) hα hdec
    have hfun :
        (fun j : ℤ => ‖preGramianMatrix g α x j k‖) =
          fun j : ℤ => |g ((x - (k : ℝ)) + α * (j : ℝ))| := by
      funext j
      have harg :
          x + α * (j : ℝ) - (k : ℝ) =
            (x - (k : ℝ)) + α * (j : ℝ) := by ring
      simp [preGramianMatrix, harg]
    rw [hfun]
    simpa [preGramianColBound] using hcol.2


theorem submatrix_row_bound
    {g : ℝ → ℝ} {C σ : ℝ} (hdec : HasDecayWithConstants g C σ)
    (δ : ℤ → ℝ) (k : ℤ) :
    Summable (fun l : ℤ => ‖GaborSubmatrix g δ k l‖) ∧
      (∑' l : ℤ, ‖GaborSubmatrix g δ k l‖) ≤ preGramianRowBound C σ := by
  obtain ⟨hrow, _hcol, _hsq⟩ :=
    window_lattice_row_sums (g := g) (C := C) (σ := σ) (α := 1)
      (y := (k : ℝ) + δ k) (by norm_num) hdec
  constructor
  · simpa [GaborSubmatrix] using hrow.1
  · simpa [GaborSubmatrix, preGramianRowBound] using hrow.2


def preGramianOperator
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ) (x : ℝ) :
    ellp (2 : ℝ≥0∞) →L[ℂ] ellp (2 : ℝ≥0∞) :=
  schurOperator (preGramianMatrix g α x)
    (preGramianRowBound C σ) (preGramianColBound C σ α)
    (preGramian_row_col_bounds hα hdec)


theorem preGramianOperator_isMatrixOperator
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ) (x : ℝ) :
    IsMatrixOperator (2 : ℝ≥0∞) (preGramianMatrix g α x)
      (preGramianOperator g α C σ hα hdec x) := by
  dsimp [preGramianOperator]
  exact schurOperator_isMatrixOperator
    (preGramianMatrix g α x)
    (preGramianRowBound C σ) (preGramianColBound C σ α)
    (preGramian_row_col_bounds hα hdec)


theorem preGramian_opNorm_le
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ) (x : ℝ) :
    ‖preGramianOperator g α C σ hα hdec x‖ ≤
      preGramianNormBound C σ α := by
  dsimp [preGramianOperator, preGramianNormBound]
  exact schurOperator_norm_le
    (preGramianMatrix g α x)
    (preGramianRowBound C σ) (preGramianColBound C σ α)
    (preGramian_row_col_bounds hα hdec)


theorem preGramian_norm_sq_le
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ)
    (x : ℝ) (c : ellp (2 : ℝ≥0∞)) :
    ‖preGramianOperator g α C σ hα hdec x c‖ ^ 2 ≤
      preGramianBesselBound C σ α * ‖c‖ ^ 2 := by
  let P := preGramianOperator g α C σ hα hdec x
  let M := preGramianNormBound C σ α
  have hnorm : ‖P c‖ ≤ M * ‖c‖ := by
    calc
      ‖P c‖ ≤ ‖P‖ * ‖c‖ := P.le_opNorm c
      _ ≤ M * ‖c‖ := by
        exact mul_le_mul_of_nonneg_right
          (by simpa [P, M] using preGramian_opNorm_le g α C σ hα hdec x)
          (norm_nonneg c)
  have hPc_nonneg : 0 ≤ ‖P c‖ := norm_nonneg _
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, preGramianNormBound]
    exact Real.sqrt_nonneg _
  have hMc_nonneg : 0 ≤ M * ‖c‖ := mul_nonneg hM_nonneg (norm_nonneg c)
  calc
    ‖preGramianOperator g α C σ hα hdec x c‖ ^ 2 ≤ (M * ‖c‖) ^ 2 := by
      change ‖P c‖ ^ 2 ≤ (M * ‖c‖) ^ 2
      nlinarith
    _ = preGramianBesselBound C σ α * ‖c‖ ^ 2 := by
      dsimp [M, preGramianBesselBound]
      ring



theorem preGramian_sub_apply
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ)
    (x h : ℝ) (c : ellp (2 : ℝ≥0∞)) (j : ℤ) :
    ((preGramianOperator g α C σ hα hdec (x + h) -
        preGramianOperator g α C σ hα hdec x) c) j =
      ∑' l : ℤ,
        c l * ((g (x + h + α * (j : ℝ) - (l : ℝ)) : ℂ) -
          (g (x + α * (j : ℝ) - (l : ℝ)) : ℂ)) := by
  let P1 := preGramianOperator g α C σ hα hdec (x + h)
  let P0 := preGramianOperator g α C σ hα hdec x
  let A1 := preGramianMatrix g α (x + h)
  let A0 := preGramianMatrix g α x
  have h1 := preGramianOperator_isMatrixOperator g α C σ hα hdec (x + h) c j
  have h0 := preGramianOperator_isMatrixOperator g α C σ hα hdec x c j
  have hsubsum :
      (∑' l : ℤ, (A1 j l * c l - A0 j l * c l)) =
        (∑' l : ℤ, A1 j l * c l) - (∑' l : ℤ, A0 j l * c l) := by
    exact h1.1.tsum_sub h0.1
  have hcongr :
      (∑' l : ℤ, (A1 j l * c l - A0 j l * c l)) =
        ∑' l : ℤ,
          c l * ((g (x + h + α * (j : ℝ) - (l : ℝ)) : ℂ) -
            (g (x + α * (j : ℝ) - (l : ℝ)) : ℂ)) := by
    apply tsum_congr
    intro l
    dsimp [A1, A0, preGramianMatrix]
    ring
  calc
    ((preGramianOperator g α C σ hα hdec (x + h) -
        preGramianOperator g α C σ hα hdec x) c) j
        = (P1 c) j - (P0 c) j := by
          simp [P1, P0]
    _ = (∑' l : ℤ, A1 j l * c l) - (∑' l : ℤ, A0 j l * c l) := by
          rw [h1.2, h0.2]
    _ = (∑' l : ℤ, (A1 j l * c l - A0 j l * c l)) := hsubsum.symm
    _ = ∑' l : ℤ,
        c l * ((g (x + h + α * (j : ℝ) - (l : ℝ)) : ℂ) -
          (g (x + α * (j : ℝ) - (l : ℝ)) : ℂ)) := hcongr


theorem preGramian_norm_continuous_uniform
    (g : ℝ → ℝ) (α C σ : ℝ)
    (hgc : Continuous g) (hα : 0 < α) (hdec : HasDecayWithConstants g C σ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x h : ℝ, |h| ≤ δ →
        ‖preGramianOperator g α C σ hα hdec (x + h) -
          preGramianOperator g α C σ hα hdec x‖ ≤ ε := by
  intro ε hε
  have hpoly : HasPolynomialDecay g := ⟨C, σ, hdec.1, hdec.2.1, hdec.2.2⟩
  obtain ⟨δrow, hδrow_pos, _hδrow_le, hδrow⟩ :=
    summable_shift_difference_uniform
      (g := g) (a := 1) hgc hpoly (by norm_num) hε
  obtain ⟨δcol, hδcol_pos, _hδcol_le, hδcol⟩ :=
    summable_shift_difference_uniform
      (g := g) (a := α) hgc hpoly hα hε
  refine ⟨min δrow δcol, lt_min hδrow_pos hδcol_pos, ?_⟩
  intro x h hh
  have hhrow : |h| ≤ δrow := hh.trans (min_le_left _ _)
  have hhcol : |h| ≤ δcol := hh.trans (min_le_right _ _)
  let D : ℤ → ℤ → ℂ := fun j l =>
    ((g (x + h + α * (j : ℝ) - (l : ℝ)) -
      g (x + α * (j : ℝ) - (l : ℝ))) : ℂ)
  have hD : SchurBounds D ε ε := by
    refine
      { R_nonneg := hε.le
        S_nonneg := hε.le
        row_summable := ?_
        row_bound := ?_
        col_summable := ?_
        col_bound := ?_ }
    · intro j
      have hrow := (hδrow h (x + α * (j : ℝ)) hhrow).1
      have hcomp :
          Summable (fun l : ℤ =>
            |g ((x + α * (j : ℝ)) + h + 1 * ((-l : ℤ) : ℝ)) -
              g ((x + α * (j : ℝ)) + 1 * ((-l : ℤ) : ℝ))|) :=
        hrow.comp_injective (Equiv.neg ℤ).injective
      have hfun :
          (fun l : ℤ => ‖D j l‖) =
            fun l : ℤ =>
              |g ((x + α * (j : ℝ)) + h + 1 * ((-l : ℤ) : ℝ)) -
                g ((x + α * (j : ℝ)) + 1 * ((-l : ℤ) : ℝ))| := by
        funext l
        dsimp [D]
        rw [show x + h + α * (j : ℝ) - (l : ℝ) =
            (x + α * (j : ℝ)) + h + 1 * ((-l : ℤ) : ℝ) by
              norm_num
              ring,
          show x + α * (j : ℝ) - (l : ℝ) =
            (x + α * (j : ℝ)) + 1 * ((-l : ℤ) : ℝ) by
              norm_num
              ring]
        simpa only [← Complex.ofReal_sub, Real.norm_eq_abs] using
          (Complex.norm_real
            (g ((x + α * (j : ℝ)) + h + 1 * ((-l : ℤ) : ℝ)) -
              g ((x + α * (j : ℝ)) + 1 * ((-l : ℤ) : ℝ))))
      rw [hfun]
      exact hcomp
    · intro j
      have hrow := hδrow h (x + α * (j : ℝ)) hhrow
      let r : ℤ → ℝ := fun n =>
        |g ((x + α * (j : ℝ)) + h + 1 * (n : ℝ)) -
          g ((x + α * (j : ℝ)) + 1 * (n : ℝ))|
      have hfun :
          (fun l : ℤ => ‖D j l‖) = fun l : ℤ => r (-l) := by
        funext l
        dsimp [D, r]
        rw [show x + h + α * (j : ℝ) - (l : ℝ) =
            (x + α * (j : ℝ)) + h + 1 * ((-l : ℤ) : ℝ) by
              norm_num
              ring,
          show x + α * (j : ℝ) - (l : ℝ) =
            (x + α * (j : ℝ)) + 1 * ((-l : ℤ) : ℝ) by
              norm_num
              ring]
        simpa only [← Complex.ofReal_sub, Real.norm_eq_abs] using
          (Complex.norm_real
            (g ((x + α * (j : ℝ)) + h + 1 * ((-l : ℤ) : ℝ)) -
              g ((x + α * (j : ℝ)) + 1 * ((-l : ℤ) : ℝ))))
      have htsum :
          (∑' l : ℤ, r (-l)) = ∑' n : ℤ, r n := by
        exact (Equiv.neg ℤ).tsum_eq r
      calc
        (∑' l : ℤ, ‖D j l‖)
            = ∑' l : ℤ, r (-l) := by rw [hfun]
        _ = ∑' n : ℤ, r n := htsum
        _ ≤ ε := by
              simpa [r] using hrow.2
    · intro l
      have hcol := (hδcol h (x - (l : ℝ)) hhcol).1
      have hfun :
          (fun j : ℤ => ‖D j l‖) =
            fun j : ℤ =>
              |g ((x - (l : ℝ)) + h + α * (j : ℝ)) -
                g ((x - (l : ℝ)) + α * (j : ℝ))| := by
        funext j
        dsimp [D]
        rw [show x + h + α * (j : ℝ) - (l : ℝ) =
            (x - (l : ℝ)) + h + α * (j : ℝ) by ring,
          show x + α * (j : ℝ) - (l : ℝ) =
            (x - (l : ℝ)) + α * (j : ℝ) by ring]
        simpa only [← Complex.ofReal_sub, Real.norm_eq_abs] using
          (Complex.norm_real
            (g ((x - (l : ℝ)) + h + α * (j : ℝ)) -
              g ((x - (l : ℝ)) + α * (j : ℝ))))
      rw [hfun]
      exact hcol
    · intro l
      have hcol := hδcol h (x - (l : ℝ)) hhcol
      have hfun :
          (fun j : ℤ => ‖D j l‖) =
            fun j : ℤ =>
              |g ((x - (l : ℝ)) + h + α * (j : ℝ)) -
                g ((x - (l : ℝ)) + α * (j : ℝ))| := by
        funext j
        dsimp [D]
        rw [show x + h + α * (j : ℝ) - (l : ℝ) =
            (x - (l : ℝ)) + h + α * (j : ℝ) by ring,
          show x + α * (j : ℝ) - (l : ℝ) =
            (x - (l : ℝ)) + α * (j : ℝ) by ring]
        simpa only [← Complex.ofReal_sub, Real.norm_eq_abs] using
          (Complex.norm_real
            (g ((x - (l : ℝ)) + h + α * (j : ℝ)) -
              g ((x - (l : ℝ)) + α * (j : ℝ))))
      calc
        (∑' j : ℤ, ‖D j l‖)
            = ∑' j : ℤ,
              |g ((x - (l : ℝ)) + h + α * (j : ℝ)) -
                g ((x - (l : ℝ)) + α * (j : ℝ))| := by
              rw [hfun]
        _ ≤ ε := by
              simpa using hcol.2
  let T :=
    preGramianOperator g α C σ hα hdec (x + h) -
      preGramianOperator g α C σ hα hdec x
  have hcoord :
      ∀ c : ellp (2 : ℝ≥0∞), ∀ j : ℤ,
        (T c) j = ∑' l : ℤ, D j l * c l := by
    intro c j
    have hsub := preGramian_sub_apply g α C σ hα hdec x h c j
    calc
      (T c) j
          = ∑' l : ℤ,
              c l * ((g (x + h + α * (j : ℝ) - (l : ℝ)) : ℂ) -
                (g (x + α * (j : ℝ) - (l : ℝ)) : ℂ)) := hsub
      _ = ∑' l : ℤ, D j l * c l := by
            apply tsum_congr
            intro l
            dsimp [D]
            ring
  have hTbound :
      ‖T‖ ≤ ε := by
    refine T.opNorm_le_bound hε.le ?_
    intro c
    have hnormsq :
        ‖T c‖ ^ 2 = ∑' j : ℤ, ‖∑' l : ℤ, D j l * c l‖ ^ 2 := by
      have hnorm :
          ‖T c‖ ^ 2 = ∑' j : ℤ, ‖(T c) j‖ ^ 2 := by
        simpa using
          (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ)
            (by norm_num) (T c))
      rw [hnorm]
      apply tsum_congr
      intro j
      rw [hcoord c j]
    have hschur := (schur_square_sum_bound hD c).2
    have hsq :
        ‖T c‖ ^ 2 ≤ (ε * ‖c‖) ^ 2 := by
      calc
        ‖T c‖ ^ 2 = ∑' j : ℤ, ‖∑' l : ℤ, D j l * c l‖ ^ 2 := hnormsq
        _ ≤ ε * ε * ‖c‖ ^ 2 := hschur
        _ = (ε * ‖c‖) ^ 2 := by ring
    have hright_nonneg : 0 ≤ ε * ‖c‖ :=
      mul_nonneg hε.le (norm_nonneg _)
    have hle := sq_le_sq.mp hsq
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hright_nonneg] using hle
  simpa [T] using hTbound

end

end VendorE3
