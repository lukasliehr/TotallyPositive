import LeanCode.Vocab
import LeanCode.E7Vocab

















open Classical
noncomputable section

namespace Assembly.Hard



private theorem row_matVec_eq
    (g : ℝ → ℝ) (δ : ℤ → ℝ) (yr yi vr vi : ℤ → ℝ) (v : ℤ → ℂ) (k : ℤ)
    (hyr_eq : ∑' l : ℤ, Assembly.GaborSubmatrixR g δ k l * yr l = vr k)
    (hyi_eq : ∑' l : ℤ, Assembly.GaborSubmatrixR g δ k l * yi l = vi k)
    (har : Summable (fun l : ℤ => Assembly.GaborSubmatrixR g δ k l * yr l))
    (hai : Summable (fun l : ℤ => Assembly.GaborSubmatrixR g δ k l * yi l))
    (hvk : v k = (vr k : ℂ) + Complex.I * (vi k : ℂ)) :
    ∑' l : ℤ, Assembly.GaborSubmatrixC g δ k l *
        ((yr l : ℂ) + Complex.I * (yi l : ℂ)) = v k := by
  have hentry : ∀ l : ℤ, Assembly.GaborSubmatrixC g δ k l
      = ((Assembly.GaborSubmatrixR g δ k l : ℝ) : ℂ) := fun l => rfl
  have hsummand : ∀ l : ℤ,
      Assembly.GaborSubmatrixC g δ k l * ((yr l : ℂ) + Complex.I * (yi l : ℂ))
        = ((Assembly.GaborSubmatrixR g δ k l * yr l : ℝ) : ℂ)
          + Complex.I * ((Assembly.GaborSubmatrixR g δ k l * yi l : ℝ) : ℂ) := by
    intro l
    rw [hentry l]; push_cast; ring
  rw [tsum_congr hsummand]
  have hsum1 : Summable (fun l : ℤ => ((Assembly.GaborSubmatrixR g δ k l * yr l : ℝ) : ℂ)) :=
    Complex.ofRealCLM.summable har
  have hsum2 : Summable (fun l : ℤ =>
      Complex.I * ((Assembly.GaborSubmatrixR g δ k l * yi l : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.summable hai).mul_left _
  rw [hsum1.tsum_add hsum2, ← Complex.ofReal_tsum, tsum_mul_left, ← Complex.ofReal_tsum]
  rw [hyr_eq, hyi_eq, hvk]




theorem real_to_complex_surjOnEllOne_proof
    (g : ℝ → ℝ) (δ : ℤ → ℝ)
    (hg : Assembly.HasPolynomialDecay g)
    (hsurj : ∀ v : ℤ → ℝ, Assembly.IsSummableSequence v →
      ∃ y : ℤ → ℝ, Assembly.IsSummableSequence y ∧
        Assembly.MatVec (Assembly.GaborSubmatrixR g δ) y = v) :
    Assembly.E7.MatrixSurjectiveOnEllOne (Assembly.GaborSubmatrixC g δ) := by
  intro v hv

  obtain ⟨C, η, hC, hη, hdecay⟩ := hg
  have hgbdd : ∀ t : ℝ, |g t| ≤ C := by
    intro t
    have hden_ge_one : (1 : ℝ) ≤ (1 + |t|) ^ η := by
      apply Real.one_le_rpow (by linarith [abs_nonneg t]) (le_of_lt (by linarith))
    have hpos : (0 : ℝ) < (1 + |t|) ^ η := by positivity
    calc |g t| ≤ C / ((1 + |t|) ^ η) := hdecay t
      _ ≤ C / 1 := by
            apply div_le_div_of_nonneg_left (le_of_lt hC) (by norm_num) hden_ge_one
      _ = C := by ring


  have hentryR : ∀ k l : ℤ, |Assembly.GaborSubmatrixR g δ k l| ≤ C := by
    intro k l; exact hgbdd _

  set vr : ℤ → ℝ := fun k => (v k).re with hvr_def
  set vi : ℤ → ℝ := fun k => (v k).im with hvi_def
  have hv_summ : Summable (fun k : ℤ => ‖v k‖) := hv

  have hvr_summ : Assembly.IsSummableSequence vr :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _)
      (fun k => Complex.abs_re_le_norm (v k)) hv_summ
  have hvi_summ : Assembly.IsSummableSequence vi :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _)
      (fun k => Complex.abs_im_le_norm (v k)) hv_summ

  obtain ⟨yr, hyr_summ, hyr_eq⟩ := hsurj vr hvr_summ
  obtain ⟨yi, hyi_summ, hyi_eq⟩ := hsurj vi hvi_summ

  refine ⟨fun l => (yr l : ℂ) + Complex.I * (yi l : ℂ), ?_, ?_⟩
  ·
    have hbound : ∀ l : ℤ,
        ‖(yr l : ℂ) + Complex.I * (yi l : ℂ)‖ ≤ |yr l| + |yi l| := by
      intro l
      calc ‖(yr l : ℂ) + Complex.I * (yi l : ℂ)‖
          ≤ ‖(yr l : ℂ)‖ + ‖Complex.I * (yi l : ℂ)‖ := norm_add_le _ _
        _ = |yr l| + |yi l| := by
              rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs]
    exact Summable.of_nonneg_of_le (fun l => norm_nonneg _) hbound (hyr_summ.add hyi_summ)
  ·
    funext k
    show ∑' l : ℤ, Assembly.GaborSubmatrixC g δ k l *
        ((yr l : ℂ) + Complex.I * (yi l : ℂ)) = v k

    have hyr_row : ∑' l : ℤ, Assembly.GaborSubmatrixR g δ k l * yr l = vr k :=
      congrFun hyr_eq k
    have hyi_row : ∑' l : ℤ, Assembly.GaborSubmatrixR g δ k l * yi l = vi k :=
      congrFun hyi_eq k

    have hvk : v k = (vr k : ℂ) + Complex.I * (vi k : ℂ) := by
      simp only [hvr_def, hvi_def]
      rw [mul_comm]
      exact (Complex.re_add_im (v k)).symm

    have har : Summable (fun l : ℤ => Assembly.GaborSubmatrixR g δ k l * yr l) := by
      apply Summable.of_norm_bounded (g := fun l : ℤ => C * |yr l|) (hyr_summ.mul_left C)
      intro l
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hentryR k l) (abs_nonneg _)
    have hai : Summable (fun l : ℤ => Assembly.GaborSubmatrixR g δ k l * yi l) := by
      apply Summable.of_norm_bounded (g := fun l : ℤ => C * |yi l|) (hyi_summ.mul_left C)
      intro l
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hentryR k l) (abs_nonneg _)
    exact row_matVec_eq g δ yr yi vr vi v k hyr_row hyi_row har hai hvk

end Assembly.Hard

end
