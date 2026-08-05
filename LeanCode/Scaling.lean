import LeanCode.Base



























open Matrix

namespace Assembly.Scaling




noncomputable def scaleWindow (β : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (Real.sqrt β)⁻¹ * g (t / β)


theorem scaleWindow_const_pos {β : ℝ} (hβ : 0 < β) : 0 < (Real.sqrt β)⁻¹ :=
  inv_pos.mpr (Real.sqrt_pos.mpr hβ)




theorem isTotallyPositive_n_scaleWindow {β : ℝ} (hβ : 0 < β) {n : ℕ} {g : ℝ → ℝ}
    (hg : IsTotallyPositive_n n g) : IsTotallyPositive_n n (scaleWindow β g) := by
  intro a b ha hb

  set c : ℝ := (Real.sqrt β)⁻¹ with hc
  have hc_pos : 0 < c := scaleWindow_const_pos hβ
  set a' : Fin n → ℝ := fun i => a i / β with ha'
  set b' : Fin n → ℝ := fun j => b j / β with hb'

  have ha'_mono : StrictMono a' := by
    intro i j hij
    have := ha hij
    simpa [ha'] using div_lt_div_of_pos_right this hβ
  have hb'_mono : StrictMono b' := by
    intro i j hij
    have := hb hij
    simpa [hb'] using div_lt_div_of_pos_right this hβ

  have hmat :
      (Matrix.of (fun i j => scaleWindow β g (a i - b j)))
        = c • (Matrix.of (fun i j => g (a' i - b' j))) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, scaleWindow, ha', hb', hc]
    rw [sub_div]
  rw [hmat]

  rw [Matrix.det_smul]
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  rw [hcard]

  have h1 : (0 : ℝ) ≤ c ^ n := pow_nonneg hc_pos.le n
  have h2 : (0 : ℝ) ≤ (Matrix.of (fun i j => g (a' i - b' j))).det :=
    hg a' b' ha'_mono hb'_mono
  exact mul_nonneg h1 h2



theorem isTotallyPositive_scaleWindow {β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ}
    (hg : IsTotallyPositive g) : IsTotallyPositive (scaleWindow β g) :=
  fun n => isTotallyPositive_n_scaleWindow hβ (hg n)






theorem scaleWindow_scaleWindow_inv {β : ℝ} (hβ : 0 < β) (g : ℝ → ℝ) (t : ℝ) :
    scaleWindow (1 / β) (scaleWindow β g) t = g t := by
  have hβ' : 0 < 1 / β := by positivity
  simp only [scaleWindow]

  have harg : (t / (1 / β)) / β = t := by
    field_simp
  rw [harg]

  have hsqrt_ne : Real.sqrt β ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hβ)
  have hconst : (Real.sqrt (1 / β))⁻¹ * (Real.sqrt β)⁻¹ = 1 := by
    have h1 : Real.sqrt (1 / β) = (Real.sqrt β)⁻¹ := by
      rw [one_div, Real.sqrt_inv]
    rw [h1, inv_inv]
    exact mul_inv_cancel₀ hsqrt_ne
  rw [← mul_assoc, hconst, one_mul]




theorem isTotallyPositive_scaleWindow_iff {β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ} :
    IsTotallyPositive g ↔ IsTotallyPositive (scaleWindow β g) := by
  constructor
  · exact isTotallyPositive_scaleWindow hβ
  · intro h
    have hβ' : 0 < 1 / β := by positivity
    have hround : IsTotallyPositive (scaleWindow (1 / β) (scaleWindow β g)) :=
      isTotallyPositive_scaleWindow hβ' h

    have hfun : scaleWindow (1 / β) (scaleWindow β g) = g :=
      funext (scaleWindow_scaleWindow_inv hβ g)
    rwa [hfun] at hround



theorem continuous_scaleWindow {β : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (scaleWindow β g) := by
  unfold scaleWindow
  fun_prop



theorem hasPolynomialDecay_scaleWindow {β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ}
    (hg : HasPolynomialDecay g) : HasPolynomialDecay (scaleWindow β g) := by
  obtain ⟨C, η, hC, hη, hbound⟩ := hg
  set c : ℝ := (Real.sqrt β)⁻¹ with hc
  have hc_pos : 0 < c := scaleWindow_const_pos hβ
  set K : ℝ := max 1 β with hK
  have hK_pos : 0 < K := lt_of_lt_of_le one_pos (le_max_left 1 β)

  refine ⟨c * C * K ^ η, η, ?_, hη, ?_⟩
  · have : (0 : ℝ) < K ^ η := Real.rpow_pos_of_pos hK_pos η
    positivity
  · intro t

    have hval : scaleWindow β g t = c * g (t / β) := rfl
    rw [hval, abs_mul, abs_of_pos hc_pos]

    have hgb : |g (t / β)| ≤ C / ((1 + |t / β|) ^ η) := hbound (t / β)

    have habs : |t / β| = |t| / β := by
      rw [abs_div, abs_of_pos hβ]

    have hpos1 : (0 : ℝ) < 1 + |t| := by positivity
    have hpos2 : (0 : ℝ) < 1 + |t / β| := by positivity
    have hden : (1 + |t|) ≤ K * (1 + |t / β|) := by
      rw [habs]
      have hb1 : (1 : ℝ) ≤ K * 1 := by rw [mul_one]; exact le_max_left 1 β
      have hb2 : |t| ≤ K * (|t| / β) := by
        rw [mul_div_assoc']
        rw [le_div_iff₀ hβ]
        have : |t| * β ≤ |t| * K := by
          apply mul_le_mul_of_nonneg_left (le_max_right 1 β) (abs_nonneg t)
        rw [mul_comm K |t|]
        linarith [this]
      calc 1 + |t| ≤ K * 1 + K * (|t| / β) := by linarith
        _ = K * (1 + |t| / β) := by ring

    have hηnn : (0 : ℝ) ≤ η := le_of_lt (lt_trans one_pos hη)
    have hpow : (1 + |t|) ^ η ≤ (K * (1 + |t / β|)) ^ η :=
      Real.rpow_le_rpow (le_of_lt hpos1) hden hηnn
    have hpow2 : (K * (1 + |t / β|)) ^ η = K ^ η * (1 + |t / β|) ^ η :=
      Real.mul_rpow (le_of_lt hK_pos) (le_of_lt hpos2)
    rw [hpow2] at hpow

    have hden_pos : (0 : ℝ) < (1 + |t / β|) ^ η := Real.rpow_pos_of_pos hpos2 η
    have hden_pos' : (0 : ℝ) < (1 + |t|) ^ η := Real.rpow_pos_of_pos hpos1 η
    have hKη_pos : (0 : ℝ) < K ^ η := Real.rpow_pos_of_pos hK_pos η

    have step1 : c * |g (t / β)| ≤ c * (C / ((1 + |t / β|) ^ η)) :=
      mul_le_mul_of_nonneg_left hgb (le_of_lt hc_pos)

    have step2 : C / ((1 + |t / β|) ^ η) ≤ (C * K ^ η) / ((1 + |t|) ^ η) := by
      rw [div_le_div_iff₀ hden_pos hden_pos']

      calc C * (1 + |t|) ^ η
          ≤ C * (K ^ η * (1 + |t / β|) ^ η) :=
            mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
        _ = C * K ^ η * (1 + |t / β|) ^ η := by ring
    calc c * |g (t / β)|
        ≤ c * (C / ((1 + |t / β|) ^ η)) := step1
      _ ≤ c * ((C * K ^ η) / ((1 + |t|) ^ η)) :=
          mul_le_mul_of_nonneg_left step2 (le_of_lt hc_pos)
      _ = (c * C * K ^ η) / ((1 + |t|) ^ η) := by ring

end Assembly.Scaling
