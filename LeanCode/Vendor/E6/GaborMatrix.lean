import LeanCode.Vendor.E6.PerturbationInterval

noncomputable section

namespace E6

theorem alternatingVector_bounded :
    IsBoundedSequence alternatingVector := by
  refine ⟨1, ?_⟩
  intro k
  simp [alternatingVector]

theorem abs_delta_le_one_of_mem_perturbationInterval {x₀ ε : ℝ}
    (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2)
    (δ : ℤ → ℝ)
    (hδ : ∀ k : ℤ, δ k ∈ PerturbationInterval x₀ ε) :
    ∀ k : ℤ, |δ k| ≤ 1 := by
  intro k
  exact perturbationInterval_abs_le_one hx₀ hε₀ hε₁ (hδ k)

theorem gaborSubmatrix_hasPolynomialOffDiagonalDecay (g : ℝ → ℝ)
    (hdecay : HasExponentialDecay g)
    {x₀ ε : ℝ}
    (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2)
    (δ : ℤ → ℝ)
    (hδ : ∀ k : ℤ, δ k ∈ PerturbationInterval x₀ ε) :
    HasPolynomialOffDiagonalDecay (GaborSubmatrix g δ) := by
  rcases expDecay_bound_by_polynomial g hdecay 2 (by norm_num) with ⟨C, hCpos, hC⟩
  refine ⟨4 * C, 2, by positivity, by norm_num, ?_⟩
  intro k l
  let t : ℝ := (k : ℝ) + δ k - (l : ℝ)
  have hg_bound : |g t| ≤ C / ((1 : ℝ) + |t|) ^ 2 := hC t
  have hdelta : |δ k| ≤ 1 :=
    abs_delta_le_one_of_mem_perturbationInterval hx₀ hε₀ hε₁ δ hδ k
  have hnorm_int : ‖(k - l : ℤ)‖ = |((k : ℝ) - (l : ℝ))| := by
    rw [Int.norm_eq_abs, Int.cast_sub]
  have hdiff_eq : (k : ℝ) - (l : ℝ) = t - δ k := by
    simp [t]
    ring
  have htri : |t - δ k| ≤ |t| + |δ k| := by
    rw [abs_sub_le_iff]
    constructor
    · nlinarith [le_abs_self t, neg_le_abs (δ k)]
    · nlinarith [le_abs_self (δ k), neg_le_abs t]
  have hbase : (1 : ℝ) + ‖(k - l : ℤ)‖ ≤ 2 * ((1 : ℝ) + |t|) := by
    rw [hnorm_int, hdiff_eq]
    nlinarith [htri, hdelta, abs_nonneg t]
  have hden_pos_t : 0 < ((1 : ℝ) + |t|) ^ 2 := by positivity
  have hden_pos_kl : 0 < ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ 2 := by positivity
  have hsq :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (1 : ℝ) + ‖(k - l : ℤ)‖) hbase 2
  have hden_le :
      ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ 2 ≤ 4 * ((1 : ℝ) + |t|) ^ 2 := by
    nlinarith [hsq]
  have hfrac : C / ((1 : ℝ) + |t|) ^ 2 ≤
      (4 * C) / ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ 2 := by
    rw [div_le_div_iff₀ hden_pos_t hden_pos_kl]
    nlinarith
  calc
    ‖GaborSubmatrix g δ k l‖ = |g t| := by simp [GaborSubmatrix, t]
    _ ≤ C / ((1 : ℝ) + |t|) ^ 2 := hg_bound
    _ ≤ (4 * C) / ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ 2 := hfrac

theorem gaborSubmatrix_complex_hasPolynomialOffDiagonalDecay (g : ℝ → ℝ)
    (hdecay : HasExponentialDecay g)
    {x₀ ε : ℝ}
    (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2)
    (δ : ℤ → ℝ)
    (hδ : ∀ k : ℤ, δ k ∈ PerturbationInterval x₀ ε) :
    HasPolynomialOffDiagonalDecay (ComplexifyMatrix (GaborSubmatrix g δ)) := by
  rcases gaborSubmatrix_hasPolynomialOffDiagonalDecay g hdecay hx₀ hε₀ hε₁ δ hδ with
    ⟨C, n, hC, hn, hbound⟩
  refine ⟨C, n, hC, hn, ?_⟩
  intro k l
  simpa [ComplexifyMatrix] using hbound k l

theorem gabor_nodes_strictMono {n : ℕ}
    {x₀ ε : ℝ}
    (_hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hε₀ : 0 < ε) (_hε₁ : ε < 1 / 2)
    (δ : ℤ → ℝ)
    (hδ : ∀ k : ℤ, δ k ∈ PerturbationInterval x₀ ε)
    (ks : Fin n → ℤ) (hks : StrictMono ks) :
    StrictMono fun i : Fin n => (ks i : ℝ) + δ (ks i) := by
  intro i j hij
  have hksij : ks i < ks j := hks hij
  have hint : (1 : ℤ) ≤ ks j - ks i := by omega
  have hreal : (1 : ℝ) ≤ (ks j - ks i : ℤ) := by exact_mod_cast hint
  have hreal_sub : (1 : ℝ) ≤ (ks j : ℝ) - (ks i : ℝ) := by
    simpa [Int.cast_sub] using hreal
  have hdi := hδ (ks i)
  have hdj := hδ (ks j)
  rw [PerturbationInterval] at hdi hdj
  have hgap : (0 : ℝ) < ((ks j : ℝ) + δ (ks j)) - ((ks i : ℝ) + δ (ks i)) := by
    nlinarith [hreal_sub, hdi.2, hdj.1, hε₀]
  linarith

theorem gaborSubmatrix_totallyPositiveMatrix (g : ℝ → ℝ)
    (hgTP : IsTotallyPositive g)
    {x₀ ε : ℝ}
    (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2)
    (δ : ℤ → ℝ)
    (hδ : ∀ k : ℤ, δ k ∈ PerturbationInterval x₀ ε) :
    IsTotallyPositiveMatrix (GaborSubmatrix g δ) := by
  intro n r c hr hc
  have hX : StrictMono fun i : Fin n => (r i : ℝ) + δ (r i) :=
    gabor_nodes_strictMono hx₀ hε₀ hε₁ δ hδ r hr
  have hY : StrictMono fun j : Fin n => (c j : ℝ) := by
    intro i j hij
    exact Int.cast_lt.mpr (hc hij)
  simpa [IsTotallyPositive_n, IsTotallyPositiveMatrix_n, GaborSubmatrix] using
    hgTP n (fun i : Fin n => (r i : ℝ) + δ (r i))
      (fun j : Fin n => (c j : ℝ)) hX hY

theorem gaborSubmatrix_alternatingVector_formula (g : ℝ → ℝ)
    (_hdecay : HasExponentialDecay g) (δ : ℤ → ℝ) :
    MatVec (GaborSubmatrix g δ) alternatingVector =
      fun k : ℤ => alternatingVector k * criticalLineFunction g (δ k) := by
  funext k
  change
    (∑' l : ℤ, g ((k : ℝ) + δ k - (l : ℝ)) * (-1 : ℝ) ^ l) =
      (-1 : ℝ) ^ k * (∑' m : ℤ, (-1 : ℝ) ^ m * g (δ k - (m : ℝ)))
  calc
    (∑' l : ℤ, g ((k : ℝ) + δ k - (l : ℝ)) * (-1 : ℝ) ^ l) =
        ∑' m : ℤ, (-1 : ℝ) ^ k * (((-1 : ℝ) ^ m) * g (δ k - (m : ℝ))) := by
      rw [← (Equiv.addLeft k).tsum_eq
        (fun l : ℤ => g ((k : ℝ) + δ k - (l : ℝ)) * (-1 : ℝ) ^ l)]
      apply tsum_congr
      intro m
      have hpow :
          (-1 : ℝ) ^ (((Equiv.addLeft k) m : ℤ)) =
            (-1 : ℝ) ^ k * (-1 : ℝ) ^ m := by
        change (-1 : ℝ) ^ (k + m) = (-1 : ℝ) ^ k * (-1 : ℝ) ^ m
        rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      have harg :
          (k : ℝ) + δ k - (((Equiv.addLeft k) m : ℤ) : ℝ) =
            δ k - (m : ℝ) := by
        change (k : ℝ) + δ k - ((k + m : ℤ) : ℝ) = δ k - (m : ℝ)
        norm_num [Int.cast_add]
      rw [hpow, harg]
      ring
    _ = (-1 : ℝ) ^ k * ∑' m : ℤ, (-1 : ℝ) ^ m * g (δ k - (m : ℝ)) := by
      rw [tsum_mul_left]

theorem gaborSubmatrix_image_alternatingVector_uniform (g : ℝ → ℝ)
    (hg₀ : g ≠ 0) (hg : IsTotallyPositiveIntegrableContinuous g)
    (hdecay : HasExponentialDecay g)
    {x₀ ε : ℝ}
    (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) 1)
    (hx₀zero : Z g hdecay (x₀, 1 / 2) = 0)
    (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2)
    (δ : ℤ → ℝ)
    (hδ : ∀ k : ℤ, δ k ∈ PerturbationInterval x₀ ε) :
    IsUniformlyAlternating (MatVec (GaborSubmatrix g δ) alternatingVector) ∧
      IsUniformlyBoundedFromBelow (MatVec (GaborSubmatrix g δ) alternatingVector) := by
  rcases criticalLine_uniform_sign_on_perturbationInterval
      g hg₀ hg hdecay hx₀ hx₀zero hε₀ hε₁ with
    ⟨m, σ, hmpos, hsigma, hsign⟩
  have hformula := gaborSubmatrix_alternatingVector_formula g hdecay δ
  have halt_abs : ∀ k : ℤ, |alternatingVector k| = 1 := by
    intro k
    simp [alternatingVector]
  have halt_prod : ∀ k : ℤ, alternatingVector k * alternatingVector (k + 1) = -1 := by
    intro k
    simp [alternatingVector, zpow_add₀]
    rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    rw [← two_mul]
    rw [zpow_mul]
    norm_num
  constructor
  · intro k
    have hk0 := hsign (hδ k)
    have hk1 := hsign (hδ (k + 1))
    let a := criticalLineFunction g (δ k)
    let b := criticalLineFunction g (δ (k + 1))
    have hprod_pos : 0 < a * b := by
      rcases hsigma with rfl | rfl
      · have ha : m ≤ a := by simpa [a] using hk0
        have hb : m ≤ b := by simpa [b] using hk1
        nlinarith [hmpos, ha, hb]
      · have ha : m ≤ -a := by simpa [a] using hk0
        have hb : m ≤ -b := by simpa [b] using hk1
        nlinarith [hmpos, ha, hb]
    have hval0 : MatVec (GaborSubmatrix g δ) alternatingVector k =
        alternatingVector k * a := by
      dsimp [a]
      exact congrFun hformula k
    have hval1 : MatVec (GaborSubmatrix g δ) alternatingVector (k + 1) =
        alternatingVector (k + 1) * b := by
      dsimp [b]
      exact congrFun hformula (k + 1)
    calc
      MatVec (GaborSubmatrix g δ) alternatingVector k *
          MatVec (GaborSubmatrix g δ) alternatingVector (k + 1)
          = (alternatingVector k * a) * (alternatingVector (k + 1) * b) := by
              rw [hval0, hval1]
      _ = (alternatingVector k * alternatingVector (k + 1)) * (a * b) := by ring
      _ = (-1) * (a * b) := by rw [halt_prod]
      _ < 0 := by nlinarith
  · refine ⟨m, hmpos, ?_⟩
    intro k
    have hk := hsign (hδ k)
    let a := criticalLineFunction g (δ k)
    have hval : MatVec (GaborSubmatrix g δ) alternatingVector k =
        alternatingVector k * a := by
      dsimp [a]
      exact congrFun hformula k
    have habs_a : m ≤ |a| := by
      rcases hsigma with rfl | rfl
      · have ha : m ≤ a := by simpa [a] using hk
        have hanonneg : 0 ≤ a := by nlinarith [hmpos, ha]
        simpa [abs_of_nonneg hanonneg] using ha
      · have ha : m ≤ -a := by simpa [a] using hk
        have hanonpos : a ≤ 0 := by nlinarith [hmpos, ha]
        simpa [abs_of_nonpos hanonpos] using ha
    calc
      m ≤ |a| := habs_a
      _ = |MatVec (GaborSubmatrix g δ) alternatingVector k| := by
        rw [hval, abs_mul, halt_abs]
        ring

end E6
