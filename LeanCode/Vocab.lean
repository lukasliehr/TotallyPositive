import LeanCode.Base




























open Matrix
open MeasureTheory
open scoped ENNReal
open lp

namespace Assembly






abbrev ellp (p : ℝ≥0∞) : Type := lp (fun _ : ℤ => ℂ) p


def IsMatrixOperator (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ)
    (T : ellp p →L[ℂ] ellp p) : Prop :=
  ∀ x : ellp p, ∀ n : ℤ,
    Summable (fun m : ℤ => A n m * x m) ∧
      (T x) n = ∑' m : ℤ, A n m * x m



def HasPolynomialOffDiagonalDecayC (A : ℤ → ℤ → ℂ) : Prop :=
  ∃ C η : ℝ, 0 < C ∧ 1 < η ∧
    ∀ n m : ℤ, ‖A n m‖ ≤ C / (1 + |(n - m : ℝ)|)^η



def MatrixInvertibleOn (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) : Prop :=
  ∃ T : ellp p →L[ℂ] ellp p, IsMatrixOperator p A T ∧ IsUnit T



def MatrixSurjectiveOn (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) : Prop :=
  ∃ T : ellp p →L[ℂ] ellp p, IsMatrixOperator p A T ∧ Function.Surjective T



noncomputable def GaborSubmatrixC (g : ℝ → ℝ) (δ : ℤ → ℝ) : ℤ → ℤ → ℂ :=
  fun k l => (g ((k : ℝ) + δ k - (l : ℝ)) : ℂ)


def SubmatrixCondition (g : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ x : ℝ, ∃ (δ : ℤ → ℝ) (ν : ℤ → ℤ),
    Function.Injective ν ∧
    (∀ k : ℤ, x + α * (ν k : ℝ) = (k : ℝ) + δ k) ∧
    MatrixInvertibleOn (2 : ℝ≥0∞) (GaborSubmatrixC g δ)







def HasPolynomialOffDiagonalDecayR (A : ℤ → ℤ → ℝ) : Prop :=
  ∃ C η : ℝ, 0 < C ∧ 1 < η ∧
    ∀ n m : ℤ, ‖A n m‖ ≤ C / (1 + |(n - m : ℝ)|)^η




def IsTotallyPositiveMatrix (A : ℤ → ℤ → ℝ) : Prop :=
  ∀ (r : ℕ) (i j : Fin r → ℤ), StrictMono i → StrictMono j →
    0 ≤ (Matrix.of fun p q => A (i p) (j q)).det


def IsUniformlyAlternating (u : ℤ → ℝ) : Prop :=
  ∀ k : ℤ,  (u k) * (u (k+1)) < 0


def IsUniformlyBoundedFromBelow (u : ℤ → ℝ) : Prop :=
  ∃ c > 0, ∀ k : ℤ, |u k| ≥ c


def IsBoundedSequence (u : ℤ → ℝ) : Prop :=
  ∃ M > 0, ∀ k : ℤ, |u k| ≤ M



noncomputable def MatVec (G : ℤ → ℤ → ℝ) (c : ℤ → ℝ) : ℤ → ℝ :=
  fun k => ∑' l : ℤ, G k l * c l


def IsSummableSequence (u : ℤ → ℝ) : Prop :=
  Summable (fun k : ℤ => |u k|)



noncomputable def GaborSubmatrixR (g : ℝ → ℝ) (δ : ℤ → ℝ) : ℤ → ℤ → ℝ :=
  fun k l => g ((k : ℝ) + δ k - (l : ℝ))





noncomputable def HasExponentialDecay (g : ℝ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ( ∀ x : ℝ, |g x| ≤ C * (Real.exp (-c * |x|)) )



noncomputable def Z (g : ℝ → ℝ) (_ : HasExponentialDecay g) :  ℝ × ℝ → ℂ :=
  fun z => ∑' k : ℤ, Complex.exp (2 * Real.pi * Complex.I * k * z.2) * g (z.1 - k)













noncomputable def GaborAtom (g : ℝ → ℝ) (α : ℝ) (β : ℝ) (m : ℤ) (n : ℤ) : ℝ → ℂ :=
  fun x => Complex.exp (2 * Real.pi * Complex.I * β * n * x) * g (x - (α * m))






private theorem polyDecay_memL2 (g : ℝ → ℝ)
    (hg : Continuous g) (h : HasPolynomialDecay g) :
    MemLp g 2 (volume : Measure ℝ) := by
  obtain ⟨C, η, hC, hη, hbound⟩ := h
  rw [memLp_two_iff_integrable_sq hg.aestronglyMeasurable]
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * η := by
    rw [Module.finrank_self]; push_cast; linarith
  have hInt0 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 * η))) (volume : Measure ℝ) :=
    integrable_one_add_norm hr
  have hdom : Integrable (fun x : ℝ => C ^ 2 * (1 + ‖x‖) ^ (-(2 * η))) (volume : Measure ℝ) :=
    hInt0.const_mul (C ^ 2)
  refine hdom.mono' (hg.pow 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hbx : |g x| ≤ C / (1 + |x|) ^ η := hbound x
  have hnorm : ‖g x ^ 2‖ = |g x| ^ 2 := by rw [Real.norm_eq_abs, abs_pow]
  rw [hnorm]
  have hsq : |g x| ^ 2 ≤ (C / (1 + |x|) ^ η) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hbx 2
  have hupos : (0 : ℝ) < 1 + |x| := by positivity
  have hnormx : (1 + ‖x‖) = (1 + |x|) := by rw [Real.norm_eq_abs]
  have hrhs : (C / (1 + |x|) ^ η) ^ 2 = C ^ 2 * (1 + ‖x‖) ^ (-(2 * η)) := by
    rw [hnormx, div_pow, ← Real.rpow_natCast ((1 + |x|) ^ η) 2,
      ← Real.rpow_mul (le_of_lt hupos), Real.rpow_neg (le_of_lt hupos)]
    have hexp : η * (2 : ℕ) = 2 * η := by push_cast; ring
    rw [hexp, div_eq_mul_inv, mul_comm]
  rw [hrhs] at hsq
  exact hsq





lemma memL2_GaborAtom (g : ℝ → ℝ) (hg : Continuous g) (h : HasPolynomialDecay g)
    (α : ℝ) (β : ℝ) (m : ℤ) (n : ℤ) :
    MemLp (GaborAtom g α β m n) 2 (volume : Measure ℝ) := by

  have hgL2 : MemLp g 2 (volume : Measure ℝ) := polyDecay_memL2 g hg h
  have hgL2C : MemLp (fun y : ℝ => ((g y : ℂ))) 2 (volume : Measure ℝ) := hgL2.ofReal
  have hshift : MeasurePreserving (fun x : ℝ => x - α * (m : ℝ)) volume volume :=
    measurePreserving_sub_right volume (α * (m : ℝ))
  have hf0 : MemLp (fun x : ℝ => ((g (x - α * (m : ℝ)) : ℂ))) 2 (volume : Measure ℝ) :=
    hgL2C.comp_measurePreserving hshift

  have hmeas : AEStronglyMeasurable (GaborAtom g α β m n) (volume : Measure ℝ) := by
    apply Continuous.aestronglyMeasurable
    unfold GaborAtom
    fun_prop

  refine hf0.of_le hmeas (Filter.Eventually.of_forall (fun x => ?_))
  have hmod : ‖Complex.exp (2 * Real.pi * Complex.I * β * n * x)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * β * n * x).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  have : ‖GaborAtom g α β m n x‖ = ‖((g (x - α * (m : ℝ)) : ℂ))‖ := by
    unfold GaborAtom
    rw [norm_mul, hmod, one_mul]
  rw [this]


noncomputable def GaborAtom_L2 (g : ℝ → ℝ) (hg : Continuous g) (h : HasPolynomialDecay g)
    (α β : ℝ) (m n : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memL2_GaborAtom g hg h α β m n).toLp


def IsGaborFrame (g : ℝ → ℝ) (hg : Continuous g) (h : HasPolynomialDecay g) (α : ℝ) (β : ℝ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ x : Lp ℂ 2 (volume : Measure ℝ),
    A * ‖x‖ ^ 2 ≤ ∑' (m : ℤ) (n : ℤ), ‖inner ℂ x (GaborAtom_L2 g hg h α β m n)‖ ^ 2
    ∧ ∑' (m : ℤ) (n : ℤ), ‖inner ℂ x (GaborAtom_L2 g hg h α β m n)‖ ^ 2 ≤ B * ‖x‖ ^ 2

end Assembly
