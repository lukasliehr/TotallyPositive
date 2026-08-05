import Mathlib

open Matrix
open MeasureTheory
open scoped ENNReal
open lp

namespace VendorE3
noncomputable section








def HasPolynomialDecay (g : ℝ → ℝ) : Prop :=
  ∃ C η : ℝ, 0 < C ∧ 1 < η ∧
    ∀ x : ℝ, |g x| ≤ C / ((1 + |x|)^η)



def HasDecayWithConstants (g : ℝ → ℝ) (C η : ℝ) : Prop :=
  0 < C ∧ 1 < η ∧
    ∀ x : ℝ, |g x| ≤ C / ((1 + |x|)^η)



def GaborAtom (g : ℝ → ℝ) (α : ℝ) (β : ℝ) (m : ℤ) (n : ℤ) : ℝ → ℂ :=
  fun x => Complex.exp (2 * Real.pi * Complex.I * β * n * x) *
    (g (x - (α * m)) : ℂ)

private def decayKernel (η a : ℝ) : ℝ → ℝ :=
  fun x => (1 + |x - a|) ^ (-η)

private lemma continuous_decayKernel (η a : ℝ) : Continuous (decayKernel η a) := by
  unfold decayKernel
  exact (by fun_prop : Continuous fun x : ℝ => 1 + |x - a|).rpow_const
    (fun x => Or.inl (ne_of_gt (by positivity)))

private lemma integrable_shifted_decay_sq (η a : ℝ) (hη : 1 < η) :
    Integrable (fun x : ℝ => (1 + ‖x - a‖) ^ (-(2 * η))) (volume : Measure ℝ) := by
  have hpow : (Module.finrank ℝ ℝ : ℝ) < 2 * η := by
    norm_num [Module.finrank_self]
    nlinarith
  have hbase :
      Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 * η))) (volume : Measure ℝ) :=
    integrable_one_add_norm hpow
  simpa using hbase.comp_sub_right a

private lemma decayKernel_sq_eq (η a x : ℝ) :
    decayKernel η a x ^ 2 = (1 + ‖x - a‖) ^ (-(2 * η)) := by
  unfold decayKernel
  have hpos : 0 < 1 + |x - a| := by positivity
  have hnorm : ‖x - a‖ = |x - a| := Real.norm_eq_abs (x - a)
  rw [hnorm]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hpos.le]
  ring_nf

private lemma memLp_decayKernel (η a : ℝ) (hη : 1 < η) :
    MemLp (decayKernel η a) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (decayKernel η a) (volume : Measure ℝ) :=
    (continuous_decayKernel η a).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hint :
      Integrable (fun x : ℝ => (1 + ‖x - a‖) ^ (-(2 * η))) (volume : Measure ℝ) :=
    integrable_shifted_decay_sq η a hη
  simpa [decayKernel_sq_eq] using hint

private lemma norm_GaborAtom_eq (g : ℝ → ℝ) (α β x : ℝ) (m n : ℤ) :
    ‖GaborAtom g α β m n x‖ = |g (x - α * m)| := by
  unfold GaborAtom
  rw [norm_mul]
  have hmod : ‖Complex.exp (2 * Real.pi * Complex.I * β * n * x)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hmod]
  simp



theorem memL2_GaborAtom
    (g : ℝ → ℝ) (hg : Continuous g) (h : HasPolynomialDecay g)
    (α : ℝ) (β : ℝ) (m : ℤ) (n : ℤ) :
    MemLp (GaborAtom g α β m n) 2 (volume : Measure ℝ) := by
  rcases h with ⟨C, η, hC, hη, hbound⟩
  let a : ℝ := α * m
  have hker : MemLp (decayKernel η a) 2 (volume : Measure ℝ) :=
    memLp_decayKernel η a hη
  have hatom_meas : AEStronglyMeasurable (GaborAtom g α β m n) (volume : Measure ℝ) := by
    exact (show Continuous (GaborAtom g α β m n) by
      unfold GaborAtom
      fun_prop).aestronglyMeasurable
  refine MemLp.of_le_mul (c := C) hker hatom_meas ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  rw [norm_GaborAtom_eq]
  have hx := hbound (x - a)
  have ha : x - a = x - α * m := by simp [a]
  rw [ha] at hx
  refine hx.trans_eq ?_
  unfold decayKernel
  have hbasepos : 0 < 1 + |x - a| := by positivity
  have hnonneg : 0 ≤ (1 + |x - a|) ^ (-η) :=
    Real.rpow_nonneg hbasepos.le (-η)
  rw [Real.norm_of_nonneg hnonneg]
  rw [div_eq_mul_inv]
  rw [Real.rpow_neg hbasepos.le]


def GaborAtom_L2
    (g : ℝ → ℝ) (hg : Continuous g) (h : HasPolynomialDecay g)
    (α β : ℝ) (m n : ℤ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memL2_GaborAtom g hg h α β m n).toLp


def IsGaborFrame
    (g : ℝ → ℝ) (hg : Continuous g) (h : HasPolynomialDecay g)
    (α : ℝ) (β : ℝ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧ ∀ x : Lp ℂ 2 (volume : Measure ℝ),
    A * ‖x‖ ^ 2 ≤
        ∑' (m : ℤ) (n : ℤ),
          ‖inner ℂ x (GaborAtom_L2 g hg h α β m n)‖ ^ 2
      ∧
    ∑' (m : ℤ) (n : ℤ),
          ‖inner ℂ x (GaborAtom_L2 g hg h α β m n)‖ ^ 2
      ≤ B * ‖x‖ ^ 2


abbrev ellp (p : ℝ≥0∞) : Type := lp (fun _ : ℤ => ℂ) p


def IsMatrixOperator (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ)
    (T : ellp p →L[ℂ] ellp p) : Prop :=
  ∀ x : ellp p, ∀ n : ℤ,
    Summable (fun m : ℤ => A n m * x m) ∧
      (T x) n = ∑' m : ℤ, A n m * x m


def MatrixInvertibleOn (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : ℤ → ℤ → ℂ) : Prop :=
  ∃ T : ellp p →L[ℂ] ellp p, IsMatrixOperator p A T ∧ IsUnit T


def GaborSubmatrix (g : ℝ → ℝ) (δ : ℤ → ℝ) : ℤ → ℤ → ℂ :=
  fun k l => (g ((k : ℝ) + δ k - (l : ℝ)) : ℂ)


def SubmatrixCondition (g : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ x : ℝ, ∃ (δ : ℤ → ℝ) (ν : ℤ → ℤ),
    Function.Injective ν ∧
    (∀ k : ℤ, x + α * (ν k : ℝ) = (k : ℝ) + δ k) ∧
    MatrixInvertibleOn (2 : ℝ≥0∞) (GaborSubmatrix g δ)

end

end VendorE3
