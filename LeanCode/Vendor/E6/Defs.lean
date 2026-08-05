import Mathlib

noncomputable section

open Matrix
open scoped BigOperators

namespace E6

def IsTotallyPositive_n (n : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ a b : Fin n → ℝ, StrictMono a → StrictMono b →
    0 ≤ Matrix.det (Matrix.of fun i j => g (a i - b j))

def IsTotallyPositive (g : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, IsTotallyPositive_n n g

def IsTotallyPositiveIntegrable (g : ℝ → ℝ) : Prop :=
  IsTotallyPositive g ∧ MeasureTheory.Integrable g

def IsTotallyPositiveIntegrableContinuous (g : ℝ → ℝ) : Prop :=
  IsTotallyPositive g ∧ MeasureTheory.Integrable g ∧ Continuous g

def IsTotallyPositiveMatrix_n (n : ℕ) (A : ℤ → ℤ → ℝ) : Prop :=
  ∀ r c : Fin n → ℤ, StrictMono r → StrictMono c →
    0 ≤ Matrix.det (Matrix.of fun i j => A (r i) (c j))

def IsTotallyPositiveMatrix (A : ℤ → ℤ → ℝ) : Prop :=
  ∀ n : ℕ, IsTotallyPositiveMatrix_n n A

def HasExponentialDecay (g : ℝ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)

def HasPolynomialOffDiagonalDecay {𝕜 : Type*} [Norm 𝕜]
    (A : ℤ → ℤ → 𝕜) : Prop :=
  ∃ C : ℝ, ∃ n : ℕ, 0 < C ∧ 1 < n ∧
    ∀ k l : ℤ, ‖A k l‖ ≤ C / ((1 : ℝ) + ‖(k - l : ℤ)‖) ^ n

def IsBoundedSequence {𝕜 : Type*} [Norm 𝕜] (u : ℤ → 𝕜) : Prop :=
  ∃ M : ℝ, ∀ k : ℤ, ‖u k‖ ≤ M

def IsSummableSequence {𝕜 : Type*} [Norm 𝕜] (u : ℤ → 𝕜) : Prop :=
  Summable fun k : ℤ => ‖u k‖

noncomputable def MatVec (A : ℤ → ℤ → ℝ) (c : ℤ → ℝ) : ℤ → ℝ :=
  fun k => ∑' l : ℤ, A k l * c l

noncomputable def CMatVec (A : ℤ → ℤ → ℂ) (c : ℤ → ℂ) : ℤ → ℂ :=
  fun k => ∑' l : ℤ, A k l * c l

def IsUniformlyAlternating (u : ℤ → ℝ) : Prop :=
  ∀ k : ℤ, u k * u (k + 1) < 0

def IsUniformlyBoundedFromBelow (u : ℤ → ℝ) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ k : ℤ, m ≤ |u k|

noncomputable def Z (g : ℝ → ℝ) (_ : HasExponentialDecay g) : ℝ × ℝ → ℂ :=
  fun z =>
    ∑' k : ℤ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (z.2 : ℂ)) *
        (g (z.1 - (k : ℝ)) : ℂ)

noncomputable def criticalLineFunction (g : ℝ → ℝ) : ℝ → ℝ :=
  fun t => ∑' m : ℤ, ((-1 : ℝ) ^ m) * g (t - (m : ℝ))

def PerturbationInterval (x₀ ε : ℝ) : Set ℝ :=
  Set.Icc (x₀ - 1 + ε) (x₀ - ε)

def GaborSubmatrix (g : ℝ → ℝ) (δ : ℤ → ℝ) : ℤ → ℤ → ℝ :=
  fun k l => g ((k : ℝ) + δ k - (l : ℝ))

def ComplexifyMatrix (A : ℤ → ℤ → ℝ) : ℤ → ℤ → ℂ :=
  fun k l => (A k l : ℂ)

noncomputable def alternatingVector : ℤ → ℝ :=
  fun k => (-1 : ℝ) ^ k

inductive SequenceSpace where
  | one
  | infinity
  deriving DecidableEq, Repr

def InComplexSequenceSpace : SequenceSpace → (ℤ → ℂ) → Prop
  | .one, u => IsSummableSequence u
  | .infinity, u => IsBoundedSequence u

def IsMatrixOperator (A : ℤ → ℤ → ℂ) (p : SequenceSpace) : Prop :=
  ∀ x : ℤ → ℂ, InComplexSequenceSpace p x →
    ∀ k : ℤ, Summable fun l : ℤ => A k l * x l

def MatrixSurjectiveOn (A : ℤ → ℤ → ℂ) (p : SequenceSpace) : Prop :=
  ∀ v : ℤ → ℂ, InComplexSequenceSpace p v →
    ∃ y : ℤ → ℂ, InComplexSequenceSpace p y ∧ CMatVec A y = v

end E6
