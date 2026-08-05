import Mathlib














open Matrix
open MeasureTheory

namespace Assembly


def IsTotallyPositive_n (n : ℕ) (g : ℝ → ℝ) : Prop :=
    ∀ a b : Fin n → ℝ, StrictMono a → StrictMono b →
    (Matrix.det (Matrix.of (fun i j => g (a i - b j)))) ≥ 0


def IsTotallyPositive (g : ℝ → ℝ) : Prop :=
    ∀ n : ℕ, IsTotallyPositive_n n g

def IsTotallyPositiveIntegrable (g : ℝ → ℝ) : Prop :=
    (IsTotallyPositive g ∧  MeasureTheory.Integrable g)

def IsTotallyPositiveIntegrableContinuous (g : ℝ → ℝ) : Prop :=
    (IsTotallyPositive g ∧  MeasureTheory.Integrable g ∧ Continuous g)


noncomputable def HasPolynomialDecay (g : ℝ → ℝ) : Prop :=
  ∃ C η : ℝ, 0 < C ∧ 1 < η ∧
    ∀ x : ℝ, |g x| ≤ C / ((1 + |x|)^η)

end Assembly
