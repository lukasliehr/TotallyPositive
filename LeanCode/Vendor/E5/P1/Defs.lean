import Mathlib
import LeanCode.Vendor.E5.Defs

noncomputable section

open MeasureTheory

namespace VendorE5ExpDecay


def IsTotallyPositive_n (n : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ a b : Fin n → ℝ, StrictMono a → StrictMono b →
    0 ≤ Matrix.det (Matrix.of (fun i j => g (a i - b j)))


def IsTotallyPositive (g : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, IsTotallyPositive_n n g


def IsTotallyPositiveIntegrable (g : ℝ → ℝ) : Prop :=
  IsTotallyPositive g ∧ Integrable g


def positivitySet (g : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | 0 < g x}


def totalMass (g : ℝ → ℝ) : ℝ :=
  ∫ x, g x


def reflected (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => g (-x)

end VendorE5ExpDecay
