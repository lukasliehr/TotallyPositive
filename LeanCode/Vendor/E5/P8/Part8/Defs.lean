import Mathlib
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open scoped BigOperators









namespace Part8

noncomputable section


def translate (c : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x => u (x - c)


def geomBound (c : ℝ) : ℝ :=
  (1 + Real.exp (-c)) / (1 - Real.exp (-c))


def LatticeEnvelope (f : ℝ → ℝ) (b : ℤ → ℝ) : Prop :=
  Summable b ∧ ∀ (k : ℤ), ∀ x ∈ Set.Icc (0 : ℝ) 1, |f (x + k)| ≤ b k


def HasExpBound (f : ℝ → ℝ) (C c : ℝ) : Prop :=
  0 < C ∧ 0 < c ∧ ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|)


def SchoenbergData (g : ℝ → ℝ) (Cst γ δ : ℝ) (α : ℕ → ℝ) : Prop :=
  0 < Cst ∧ 0 ≤ γ ∧
    Summable (fun ν => (α ν) ^ 2) ∧
    (∀ ξ : ℝ, Multipliable (fun ν : ℕ => expFactor (α ν) ξ)) ∧
    (∀ ξ : ℝ, FT g ξ =
      (Cst : ℂ) * Complex.exp (-(γ : ℂ) * ξ ^ 2 + 2 * Real.pi * Complex.I * δ * ξ) *
        ∏' ν : ℕ, expFactor (α ν) ξ) ∧
    (∀ ξ : ℝ, FT g ξ ≠ 0) ∧
    (∀ ξ : ℝ, ‖FT g ξ‖ ≤ Cst * Real.exp (-γ * ξ ^ 2))


def Phi (α : ℕ → ℝ) (ξ : ℝ) : ℂ :=
  ∏' ν : ℕ, expFactor (α ν) ξ


def nonzeroFactorSet (α : ℕ → ℝ) : Set ℕ :=
  {ν | α ν ≠ 0}


def measureFT (μ : Measure ℝ) : ℝ → ℂ :=
  fun ξ => ∫ y : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ξ * y) ∂μ


def kernelMeasureConv (r : ℝ → ℝ) (μ : Measure ℝ) : ℝ → ℝ :=
  fun x => ∫ y : ℝ, r (x - y) ∂μ


def PositivityTrichotomy (f : ℝ → ℝ) : Prop :=
  (∃ u : ℝ, ∀ x : ℝ, u < x → 0 < f x) ∨
  (∃ u : ℝ, ∀ x : ℝ, x < u → 0 < f x) ∨
  (∀ x : ℝ, 0 < f x)

end

end Part8
