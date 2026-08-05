import Mathlib

open MeasureTheory




namespace VendorE5

def IsTotallyPositive_n (n : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ a b : Fin n → ℝ, StrictMono a → StrictMono b →
    (Matrix.det (Matrix.of (fun i j => g (a i - b j)))) ≥ 0

def IsTotallyPositive (g : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, IsTotallyPositive_n n g

def IsTotallyPositiveIntegrableContinuous (g : ℝ → ℝ) : Prop :=
  IsTotallyPositive g ∧ MeasureTheory.Integrable g ∧ Continuous g

def HasExponentialDecay (g : ℝ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|)

end VendorE5

open VendorE5

noncomputable def Zak (g : ℝ → ℝ) : ℝ × ℝ → ℂ :=
  fun z => ∑' k : ℤ, Complex.exp (2 * Real.pi * Complex.I * k * z.2) * g (z.1 - k)

noncomputable def Halt (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∑' k : ℤ, (-1 : ℝ) ^ k * f (x + k)


noncomputable def expKernel (a : ℝ) : ℝ → ℝ :=
  fun t => if 0 ≤ a * t then |a| * Real.exp (-(a * t)) else 0


noncomputable def conv (f h : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ t : ℝ, f t * h (x - t)


noncomputable def finiteType : (m : ℕ) → (Fin (m + 1) → ℝ) → (ℝ → ℝ)
  | 0, a => expKernel (a 0)
  | m + 1, a => conv (expKernel (a 0)) (finiteType m (fun i => a i.succ))


noncomputable def centeredExp (α : ℝ) : ℝ → ℝ :=
  fun t => expKernel (1 / α) (t + α)



def StrictOneCrossing (F : ℝ → ℝ) : Prop :=
  ∃ r : ℝ, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ F r = 0 ∧
    (∀ x : ℝ, r - 1 < x → x < r → ε * F x < 0) ∧
    (∀ x : ℝ, r < x → x < r + 1 → 0 < ε * F x)

def TotallyNonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (k : ℕ) (r : Fin k → Fin m) (c : Fin k → Fin n),
    StrictMono r → StrictMono c →
      0 ≤ Matrix.det (Matrix.of (fun i j => A (r i) (c j)))




def SignChangesGE {n : ℕ} (v : Fin n → ℝ) (s : ℕ) : Prop :=
  ∃ idx : Fin (s + 1) → Fin n, StrictMono idx ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ i : Fin (s + 1), 0 < ε * (-1 : ℝ) ^ (i : ℕ) * v (idx i)




def CyclicAlt4 (F : ℝ → ℝ) : Prop :=
  ∃ t : Fin 4 → ℝ, StrictMono t ∧ t 3 < t 0 + 2 ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ i : Fin 4, 0 < ε * (-1 : ℝ) ^ (i : ℕ) * F (t i)

noncomputable def Acol (g : ℝ → ℝ) : ℝ → ℝ := fun x => ∑' n : ℤ, g (x + 2 * n)

noncomputable def Bcol (g : ℝ → ℝ) : ℝ → ℝ := fun x => ∑' n : ℤ, g (x - 1 + 2 * n)



def LatticeDominated (f : ℝ → ℝ) : Prop :=
  ∃ b : ℤ → ℝ, Summable b ∧
    ∀ (k : ℤ), ∀ x ∈ Set.Icc (0 : ℝ) 1, |f (x + k)| ≤ b k


noncomputable def FT (g : ℝ → ℝ) : ℝ → ℂ :=
  fun ξ => ∫ x : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ξ * x) * g x


noncomputable def mom (g : ℝ → ℝ) (i : ℕ) : ℝ := ∫ y : ℝ, y ^ i * g y




def MomentReciprocal (g : ℝ → ℝ) (β : ℕ → ℝ) : Prop :=
  (mom g 0) * β 0 = 1 ∧
  ∀ m : ℕ, 0 < m →
    (∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * (-1 : ℝ) ^ i * mom g i * β (m - i)) = 0


def RealRooted (p : Polynomial ℝ) : Prop :=
  ∀ z : ℂ, Polynomial.aeval z p = 0 → z.im = 0


noncomputable def jensenPoly (β : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ m ∈ Finset.range (n + 1),
    Polynomial.C ((n.choose m : ℝ) * β m) * Polynomial.X ^ (n - m)


noncomputable def expFactor (α : ℝ) (ξ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * α * ξ) /
    (1 + 2 * Real.pi * Complex.I * α * ξ)



def SchoenbergProduct (g : ℝ → ℝ) : Prop :=
  ∃ (Cst γ δ : ℝ) (α : ℕ → ℝ), 0 < Cst ∧ 0 ≤ γ ∧
    Summable (fun ν => (α ν) ^ 2) ∧
    (∀ ξ : ℝ, Multipliable (fun ν : ℕ => expFactor (α ν) ξ)) ∧
    (∀ ξ : ℝ, FT g ξ =
      (Cst : ℂ) * Complex.exp (-(γ : ℂ) * ξ ^ 2 + 2 * Real.pi * Complex.I * δ * ξ) *
        ∏' ν : ℕ, expFactor (α ν) ξ) ∧
    (∀ ξ : ℝ, FT g ξ ≠ 0) ∧
    (∀ ξ : ℝ, ‖FT g ξ‖ ≤ Cst * Real.exp (-γ * ξ ^ 2))



def FiniteTypeForm (g : ℝ → ℝ) : Prop :=
  ∃ (Cst η : ℝ) (m : ℕ) (a : Fin (m + 1) → ℝ),
    0 < Cst ∧ 1 ≤ m ∧ (∀ j, a j ≠ 0) ∧
    ∀ x : ℝ, g x = Cst * finiteType m a (x - η)


def GaussianForm (g : ℝ → ℝ) : Prop :=
  ∃ C₀ γ : ℝ, 0 < C₀ ∧ 0 < γ ∧
    (∀ ξ : ℝ, ‖FT g ξ‖ ≤ C₀ * Real.exp (-γ * ξ ^ 2)) ∧
    FT g (1 / 2) ≠ 0






def InfiniteProductForm (g : ℝ → ℝ) : Prop :=
  ∃ (Cst η a₁ a₂ : ℝ) (F : ℕ → ℝ → ℝ) (σ : ℕ → ℝ),
    0 < Cst ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
    (∀ x : ℝ, g x = Cst * F 2 (x - η)) ∧
    (∀ m : ℕ, 2 ≤ m →
      Continuous (F m) ∧ MeasureTheory.Integrable (F m) ∧ LatticeDominated (F m)) ∧
    (∀ m : ℕ, 3 ≤ m → σ m ≠ 0 ∧
      ∀ x : ℝ, F (m - 1) x = conv (centeredExp (σ m)) (F m) x) ∧
    (∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun N x => Halt (F N) x)
        (fun x => Halt (conv (centeredExp a₁) (centeredExp a₂)) x)
        Filter.atTop K)



def RealizationConclusion (g : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, 0 < Acol g x) ∧ (∀ x : ℝ, 0 < Bcol g x) ∧
  (FiniteTypeForm g ∨ GaussianForm g ∨ InfiniteProductForm g)

def Statement_Part_1 : Prop :=
  ∀ g : ℝ → ℝ, IsTotallyPositiveIntegrableContinuous g → HasExponentialDecay g

def Statement_Part_2 : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → HasExponentialDecay f →
    Continuous (Halt f) ∧
    (∀ x : ℝ, Halt f (x + 1) = - Halt f x) ∧
    (∀ x : ℝ, Zak f (x, 1 / 2) = Halt f x)

def Statement_Part_3 : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), TotallyNonneg A →
    ∀ (c : Fin n → ℝ) (s : ℕ),
      SignChangesGE (A.mulVec c) s → SignChangesGE c s

def Statement_Part_4 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ a : Fin (m + 1) → ℝ, (∀ j, a j ≠ 0) →
    Continuous (finiteType m a) ∧
    MeasureTheory.Integrable (finiteType m a) ∧
    HasExponentialDecay (finiteType m a) ∧
    StrictOneCrossing (Halt (finiteType m a))

def Statement_Part_5 : Prop :=
  ∀ g : ℝ → ℝ, IsTotallyPositiveIntegrableContinuous g → g ≠ 0 →
    HasExponentialDecay g →
    ∃ β : ℕ → ℝ, MomentReciprocal g β ∧ 0 < β 0 ∧
      ∀ n : ℕ, RealRooted (jensenPoly β n)

def Statement_Part_6 : Prop :=
  ∀ β : ℕ → ℝ, 0 < β 0 → (∀ n : ℕ, RealRooted (jensenPoly β n)) →
    ∃ (γ δ : ℝ) (α : ℕ → ℝ), 0 ≤ γ ∧ Summable (fun ν => (α ν) ^ 2) ∧
      ∀ s : ℂ,
        Multipliable (fun ν : ℕ => (1 + (α ν : ℂ) * s) * Complex.exp (-(α ν : ℂ) * s)) ∧
        HasSum (fun m : ℕ => ((β m / m.factorial : ℝ) : ℂ) * s ^ m)
          ((β 0 : ℂ) * Complex.exp (-(γ : ℂ) * s ^ 2 + (δ : ℂ) * s) *
            ∏' ν : ℕ, ((1 + (α ν : ℂ) * s) * Complex.exp (-(α ν : ℂ) * s)))

def Statement_Part_7 : Prop :=
  ∀ g : ℝ → ℝ, IsTotallyPositiveIntegrableContinuous g → g ≠ 0 →
    HasExponentialDecay g → SchoenbergProduct g

def Statement_Part_8 : Prop :=
  ∀ g : ℝ → ℝ, IsTotallyPositiveIntegrableContinuous g → g ≠ 0 →
    HasExponentialDecay g → SchoenbergProduct g → RealizationConclusion g

def Statement_Part_9 : Prop :=
  ∀ g : ℝ → ℝ, IsTotallyPositiveIntegrableContinuous g →
    HasExponentialDecay g →
    ∀ c : ℝ, 0 < c → ¬ CyclicAlt4 (fun x => Acol g x - c * Bcol g x)

def Statement_Part_10 : Prop :=
  ∀ g : ℝ → ℝ, Continuous g → MeasureTheory.Integrable g →
    HasExponentialDecay g → RealizationConclusion g →
    ∀ u v : ℝ, u < v → ∃ x : ℝ, u < x ∧ x < v ∧ Halt g x ≠ 0

def Statement_Part_11 : Prop :=
  ∀ R : ℝ → ℝ, Continuous R → (∀ x : ℝ, 0 < R x) →
    (∀ x : ℝ, R (x + 1) = (R x)⁻¹) →
    (∀ c : ℝ, 0 < c → ¬ CyclicAlt4 (fun x => R x - c)) →
    (∀ u v : ℝ, u < v → ∃ x : ℝ, u < x ∧ x < v ∧ R x ≠ 1) →
    ∀ r s : ℝ, r ∈ Set.Ico (0 : ℝ) 1 → s ∈ Set.Ico (0 : ℝ) 1 →
      R r = 1 → R s = 1 → r = s

def Statement_Part_12 : Prop :=
  ∀ g : ℝ → ℝ, g ≠ 0 → IsTotallyPositiveIntegrableContinuous g →
    ∃! x : ℝ, x ∈ Set.Ico (0 : ℝ) 1 ∧ Zak g (x, 1 / 2) = 0
