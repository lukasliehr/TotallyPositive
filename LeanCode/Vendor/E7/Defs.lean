import LeanCode.Vendor.E7.Operators
import LeanCode.Vendor.E7.Decay
import LeanCode.Vendor.E7.SchurBound








open scoped ENNReal
open Classical
noncomputable section
namespace LimitOps


def IsInEllOne (c : ℤ → ℂ) : Prop :=
  Summable fun k : ℤ => ‖c k‖


def matVec (A : ℤ → ℤ → ℂ) (c : ℤ → ℂ) : ℤ → ℂ :=
  fun k => ∑' l : ℤ, A k l * c l


def MatrixSurjectiveOnEllOne (A : ℤ → ℤ → ℂ) : Prop :=
  ∀ v : ℤ → ℂ, IsInEllOne v → ∃ y : ℤ → ℂ, IsInEllOne y ∧ matVec A y = v



structure Fredholm (T : ℓ1 →L[ℂ] ℓ1) : Prop where
  isClosed_range : IsClosed (Set.range T)
  finiteDimensional_ker : FiniteDimensional ℂ (LinearMap.ker T.toLinearMap)
  finiteDimensional_coker : FiniteDimensional ℂ (ℓ1 ⧸ LinearMap.range T.toLinearMap)





def opOfMatrix (A : ℤ → ℤ → ℂ) : ℓ1 →L[ℂ] ℓ1 :=
  if h : ∃ T : ℓ1 →L[ℂ] ℓ1, ∀ (c : ℓ1) (k : ℤ), (T c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l
  then h.choose else 0


theorem opOfMatrix_apply {A : ℤ → ℤ → ℂ} (h : HasPolynomialOffDiagonalDecay A)
    (c : ℓ1) (k : ℤ) :
    (opOfMatrix A c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l := by
  have hex := exists_bounded_realizing h
  rw [opOfMatrix, dif_pos hex]
  exact hex.choose_spec c k


def PConvergesTo (Aseq : ℕ → ℓ1 →L[ℂ] ℓ1) (A : ℓ1 →L[ℂ] ℓ1) : Prop :=
  ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
    ‖projCLM m ∘L (Aseq j - A)‖ + ‖(Aseq j - A) ∘L projCLM m‖ < ε


def IsLimitOperator (A B : ℓ1 →L[ℂ] ℓ1) : Prop :=
  ∃ h : ℕ → ℤ,
    (∀ M : ℤ, ∃ N : ℕ, ∀ j : ℕ, N ≤ j → M ≤ |h j|) ∧
    PConvergesTo (fun j => shiftCLM (-h j) ∘L A ∘L shiftCLM (h j)) B


def operatorSpectrum (A : ℓ1 →L[ℂ] ℓ1) : Set (ℓ1 →L[ℂ] ℓ1) :=
  {B | IsLimitOperator A B}

end LimitOps
