import Mathlib
import LeanCode.Vendor.E5.Defs

open MeasureTheory
















namespace Part12


def evenEquiv : ℤ ≃ ({k : ℤ | Even k} : Set ℤ) where
  toFun n := ⟨2 * n, even_two_mul n⟩
  invFun k := k.1 / 2
  left_inv n := by show 2 * n / 2 = n; omega
  right_inv := by
    rintro ⟨k, hk⟩
    simp only [Set.mem_setOf_eq] at hk
    obtain ⟨m, rfl⟩ := hk
    apply Subtype.ext
    show 2 * ((m + m) / 2) = m + m
    omega


def oddEquiv : ℤ ≃ ({k : ℤ | Even k}ᶜ : Set ℤ) where
  toFun n := ⟨2 * n + 1, by
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Int.not_even_iff_odd]
    exact odd_two_mul_add_one n⟩
  invFun k := (k.1 - 1) / 2
  left_inv n := by show (2 * n + 1 - 1) / 2 = n; omega
  right_inv := by
    rintro ⟨k, hk⟩
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Int.not_even_iff_odd] at hk
    obtain ⟨m, rfl⟩ := hk
    apply Subtype.ext
    show 2 * ((2 * m + 1 - 1) / 2) + 1 = 2 * m + 1
    omega



theorem reindex_shift (h : ℤ → ℝ) :
    (∑' n : ℤ, h (n + 1)) = ∑' n : ℤ, h n :=
  Equiv.tsum_eq
    (⟨fun n : ℤ => n + 1, fun n : ℤ => n - 1,
      fun n => by show n + 1 - 1 = n; omega,
      fun n => by show n - 1 + 1 = n; omega⟩ : ℤ ≃ ℤ) h




theorem parity_split (f : ℤ → ℝ) (hf : Summable (fun k : ℤ => |f k|)) :
    (Summable (fun n : ℤ => f (2 * n)) ∧ Summable (fun n : ℤ => f (2 * n + 1))) ∧
    (∑' k : ℤ, f k) = (∑' n : ℤ, f (2 * n)) + ∑' n : ℤ, f (2 * n + 1) := by
  have hsum : Summable f := Summable.of_abs hf

  have hES : Summable (fun x : ({k : ℤ | Even k} : Set ℤ) => f x.1) :=
    hsum.subtype (· ∈ ({k : ℤ | Even k} : Set ℤ))
  have hOS : Summable (fun x : ({k : ℤ | Even k}ᶜ : Set ℤ) => f x.1) :=
    hsum.subtype (· ∈ ({k : ℤ | Even k}ᶜ : Set ℤ))

  have hEvenSum : Summable (fun n : ℤ => f (2 * n)) :=
    (Equiv.summable_iff evenEquiv).mpr hES
  have hOddSum : Summable (fun n : ℤ => f (2 * n + 1)) :=
    (Equiv.summable_iff oddEquiv).mpr hOS
  refine ⟨⟨hEvenSum, hOddSum⟩, ?_⟩

  have hE_tsum : (∑' x : ({k : ℤ | Even k} : Set ℤ), f x.1) = ∑' n : ℤ, f (2 * n) :=
    (Equiv.tsum_eq evenEquiv (fun x : ({k : ℤ | Even k} : Set ℤ) => f x.1)).symm
  have hO_tsum :
      (∑' x : ({k : ℤ | Even k}ᶜ : Set ℤ), f x.1) = ∑' n : ℤ, f (2 * n + 1) :=
    (Equiv.tsum_eq oddEquiv (fun x : ({k : ℤ | Even k}ᶜ : Set ℤ) => f x.1)).symm

  have hsplit :
      (∑' x : ({k : ℤ | Even k} : Set ℤ), f x.1)
        + (∑' x : ({k : ℤ | Even k}ᶜ : Set ℤ), f x.1) = ∑' k : ℤ, f k :=
    Summable.tsum_add_tsum_compl hES hOS
  rw [← hsplit, hE_tsum, hO_tsum]

end Part12
