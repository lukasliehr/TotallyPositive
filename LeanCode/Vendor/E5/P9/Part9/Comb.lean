import LeanCode.Vendor.E5.P9.Part9.Basic
import LeanCode.Vendor.E5.Defs
open VendorE5

open scoped BigOperators








def combAtom (N : ℕ) : Fin (4 * N + 2) → ℤ := fun j => ((j : ℕ) : ℤ) - 2 * (N : ℤ)


noncomputable def combWeight (c : ℝ) (N : ℕ) : Fin (4 * N + 2) → ℝ :=
  fun j => if Even (j : ℕ) then (1 : ℝ) else -c






theorem lem_comb (g : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    StrictMono (fun j : Fin (4 * N + 2) => ((combAtom N j : ℤ) : ℝ)) ∧
      (∀ x : ℝ, Ftrunc g c N x
        = ∑ j : Fin (4 * N + 2), combWeight c N j * g (x - ((combAtom N j : ℤ) : ℝ))) := by
  constructor
  ·
    intro a b hab
    simp only [combAtom]
    have hnat : (a : ℕ) < (b : ℕ) := hab
    have hr : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast
    linarith
  ·
    intro x
    rw [Ftrunc]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => Even ((j : Fin (4*N+2)) : ℕ))]
    have heven :
        (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g (x + 2 * (n : ℝ)))
          = ∑ j ∈ Finset.univ.filter (fun j : Fin (4*N+2) => Even ((j : ℕ))),
              combWeight c N j * g (x - ((combAtom N j : ℤ) : ℝ)) := by
      apply Finset.sum_bij'
        (i := fun (n : ℤ) (hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) =>
          (⟨(2*(N - n)).toNat, by simp only [Finset.mem_Icc] at hn; omega⟩ : Fin (4*N+2)))
        (j := fun (j : Fin (4*N+2)) (_ : j ∈ Finset.univ.filter (fun j : Fin (4*N+2) => Even ((j : ℕ)))) =>
          (N : ℤ) - ((j : ℕ) / 2 : ℤ))
      case hi =>
        intro a ha
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_Icc] at ha
        show Even (2*((N:ℤ) - a)).toNat
        exact ⟨(N - a).toNat, by omega⟩
      case hj =>
        intro a ha
        rw [Finset.mem_filter] at ha
        obtain ⟨_, ha2⟩ := ha
        simp only [Finset.mem_Icc]
        have hlt : (a : ℕ) < 4*N+2 := a.isLt
        obtain ⟨m, hm⟩ := ha2
        omega
      case left_neg =>
        intro a ha
        simp only [Finset.mem_Icc] at ha
        show (N:ℤ) - ((2*((N:ℤ) - a)).toNat : ℤ) / 2 = a
        have h1 : ((2*((N:ℤ) - a)).toNat : ℤ) = 2*((N:ℤ) - a) := Int.toNat_of_nonneg (by omega)
        rw [h1]
        omega
      case right_neg =>
        intro a ha
        rw [Finset.mem_filter] at ha
        obtain ⟨_, ha2⟩ := ha
        apply Fin.ext
        show (2*((N:ℤ) - ((N:ℤ) - ((a:ℕ):ℤ)/2))).toNat = (a:ℕ)
        obtain ⟨m, hm⟩ := ha2
        omega
      case h =>
        intro a ha
        simp only [Finset.mem_Icc] at ha
        have hval : ((⟨(2*((N:ℤ) - a)).toNat, by omega⟩ : Fin (4*N+2)) : ℕ) = (2*((N:ℤ) - a)).toNat := rfl
        have heven : Even ((⟨(2*((N:ℤ) - a)).toNat, by omega⟩ : Fin (4*N+2)) : ℕ) := by
          rw [hval]; exact ⟨(N-a).toNat, by omega⟩
        simp only [combWeight, combAtom, heven, if_true, one_mul]
        congr 1
        have h1 : ((2*((N:ℤ) - a)).toNat : ℤ) = 2*((N:ℤ) - a) := Int.toNat_of_nonneg (by omega)
        rw [show (((⟨(2*((N:ℤ) - a)).toNat, by omega⟩ : Fin (4*N+2)) : ℕ) : ℤ) = ((2*((N:ℤ) - a)).toNat : ℤ) from rfl, h1]
        push_cast
        ring
    have hodd :
        (-c * ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g (x - 1 + 2 * (n : ℝ)))
          = ∑ j ∈ Finset.univ.filter (fun j : Fin (4*N+2) => ¬ Even ((j : ℕ))),
              combWeight c N j * g (x - ((combAtom N j : ℤ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_bij'
        (i := fun (n : ℤ) (hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) =>
          (⟨(2*(N - n) + 1).toNat, by simp only [Finset.mem_Icc] at hn; omega⟩ : Fin (4*N+2)))
        (j := fun (j : Fin (4*N+2)) (_ : j ∈ Finset.univ.filter (fun j : Fin (4*N+2) => ¬ Even ((j : ℕ)))) =>
          (N : ℤ) - ((j : ℕ) / 2 : ℤ))
      case hi =>
        intro a ha
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_Icc] at ha
        have hval : ((⟨(2*((N:ℤ) - a) + 1).toNat, by omega⟩ : Fin (4*N+2)) : ℕ) = (2*((N:ℤ) - a) + 1).toNat := rfl
        rw [hval, Nat.not_even_iff_odd]
        exact ⟨(N - a).toNat, by omega⟩
      case hj =>
        intro a ha
        rw [Finset.mem_filter] at ha
        obtain ⟨_, ha2⟩ := ha
        rw [Nat.not_even_iff_odd] at ha2
        simp only [Finset.mem_Icc]
        have hlt : (a : ℕ) < 4*N+2 := a.isLt
        obtain ⟨m, hm⟩ := ha2
        omega
      case left_neg =>
        intro a ha
        simp only [Finset.mem_Icc] at ha
        show (N:ℤ) - ((2*((N:ℤ) - a) + 1).toNat : ℤ) / 2 = a
        have h1 : ((2*((N:ℤ) - a) + 1).toNat : ℤ) = 2*((N:ℤ) - a) + 1 := Int.toNat_of_nonneg (by omega)
        rw [h1]
        omega
      case right_neg =>
        intro a ha
        rw [Finset.mem_filter] at ha
        obtain ⟨_, ha2⟩ := ha
        rw [Nat.not_even_iff_odd] at ha2
        apply Fin.ext
        show (2*((N:ℤ) - ((N:ℤ) - ((a:ℕ):ℤ)/2)) + 1).toNat = (a:ℕ)
        obtain ⟨m, hm⟩ := ha2
        omega
      case h =>
        intro a ha
        simp only [Finset.mem_Icc] at ha
        have hval : ((⟨(2*((N:ℤ) - a) + 1).toNat, by omega⟩ : Fin (4*N+2)) : ℕ) = (2*((N:ℤ) - a) + 1).toNat := rfl
        have hodd : ¬ Even ((⟨(2*((N:ℤ) - a) + 1).toNat, by omega⟩ : Fin (4*N+2)) : ℕ) := by
          rw [hval, Nat.not_even_iff_odd]; exact ⟨(N-a).toNat, by omega⟩
        simp only [combWeight, combAtom, hodd, if_false, neg_mul]
        have h1 : ((2*((N:ℤ) - a) + 1).toNat : ℤ) = 2*((N:ℤ) - a) + 1 := Int.toNat_of_nonneg (by omega)
        have hatom : (((⟨(2*((N:ℤ) - a) + 1).toNat, by omega⟩ : Fin (4*N+2)) : ℕ) : ℤ) - 2 * (N : ℤ) = 1 - 2 * a := by
          rw [show (((⟨(2*((N:ℤ) - a) + 1).toNat, by omega⟩ : Fin (4*N+2)) : ℕ) : ℤ) = ((2*((N:ℤ) - a) + 1).toNat : ℤ) from rfl, h1]
          ring
        rw [hatom]
        have harg : x - 1 + 2 * (a : ℝ) = x - (((1 - 2 * a : ℤ)) : ℝ) := by push_cast; ring
        rw [harg]
    rw [← heven, ← hodd]
    ring



theorem lem_sampleTN {g : ℝ → ℝ} (hg : IsTotallyPositive g) {m n : ℕ}
    {x : Fin m → ℝ} {t : Fin n → ℝ} (hx : StrictMono x) (ht : StrictMono t) :
    TotallyNonneg (Matrix.of (fun i j => g (x i - t j))) := by
  intro k r c hr hc
  have ha : StrictMono (x ∘ r) := hx.comp hr
  have hb : StrictMono (t ∘ c) := ht.comp hc
  have hdet := hg k (x ∘ r) (t ∘ c) ha hb
  simpa [Matrix.of_apply, Function.comp] using hdet



theorem lem_pigeonhole {d s : ℕ} (hsd : d < s + 1) (v : Fin d → ℝ) :
    ¬ SignChangesGE v s := by
  intro h
  obtain ⟨idx, hmono, -⟩ := h
  have hcard := Fintype.card_le_of_injective idx hmono.injective
  simp only [Fintype.card_fin] at hcard
  omega
