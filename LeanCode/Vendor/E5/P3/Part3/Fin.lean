import LeanCode.Vendor.E5.P3.Part3.Basic
import LeanCode.Vendor.E5.Defs

open MeasureTheory













namespace Part3



theorem strictMono_comp {k N M : ℕ} {φ : Fin k → Fin N} {ψ : Fin N → Fin M}
    (hφ : StrictMono φ) (hψ : StrictMono ψ) : StrictMono (ψ ∘ φ) :=
  hψ.comp hφ


theorem strictMono_inj {k N : ℕ} {φ : Fin k → Fin N} (hφ : StrictMono φ) :
    Function.Injective φ :=
  hφ.injective




theorem strictMono_fin_id {k : ℕ} {φ : Fin k → Fin k} (hφ : StrictMono φ)
    (i : Fin k) : φ i = i :=
  le_antisymm hφ.apply_le hφ.le_apply



theorem strictMono_range_eq {k N : ℕ} {φ ψ : Fin k → Fin N}
    (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hrange : Set.range φ = Set.range ψ) : φ = ψ :=
  (hφ.range_inj hψ).mp hrange



theorem enum {p q : ℕ} (Q : Finset (Fin p)) (hcard : Q.card = q) :
    ∃! ρ : Fin q → Fin p, StrictMono ρ ∧ Set.range ρ = (↑Q : Set (Fin p)) := by
  refine ⟨⇑(Q.orderEmbOfFin hcard),
    ⟨(Q.orderEmbOfFin hcard).strictMono, Q.range_orderEmbOfFin hcard⟩, ?_⟩
  rintro ρ ⟨hmono, hrange⟩
  refine strictMono_range_eq hmono (Q.orderEmbOfFin hcard).strictMono ?_
  rw [hrange, Q.range_orderEmbOfFin hcard]



theorem skip_basic {q : ℕ} (ℓ : Fin (q + 1)) :
    StrictMono ℓ.succAbove ∧
      Set.range ℓ.succAbove = ({ℓ} : Set (Fin (q + 1)))ᶜ :=
  ⟨Fin.strictMono_succAbove ℓ, Fin.range_succAbove ℓ⟩



theorem skip_classify {q : ℕ} {ρ : Fin q → Fin (q + 1)} (hρ : StrictMono ρ) :
    ∃! ℓ : Fin (q + 1), ρ = ℓ.succAbove := by
  classical
  have hinj : Function.Injective ρ := hρ.injective
  set R : Finset (Fin (q + 1)) := Finset.univ.image ρ with hR
  have hRcard : R.card = q := by
    rw [hR, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hcompl : Rᶜ.card = 1 := by
    rw [Finset.card_compl, hRcard, Fintype.card_fin]; omega
  obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp hcompl
  have hrangeR : Set.range ρ = (↑R : Set (Fin (q + 1))) := by
    rw [hR, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hcoe : ((↑R : Set (Fin (q + 1)))ᶜ) = ({ℓ} : Set (Fin (q + 1))) := by
    rw [← Finset.coe_compl, hℓ, Finset.coe_singleton]
  have hrange_compl : Set.range ρ = ({ℓ} : Set (Fin (q + 1)))ᶜ := by
    rw [hrangeR, ← hcoe, compl_compl]
  refine ⟨ℓ, ?_, ?_⟩
  · refine strictMono_range_eq hρ (Fin.strictMono_succAbove ℓ) ?_
    rw [Fin.range_succAbove]; exact hrange_compl
  · intro ℓ' hℓ'
    have hset : ({ℓ'} : Set (Fin (q + 1)))ᶜ = ({ℓ} : Set (Fin (q + 1)))ᶜ := by
      rw [← Fin.range_succAbove ℓ', ← hℓ']; exact hrange_compl
    have h2 : ({ℓ'} : Set (Fin (q + 1))) = {ℓ} := by
      rw [← compl_compl ({ℓ'} : Set (Fin (q + 1))), hset, compl_compl]
    exact Set.singleton_eq_singleton_iff.mp h2



theorem reselect {m n p q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonneg A) {ρ : Fin p → Fin m} {γ : Fin q → Fin n}
    (hρ : StrictMono ρ) (hγ : StrictMono γ) :
    TotallyNonneg (Matrix.of (fun i j => A (ρ i) (γ j))) := by
  intro k r' c' hr' hc'
  exact hA k (ρ ∘ r') (γ ∘ c') (hρ.comp hr') (hγ.comp hc')


theorem colselect {m n q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonneg A) {γ : Fin q → Fin n} (hγ : StrictMono γ) :
    TotallyNonneg (Matrix.of (fun i j => A i (γ j))) := by
  simpa using reselect hA (strictMono_id) hγ

end Part3
