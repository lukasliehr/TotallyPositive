import LeanCode.Vendor.E5.P3.Part3.Basic
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open scoped Classical











namespace Part3


noncomputable def supp {n : ℕ} (c : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => c j ≠ 0)


private theorem disjoint_of_cross {n k : ℕ} (J : Fin (k + 1) → Finset (Fin n))
    (hcross : ∀ ν ν' : Fin (k + 1), ν < ν' → ∀ j ∈ J ν, ∀ j' ∈ J ν', j < j') :
    ∀ ν ν' : Fin (k + 1), ν ≠ ν' → Disjoint (J ν) (J ν') := by
  intro ν ν' hne
  rw [Finset.disjoint_left]
  intro j hj hj'
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (hcross ν ν' h j hj j hj') (lt_irrefl j)
  · exact absurd (hcross ν' ν h j hj' j hj) (lt_irrefl j)



private theorem blocks_core :
    ∀ (n : ℕ) (c : Fin n → ℝ), c ≠ 0 →
      ∃ (k : ℕ) (ε : ℝ) (J : Fin (k + 1) → Finset (Fin n)),
        (ε = 1 ∨ ε = -1) ∧
        (∀ ν, (J ν).Nonempty) ∧
        (Finset.univ.biUnion J = supp c) ∧
        (∀ ν ν' : Fin (k + 1), ν < ν' → ∀ j ∈ J ν, ∀ j' ∈ J ν', j < j') ∧
        (∀ ν, ∀ j ∈ J ν, 0 < ε * (-1 : ℝ) ^ (ν : ℕ) * c j) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro c hc
    have hmem : ∀ j, j ∈ supp c ↔ c j ≠ 0 := fun j => by simp [supp]
    have hsupp : (supp c).Nonempty := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
      exact ⟨j, (hmem j).mpr (by simpa using hj)⟩
    set jstar := (supp c).max' hsupp with hjstar
    have hjstar_mem : jstar ∈ supp c := (supp c).max'_mem hsupp
    have hc_jstar : c jstar ≠ 0 := (hmem jstar).mp hjstar_mem
    set σ : ℝ := if 0 < c jstar then 1 else -1 with hσdef
    have hσ : σ = 1 ∨ σ = -1 := by rw [hσdef]; split <;> simp
    have hσ_ne : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    have hσc_ne : ∀ j, c j ≠ 0 → σ * c j ≠ 0 := fun j hcj => mul_ne_zero hσ_ne hcj
    have hσc_jstar : 0 < σ * c jstar := by
      rw [hσdef]; split
      · rename_i h; simpa using h
      · rename_i h
        have : c jstar < 0 := lt_of_le_of_ne (not_lt.mp h) hc_jstar
        simpa using this
    set N : Finset (Fin n) := (supp c).filter (fun j => 0 < -(σ * c j)) with hNdef
    have hNsub : N ⊆ supp c := by rw [hNdef]; exact Finset.filter_subset _ _
    have hinN : ∀ j, j ∈ N → 0 < -(σ * c j) := by
      intro j hj; rw [hNdef, Finset.mem_filter] at hj; exact hj.2
    have hnotN : ∀ j, j ∈ supp c → j ∉ N → 0 < σ * c j := by
      intro j hj hjN
      rw [hNdef, Finset.mem_filter, not_and] at hjN
      have h2 := hjN hj
      rw [not_lt] at h2
      have h0le : 0 ≤ σ * c j := by linarith
      exact lt_of_le_of_ne h0le (hσc_ne j ((hmem j).mp hj)).symm
    by_cases hN : N = ∅
    ·
      refine ⟨0, σ, fun _ => supp c, hσ, fun _ => hsupp, ?_, ?_, ?_⟩
      · ext i; simp
      · intro ν ν' hlt
        exact absurd (Fin.lt_def.mp hlt) (by have := ν.isLt; have := ν'.isLt; omega)
      · intro ν j hj
        have hν0 : (ν : ℕ) = 0 := by have := ν.isLt; omega
        rw [hν0, pow_zero, mul_one]
        exact hnotN j hj (by rw [hN]; exact Finset.notMem_empty j)
    ·
      have hNne : N.Nonempty := Finset.nonempty_iff_ne_empty.mpr hN
      set mstar := N.max' hNne with hmstar
      have hmstar_mem : mstar ∈ N := N.max'_mem hNne
      have hmstar_supp : mstar ∈ supp c := hNsub hmstar_mem
      have hc_mstar : c mstar ≠ 0 := (hmem mstar).mp hmstar_supp
      have hmstar_lt : mstar < jstar := by
        rcases lt_or_eq_of_le ((supp c).le_max' mstar hmstar_supp) with h | h
        · exact h
        · exfalso; have h1 := hinN mstar hmstar_mem; rw [h] at h1; linarith [hσc_jstar]
      have hlt_n : mstar.val + 1 < n := by
        have h1 : mstar.val < jstar.val := hmstar_lt
        have h2 := jstar.isLt; omega
      have h : mstar.val + 1 ≤ n := by omega
      set c' : Fin (mstar.val + 1) → ℝ := fun j => c (Fin.castLE h j) with hc'def
      have hmem' : ∀ j, j ∈ supp c' ↔ c' j ≠ 0 := fun j => by simp [supp]
      set mlast : Fin (mstar.val + 1) := Fin.last mstar.val with hmlastdef
      have hcast_last : Fin.castLE h mlast = mstar := by
        apply Fin.ext; simp [hmlastdef]
      have hc'mlast : c' mlast = c mstar := by simp only [hc'def, hcast_last]
      have hc' : c' ≠ 0 := by
        intro h0; apply hc_mstar
        have := congrFun h0 mlast; rw [hc'mlast, Pi.zero_apply] at this; exact this
      obtain ⟨k', ε', J', hε', hne', hunion', hcross', hsign'⟩ := IH _ hlt_n c' hc'

      have hb3 : mlast ∈ J' (Fin.last k') := by
        have hml : mlast ∈ supp c' := (hmem' mlast).mpr (by rw [hc'mlast]; exact hc_mstar)
        rw [← hunion', Finset.mem_biUnion] at hml
        obtain ⟨ν, -, hν⟩ := hml
        rcases (Fin.eq_castSucc_or_eq_last ν) with ⟨a, rfl⟩ | rfl
        · exfalso
          obtain ⟨j', hj'⟩ := hne' (Fin.last k')
          have hlt2 := hcross' _ _ (Fin.castSucc_lt_last a) mlast hν j' hj'
          have e1 : mlast.val < j'.val := hlt2
          have e2 := j'.isLt
          have e3 : mlast.val = mstar.val := by simp [hmlastdef]
          omega
        · exact hν

      have hb4 : ε' * (-1 : ℝ) ^ k' = -σ := by
        have hA : 0 < ε' * (-1 : ℝ) ^ k' * c mstar := by
          have := hsign' (Fin.last k') mlast hb3
          rwa [Fin.val_last, hc'mlast] at this
        have hB' : 0 < -σ * c mstar := by
          have := hinN mstar hmstar_mem; rwa [← neg_mul] at this
        have hpow : (-1 : ℝ) ^ k' = 1 ∨ (-1 : ℝ) ^ k' = -1 := by
          rcases Nat.even_or_odd k' with he | ho
          · exact Or.inl he.neg_one_pow
          · exact Or.inr ho.neg_one_pow
        have hτ1 : ε' * (-1 : ℝ) ^ k' = 1 ∨ ε' * (-1 : ℝ) ^ k' = -1 := by
          rcases hε' with hh | hh <;> rcases hpow with hp | hp <;> rw [hh, hp] <;> norm_num
        have hτ2 : -σ = 1 ∨ -σ = -1 := by rcases hσ with hh | hh <;> rw [hh] <;> norm_num
        rcases hτ1 with a1 | a1 <;> rcases hτ2 with a2 | a2 <;>
          rw [a1] at hA ⊢ <;> rw [a2] at hB' ⊢ <;>
          first | rfl | (exfalso; nlinarith [hA, hB'])

      set topB : Finset (Fin n) := (supp c).filter (fun i => mstar < i) with htopB
      set J : Fin (k' + 1 + 1) → Finset (Fin n) :=
        Fin.snoc (fun ν' => (J' ν').image (Fin.castLE h)) topB with hJdef
      have hJcast : ∀ ν' : Fin (k' + 1),
          J (Fin.castSucc ν') = (J' ν').image (Fin.castLE h) := fun ν' => by
        rw [hJdef]; exact Fin.snoc_castSucc _ _ _
      have hJlast : J (Fin.last (k' + 1)) = topB := by rw [hJdef]; exact Fin.snoc_last _ _
      refine ⟨k' + 1, ε', J, hε', ?_, ?_, ?_, ?_⟩
      ·
        intro ν
        rcases (Fin.eq_castSucc_or_eq_last ν) with ⟨ν', rfl⟩ | rfl
        · rw [hJcast]; exact (hne' ν').image _
        · rw [hJlast]; exact ⟨jstar, Finset.mem_filter.mpr ⟨hjstar_mem, hmstar_lt⟩⟩
      ·
        ext i
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        rw [hmem i]
        constructor
        · rintro ⟨ν, hν⟩
          rcases (Fin.eq_castSucc_or_eq_last ν) with ⟨ν', rfl⟩ | rfl
          · rw [hJcast] at hν
            obtain ⟨j, hjJ', rfl⟩ := Finset.mem_image.mp hν
            have hjs : j ∈ supp c' :=
              (by rw [← hunion']; exact Finset.mem_biUnion.mpr ⟨ν', Finset.mem_univ ν', hjJ'⟩)
            have := (hmem' j).mp hjs
            simpa [hc'def] using this
          · rw [hJlast] at hν; exact (hmem i).mp (Finset.mem_of_mem_filter i hν)
        · intro hci
          have hisupp : i ∈ supp c := (hmem i).mpr hci
          by_cases hi : mstar < i
          · exact ⟨Fin.last _, by rw [hJlast]; exact Finset.mem_filter.mpr ⟨hisupp, hi⟩⟩
          · rw [not_lt] at hi
            have hile : i.val ≤ mstar.val := hi
            set j : Fin (mstar.val + 1) := ⟨i.val, by omega⟩ with hjdef
            have hcastj : Fin.castLE h j = i := by apply Fin.ext; simp [hjdef]
            have hcj : c' j ≠ 0 := by rw [hc'def]; simp only [hcastj]; exact hci
            have hjs : j ∈ supp c' := (hmem' j).mpr hcj
            rw [← hunion', Finset.mem_biUnion] at hjs
            obtain ⟨ν', -, hν'⟩ := hjs
            exact ⟨Fin.castSucc ν', by rw [hJcast]; exact Finset.mem_image.mpr ⟨j, hν', hcastj⟩⟩
      ·
        intro ν ν' hlt j hj j' hj'
        rcases (Fin.eq_castSucc_or_eq_last ν) with ⟨a, rfl⟩ | rfl <;>
          rcases (Fin.eq_castSucc_or_eq_last ν') with ⟨b, rfl⟩ | rfl
        · rw [hJcast] at hj; rw [hJcast] at hj'
          obtain ⟨ja, hjaJ', rfl⟩ := Finset.mem_image.mp hj
          obtain ⟨jb, hjbJ', rfl⟩ := Finset.mem_image.mp hj'
          exact Fin.strictMono_castLE h
            (hcross' a b (Fin.castSucc_lt_castSucc_iff.mp hlt) ja hjaJ' jb hjbJ')
        · rw [hJcast] at hj; rw [hJlast] at hj'
          obtain ⟨ja, hjaJ', rfl⟩ := Finset.mem_image.mp hj
          have h1 : (Fin.castLE h ja).val ≤ mstar.val := by
            have := ja.isLt; simp only [Fin.val_castLE]; omega
          have h2 : mstar.val < j'.val := (Finset.mem_filter.mp hj').2
          exact Fin.lt_def.mpr (by omega)
        · exact absurd hlt (not_lt.mpr (Fin.castSucc_lt_last b).le)
        · exact absurd hlt (lt_irrefl _)
      ·
        intro ν j hj
        rcases (Fin.eq_castSucc_or_eq_last ν) with ⟨ν', rfl⟩ | rfl
        · rw [hJcast] at hj
          obtain ⟨ja, hjaJ', rfl⟩ := Finset.mem_image.mp hj
          simpa [hc'def, Fin.val_castSucc] using hsign' ν' ja hjaJ'
        · rw [hJlast] at hj
          have hj_supp : j ∈ supp c := Finset.mem_of_mem_filter j hj
          have hj_top : mstar < j := (Finset.mem_filter.mp hj).2
          have hjN : j ∉ N := fun hjNmem =>
            absurd hj_top (not_lt.mpr (N.le_max' j hjNmem))
          have hσcj : 0 < σ * c j := hnotN j hj_supp hjN
          rw [Fin.val_last]
          have hsig : ε' * (-1 : ℝ) ^ (k' + 1) = σ := by
            rw [pow_succ, ← mul_assoc, hb4]; ring
          rw [hsig]; exact hσcj




theorem blocks {n : ℕ} (c : Fin n → ℝ) (hc : c ≠ 0) :
    ∃ (k : ℕ) (ε : ℝ) (J : Fin (k + 1) → Finset (Fin n)),
      (ε = 1 ∨ ε = -1) ∧
      (∀ ν, (J ν).Nonempty) ∧
      (Finset.univ.biUnion J = supp c) ∧
      (∀ ν ν' : Fin (k + 1), ν < ν' → ∀ j ∈ J ν, ∀ j' ∈ J ν', j < j') ∧
      (∀ ν, ∀ j ∈ J ν, 0 < ε * (-1 : ℝ) ^ (ν : ℕ) * c j) ∧
      (∀ ν ν' : Fin (k + 1), ν ≠ ν' → Disjoint (J ν) (J ν')) := by
  obtain ⟨k, ε, J, hε, hne, hunion, hcross, hsign⟩ := blocks_core n c hc
  exact ⟨k, ε, J, hε, hne, hunion, hcross, hsign, disjoint_of_cross J hcross⟩



theorem blocks_signchanges {n k : ℕ} (c : Fin n → ℝ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (J : Fin (k + 1) → Finset (Fin n)) (hne : ∀ ν, (J ν).Nonempty)
    (hcross : ∀ ν ν' : Fin (k + 1), ν < ν' → ∀ j ∈ J ν, ∀ j' ∈ J ν', j < j')
    (hsign : ∀ ν, ∀ j ∈ J ν, 0 < ε * (-1 : ℝ) ^ (ν : ℕ) * c j) :
    SignChangesGE c k := by
  refine ⟨fun ν => (J ν).min' (hne ν), ?_, ε, hε, ?_⟩
  · intro a b hab
    exact hcross a b hab ((J a).min' (hne a)) ((J a).min'_mem (hne a))
      ((J b).min' (hne b)) ((J b).min'_mem (hne b))
  · intro ν
    exact hsign ν ((J ν).min' (hne ν)) ((J ν).min'_mem (hne ν))



theorem blocks_bound {n k s : ℕ} (hs : 1 ≤ s) (c : Fin n → ℝ) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (J : Fin (k + 1) → Finset (Fin n))
    (hne : ∀ ν, (J ν).Nonempty)
    (hcross : ∀ ν ν' : Fin (k + 1), ν < ν' → ∀ j ∈ J ν, ∀ j' ∈ J ν', j < j')
    (hsign : ∀ ν, ∀ j ∈ J ν, 0 < ε * (-1 : ℝ) ^ (ν : ℕ) * c j)
    (hnsc : ¬ SignChangesGE c s) : k ≤ s - 1 := by
  by_contra h
  have hsk : s ≤ k := by omega
  exact hnsc (sign_mono c (blocks_signchanges c ε hε J hne hcross hsign) hsk)

end Part3
