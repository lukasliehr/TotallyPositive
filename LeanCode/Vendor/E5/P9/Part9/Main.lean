import LeanCode.Vendor.E5.P9.Part9.Truncation
import LeanCode.Vendor.E5.P9.Part9.Sample
import LeanCode.Vendor.E5.P9.Part9.Comb
import LeanCode.Vendor.E5.Defs
open VendorE5

open scoped BigOperators









theorem Part_9_main (h3 : Statement_Part_3) : Statement_Part_9 := by
  intro g hg_tpic hg_decay c hc hcyc

  have hg_tp : IsTotallyPositive g := hg_tpic.1
  obtain ⟨C, c0, hC, hc0, hgbd⟩ := hg_decay

  have hFeq : (fun x => Acol g x - c * Bcol g x) = Fc g c := rfl
  rw [hFeq] at hcyc
  obtain ⟨u, hu_mono, hu_gap, ε, hε, hu_sign⟩ := hcyc

  have hper : ∀ (x : ℝ) (k : ℤ), Fc g c (x + 2 * (k : ℝ)) = Fc g c x :=
    fun x k => (lem_periodic g c x k).2.2

  have hFne : ∀ j : Fin 4, Fc g c (u j) ≠ 0 := by
    intro j hj
    have h := hu_sign j
    rw [hj, mul_zero] at h
    exact lt_irrefl 0 h
  have hFpos : ∀ j : Fin 4, 0 < |Fc g c (u j)| := fun j => abs_pos.mpr (hFne j)
  set m4 := min (min |Fc g c (u 0)| |Fc g c (u 1)|) (min |Fc g c (u 2)| |Fc g c (u 3)|) with hm4
  have hm4pos : 0 < m4 := lt_min (lt_min (hFpos 0) (hFpos 1)) (lt_min (hFpos 2) (hFpos 3))
  set η := m4 / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have h2η : ∀ j : Fin 4, 2 * η ≤ |Fc g c (u j)| := by
    intro j
    have h2 : 2 * η = m4 := by rw [hηdef]; ring
    rw [h2, hm4]
    fin_cases j
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  set K := max |u 0| |u 3| + 2 with hKdef
  have hmaxnn : 0 ≤ max |u 0| |u 3| := le_trans (abs_nonneg _) (le_max_left _ _)
  have hK0 : 0 ≤ K := by rw [hKdef]; linarith
  have hKge : max |u 0| |u 3| ≤ K := by rw [hKdef]; linarith

  obtain ⟨L0, hL0⟩ := lem_truncation g hC hc0 hgbd hc K hK0 η hη
  set N := L0 + L0 with hN

  have hsmono : StrictMono (sample u L0) := lem_samplemono hu_mono hu_gap L0
  have hssign := lem_samplesign hper hu_mono L0 hε hu_sign
  have hsrange := lem_samplerange hu_mono L0 hKge

  have htrunc : ∀ i : Fin (4 * (2 * L0 + 1)),
      |Fc g c (sample u L0 i) - Ftrunc g c N (sample u L0 i)| < η := by
    intro i
    exact hL0 L0 L0 (le_refl L0) (sample u L0 i) (hsrange i)

  have htransfer := lem_transfer (sample u L0) (Fc g c) (Ftrunc g c N) hη hε
    (fun i => (hssign i).2)
    (fun i => by rw [(hssign i).1]; exact h2η ⟨(i : ℕ) % 4, by omega⟩)
    (fun i => htrunc i)

  have hsc_v : SignChangesGE (fun i => Ftrunc g c N (sample u L0 i)) (4 * (2 * L0) + 3) :=
    lem_altvec _ ⟨ε, hε, htransfer⟩


  set A : Matrix (Fin (4 * (2 * L0 + 1))) (Fin (4 * N + 2)) ℝ :=
    Matrix.of (fun i j => g (sample u L0 i - ((combAtom N j : ℤ) : ℝ))) with hA
  set w : Fin (4 * N + 2) → ℝ := combWeight c N with hw
  have hA_TN : TotallyNonneg A := by
    rw [hA]; exact lem_sampleTN hg_tp hsmono (lem_comb g c N).1
  have hv_eq : (fun i => Ftrunc g c N (sample u L0 i)) = A.mulVec w := by
    funext i
    rw [(lem_comb g c N).2 (sample u L0 i)]
    simp only [hA, hw, Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hv_eq] at hsc_v

  have hsc_w : SignChangesGE w (4 * (2 * L0) + 3) := h3 _ _ A hA_TN w _ hsc_v

  have hpigeon : ¬ SignChangesGE w (4 * (2 * L0) + 3) := by
    apply lem_pigeonhole
    rw [hN]; omega
  exact hpigeon hsc_w
