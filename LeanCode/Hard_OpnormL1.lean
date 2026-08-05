import LeanCode.E7Vocab












open scoped ENNReal
open Classical
noncomputable section

namespace Assembly.Hard

open Assembly.E7

variable {A : ℤ → ℤ → ℂ} {M : ℝ}
  (hcol : ∀ l : ℤ, Summable (fun k : ℤ => ‖A k l‖) ∧ ∑' k : ℤ, ‖A k l‖ ≤ M)

include hcol


theorem row_entry_le (k l : ℤ) : ‖A k l‖ ≤ M := by
  obtain ⟨hsum, hle⟩ := hcol l
  exact le_trans (hsum.le_tsum k (fun i _ => norm_nonneg _)) hle


theorem summable_row (c : ℓ1) (k : ℤ) :
    Summable (fun l : ℤ => A k l * (c : ℤ → ℂ) l) := by
  have hc : Summable (fun l : ℤ => ‖(c : ℤ → ℂ) l‖) := memℓp_one_iff.mp (lp.memℓp c)
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (f := fun l => M * ‖(c : ℤ → ℂ) l‖)
    ?_ (hc.mul_left M)
  intro l
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (row_entry_le hcol k l) (norm_nonneg _)


theorem summable_prod_swap (c : ℓ1) :
    Summable (fun p : ℤ × ℤ => ‖A p.2 p.1‖ * ‖(c : ℤ → ℂ) p.1‖) := by
  have hc : Summable (fun l : ℤ => ‖(c : ℤ → ℂ) l‖) := memℓp_one_iff.mp (lp.memℓp c)
  have hnn : ∀ p : ℤ × ℤ, (0 : ℝ) ≤ ‖A p.2 p.1‖ * ‖(c : ℤ → ℂ) p.1‖ :=
    fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hslice : ∀ l : ℤ, Summable (fun k : ℤ => ‖A k l‖ * ‖(c : ℤ → ℂ) l‖) :=
    fun l => (hcol l).1.mul_right _
  have hbound : ∀ l : ℤ, (∑' k : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖) ≤ M * ‖(c : ℤ → ℂ) l‖ := by
    intro l
    rw [(hcol l).1.tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hcol l).2 (norm_nonneg _)
  have hsumcol : Summable (fun l : ℤ => ∑' k : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖) :=
    Summable.of_nonneg_of_le
      (fun l => tsum_nonneg (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      hbound (hc.mul_left M)
  exact (summable_prod_of_nonneg hnn).2 ⟨hslice, hsumcol⟩


theorem summable_prod (c : ℓ1) :
    Summable (Function.uncurry (fun k l : ℤ => ‖A k l‖ * ‖(c : ℤ → ℂ) l‖)) := by
  have h := (summable_prod_swap hcol c).prod_symm
  refine h.congr (fun p => ?_)
  simp [Function.uncurry, Prod.swap]


theorem memℓp_T₀ (c : ℓ1) :
    Memℓp (fun k : ℤ => ∑' l : ℤ, A k l * (c : ℤ → ℂ) l) 1 := by
  have hFsum := summable_prod hcol c
  refine memℓp_one_iff.mpr ?_
  have hslice : Summable (fun k : ℤ => ∑' l : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖) := hFsum.prod
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun k => ∑' l : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖) ?_ hslice
  intro k
  have hrow := (summable_row hcol c k).norm
  refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq ?_)
  · simpa only [norm_mul] using hrow
  · exact tsum_congr (fun l => by rw [norm_mul])


def Lmap (c : ℓ1) : ℓ1 := ⟨fun k => ∑' l : ℤ, A k l * (c : ℤ → ℂ) l, memℓp_T₀ hcol c⟩

theorem Lmap_coe (c : ℓ1) (k : ℤ) :
    (Lmap hcol c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l := rfl


def L : ℓ1 →ₗ[ℂ] ℓ1 where
  toFun := Lmap hcol
  map_add' c d := by
    apply lp.ext
    funext k
    simp only [Lmap_coe, lp.coeFn_add, Pi.add_apply]
    rw [← Summable.tsum_add (summable_row hcol c k) (summable_row hcol d k)]
    exact tsum_congr (fun l => by ring)
  map_smul' r c := by
    apply lp.ext
    funext k
    simp only [Lmap_coe, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    exact tsum_congr (fun l => by ring)

theorem L_coe (c : ℓ1) (k : ℤ) :
    (L hcol c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l := rfl


theorem L_norm_le (c : ℓ1) : ‖L hcol c‖ ≤ M * ‖c‖ := by
  have hc : Summable (fun l : ℤ => ‖(c : ℤ → ℂ) l‖) := memℓp_one_iff.mp (lp.memℓp c)
  have hFsum := summable_prod hcol c
  rw [norm_eq_tsum, norm_eq_tsum]
  have hLc : Summable (fun k : ℤ => ‖(L hcol c : ℤ → ℂ) k‖) :=
    memℓp_one_iff.mp (lp.memℓp (L hcol c))
  have hslice : Summable (fun k : ℤ => ∑' l : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖) := hFsum.prod

  have step1 : (∑' k : ℤ, ‖(L hcol c : ℤ → ℂ) k‖)
      ≤ ∑' k : ℤ, ∑' l : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖ := by
    refine hLc.tsum_le_tsum (fun k => ?_) hslice
    rw [L_coe]
    have hrow := (summable_row hcol c k).norm
    refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq ?_)
    · simpa only [norm_mul] using hrow
    · exact tsum_congr (fun l => by rw [norm_mul])

  have step2 : (∑' k : ℤ, ∑' l : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖)
      = ∑' l : ℤ, ∑' k : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖ := hFsum.tsum_comm.symm

  have hsum_l : Summable (fun l : ℤ => ∑' k : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖) :=
    hFsum.prod_symm.prod
  have step3 : (∑' l : ℤ, ∑' k : ℤ, ‖A k l‖ * ‖(c : ℤ → ℂ) l‖)
      ≤ ∑' l : ℤ, M * ‖(c : ℤ → ℂ) l‖ := by
    refine hsum_l.tsum_le_tsum (fun l => ?_) (hc.mul_left M)
    rw [(hcol l).1.tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hcol l).2 (norm_nonneg _)
  calc (∑' k : ℤ, ‖(L hcol c : ℤ → ℂ) k‖)
      ≤ _ := step1
    _ = _ := step2
    _ ≤ ∑' l : ℤ, M * ‖(c : ℤ → ℂ) l‖ := step3
    _ = M * ∑' l : ℤ, ‖(c : ℤ → ℂ) l‖ := tsum_mul_left

end Assembly.Hard

namespace Assembly.Endgame

open Assembly.E7


theorem opnorm_l1_col_sup_proof
    (A : ℤ → ℤ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hcol : ∀ l : ℤ, Summable (fun k : ℤ => ‖A k l‖) ∧ ∑' k : ℤ, ‖A k l‖ ≤ M) :
    ∃ T : Assembly.E7.ℓ1 →L[ℂ] Assembly.E7.ℓ1,
      (∀ (c : Assembly.E7.ℓ1) (k : ℤ),
        (T c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l) ∧ ‖T‖ ≤ M := by
  refine ⟨(Assembly.Hard.L hcol).mkContinuous M (Assembly.Hard.L_norm_le hcol), ?_, ?_⟩
  · intro c k
    exact Assembly.Hard.L_coe hcol c k
  · exact (Assembly.Hard.L hcol).mkContinuous_norm_le hM (Assembly.Hard.L_norm_le hcol)

end Assembly.Endgame
