import LeanCode.Vendor.E5.P6.Part6.Basic
import LeanCode.Vendor.E5.Defs

open scoped BigOperators

namespace Part6







theorem prod_bound : ∀ (p : ℕ) (u : Fin p → ℂ),
    ‖∏ j, (1 + u j)‖ ≤ ∏ j, (1 + ‖u j‖) ∧
    ∏ j, (1 + ‖u j‖) ≤ Real.exp (∑ j, ‖u j‖) := by
  intro p u
  refine ⟨?_, ?_⟩
  · rw [norm_prod]
    refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
    have h := norm_add_le (1 : ℂ) (u j); rwa [norm_one] at h
  · rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => ?_)
    have := Real.add_one_le_exp ‖u j‖; linarith


private lemma prod_diff_aux {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖(∏ j ∈ s, (1 + u j)) - 1‖ ≤ (∏ j ∈ s, (1 + ‖u j‖)) - 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hone : (1 : ℝ) ≤ ∏ j ∈ s, (1 + ‖u j‖) := by
      have h := Finset.prod_le_prod (s := s) (f := fun _ => (1 : ℝ))
        (g := fun j => 1 + ‖u j‖) (fun j _ => zero_le_one)
        (fun j _ => by have := norm_nonneg (u j); linarith)
      simpa using h
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hbound : ‖1 + u a‖ ≤ 1 + ‖u a‖ := by
      have h := norm_add_le (1 : ℂ) (u a); rwa [norm_one] at h
    have hkey : (1 + u a) * (∏ j ∈ s, (1 + u j)) - 1
        = ((∏ j ∈ s, (1 + u j)) - 1) * (1 + u a) + u a := by ring
    calc ‖(1 + u a) * (∏ j ∈ s, (1 + u j)) - 1‖
        = ‖((∏ j ∈ s, (1 + u j)) - 1) * (1 + u a) + u a‖ := by rw [hkey]
      _ ≤ ‖((∏ j ∈ s, (1 + u j)) - 1) * (1 + u a)‖ + ‖u a‖ := norm_add_le _ _
      _ = ‖(∏ j ∈ s, (1 + u j)) - 1‖ * ‖1 + u a‖ + ‖u a‖ := by rw [norm_mul]
      _ ≤ ((∏ j ∈ s, (1 + ‖u j‖)) - 1) * (1 + ‖u a‖) + ‖u a‖ := by
            have hmul := mul_le_mul ih hbound (norm_nonneg _) (by linarith)
            linarith
      _ = (1 + ‖u a‖) * (∏ j ∈ s, (1 + ‖u j‖)) - 1 := by ring


theorem prod_diff : ∀ (p : ℕ) (u : Fin p → ℂ),
    ‖(∏ j, (1 + u j)) - 1‖ ≤ (∏ j, (1 + ‖u j‖)) - 1 ∧
    (∏ j, (1 + ‖u j‖)) - 1 ≤ Real.exp (∑ j, ‖u j‖) - 1 := by
  intro p u
  exact ⟨prod_diff_aux Finset.univ u, by have := (prod_bound p u).2; linarith⟩






theorem prod_conv : ∀ (w : ℕ → ℂ), Summable (fun ν => ‖w ν‖) →
    Multipliable (fun ν => 1 + w ν) ∧
    Filter.Tendsto (fun N => ∏ j ∈ Finset.range N, (1 + w j)) Filter.atTop
        (nhds (∏' ν, (1 + w ν))) ∧
    ∀ N : ℕ, ∃ LN : ℂ,
      Filter.Tendsto (fun J => ∏ j ∈ Finset.Ico N J, (1 + w j)) Filter.atTop (nhds LN) ∧
      ‖LN - 1‖ ≤ Real.exp (∑' ν, ‖w (N + ν)‖) - 1 ∧
      (∏' ν, (1 + w ν)) = (∏ j ∈ Finset.range N, (1 + w j)) * LN := by
  intro w hSummable
  have hMult : Multipliable (fun ν => 1 + w ν) := multipliable_one_add_of_summable hSummable
  have hTendsto : Filter.Tendsto (fun N => ∏ j ∈ Finset.range N, (1 + w j)) Filter.atTop
      (nhds (∏' ν, (1 + w ν))) := hMult.hasProd.tendsto_prod_nat
  refine ⟨hMult, hTendsto, ?_⟩
  intro N
  have hTailSummable : Summable (fun n => ‖w (n + N)‖) := (summable_nat_add_iff N).2 hSummable
  have hMultTail : Multipliable (fun n => 1 + w (n + N)) :=
    multipliable_one_add_of_summable hTailSummable
  have hsplit : (∏ i ∈ Finset.range N, (1 + w i)) * (∏' i, (1 + w (i + N)))
      = ∏' i, (1 + w i) :=
    Multipliable.prod_mul_tprod_nat_mul' (f := fun ν => 1 + w ν) (k := N) hMultTail
  set LN : ℂ := ∏' n, (1 + w (n + N)) with hLN_def
  refine ⟨LN, ?_, ?_, ?_⟩
  · have hstep : Filter.Tendsto (fun M => ∏ k ∈ Finset.range M, (1 + w (k + N))) Filter.atTop
        (nhds LN) := hMultTail.hasProd.tendsto_prod_nat
    have hcomp : Filter.Tendsto (fun J => ∏ k ∈ Finset.range (J - N), (1 + w (k + N)))
        Filter.atTop (nhds LN) := hstep.comp (Filter.tendsto_sub_atTop_nat N)
    apply hcomp.congr'
    filter_upwards with J
    rw [Finset.prod_Ico_eq_prod_range]
    apply Finset.prod_congr rfl
    intro k _
    rw [add_comm N k]
  · have hnormcont : Continuous (fun z : ℂ => ‖z - 1‖) := by fun_prop
    have hpartial : Filter.Tendsto (fun M => ‖(∏ k ∈ Finset.range M, (1 + w (k + N))) - 1‖)
        Filter.atTop (nhds ‖LN - 1‖) := by
      have h := (hnormcont.tendsto LN).comp hMultTail.hasProd.tendsto_prod_nat
      simpa [Function.comp_def] using h
    have htsum_eq : (∑' ν, ‖w (N + ν)‖) = ∑' n, ‖w (n + N)‖ := by
      apply tsum_congr; intro n; rw [add_comm N n]
    rw [htsum_eq]
    apply le_of_tendsto hpartial
    filter_upwards with M
    have hpd := Part6.prod_diff M (fun i : Fin M => w ((i : ℕ) + N))
    have hbound : ‖(∏ i : Fin M, (1 + w ((i : ℕ) + N))) - 1‖
        ≤ Real.exp (∑ i : Fin M, ‖w ((i : ℕ) + N)‖) - 1 := hpd.1.trans hpd.2
    have hprodeq : (∏ i : Fin M, (1 + w ((i : ℕ) + N))) = ∏ k ∈ Finset.range M, (1 + w (k + N)) :=
      Fin.prod_univ_eq_prod_range (fun k => 1 + w (k + N)) M
    have hsumeq : (∑ i : Fin M, ‖w ((i : ℕ) + N)‖) = ∑ k ∈ Finset.range M, ‖w (k + N)‖ :=
      Fin.sum_univ_eq_sum_range (fun k => ‖w (k + N)‖) M
    rw [hprodeq, hsumeq] at hbound
    refine hbound.trans ?_
    have hle : (∑ k ∈ Finset.range M, ‖w (k + N)‖) ≤ ∑' n, ‖w (n + N)‖ :=
      hTailSummable.sum_le_tsum (Finset.range M) (fun i _ => norm_nonneg _)
    have : Real.exp (∑ k ∈ Finset.range M, ‖w (k + N)‖) ≤ Real.exp (∑' n, ‖w (n + N)‖) :=
      Real.exp_le_exp.mpr hle
    linarith
  · exact hsplit.symm

end Part6
