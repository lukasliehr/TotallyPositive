import LeanCode.Vendor.E5.P9.Part9.Basic
import LeanCode.Vendor.E5.Defs

open scoped BigOperators










theorem lem_tail (g : ℝ → ℝ) {C c0 : ℝ} (hC : 0 < C) (hc0 : 0 < c0)
    (hg : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c0 * |x|)) (y : ℝ) (N : ℕ) :
    (∑' n : ↥(((Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ), |g (y + 2 * ((n : ℤ) : ℝ))|)
      ≤ 2 * C * Real.exp (c0 * |y|) * Real.exp (-2 * c0 * ((N : ℝ) + 1)) / (1 - Real.exp (-2 * c0)) := by
  set ρ := Real.exp (-2 * c0) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    have h := Real.exp_lt_exp.mpr (show -2 * c0 < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hden : 0 < 1 - ρ := by linarith
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := ne_of_gt hden
  set D := C * Real.exp (c0 * |y|) with hDdef
  have hpt : ∀ n : ℤ, |g (y + 2 * (n : ℝ))| ≤ D * ρ ^ n.natAbs := by
    intro n
    have h1 : |g (y + 2 * (n : ℝ))| ≤ C * Real.exp (-c0 * |y + 2 * (n : ℝ)|) := hg _
    have htri : 2 * |(n : ℝ)| - |y| ≤ |y + 2 * (n : ℝ)| := by
      have hrev := abs_sub_abs_le_abs_sub (2 * (n : ℝ)) (-y)
      have e2 : |2 * (n : ℝ)| = 2 * |(n : ℝ)| := by rw [abs_mul]; norm_num
      calc 2 * |(n : ℝ)| - |y| = |2 * (n : ℝ)| - |(-y)| := by rw [e2, abs_neg]
        _ ≤ |2 * (n : ℝ) - (-y)| := hrev
        _ = |y + 2 * (n : ℝ)| := by rw [sub_neg_eq_add, add_comm]
    have hnat : (↑n.natAbs : ℝ) = |(n : ℝ)| := by simp
    have hexp : Real.exp (-c0 * |y + 2 * (n : ℝ)|) ≤ Real.exp (c0 * |y|) * ρ ^ n.natAbs := by
      have hle : -c0 * |y + 2 * (n : ℝ)| ≤ c0 * |y| + (↑n.natAbs : ℝ) * (-2 * c0) := by
        rw [hnat]; nlinarith [mul_le_mul_of_nonneg_left htri hc0.le]
      calc Real.exp (-c0 * |y + 2 * (n : ℝ)|)
          ≤ Real.exp (c0 * |y| + (↑n.natAbs : ℝ) * (-2 * c0)) := Real.exp_le_exp.mpr hle
        _ = Real.exp (c0 * |y|) * Real.exp ((↑n.natAbs : ℝ) * (-2 * c0)) := Real.exp_add _ _
        _ = Real.exp (c0 * |y|) * ρ ^ n.natAbs := by rw [Real.exp_nat_mul, ← hρdef]
    calc |g (y + 2 * (n : ℝ))| ≤ C * Real.exp (-c0 * |y + 2 * (n : ℝ)|) := h1
      _ ≤ C * (Real.exp (c0 * |y|) * ρ ^ n.natAbs) := mul_le_mul_of_nonneg_left hexp hC.le
      _ = D * ρ ^ n.natAbs := by rw [hDdef]; ring
  have hsummN : Summable (fun n : ℕ => ρ ^ n) := summable_geometric_of_lt_one hρ0.le hρ1
  have hsumm : Summable (fun n : ℤ => ρ ^ n.natAbs) := by
    rw [summable_int_iff_summable_nat_and_neg]; refine ⟨?_, ?_⟩ <;> simpa using hsummN
  have hsumρ : Summable (fun n : ℤ => D * ρ ^ n.natAbs) := hsumm.mul_left D
  have hSum : Summable (fun n : ℤ => |g (y + 2 * (n : ℝ))|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpt hsumρ
  have hstep1 :
      (∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), |g (y + 2*((n:ℤ):ℝ))|)
        ≤ ∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), D * ρ ^ (n:ℤ).natAbs := by
    apply Summable.tsum_le_tsum
    · intro n; exact hpt n
    · exact hSum.subtype _
    · exact hsumρ.subtype _
  have hcompl :
      (∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), D * ρ ^ (n:ℤ).natAbs)
        = (∑' n : ℤ, D * ρ ^ n.natAbs) - ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), D * ρ ^ n.natAbs := by
    have key := hsumρ.sum_add_tsum_compl (s := Finset.Icc (-(N:ℤ)) (N:ℤ))
    linarith [key]
  have hev : (fun n : ℤ => ρ ^ n.natAbs).Even := by intro n; simp [Int.natAbs_neg]
  have hpnat : (∑' n : ℕ+, ρ ^ ((n : ℤ).natAbs)) = ρ / (1 - ρ) := by
    have e : (∑' n : ℕ+, ρ ^ ((n : ℤ).natAbs)) = ∑' n : ℕ, ρ ^ (n + 1) := by
      rw [← Equiv.pnatEquivNat.symm.tsum_eq]; apply tsum_congr; intro m; congr 1
    rw [e]; simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hρ0.le hρ1, div_eq_inv_mul]
  have htsum : (∑' n : ℤ, ρ ^ n.natAbs) = (1 + ρ) / (1 - ρ) := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hev hsumm, hpnat]
    simp only [Int.natAbs_zero, pow_zero, nsmul_eq_mul]
    rw [eq_div_iff h1ρ]; field_simp; ring
  have hfull : (∑' n : ℤ, D * ρ ^ n.natAbs) = D * ((1 + ρ) / (1 - ρ)) := by
    rw [tsum_mul_left, htsum]
  have hfin0 : ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ρ ^ n.natAbs
      = 2 * (∑ j ∈ Finset.range (N+1), ρ ^ j) - 1 := by
    have hsplit : ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ρ ^ n.natAbs
        = ∑ k ∈ Finset.Icc (0:ℤ) N, ρ ^ k.natAbs + ∑ k ∈ Finset.Icc (-(N:ℤ)) (-1), ρ ^ k.natAbs := by
      rw [← Finset.sum_union]
      · congr 1; ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      · rw [Finset.disjoint_left]; intro a ha hb
        simp only [Finset.mem_Icc] at ha hb; omega
    have hpos : ∑ k ∈ Finset.Icc (0:ℤ) N, ρ ^ k.natAbs = ∑ j ∈ Finset.range (N+1), ρ ^ j := by
      rw [Finset.sum_bij' (i := fun (k:ℤ) (_ : k ∈ Finset.Icc (0:ℤ) N) => k.toNat)
          (j := fun (j:ℕ) (_ : j ∈ Finset.range (N+1)) => (j:ℤ))]
      · intro a ha; simp only [Finset.mem_Icc] at ha; simp only [Finset.mem_range]; omega
      · intro a ha; simp only [Finset.mem_range] at ha; simp only [Finset.mem_Icc]; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha; omega
      · intro a ha; simp only [Finset.mem_range] at ha; simp
      · intro a ha; simp only [Finset.mem_Icc] at ha; congr 1; omega
    have hneg : ∑ k ∈ Finset.Icc (-(N:ℤ)) (-1), ρ ^ k.natAbs = ∑ j ∈ Finset.Icc 1 N, ρ ^ j := by
      rw [Finset.sum_bij' (i := fun (k:ℤ) (_ : k ∈ Finset.Icc (-(N:ℤ)) (-1)) => (-k).toNat)
          (j := fun (j:ℕ) (_ : j ∈ Finset.Icc 1 N) => -(j:ℤ))]
      · intro a ha; simp only [Finset.mem_Icc] at ha; simp only [Finset.mem_Icc]; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha; simp only [Finset.mem_Icc]; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha; congr 1; omega
    have hIcc1N : ∑ j ∈ Finset.Icc 1 N, ρ ^ j = (∑ j ∈ Finset.range (N+1), ρ ^ j) - ρ^0 := by
      have h := (show (∑ j ∈ Finset.range (N+1), ρ ^ j) = ρ^0 + ∑ j ∈ Finset.Icc 1 N, ρ ^ j by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N+1)]
        rw [show Finset.Ico 1 (N+1) = Finset.Icc 1 N from ?_]
        · ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega)
      linarith
    rw [hsplit, hpos, hneg, hIcc1N]; simp only [pow_zero]; ring
  have hrange : ∑ j ∈ Finset.range (N+1), ρ ^ j = (1 - ρ^(N+1))/(1-ρ) := by
    rw [geom_sum_eq (ne_of_lt hρ1) (N+1)]
    have hne : ρ - 1 ≠ 0 := by intro h; apply h1ρ; linarith
    field_simp
    ring
  have hfin : ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), D * ρ ^ n.natAbs
      = D * (2 * (∑ j ∈ Finset.range (N+1), ρ ^ j) - 1) := by
    rw [← Finset.mul_sum, hfin0]
  have hρpow : ρ ^ (N+1) = Real.exp (-2 * c0 * ((N:ℝ)+1)) := by
    rw [hρdef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc (∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), |g (y + 2*((n:ℤ):ℝ))|)
      ≤ ∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), D * ρ ^ (n:ℤ).natAbs := hstep1
    _ = (∑' n : ℤ, D * ρ ^ n.natAbs) - ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), D * ρ ^ n.natAbs := hcompl
    _ = D * ((1 + ρ) / (1 - ρ)) - D * (2 * ((1 - ρ^(N+1))/(1-ρ)) - 1) := by
        rw [hfull, hfin, hrange]
    _ = 2 * D * ρ^(N+1) / (1 - ρ) := by
        field_simp
        ring
    _ = 2 * C * Real.exp (c0 * |y|) * Real.exp (-2 * c0 * ((N : ℝ) + 1)) / (1 - ρ) := by
        rw [hρpow, hDdef]; ring


theorem lem_truncdiff (g : ℝ → ℝ) {C c0 : ℝ} (hC : 0 < C) (hc0 : 0 < c0)
    (hg : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c0 * |x|)) {c : ℝ} (hc : 0 < c) (N : ℕ) (x : ℝ) :
    |Fc g c x - Ftrunc g c N x|
      ≤ 2 * C * (1 + c) * Real.exp (c0 * (|x| + 1)) * Real.exp (-2 * c0 * ((N : ℝ) + 1))
          / (1 - Real.exp (-2 * c0)) := by
  set ρ := Real.exp (-2 * c0) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    have h := Real.exp_lt_exp.mpr (show -2 * c0 < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hden : 0 < 1 - ρ := by linarith
  have hSA : Summable (fun n : ℤ => g (x + 2*(n:ℝ))) :=
    summable_abs_iff.mp (lem_summable g hC hc0 hg x).1
  have hSB : Summable (fun n : ℤ => g (x - 1 + 2*(n:ℝ))) :=
    summable_abs_iff.mp (lem_summable g hC hc0 hg (x-1)).1
  have hSAabs : Summable (fun n : ℤ => |g (x + 2*(n:ℝ))|) := (lem_summable g hC hc0 hg x).1
  have hSBabs : Summable (fun n : ℤ => |g (x - 1 + 2*(n:ℝ))|) := (lem_summable g hC hc0 hg (x-1)).1
  have hsplitA := hSA.sum_add_tsum_compl (s := Finset.Icc (-(N:ℤ)) (N:ℤ))
  have hsplitB := hSB.sum_add_tsum_compl (s := Finset.Icc (-(N:ℤ)) (N:ℤ))
  have htailA : (∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), g (x + 2*((n:ℤ):ℝ)))
      = Acol g x - ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), g (x + 2*(n:ℝ)) := by
    simp only [Acol]; linarith [hsplitA]
  have htailB : (∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), g (x - 1 + 2*((n:ℤ):ℝ)))
      = Bcol g x - ∑ n ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), g (x - 1 + 2*(n:ℝ)) := by
    simp only [Bcol]; linarith [hsplitB]
  have hid : Fc g c x - Ftrunc g c N x
      = (∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), g (x + 2*((n:ℤ):ℝ)))
        - c * (∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), g (x - 1 + 2*((n:ℤ):ℝ))) := by
    rw [htailA, htailB]; simp only [Fc, Ftrunc]; ring
  have habsA : |∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), g (x + 2*((n:ℤ):ℝ))|
      ≤ ∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), |g (x + 2*((n:ℤ):ℝ))| := by
    have h := norm_tsum_le_tsum_norm (f := fun n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ) => g (x + 2*((n:ℤ):ℝ)))
      (by
        have : Summable (fun n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ) => |g (x + 2*((n:ℤ):ℝ))|) :=
          hSAabs.subtype _
        simpa [Real.norm_eq_abs] using this)
    simpa [Real.norm_eq_abs] using h
  have habsB : |∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), g (x - 1 + 2*((n:ℤ):ℝ))|
      ≤ ∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), |g (x - 1 + 2*((n:ℤ):ℝ))| := by
    have h := norm_tsum_le_tsum_norm (f := fun n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ) => g (x - 1 + 2*((n:ℤ):ℝ)))
      (by
        have : Summable (fun n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ) => |g (x - 1 + 2*((n:ℤ):ℝ))|) :=
          hSBabs.subtype _
        simpa [Real.norm_eq_abs] using this)
    simpa [Real.norm_eq_abs] using h
  set TA := ∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), g (x + 2*((n:ℤ):ℝ)) with hTAdef
  set TB := ∑' n : ↥(((Finset.Icc (-(N:ℤ)) (N:ℤ)) : Set ℤ)ᶜ), g (x - 1 + 2*((n:ℤ):ℝ)) with hTBdef
  have hTailA := lem_tail g hC hc0 hg x N
  have hTailB := lem_tail g hC hc0 hg (x-1) N
  rw [← hρdef] at hTailA hTailB
  have hEA : Real.exp (c0 * |x|) ≤ Real.exp (c0 * (|x| + 1)) := by
    apply Real.exp_le_exp.mpr; nlinarith [abs_nonneg x]
  have hEB : Real.exp (c0 * |x - 1|) ≤ Real.exp (c0 * (|x| + 1)) := by
    apply Real.exp_le_exp.mpr
    have : |x - 1| ≤ |x| + 1 := by
      calc |x - 1| ≤ |x| + |(1:ℝ)| := abs_sub _ _
        _ = |x| + 1 := by norm_num
    nlinarith
  set E := Real.exp (c0 * (|x|+1)) with hEdef
  set eN := Real.exp (-2 * c0 * ((N:ℝ)+1)) with heNdef
  have heNpos : 0 < eN := Real.exp_pos _
  have hbA : |TA| ≤ 2 * C * E * eN / (1 - ρ) := by
    refine le_trans habsA (le_trans hTailA ?_)
    gcongr
  have hbB : |TB| ≤ 2 * C * E * eN / (1 - ρ) := by
    refine le_trans habsB (le_trans hTailB ?_)
    gcongr
  have htri : |TA - c * TB| ≤ |TA| + c * |TB| := by
    calc |TA - c * TB| ≤ |TA| + |c * TB| := by
          rw [sub_eq_add_neg]; exact le_trans (abs_add_le _ _) (by rw [abs_neg])
      _ = |TA| + c * |TB| := by rw [abs_mul, abs_of_pos hc]
  rw [hid]
  have hfinal : 2 * C * E * eN / (1 - ρ) + c * (2 * C * E * eN / (1 - ρ))
      = 2 * C * (1 + c) * E * eN / (1 - ρ) := by ring
  calc |TA - c * TB| ≤ |TA| + c * |TB| := htri
    _ ≤ 2 * C * E * eN / (1 - ρ) + c * (2 * C * E * eN / (1 - ρ)) := by
        gcongr
    _ = 2 * C * (1 + c) * E * eN / (1 - ρ) := hfinal




theorem lem_truncation (g : ℝ → ℝ) {C c0 : ℝ} (hC : 0 < C) (hc0 : 0 < c0)
    (hg : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c0 * |x|)) {c : ℝ} (hc : 0 < c)
    (K : ℝ) (hK : 0 ≤ K) (η : ℝ) (hη : 0 < η) :
    ∃ L0 : ℕ, ∀ M : ℕ, ∀ L : ℕ, L0 ≤ L → ∀ x : ℝ, |x| ≤ K + 2 * (M : ℝ) →
      |Fc g c x - Ftrunc g c (M + L) x| < η := by
  set ρ := Real.exp (-2 * c0) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    have h := Real.exp_lt_exp.mpr (show -2 * c0 < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hden : 0 < 1 - ρ := by linarith
  set D0 := 2 * C * (1 + c) * Real.exp (c0 * (K - 1)) / (1 - ρ) with hD0def
  have hD0 : 0 < D0 := by
    rw [hD0def]; positivity
  refine ⟨⌈max 0 (Real.log (D0/η) / (2*c0))⌉₊ + 1, ?_⟩
  intro M L hL x hx
  set L0 := ⌈max 0 (Real.log (D0/η) / (2*c0))⌉₊ + 1 with hL0def
  have htd := lem_truncdiff g hC hc0 hg hc (M + L) x
  rw [← hρdef] at htd
  have hreduce :
      2 * C * (1 + c) * Real.exp (c0 * (|x| + 1)) * Real.exp (-2 * c0 * (((M+L:ℕ):ℝ) + 1)) / (1 - ρ)
        ≤ D0 * Real.exp (-2 * c0 * (L:ℝ)) := by
    rw [hD0def, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hden]
    have hcoef : 0 ≤ 2 * C * (1 + c) := by positivity
    rw [mul_assoc (2 * C * (1 + c)), mul_assoc (2 * C * (1 + c)), ← Real.exp_add, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left ?_ hcoef
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [hx]
  have hlt : D0 * Real.exp (-2 * c0 * (L:ℝ)) < η := by
    have hkey : Real.exp (-2 * c0 * (L:ℝ)) < η / D0 := by
      rw [show η / D0 = Real.exp (Real.log (η/D0)) from (Real.exp_log (by positivity)).symm]
      apply Real.exp_lt_exp.mpr
      have hlogdiv : Real.log (η/D0) = - Real.log (D0/η) := by
        rw [Real.log_div (ne_of_gt hη) (ne_of_gt hD0), Real.log_div (ne_of_gt hD0) (ne_of_gt hη)]
        ring
      rw [hlogdiv]
      have hL0gt : Real.log (D0/η) / (2*c0) < (L0:ℝ) := by
        rw [hL0def]; push_cast
        have h1 : (⌈max 0 (Real.log (D0/η) / (2*c0))⌉₊ : ℝ) ≥ max 0 (Real.log (D0/η) / (2*c0)) := Nat.le_ceil _
        have hmax : Real.log (D0/η) / (2*c0) ≤ max 0 (Real.log (D0/η) / (2*c0)) := le_max_right _ _
        linarith
      have hLL0 : (L0:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
      have h2c0 : 0 < 2*c0 := by linarith
      have : Real.log (D0/η) < 2*c0 * (L:ℝ) := by
        have hlt2 : Real.log (D0/η) < 2*c0 * (L0:ℝ) := by
          rw [div_lt_iff₀ h2c0] at hL0gt; linarith
        nlinarith
      linarith
    calc D0 * Real.exp (-2 * c0 * (L:ℝ)) < D0 * (η / D0) := mul_lt_mul_of_pos_left hkey hD0
      _ = η := by field_simp
  calc |Fc g c x - Ftrunc g c (M + L) x|
      ≤ 2 * C * (1 + c) * Real.exp (c0 * (|x| + 1)) * Real.exp (-2 * c0 * (((M+L:ℕ):ℝ) + 1)) / (1 - ρ) := htd
    _ ≤ D0 * Real.exp (-2 * c0 * (L:ℝ)) := hreduce
    _ < η := hlt
