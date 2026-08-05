import LeanCode.Vendor.E5.P9.Part9.Defs
import LeanCode.Vendor.E5.Defs

open scoped BigOperators









noncomputable def Fc (g : ℝ → ℝ) (c : ℝ) (x : ℝ) : ℝ := Acol g x - c * Bcol g x



noncomputable def Ftrunc (g : ℝ → ℝ) (c : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g (x + 2 * (n : ℝ)))
    - c * ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g (x - 1 + 2 * (n : ℝ))



theorem lem_summable (g : ℝ → ℝ) {C c0 : ℝ} (hC : 0 < C) (hc0 : 0 < c0)
    (hg : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c0 * |x|)) (y : ℝ) :
    Summable (fun n : ℤ => |g (y + 2 * (n : ℝ))|) ∧
      (∑' n : ℤ, |g (y + 2 * (n : ℝ))|)
        ≤ C * Real.exp (c0 * |y|) * ((1 + Real.exp (-2 * c0)) / (1 - Real.exp (-2 * c0))) := by
  set ρ := Real.exp (-2 * c0) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    have h := Real.exp_lt_exp.mpr (show -2 * c0 < 0 by linarith)
    rwa [Real.exp_zero] at h
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := fun h => by linarith
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
  refine ⟨hSum, ?_⟩

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
  calc (∑' n : ℤ, |g (y + 2 * (n : ℝ))|)
      ≤ ∑' n : ℤ, D * ρ ^ n.natAbs := Summable.tsum_le_tsum hpt hSum hsumρ
    _ = D * ∑' n : ℤ, ρ ^ n.natAbs := tsum_mul_left
    _ = D * ((1 + ρ) / (1 - ρ)) := by rw [htsum]



theorem lem_periodic (g : ℝ → ℝ) (c : ℝ) (x : ℝ) (k : ℤ) :
    Acol g (x + 2 * (k : ℝ)) = Acol g x ∧
      Bcol g (x + 2 * (k : ℝ)) = Bcol g x ∧
      Fc g c (x + 2 * (k : ℝ)) = Fc g c x := by
  have shift : ∀ h : ℝ,
      (∑' n : ℤ, g (h + 2 * (k : ℝ) + 2 * (n : ℝ))) = ∑' n : ℤ, g (h + 2 * (n : ℝ)) := by
    intro h
    rw [← Equiv.tsum_eq (Equiv.addRight k) (fun m : ℤ => g (h + 2 * (m : ℝ)))]
    apply tsum_congr
    intro n
    congr 1
    simp only [Equiv.coe_addRight]
    push_cast
    ring
  have hA : Acol g (x + 2 * (k : ℝ)) = Acol g x := by
    simp only [Acol]; exact shift x
  have hB : Bcol g (x + 2 * (k : ℝ)) = Bcol g x := by
    simp only [Bcol]
    have hs := shift (x - 1)
    have e1 : (∑' n : ℤ, g (x + 2 * (k : ℝ) - 1 + 2 * (n : ℝ)))
            = ∑' n : ℤ, g (x - 1 + 2 * (k : ℝ) + 2 * (n : ℝ)) := by
      apply tsum_congr; intro n; congr 1; ring
    rw [e1]; exact hs
  have hF : Fc g c (x + 2 * (k : ℝ)) = Fc g c x := by
    simp only [Fc, hA, hB]
  exact ⟨hA, hB, hF⟩
