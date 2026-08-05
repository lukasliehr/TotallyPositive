import LeanCode.Vendor.E5.P5.Part5.Basic
import LeanCode.Vendor.E5.Defs




open Polynomial

namespace Part5


noncomputable def FMD (μ : ℕ → ℝ) (M : ℕ) (r : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (M + 1),
    Polynomial.C (((-1 : ℝ) ^ i * μ i) / (i.factorial : ℝ)) *
      (Polynomial.derivative^[i] r)


noncomputable def PsiMD (β : ℕ → ℝ) (M : ℕ) (r : Polynomial ℝ) : Polynomial ℝ :=
  ∑ m ∈ Finset.range (M + 1),
    Polynomial.C ((β m) / (m.factorial : ℝ)) * (Polynomial.derivative^[m] r)


noncomputable def FD (μ : ℕ → ℝ) (r : Polynomial ℝ) : Polynomial ℝ :=
  FMD μ r.natDegree r


noncomputable def PsiD (β : ℕ → ℝ) (r : Polynomial ℝ) : Polynomial ℝ :=
  PsiMD β r.natDegree r



theorem iter_deriv_coeff (p : Polynomial ℝ) (m j : ℕ) :
    (Polynomial.derivative^[m] p).coeff j
      = ((j + m).factorial : ℝ) / (j.factorial : ℝ) * p.coeff (j + m) := by
  rw [Polynomial.coeff_iterate_derivative, nsmul_eq_mul]
  congr 1
  rw [Nat.descFactorial_eq_div (Nat.le_add_left m j), Nat.add_sub_cancel,
    Nat.cast_div (Nat.factorial_dvd_factorial (Nat.le_add_right j m))
      (by exact_mod_cast Nat.factorial_ne_zero j)]


theorem DmXn (m n : ℕ) :
    Polynomial.derivative^[m] (Polynomial.X ^ n : Polynomial ℝ)
      = if m ≤ n then
          Polynomial.C ((n.factorial : ℝ) / ((n - m).factorial : ℝ)) *
            Polynomial.X ^ (n - m)
        else 0 := by
  rw [Polynomial.iterate_derivative_X_pow_eq_C_mul]
  split_ifs with h
  · have hcast : ((n.descFactorial m : ℕ) : ℝ)
        = (n.factorial : ℝ) / ((n - m).factorial : ℝ) := by
      rw [Nat.descFactorial_eq_div h,
        Nat.cast_div (Nat.factorial_dvd_factorial (Nat.sub_le n m))
          (by exact_mod_cast Nat.factorial_ne_zero _)]
    rw [hcast]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp h), Nat.cast_zero,
      Polynomial.C_0, zero_mul]


theorem cutoff (μ β : ℕ → ℝ) (r : Polynomial ℝ) (M : ℕ) (hM : r.natDegree ≤ M) :
    FMD μ M r = FD μ r ∧ PsiMD β M r = PsiD β r := by
  have key : ∀ (a : ℕ → ℝ),
      (∑ i ∈ Finset.range (M + 1), Polynomial.C (a i) * Polynomial.derivative^[i] r)
        = ∑ i ∈ Finset.range (r.natDegree + 1),
            Polynomial.C (a i) * Polynomial.derivative^[i] r := by
    intro a
    refine (Finset.sum_subset ?_ ?_).symm
    · intro i hi
      rw [Finset.mem_range] at hi ⊢
      omega
    · intro i _ hi
      have hi' : r.natDegree < i := by rw [Finset.mem_range, not_lt] at hi; omega
      rw [Polynomial.iterate_derivative_eq_zero hi', mul_zero]
  refine ⟨?_, ?_⟩
  · simp only [FD, FMD]; exact key _
  · simp only [PsiD, PsiMD]; exact key _


theorem PsiD_coeff (β : ℕ → ℝ) (p : Polynomial ℝ) (j : ℕ) :
    (PsiD β p).coeff j
      = ∑ m ∈ Finset.range (p.natDegree + 1),
          ((j + m).choose m : ℝ) * β m * p.coeff (j + m) := by
  simp only [PsiD, PsiMD]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m _
  rw [Polynomial.coeff_C_mul, iter_deriv_coeff, Nat.cast_choose ℝ (Nat.le_add_left m j),
    Nat.add_sub_cancel]
  have hm0 : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hj0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp


theorem PsiD_degree (β : ℕ → ℝ) (hβ : β 0 ≠ 0) (p : Polynomial ℝ) (hp : p ≠ 0) :
    (PsiD β p).natDegree = p.natDegree ∧
      (PsiD β p).leadingCoeff = β 0 * p.leadingCoeff := by
  set n := p.natDegree with hn
  have hcoeffn : (PsiD β p).coeff n = β 0 * p.leadingCoeff := by
    rw [PsiD_coeff, Finset.sum_eq_single 0
      (fun m _ hm0 => by
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero])
      (fun h0 => absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0)]
    simp only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
    show β 0 * p.coeff n = β 0 * p.coeff p.natDegree
    rw [← hn]
  have hupper : ∀ j, n < j → (PsiD β p).coeff j = 0 := by
    intro j hj
    rw [PsiD_coeff]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  have hne : (PsiD β p).coeff n ≠ 0 := by
    rw [hcoeffn]
    exact mul_ne_zero hβ (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hdeg : (PsiD β p).natDegree = n :=
    le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hupper)
      (Polynomial.le_natDegree_of_ne_zero hne)
  refine ⟨hdeg, ?_⟩
  show (PsiD β p).coeff (PsiD β p).natDegree = β 0 * p.leadingCoeff
  rw [hdeg]; exact hcoeffn


theorem taylor_identity (r : Polynomial ℝ) (d : ℕ) (hd : r.natDegree ≤ d)
    (x y : ℝ) :
    r.eval (x - y)
      = ∑ i ∈ Finset.range (d + 1),
          (Polynomial.derivative^[i] r).eval x / (i.factorial : ℝ) * (-y) ^ i := by
  have hsub : r.eval (x - y) = (Polynomial.taylor x r).eval (-y) := by
    rw [Polynomial.taylor_eval]; ring_nf
  rw [hsub,
    Polynomial.eval_eq_sum_range' (p := Polynomial.taylor x r) (n := d + 1)
      (by rw [Polynomial.natDegree_taylor]; omega) (-y)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.taylor_coeff]
  have hkey : (Polynomial.derivative^[i] r).eval x
      = (i.factorial : ℝ) * (Polynomial.hasseDeriv i r).eval x := by
    have hfun : (Polynomial.derivative^[i]) r
        = (i.factorial • Polynomial.hasseDeriv i) r := by
      rw [Polynomial.factorial_smul_hasseDeriv]
    rw [hfun, LinearMap.smul_apply, Polynomial.eval_smul, nsmul_eq_mul]
  rw [hkey]
  field_simp


theorem reflection (g : ℝ → ℝ) (hg : Continuous g) (C c : ℝ) (hC : 0 < C)
    (hc : 0 < c) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (r : Polynomial ℝ) (x : ℝ) :
    (∫ y, g (x - y) * r.eval y) = ∫ y, g y * r.eval (x - y) := by
  have h := MeasureTheory.integral_sub_left_eq_self
    (fun y => g y * r.eval (x - y)) MeasureTheory.volume x
  rw [← h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  have hy : x - (x - y) = y := by ring
  simp only [hy]


theorem conv_is_FD (g : ℝ → ℝ) (hg : Continuous g) (C c : ℝ) (hC : 0 < C)
    (hc : 0 < c) (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (r : Polynomial ℝ) (x : ℝ) :
    convPoly g r x = (FD (mom g) r).eval x := by
  have hconv : convPoly g r x = ∫ y, g y * r.eval (x - y) := by
    rw [convPoly]; exact reflection g hg C c hC hc hbound r x
  have htay : ∀ y : ℝ, g y * r.eval (x - y)
      = ∑ i ∈ Finset.range (r.natDegree + 1),
          ((Polynomial.derivative^[i] r).eval x / (i.factorial : ℝ) * (-1 : ℝ) ^ i) *
            (y ^ i * g y) := by
    intro y
    rw [taylor_identity r r.natDegree le_rfl x y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [neg_pow]; ring
  rw [hconv]
  simp_rw [htay]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
    (moment_integrand g hg C c hC hc hbound i).const_mul _)]
  simp only [FD, FMD]
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_const_mul, Polynomial.eval_mul, Polynomial.eval_C,
    show (∫ (y : ℝ), y ^ i * g y) = mom g i from rfl]
  ring


theorem FD_PsiD (μ β : ℕ → ℝ) (h0 : μ 0 * β 0 = 1)
    (hrec : ∀ k : ℕ, 0 < k →
      (∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (-1 : ℝ) ^ i * μ i * β (k - i)) = 0)
    (r : Polynomial ℝ) :
    FD μ (PsiD β r) = r := by
  set d := r.natDegree with hd
  have hdeg : (PsiD β r).natDegree ≤ d := by
    simp only [PsiD, PsiMD]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro m _
    calc (Polynomial.C (β m / (m.factorial : ℝ)) * Polynomial.derivative^[m] r).natDegree
        ≤ (Polynomial.derivative^[m] r).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ r.natDegree - m := Polynomial.natDegree_iterate_derivative _ _
      _ ≤ d := by rw [hd]; exact Nat.sub_le _ _
  have hcut : FD μ (PsiD β r) = FMD μ d (PsiD β r) := (cutoff μ β (PsiD β r) d hdeg).1.symm
  apply Polynomial.ext
  intro j
  rw [hcut]
  have step1 : (FMD μ d (PsiD β r)).coeff j
      = ∑ i ∈ Finset.range (d + 1),
          ∑ m ∈ Finset.range (d + 1),
            ((-1 : ℝ) ^ i * μ i / (i.factorial : ℝ)) *
              (((j + i).factorial : ℝ) / (j.factorial : ℝ) *
                (((j + i + m).choose m : ℝ) * β m * r.coeff (j + i + m))) := by
    simp only [FMD]
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.coeff_C_mul, iter_deriv_coeff, PsiD_coeff, ← hd, Finset.mul_sum, Finset.mul_sum]
  rw [step1]
  set G : ℕ → ℕ → ℝ := fun i m =>
    ((-1 : ℝ) ^ i * μ i / (i.factorial : ℝ)) *
      (((j + i).factorial : ℝ) / (j.factorial : ℝ) *
        (((j + i + m).choose m : ℝ) * β m * r.coeff (j + i + m))) with hG
  change (∑ i ∈ Finset.range (d + 1), ∑ m ∈ Finset.range (d + 1), G i m) = r.coeff j
  have hGzero : ∀ i m : ℕ, d < i + m → G i m = 0 := by
    intro i m hlt
    simp only [hG]
    have : r.coeff (j + i + m) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [← hd]; omega
    rw [this]; ring
  have hkill : ∀ i ∈ Finset.range (d + 1),
      (∑ m ∈ Finset.range (d + 1), G i m) = ∑ m ∈ Finset.range (d - i + 1), G i m := by
    intro i hi
    rw [Finset.mem_range] at hi
    refine (Finset.sum_subset ?_ ?_).symm
    · intro m hm
      rw [Finset.mem_range] at hm ⊢
      omega
    · intro m hm hm'
      rw [Finset.mem_range] at hm hm'
      exact hGzero i m (by omega)
  rw [Finset.sum_congr rfl hkill]
  have reindex : (∑ i ∈ Finset.range (d + 1), ∑ m ∈ Finset.range (d - i + 1), G i m)
      = ∑ k ∈ Finset.range (d + 1), ∑ i ∈ Finset.range (k + 1), G i (k - i) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun x => ⟨x.1 + x.2, x.1⟩) (fun x => ⟨x.2, x.1 - x.2⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨i, m⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
      omega
    · rintro ⟨k, i⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
      omega
    · rintro ⟨i, m⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [Nat.add_sub_cancel_left]
    · rintro ⟨k, i⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      have : i ≤ k := by omega
      simp only [Nat.add_sub_cancel' this]
    · rintro ⟨i, m⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [Nat.add_sub_cancel_left]
  rw [reindex]
  have hj0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hSk : ∀ k : ℕ, 0 < k → (∑ i ∈ Finset.range (k + 1), G i (k - i)) = 0 := by
    intro k hk
    have key : (∑ i ∈ Finset.range (k + 1), G i (k - i))
        = (r.coeff (j + k) * ((j + k).factorial : ℝ) / ((j.factorial : ℝ) * (k.factorial : ℝ))) *
            (∑ i ∈ Finset.range (k + 1),
              (k.choose i : ℝ) * (-1 : ℝ) ^ i * μ i * β (k - i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      simp only [hG]
      have hik : i + (k - i) = k := Nat.add_sub_cancel' hi
      have hjk : j + i + (k - i) = j + k := by omega
      rw [hjk]
      have hchoose1 : ((j + k).choose (k - i) : ℝ)
          = ((j + k).factorial : ℝ) / (((k - i).factorial : ℝ) * ((j + i).factorial : ℝ)) := by
        rw [Nat.cast_choose ℝ (by omega : k - i ≤ j + k)]
        have hsub : (j + k) - (k - i) = j + i := by omega
        rw [hsub]
      have hchoose2 : (k.choose i : ℝ)
          = (k.factorial : ℝ) / ((i.factorial : ℝ) * ((k - i).factorial : ℝ)) := by
        rw [Nat.cast_choose ℝ hi]
      rw [hchoose1, hchoose2]
      have hi0 : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
      have hki0 : ((k - i).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - i)
      have hji0 : ((j + i).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j + i)
      have hk0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      field_simp
    rw [key, hrec k hk, mul_zero]
  rw [Finset.sum_eq_single 0 (fun k _ hk => hSk k (Nat.pos_of_ne_zero hk))
    (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos d)) h)]
  rw [Finset.sum_range_one]
  have hval : G 0 (0 - 0) = μ 0 * β 0 * r.coeff j := by
    simp only [hG, Nat.sub_zero, Nat.add_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      Nat.choose_zero_right, one_mul, div_one]
    rw [div_self hj0]
    ring
  rw [hval, h0, one_mul]


theorem Jensen_form (β : ℕ → ℝ) (n : ℕ) :
    PsiD β (Polynomial.X ^ n) = jensenPoly β n := by
  simp only [PsiD, PsiMD, Polynomial.natDegree_X_pow, jensenPoly]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range, Nat.lt_succ_iff] at hm
  rw [DmXn, if_pos hm, ← mul_assoc, ← Polynomial.C_mul]
  congr 2
  rw [Nat.cast_choose ℝ hm]
  have hm0 : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hnm0 : ((n - m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - m)
  field_simp

end Part5
