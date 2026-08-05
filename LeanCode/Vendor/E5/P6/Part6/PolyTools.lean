import LeanCode.Vendor.E5.P6.Part6.Basic
import LeanCode.Vendor.E5.Defs

open scoped BigOperators

namespace Part6









theorem orth : ∀ (d : ℕ) (r : ℤ) (ω : ℂ),
    ω = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((d : ℂ) + 1)) →
    (∑ k ∈ Finset.range (d + 1), ω ^ ((k : ℤ) * r))
      = if ((d : ℤ) + 1) ∣ r then ((d : ℂ) + 1) else 0 := by
  intro d r ω hω
  have hd1 : (d + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero d
  have hprim : IsPrimitiveRoot ω (d + 1) := by
    rw [hω]
    have := Complex.isPrimitiveRoot_exp (d + 1) hd1
    convert this using 2
    push_cast; ring
  split_ifs with hdvd
  · have hωr : ω ^ r = 1 := by
      rw [hprim.zpow_eq_one_iff_dvd]; exact_mod_cast hdvd
    have hterm : ∀ k ∈ Finset.range (d + 1), ω ^ ((k : ℤ) * r) = 1 := by
      intro k _; rw [mul_comm, zpow_mul, zpow_natCast, hωr, one_pow]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]; simp
  · have hωr : ω ^ r ≠ 1 := by
      rw [Ne, hprim.zpow_eq_one_iff_dvd]; intro h; exact hdvd (by exact_mod_cast h)
    have hterm : ∀ k ∈ Finset.range (d + 1), ω ^ ((k : ℤ) * r) = (ω ^ r) ^ k := by
      intro k _; rw [mul_comm, zpow_mul, zpow_natCast]
    rw [Finset.sum_congr rfl hterm]
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · exact absurd (by subst hd0; simp) hdvd
    · have hpow : (ω ^ r) ^ (d + 1) = 1 := by
        rw [← zpow_natCast (ω ^ r) (d + 1), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
            hprim.pow_eq_one, one_zpow]
      rw [geom_sum_eq hωr, hpow]; simp




theorem dft : ∀ (d : ℕ) (c : ℕ → ℂ) (ρ : ℝ) (ω : ℂ),
    0 < ρ → ω = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((d : ℂ) + 1)) →
    ∀ m : ℕ, m ≤ d →
      c m = (((d : ℂ) + 1) * (ρ : ℂ) ^ m)⁻¹ *
        ∑ k ∈ Finset.range (d + 1),
          ω ^ (-((k : ℤ) * (m : ℤ))) *
            (∑ j ∈ Finset.range (d + 1), c j * ((ρ : ℂ) * ω ^ k) ^ j) := by
  intro d c ρ ω hρ hω m hm
  have hω0 : ω ≠ 0 := by rw [hω]; exact Complex.exp_ne_zero _
  have step1 : ∀ k ∈ Finset.range (d + 1),
      ω ^ (-((k : ℤ) * (m : ℤ))) *
        (∑ j ∈ Finset.range (d + 1), c j * ((ρ : ℂ) * ω ^ k) ^ j)
      = ∑ j ∈ Finset.range (d + 1),
          c j * (ρ : ℂ) ^ j * ω ^ ((k : ℤ) * ((j : ℤ) - (m : ℤ))) := by
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow, ← pow_mul, ← zpow_natCast ω (k * j)]
    push_cast
    rw [show ω ^ (-((k : ℤ) * (m : ℤ))) * (c j * ((ρ:ℂ)^j * ω ^ ((k:ℤ) * (j:ℤ))))
          = c j * (ρ:ℂ)^j * (ω ^ (-((k:ℤ) * (m:ℤ))) * ω ^ ((k:ℤ) * (j:ℤ))) by ring]
    rw [← zpow_add₀ hω0]
    ring_nf
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  have step2 : ∀ j ∈ Finset.range (d + 1),
      (∑ k ∈ Finset.range (d + 1), c j * (ρ : ℂ) ^ j * ω ^ ((k : ℤ) * ((j : ℤ) - (m : ℤ))))
      = c j * (ρ : ℂ) ^ j * (if ((d : ℤ) + 1) ∣ ((j : ℤ) - (m : ℤ)) then ((d : ℂ) + 1) else 0) := by
    intro j _
    rw [← Finset.mul_sum]
    congr 1
    have := Part6.orth d ((j : ℤ) - (m : ℤ)) ω hω
    rw [← this]
  rw [Finset.sum_congr rfl step2, Finset.sum_eq_single m]
  · have h0 : (↑m : ℤ) - ↑m = 0 := by ring
    rw [h0]
    simp only [dvd_zero, if_true]
    have hd1 : ((d : ℂ) + 1) ≠ 0 := by
      have : ((d : ℂ) + 1) = ((d + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast Nat.succ_ne_zero d
    have hrm : ((ρ : ℂ) ^ m) ≠ 0 := by
      apply pow_ne_zero; exact_mod_cast ne_of_gt hρ
    field_simp
  · intro j hj hjm
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    have hne : ((j : ℤ) - (m : ℤ)) ≠ 0 := by intro h; apply hjm; omega
    have hnd : ¬ ((↑d + 1 : ℤ) ∣ ((j : ℤ) - (m : ℤ))) := by
      intro hdvd
      have hpos : (0:ℤ) < |(j : ℤ) - (m : ℤ)| := abs_pos.mpr hne
      have hdvd2 : (↑d + 1 : ℤ) ∣ |(j : ℤ) - (m : ℤ)| := (dvd_abs _ _).mpr hdvd
      have hle := Int.le_of_dvd hpos hdvd2
      have hbnd : |(j : ℤ) - (m : ℤ)| ≤ (d:ℤ) := by rw [abs_le]; omega
      omega
    rw [if_neg hnd, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)) hmem




theorem coeff_bound : ∀ (d : ℕ) (c : ℕ → ℂ) (ρ C : ℝ),
    0 < ρ → (∀ m : ℕ, d < m → c m = 0) →
    (∀ z : ℂ, ‖z‖ = ρ → ‖∑ j ∈ Finset.range (d + 1), c j * z ^ j‖ ≤ C) →
    ∀ m : ℕ, ‖c m‖ ≤ C * ρ ^ (-(m : ℤ)) := by
  intro d c ρ C hρ hvan hbound m
  set ω : ℂ := Complex.exp (2*(Real.pi:ℂ)*Complex.I/((d:ℂ)+1)) with hω_def
  have hω_norm : ‖ω‖ = 1 := by
    have hexp : (2*(Real.pi:ℂ)*Complex.I/((d:ℂ)+1))
        = ((2*Real.pi/((d:ℝ)+1) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hω_def, hexp, Complex.norm_exp_ofReal_mul_I]
  have hρC : ‖(ρ:ℂ)‖ = ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hbound (ρ:ℂ) hρC)
  have hρm_pos : (0:ℝ) < ρ ^ (-(m:ℤ)) := zpow_pos hρ _
  rcases le_or_gt m d with hm | hm
  · have hdftc := Part6.dft d c ρ ω hρ hω_def m hm
    have hd1_pos : (0:ℝ) < (d:ℝ) + 1 := by positivity
    have hρpow_pos : (0:ℝ) < ρ ^ m := pow_pos hρ m
    have hpre_norm : ‖(((d:ℂ)+1)*(ρ:ℂ)^m)⁻¹‖ = 1 / (((d:ℝ)+1) * ρ ^ m) := by
      rw [norm_inv, Complex.norm_mul, Complex.norm_pow, hρC]
      have : ‖(d:ℂ)+1‖ = (d:ℝ)+1 := by
        rw [show ((d:ℂ)+1) = ((((d:ℝ)+1):ℝ):ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd1_pos]
      rw [this, one_div]
    have hsum_bound : ‖∑ k ∈ Finset.range (d+1),
        ω^(-((k:ℤ)*(m:ℤ))) * (∑ j ∈ Finset.range (d+1), c j * ((ρ:ℂ)*ω^k)^j)‖
        ≤ ((d:ℝ)+1) * C := by
      calc ‖∑ k ∈ Finset.range (d+1),
            ω^(-((k:ℤ)*(m:ℤ))) * (∑ j ∈ Finset.range (d+1), c j * ((ρ:ℂ)*ω^k)^j)‖
          ≤ ∑ k ∈ Finset.range (d+1),
            ‖ω^(-((k:ℤ)*(m:ℤ))) * (∑ j ∈ Finset.range (d+1), c j * ((ρ:ℂ)*ω^k)^j)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range (d+1), C := by
            apply Finset.sum_le_sum
            intro k _hk
            rw [norm_mul, Complex.norm_zpow, hω_norm]
            simp only [one_zpow, one_mul]
            apply hbound
            rw [norm_mul, Complex.norm_pow, hω_norm, one_pow, mul_one, hρC]
        _ = ((d:ℝ)+1) * C := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast; ring
    rw [hdftc, norm_mul, hpre_norm]
    calc (1 / (((d:ℝ)+1) * ρ ^ m)) * ‖∑ k ∈ Finset.range (d+1),
          ω^(-((k:ℤ)*(m:ℤ))) * (∑ j ∈ Finset.range (d+1), c j * ((ρ:ℂ)*ω^k)^j)‖
        ≤ (1 / (((d:ℝ)+1) * ρ ^ m)) * (((d:ℝ)+1) * C) := by
          apply mul_le_mul_of_nonneg_left hsum_bound
          positivity
      _ = C * ρ ^ (-(m:ℤ)) := by
          rw [zpow_neg, zpow_natCast]
          field_simp
  · rw [hvan m hm, norm_zero]
    positivity


private lemma coeff_sum_CX {d : ℕ} (a : ℕ → ℂ) {j : ℕ} (hjd : j ≤ d) :
    (∑ i ∈ Finset.range (d + 1), Polynomial.C (a i) * Polynomial.X ^ i).coeff j = a j := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro i _ hij
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hij), mul_zero]
  · intro hj
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hjd)) hj


theorem poly_ext : ∀ (d : ℕ) (a b : ℕ → ℂ),
    (∀ z : ℂ, (∑ j ∈ Finset.range (d + 1), a j * z ^ j)
              = ∑ j ∈ Finset.range (d + 1), b j * z ^ j) →
    ∀ j : ℕ, j ≤ d → a j = b j := by
  intro d a b hab j hjd
  have hPQ : (∑ i ∈ Finset.range (d + 1), Polynomial.C (a i) * Polynomial.X ^ i)
      = ∑ i ∈ Finset.range (d + 1), Polynomial.C (b i) * Polynomial.X ^ i := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact hab z
  have h := congrArg (fun p : Polynomial ℂ => p.coeff j) hPQ
  simpa only [coeff_sum_CX a hjd, coeff_sum_CX b hjd] using h



theorem vieta : ∀ (d : ℕ) (lam : ℕ → ℂ) (z : ℂ),
    (∏ j ∈ Finset.range d, (1 + lam j * z))
      = ∑ k ∈ Finset.range (d + 1),
          (∑ S ∈ Finset.powersetCard k (Finset.range d), ∏ i ∈ S, lam i) * z ^ k := by
  intro d lam z
  rw [Finset.prod_one_add, Finset.sum_powerset, Finset.card_range]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [Finset.mem_powersetCard] at hS
  rw [Finset.prod_mul_distrib, Finset.prod_const, hS.2]



theorem newton : ∀ (d : ℕ) (lam : ℕ → ℝ),
    (∑ j ∈ Finset.range d, lam j) ^ 2
      = (∑ j ∈ Finset.range d, (lam j) ^ 2)
        + 2 * ∑ S ∈ Finset.powersetCard 2 (Finset.range d), ∏ i ∈ S, lam i := by
  intro d lam
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← Finset.diag_union_offDiag (Finset.range d),
      Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  congr 1
  · rw [Finset.sum_diag]
    exact Finset.sum_congr rfl (fun j _ => by rw [sq])
  · have hstep : ∑ x ∈ (Finset.range d).offDiag, lam x.1 * lam x.2 =
        2 * ∑ x ∈ (Finset.range d).offDiag with x.1 < x.2, lam x.1 * lam x.2 := by
      rw [two_mul, ← Finset.sum_filter_add_sum_filter_not (Finset.range d).offDiag (fun p => p.1 < p.2)]
      congr 1
      apply Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_offDiag] at ha ⊢
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ha
        exact ⟨⟨h2, h1, fun h => h3 h.symm⟩, by omega⟩
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_offDiag] at ha ⊢
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ha
        exact ⟨⟨h2, h1, fun h => h3 h.symm⟩, by omega⟩
      · intro a _; rfl
      · intro a _; rfl
      · intro a _; simp only [mul_comm]
    rw [hstep]
    congr 1
    refine Finset.sum_bij'
      (i := fun p _ => ({p.1, p.2} : Finset ℕ))
      (j := fun S hS => (S.min' (by
          rw [Finset.mem_powersetCard] at hS; exact Finset.card_pos.mp (by omega)),
        S.max' (by
          rw [Finset.mem_powersetCard] at hS; exact Finset.card_pos.mp (by omega))))
      ?hi ?hj ?linv ?rinv ?hval
    case hi =>
      intro p hp
      rw [Finset.mem_filter, Finset.mem_offDiag] at hp
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hp
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair_eq_two_iff.mpr h3⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1
      · exact h2
    case hj =>
      intro S hS
      rw [Finset.mem_powersetCard] at hS
      obtain ⟨hsub, hcard⟩ := hS
      rw [Finset.mem_filter, Finset.mem_offDiag]
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      refine ⟨⟨hsub (Finset.min'_mem S hne), hsub (Finset.max'_mem S hne), ?_⟩, ?_⟩
      · exact ne_of_lt (Finset.min'_lt_max'_of_card S (by omega))
      · exact Finset.min'_lt_max'_of_card S (by omega)
    case linv =>
      intro p hp
      rw [Finset.mem_filter, Finset.mem_offDiag] at hp
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hp
      have hmin : ({p.1, p.2} : Finset ℕ).min' (by simp) = p.1 := by
        rw [Finset.min'_eq_iff]
        refine ⟨by simp, ?_⟩
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact le_refl _
        · exact le_of_lt h4
      have hmax : ({p.1, p.2} : Finset ℕ).max' (by simp) = p.2 := by
        rw [Finset.max'_eq_iff]
        refine ⟨by simp, ?_⟩
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact le_of_lt h4
        · exact le_refl _
      rw [Prod.ext_iff]
      exact ⟨hmin, hmax⟩
    case rinv =>
      intro S hS
      rw [Finset.mem_powersetCard] at hS
      obtain ⟨hsub, hcard⟩ := hS
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
      simp only
      rcases lt_or_gt_of_ne hxy with hlt | hlt
      · have ha : ({x, y} : Finset ℕ).min' (by simp) = x := by
          rw [Finset.min'_eq_iff]; refine ⟨by simp, ?_⟩
          rintro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl
          · exact le_refl _
          · exact le_of_lt hlt
        have hb : ({x, y} : Finset ℕ).max' (by simp) = y := by
          rw [Finset.max'_eq_iff]; refine ⟨by simp, ?_⟩
          rintro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl
          · exact le_of_lt hlt
          · exact le_refl _
        rw [ha, hb]
      · have ha : ({x, y} : Finset ℕ).min' (by simp) = y := by
          rw [Finset.min'_eq_iff]; refine ⟨by simp, ?_⟩
          rintro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl
          · exact le_of_lt hlt
          · exact le_refl _
        have hb : ({x, y} : Finset ℕ).max' (by simp) = x := by
          rw [Finset.max'_eq_iff]; refine ⟨by simp, ?_⟩
          rintro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl
          · exact le_refl _
          · exact le_of_lt hlt
        rw [ha, hb, Finset.pair_comm]
    case hval =>
      intro p hp
      rw [Finset.mem_filter, Finset.mem_offDiag] at hp
      rw [Finset.prod_pair hp.1.2.2]





theorem factorization : ∀ (d : ℕ) (a : ℕ → ℝ),
    a 0 = 1 → (∀ m : ℕ, d < m → a m = 0) →
    (∀ z : ℂ, (∑ m ∈ Finset.range (d + 1), (a m : ℂ) * z ^ m) = 0 → z.im = 0) →
    ∃ (D : ℕ) (lam : ℕ → ℝ), D ≤ d ∧ (∀ j : ℕ, j < D → lam j ≠ 0) ∧
      ∀ z : ℂ, (∑ m ∈ Finset.range (d + 1), (a m : ℂ) * z ^ m)
                = ∏ j ∈ Finset.range D, (1 + (lam j : ℂ) * z) := by
  classical
  intro d a ha0 hatail hreal
  set P : Polynomial ℂ :=
    ∑ m ∈ Finset.range (d + 1), Polynomial.C (a m : ℂ) * Polynomial.X ^ m with hPdef
  have hPeval : ∀ z : ℂ, P.eval z = ∑ m ∈ Finset.range (d + 1), (a m : ℂ) * z ^ m := by
    intro z
    rw [hPdef, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hP0 : P.eval 0 = 1 := by
    rw [hPeval, Finset.sum_eq_single 0]
    · simp [ha0]
    · intro m _ hm
      rw [zero_pow hm, mul_zero]
    · intro h; simp at h
  have hPne : P ≠ 0 := by
    intro hP; rw [hP] at hP0; simp at hP0
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hPdeg : P.natDegree ≤ d := by
    rw [hPdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro m hm
    rw [Finset.mem_range] at hm
    calc (Polynomial.C (a m : ℂ) * Polynomial.X ^ m).natDegree
        ≤ (Polynomial.X ^ m : Polynomial ℂ).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ m := Polynomial.natDegree_X_pow_le m
      _ ≤ d := by omega
  set L : List ℂ := P.roots.toList with hLdef
  set D : ℕ := L.length with hDdef
  have hDcard : D = Multiset.card P.roots := by
    rw [hDdef, hLdef, Multiset.length_toList]
  have hDnat : D = P.natDegree := by
    rw [hDcard, hsplit.natDegree_eq_card_roots]
  have hDd : D ≤ d := by rw [hDnat]; exact hPdeg
  have hroots : ∀ r ∈ P.roots, r.im = 0 ∧ r ≠ 0 := by
    intro r hr
    have hrr : P.eval r = 0 := Polynomial.isRoot_of_mem_roots hr
    constructor
    · apply hreal r; rw [← hPeval]; exact hrr
    · intro h0
      rw [h0] at hrr; rw [hP0] at hrr; exact one_ne_zero hrr
  have hmemL : ∀ r ∈ L, r ∈ P.roots := by
    intro r hr; rw [hLdef, Multiset.mem_toList] at hr; exact hr
  have hLget : ∀ (j : ℕ) (h : j < D), (L[j]'h) ∈ P.roots := by
    intro j h; apply hmemL; exact List.getElem_mem h
  set lam : ℕ → ℝ := fun j => if h : j < D then -(1 / (L[j]'h).re) else 0 with hlamdef
  have hlam_ne : ∀ j : ℕ, j < D → lam j ≠ 0 := by
    intro j hj
    simp only [hlamdef, dif_pos hj]
    have hmem := hLget j hj
    have hre : (L[j]'hj).im = 0 := (hroots _ hmem).1
    have hne : (L[j]'hj) ≠ 0 := (hroots _ hmem).2
    have hrene : (L[j]'hj).re ≠ 0 := by
      intro hc
      apply hne; apply Complex.ext
      · exact hc
      · rw [hre]; rfl
    intro hcontra
    rw [neg_eq_zero, div_eq_zero_iff] at hcontra
    rcases hcontra with h1 | h2
    · exact one_ne_zero h1
    · exact hrene h2
  have hpr_ne : P.roots.prod ≠ 0 := by
    rw [Ne, Multiset.prod_eq_zero_iff]
    intro hc; exact (hroots 0 hc).2 rfl
  have hkey : P.leadingCoeff * P.roots.prod = (-1) ^ D := by
    have hcoeff := hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots
    rw [Polynomial.coeff_zero_eq_eval_zero, hP0, ← hDnat] at hcoeff
    have hunit : ((-1 : ℂ) ^ D) * ((-1 : ℂ) ^ D) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc P.leadingCoeff * P.roots.prod
        = ((-1) ^ D * P.leadingCoeff * P.roots.prod) * (-1) ^ D := by
          rw [mul_comm ((-1:ℂ)^D * P.leadingCoeff * P.roots.prod) ((-1)^D)]
          rw [← mul_assoc, ← mul_assoc, hunit, one_mul]
      _ = 1 * (-1) ^ D := by rw [← hcoeff]
      _ = (-1) ^ D := by rw [one_mul]
  refine ⟨D, lam, hDd, hlam_ne, ?_⟩
  intro z
  rw [← hPeval z]
  rw [← Fin.prod_univ_eq_prod_range (fun j => 1 + (lam j : ℂ) * z) D]
  have hfactor : ∀ j : Fin D, (1 + (lam (j : ℕ) : ℂ) * z) = 1 - z / (L[(j : ℕ)]'j.isLt) := by
    intro j
    have hjlt : (j : ℕ) < D := j.isLt
    have hmem := hLget (j : ℕ) hjlt
    have hre : (L[(j:ℕ)]'hjlt).im = 0 := (hroots _ hmem).1
    have hreal : ((L[(j:ℕ)]'hjlt).re : ℂ) = L[(j:ℕ)]'hjlt := by
      apply Complex.ext
      · rw [Complex.ofReal_re]
      · rw [Complex.ofReal_im, hre]
    simp only [hlamdef, dif_pos hjlt]
    push_cast
    rw [hreal]
    have hne : (L[(j:ℕ)]'hjlt) ≠ 0 := (hroots _ hmem).2
    field_simp
    ring
  rw [Finset.prod_congr rfl (fun j _ => hfactor j)]
  have hlist : (∏ j : Fin D, (1 - z / (L[(j : ℕ)]'j.isLt)))
      = (P.roots.map (fun w => 1 - z / w)).prod := by
    rw [← Fin.prod_ofFn (fun j : Fin D => 1 - z / (L[(j : ℕ)]'j.isLt))]
    have step : (List.ofFn (fun j : Fin L.length => 1 - z / (L[(j : ℕ)]'j.isLt)))
        = L.map (fun w => 1 - z / w) := List.ofFn_getElem_eq_map L (fun w => 1 - z / w)
    rw [show (List.ofFn (fun j : Fin D => 1 - z / (L[(j : ℕ)]'j.isLt))) = L.map (fun w => 1 - z / w) from step]
    rw [← Multiset.prod_coe, ← Multiset.map_coe, hLdef, Multiset.coe_toList]
  rw [hlist]
  have hmapcongr : P.roots.map (fun w => 1 - z / w)
      = P.roots.map (fun w => (w - z) / w) := by
    apply Multiset.map_congr rfl
    intro w hw
    have hwne : w ≠ 0 := (hroots w hw).2
    field_simp
  rw [hmapcongr, Multiset.prod_map_div]
  have hden : (P.roots.map (fun w => w)).prod = P.roots.prod := by rw [Multiset.map_id']
  rw [hden]
  have hnum : P.roots.map (fun w => w - z)
      = P.roots.map (fun w => (-1 : ℂ) * (z - w)) := by
    apply Multiset.map_congr rfl
    intro w _; ring
  rw [hnum]
  have hnum2 : (P.roots.map (fun w => (-1 : ℂ) * (z - w))).prod
      = ((-1 : ℂ) ^ D) * (P.roots.map (fun w => z - w)).prod := by
    rw [show (fun w => (-1 : ℂ) * (z - w)) = (fun w => (fun _ => (-1:ℂ)) w * (z - w)) from rfl]
    rw [Multiset.prod_map_mul]
    congr 1
    rw [Multiset.map_const', Multiset.prod_replicate, hDcard]
  rw [hnum2, hsplit.eval_eq_prod_roots z, eq_div_iff hpr_ne, mul_comm (P.leadingCoeff) _,
      mul_assoc, mul_comm ((P.roots.map (fun w => z - w)).prod) (P.leadingCoeff * P.roots.prod),
      hkey]




theorem sorting : ∀ (D : ℕ) (lam : Fin D → ℝ),
    (∃ π : Equiv.Perm (Fin D),
      (∀ i j : Fin D, i ≤ j → |lam (π j)| ≤ |lam (π i)|) ∧
      (∀ z : ℂ, (∏ j, (1 + (lam (π j) : ℂ) * z)) = ∏ j, (1 + (lam j : ℂ) * z)) ∧
      (∑ j, lam (π j) = ∑ j, lam j) ∧
      (∑ j, (lam (π j)) ^ 2 = ∑ j, (lam j) ^ 2)) ∧
    (∀ μ : Fin D → ℝ, (∀ i j : Fin D, i ≤ j → |μ j| ≤ |μ i|) →
      ∀ j : Fin D, (((j : ℕ) : ℝ) + 1) * (μ j) ^ 2 ≤ ∑ i, (μ i) ^ 2) := by
  intro D lam
  refine ⟨?_, ?_⟩
  · refine ⟨Tuple.sort (fun i => -(|lam i|)), ?_, ?_, ?_, ?_⟩
    · intro i j hij
      have hmono := Tuple.monotone_sort (fun i => -(|lam i|)) hij
      simp only [Function.comp_apply] at hmono
      linarith
    · intro z
      exact Equiv.prod_comp (Tuple.sort (fun i => -(|lam i|))) (fun j => 1 + (lam j : ℂ) * z)
    · exact Equiv.sum_comp (Tuple.sort (fun i => -(|lam i|))) lam
    · exact Equiv.sum_comp (Tuple.sort (fun i => -(|lam i|))) (fun j => (lam j) ^ 2)
  · intro μ hμ j
    have hsq : ∀ i ∈ Finset.Iic j, (μ j) ^ 2 ≤ (μ i) ^ 2 := by
      intro i hi
      rw [Finset.mem_Iic] at hi
      have := hμ i j hi
      rw [← sq_abs (μ j), ← sq_abs (μ i)]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hcard : (Finset.Iic j).card = (j : ℕ) + 1 := Fin.card_Iic j
    have hconst : (((j : ℕ) : ℝ) + 1) * (μ j) ^ 2 = ∑ _i ∈ Finset.Iic j, (μ j) ^ 2 := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
    rw [hconst]
    calc ∑ _i ∈ Finset.Iic j, (μ j) ^ 2
        ≤ ∑ i ∈ Finset.Iic j, (μ i) ^ 2 := Finset.sum_le_sum hsq
      _ ≤ ∑ i, (μ i) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro i _ _; exact sq_nonneg _

end Part6
