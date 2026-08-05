import LeanCode.Vendor.E5.P5.Part5.Basic
import LeanCode.Vendor.E5.Defs




namespace Part5


theorem alt_to_vec (s : ℕ) (v : Fin (s + 1) → ℝ)
    (h : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ i : Fin (s + 1), 0 < ε * (-1 : ℝ) ^ (i : ℕ) * v i) :
    SignChangesGE v s := by
  obtain ⟨ε, hε, hpos⟩ := h
  exact ⟨id, strictMono_id, ε, hε, fun i => hpos i⟩



theorem weighted_transfer (K : ℕ) (hK : 1 ≤ K) (y : Fin K → ℝ) (hy : StrictMono y)
    (w : Fin K → ℝ) (hw : ∀ j, 0 < w j) (h : ℝ → ℝ) (s : ℕ)
    (hsc : SignChangesGE (fun j => w j * h (y j)) s) :
    SignChangesFnGE h s := by
  obtain ⟨idx, hidx, ε, hε, hpos⟩ := hsc
  refine ⟨fun i => y (idx i), hy.comp hidx, ε, hε, fun i => ?_⟩
  have hp := hpos i
  have hwpos := hw (idx i)
  have hrw : ε * (-1 : ℝ) ^ (i : ℕ) * (w (idx i) * h (y (idx i)))
      = (ε * (-1 : ℝ) ^ (i : ℕ) * h (y (idx i))) * w (idx i) := by ring
  rw [hrw] at hp
  exact (mul_pos_iff_of_pos_right hwpos).mp hp




theorem factor_theorem {K : Type*} [CommRing K] (p : Polynomial K) (r : K)
    (hr : p.IsRoot r) :
    ∃ q : Polynomial K, p = (Polynomial.X - Polynomial.C r) * q ∧
      q.natDegree ≤ p.natDegree - 1 ∧ q.coeff (p.natDegree - 1) = p.leadingCoeff := by
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hr
  have hmonic : (Polynomial.X - Polynomial.C r : Polynomial K).Monic :=
    Polynomial.monic_X_sub_C r
  refine ⟨q, hq, ?_, ?_⟩
  · rcases eq_or_ne q 0 with rfl | hq0
    · simp
    · haveI : Nontrivial K := Polynomial.Nontrivial.of_polynomial_ne hq0
      have hdeg : p.natDegree = q.natDegree + 1 := by
        rw [hq, Polynomial.natDegree_mul' ?_, Polynomial.natDegree_X_sub_C, add_comm]
        rw [hmonic.leadingCoeff, one_mul]
        exact Polynomial.leadingCoeff_ne_zero.mpr hq0
      omega
  · rcases eq_or_ne q 0 with rfl | hq0
    · rw [mul_zero] at hq; rw [hq]; simp
    · haveI : Nontrivial K := Polynomial.Nontrivial.of_polynomial_ne hq0
      have hlc : p.leadingCoeff = q.leadingCoeff := by
        rw [hq, Polynomial.leadingCoeff_monic_mul hmonic]
      have hdeg : p.natDegree = q.natDegree + 1 := by
        rw [hq, Polynomial.natDegree_mul' ?_, Polynomial.natDegree_X_sub_C, add_comm]
        rw [hmonic.leadingCoeff, one_mul]
        exact Polynomial.leadingCoeff_ne_zero.mpr hq0
      rw [hdeg, Nat.add_sub_cancel, hlc]; rfl



theorem factor_out_roots {K : Type*} [CommRing K] [IsDomain K] (p : Polynomial K)
    (hp : p ≠ 0) (m : ℕ) (r : Fin m → K) (hinj : Function.Injective r)
    (hroots : ∀ j, p.IsRoot (r j)) :
    m ≤ p.natDegree ∧ ∃ q : Polynomial K,
      p = q * ∏ j, (Polynomial.X - Polynomial.C (r j)) ∧
      q.natDegree = p.natDegree - m ∧ q.leadingCoeff = p.leadingCoeff := by
  classical
  set s : Multiset K := (Finset.univ : Finset (Fin m)).val.map r with hs
  have hsnodup : s.Nodup := by
    rw [hs]
    exact (Finset.univ : Finset (Fin m)).nodup.map hinj
  have hscard : Multiset.card s = m := by
    rw [hs, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  have hprodeq : (∏ j, (Polynomial.X - Polynomial.C (r j)))
      = (s.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Finset.prod_eq_multiset_prod, hs, Multiset.map_map]
    rfl
  have hmonic : (s.map fun a => Polynomial.X - Polynomial.C a).prod.Monic :=
    Polynomial.monic_multisetProd_X_sub_C s
  have hle : s ≤ p.roots := by
    rw [Multiset.le_iff_count]
    intro x
    by_cases hx : x ∈ s
    · have hcount_s : s.count x = 1 := Multiset.count_eq_one_of_mem hsnodup hx
      rw [hcount_s]
      have hx' := hx
      rw [hs, Multiset.mem_map] at hx'
      obtain ⟨j, _, rfl⟩ := hx'
      rw [Polynomial.count_roots]
      exact (Polynomial.rootMultiplicity_pos hp).mpr (hroots j)
    · rw [Multiset.count_eq_zero_of_notMem hx]
      exact Nat.zero_le _
  have hdvd : (s.map fun a => Polynomial.X - Polynomial.C a).prod ∣ p :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hp s).mpr hle
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hp hq
  have hqfact : p = q * ∏ j, (Polynomial.X - Polynomial.C (r j)) := by
    rw [hprodeq, hq, mul_comm]
  have hdeg : p.natDegree = q.natDegree + m := by
    rw [hq, Polynomial.natDegree_mul hmonic.ne_zero hq0,
        Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hscard, add_comm]
  have hlc : q.leadingCoeff = p.leadingCoeff := by
    rw [hq, Polynomial.leadingCoeff_monic_mul hmonic]
  refine ⟨?_, q, hqfact, ?_, hlc⟩
  · rw [hdeg]; exact Nat.le_add_left m q.natDegree
  · rw [hdeg, Nat.add_sub_cancel]



theorem roots_bound {K : Type*} [CommRing K] [IsDomain K] (p : Polynomial K)
    (hp : p ≠ 0) (m : ℕ) (r : Fin m → K) (hinj : Function.Injective r)
    (hroots : ∀ j, p.IsRoot (r j)) :
    m ≤ p.natDegree := by
  classical
  have hsub : (Finset.univ.image r) ⊆ p.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨j, _, rfl⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hp, hroots j⟩
  calc m = (Finset.univ.image r).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := p.roots.toFinset_card_le
    _ ≤ p.natDegree := Polynomial.card_roots' p



theorem poly_factorization (p : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) (r : Fin n → ℝ) (hr : StrictMono r)
    (hroots : ∀ j, p.IsRoot (r j)) :
    p = Polynomial.C p.leadingCoeff * ∏ j, (Polynomial.X - Polynomial.C (r j)) := by
  have hp : p ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
  obtain ⟨-, q, hpq, hqdeg, hqlc⟩ := factor_out_roots p hp n r hr.injective hroots
  have hq0 : q.natDegree = 0 := by rw [hqdeg, hdeg, Nat.sub_self]
  have hqC : q = Polynomial.C p.leadingCoeff := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hq0]
    congr 1
    rw [← hqlc]
    show q.coeff 0 = q.coeff q.natDegree
    rw [hq0]
  rw [hqC] at hpq
  exact hpq


theorem prod_sign (m : ℕ) (a : Fin m → ℝ) (hne : ∀ j, a j ≠ 0) :
    0 < (-1 : ℝ) ^ (Finset.univ.filter (fun j => a j < 0)).card * ∏ j, a j := by
  classical
  have habs : (∏ j, |a j|) = (-1:ℝ)^(Finset.univ.filter (fun j => a j < 0)).card * ∏ j, a j := by
    have h1 : ∀ j, |a j| = (if a j < 0 then (-1:ℝ) else 1) * a j := by
      intro j
      by_cases h : a j < 0
      · rw [if_pos h, abs_of_neg h]; ring
      · rw [if_neg h, abs_of_nonneg (le_of_not_gt h), one_mul]
    calc (∏ j, |a j|) = ∏ j, ((if a j < 0 then (-1:ℝ) else 1) * a j) :=
            Finset.prod_congr rfl (fun j _ => h1 j)
      _ = (∏ j, (if a j < 0 then (-1:ℝ) else 1)) * ∏ j, a j := Finset.prod_mul_distrib
      _ = (-1:ℝ)^(Finset.univ.filter (fun j => a j < 0)).card * ∏ j, a j := by
            congr 1
            rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rw [← habs]
  exact Finset.prod_pos (fun j _ => abs_pos.mpr (hne j))



private noncomputable def stcSamples (n : ℕ) (hn : 0 < n) (r : Fin n → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  if h0 : (i : ℕ) = 0 then r ⟨0, hn⟩ - 1
  else if hnn : (i : ℕ) = n then r ⟨n - 1, by omega⟩ + 1
  else (r ⟨(i : ℕ) - 1, by omega⟩ + r ⟨(i : ℕ), by omega⟩) / 2

private theorem stcSamples_lt_root (n : ℕ) (hn : 0 < n) (r : Fin n → ℝ)
    (hr : StrictMono r) (i : Fin (n + 1)) (j : Fin n) :
    stcSamples n hn r i < r j ↔ (i : ℕ) ≤ (j : ℕ) := by
  have hi_le : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  unfold stcSamples
  split_ifs with h0 hnn
  · constructor
    · intro _; omega
    · intro _
      have : r ⟨0, hn⟩ ≤ r j := hr.monotone (by simp [Fin.le_def])
      linarith
  · have hjn : (j : ℕ) < n := j.isLt
    constructor
    · intro hlt
      exfalso
      have : r j ≤ r ⟨n - 1, by omega⟩ := hr.monotone (by rw [Fin.le_def]; simp only; omega)
      linarith
    · intro hle; omega
  · have hi1 : (i : ℕ) - 1 < n := by omega
    have hi2 : (i : ℕ) < n := by omega
    constructor
    · intro hlt
      by_contra hcon
      rw [not_le] at hcon
      have hji : (j : ℕ) ≤ (i : ℕ) - 1 := by omega
      have h1 : r j ≤ r ⟨(i : ℕ) - 1, hi1⟩ := hr.monotone (by rw [Fin.le_def]; simp only; omega)
      have h2 : r ⟨(i : ℕ) - 1, hi1⟩ < r ⟨(i : ℕ), hi2⟩ := hr (by rw [Fin.lt_def]; simp only; omega)
      linarith
    · intro hle
      have h2 : r ⟨(i : ℕ) - 1, hi1⟩ < r ⟨(i : ℕ), hi2⟩ := hr (by rw [Fin.lt_def]; simp only; omega)
      have h3 : r ⟨(i : ℕ), hi2⟩ ≤ r j := hr.monotone (by rw [Fin.le_def]; simp only; omega)
      linarith

private theorem stcSamples_root_lt (n : ℕ) (hn : 0 < n) (r : Fin n → ℝ)
    (hr : StrictMono r) (i : Fin (n + 1)) (j : Fin n) :
    r j < stcSamples n hn r i ↔ (j : ℕ) < (i : ℕ) := by
  have hi_le : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  unfold stcSamples
  split_ifs with h0 hnn
  · have hjn : (j : ℕ) < n := j.isLt
    constructor
    · intro hlt
      exfalso
      have : r ⟨0, hn⟩ ≤ r j := hr.monotone (by simp [Fin.le_def])
      linarith
    · intro hlt; omega
  · have hjn : (j : ℕ) < n := j.isLt
    constructor
    · intro _; omega
    · intro _
      have : r j ≤ r ⟨n - 1, by omega⟩ := hr.monotone (by rw [Fin.le_def]; simp only; omega)
      linarith
  · have hi1 : (i : ℕ) - 1 < n := by omega
    have hi2 : (i : ℕ) < n := by omega
    constructor
    · intro hlt
      by_contra hcon
      rw [not_lt] at hcon
      have h3 : r ⟨(i : ℕ), hi2⟩ ≤ r j := hr.monotone (by rw [Fin.le_def]; simp only; omega)
      have h2 : r ⟨(i : ℕ) - 1, hi1⟩ < r ⟨(i : ℕ), hi2⟩ := hr (by rw [Fin.lt_def]; simp only; omega)
      linarith
    · intro hlt
      have hji : (j : ℕ) ≤ (i : ℕ) - 1 := by omega
      have h1 : r j ≤ r ⟨(i : ℕ) - 1, hi1⟩ := hr.monotone (by rw [Fin.le_def]; simp only; omega)
      have h2 : r ⟨(i : ℕ) - 1, hi1⟩ < r ⟨(i : ℕ), hi2⟩ := hr (by rw [Fin.lt_def]; simp only; omega)
      linarith

private theorem stcSamples_ne_root (n : ℕ) (hn : 0 < n) (r : Fin n → ℝ)
    (hr : StrictMono r) (i : Fin (n + 1)) (j : Fin n) :
    stcSamples n hn r i ≠ r j := by
  rcases lt_trichotomy (stcSamples n hn r i) (r j) with h | h | h
  · exact ne_of_lt h
  · exfalso
    have hn1 : ¬ (stcSamples n hn r i < r j) := by rw [h]; exact lt_irrefl _
    have hn2 : ¬ (r j < stcSamples n hn r i) := by rw [h]; exact lt_irrefl _
    rw [stcSamples_lt_root n hn r hr] at hn1
    rw [stcSamples_root_lt n hn r hr] at hn2
    omega
  · exact ne_of_gt h

private theorem stcSamples_strictMono (n : ℕ) (hn : 0 < n) (r : Fin n → ℝ)
    (hr : StrictMono r) : StrictMono (stcSamples n hn r) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have h1 : stcSamples n hn r i.castSucc < r i := by
    rw [stcSamples_lt_root n hn r hr]; simp [Fin.val_castSucc]
  have h2 : r i < stcSamples n hn r i.succ := by
    rw [stcSamples_root_lt n hn r hr]; simp [Fin.val_succ]
  linarith

private theorem stc_card_ge (n c : ℕ) :
    (Finset.filter (fun j : Fin n => c ≤ (j : ℕ)) Finset.univ).card = n - c := by
  have himg : (Finset.filter (fun j : Fin n => c ≤ (j : ℕ)) Finset.univ).image (Fin.val)
            = Finset.filter (fun k => c ≤ k) (Finset.range n) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j.isLt, hj⟩
    · rintro ⟨hk, hck⟩; exact ⟨⟨k, hk⟩, hck, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg]
  rw [show Finset.filter (fun k => c ≤ k) (Finset.range n) = Finset.Ico c n by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega]
  rw [Nat.card_Ico]

private theorem stc_card_neg (n : ℕ) (hn : 0 < n) (r : Fin n → ℝ) (hr : StrictMono r)
    (i : Fin (n + 1)) :
    (Finset.univ.filter (fun j : Fin n => stcSamples n hn r i - r j < 0)).card
      = n - (i : ℕ) := by
  rw [← stc_card_ge n (i : ℕ)]
  congr 1
  apply Finset.filter_congr
  intro j _
  rw [sub_neg]
  exact stcSamples_lt_root n hn r hr i j



theorem simple_to_changes (p : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hdeg : p.natDegree = n) (r : Fin n → ℝ) (hr : StrictMono r)
    (hroots : ∀ j, p.IsRoot (r j)) :
    SignChangesFnGE (fun x => p.eval x) n := by
  have hn0 : 0 < n := hn
  have hpne : p ≠ 0 := by intro h; rw [h] at hdeg; simp at hdeg; omega
  set ℓ : ℝ := p.leadingCoeff with hℓdef
  have hℓ : ℓ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hfact := poly_factorization p n hn hdeg r hr hroots
  have heval : ∀ x : ℝ, p.eval x = ℓ * ∏ j, (x - r j) := by
    intro x
    conv_lhs => rw [hfact]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    congr 1; apply Finset.prod_congr rfl; intro j _
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  set x : Fin (n + 1) → ℝ := stcSamples n hn0 r with hxdef
  have hApos : ∀ i : Fin (n + 1), 0 < (-1 : ℝ) ^ (n - (i : ℕ)) * ∏ j, (x i - r j) := by
    intro i
    have hne : ∀ j, x i - r j ≠ 0 := fun j => sub_ne_zero.mpr (stcSamples_ne_root n hn0 r hr i j)
    have hps := prod_sign n (fun j => x i - r j) hne
    rw [stc_card_neg n hn0 r hr i] at hps; exact hps
  set ε : ℝ := if 0 < (-1 : ℝ) ^ n * ℓ then 1 else -1 with hεdef
  have hεval : ε = 1 ∨ ε = -1 := by rw [hεdef]; split_ifs <;> [left; right] <;> rfl
  have hεℓpos : 0 < ε * ((-1 : ℝ) ^ n * ℓ) := by
    rw [hεdef]; split_ifs with hpos
    · rw [one_mul]; exact hpos
    · rw [not_lt] at hpos
      have hne : (-1 : ℝ) ^ n * ℓ ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hℓ
      have hlt : (-1 : ℝ) ^ n * ℓ < 0 := lt_of_le_of_ne hpos hne
      linarith
  refine ⟨x, stcSamples_strictMono n hn0 r hr, ε, hεval, ?_⟩
  intro i
  have hi_le : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  have hpow2 : (-1 : ℝ) ^ (i : ℕ) = (-1 : ℝ) ^ n * (-1 : ℝ) ^ (n - (i : ℕ)) := by
    rw [← pow_add]
    have hsplit : n + (n - (i : ℕ)) = 2 * (n - (i : ℕ)) + (i : ℕ) := by omega
    rw [hsplit, pow_add, pow_mul]; norm_num
  simp only []
  rw [heval (x i)]
  have key : ε * (-1 : ℝ) ^ (i : ℕ) * (ℓ * ∏ j, (x i - r j))
      = (ε * ((-1 : ℝ) ^ n * ℓ)) * ((-1 : ℝ) ^ (n - (i : ℕ)) * ∏ j, (x i - r j)) := by
    rw [hpow2]; ring
  rw [key]
  exact mul_pos hεℓpos (hApos i)



theorem changes_to_zeros (q : Polynomial ℝ) (n : ℕ)
    (hsc : SignChangesFnGE (fun x => q.eval x) n) :
    ∃ z : Fin n → ℝ, StrictMono z ∧ ∀ i, q.IsRoot (z i) := by
  obtain ⟨x, hxmono, ε, hε, hpos⟩ := hsc
  have root_between : ∀ (a b : ℝ), a < b → q.eval a * q.eval b < 0 →
      ∃ c, a < c ∧ c < b ∧ q.eval c = 0 := by
    intro a b hab hprod
    have hcont : ContinuousOn (fun x => q.eval x) (Set.Icc a b) :=
      (Polynomial.continuous q).continuousOn
    rcases mul_neg_iff.mp hprod with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
    · obtain ⟨c, hcmem, hceval⟩ := intermediate_value_Ioo' hab.le hcont ⟨hnb, hpa⟩
      exact ⟨c, hcmem.1, hcmem.2, hceval⟩
    · obtain ⟨c, hcmem, hceval⟩ := intermediate_value_Ioo hab.le hcont ⟨hna, hpb⟩
      exact ⟨c, hcmem.1, hcmem.2, hceval⟩
  have hopp : ∀ i : Fin n, q.eval (x i.castSucc) * q.eval (x i.succ) < 0 := by
    intro i
    have h1 := hpos i.castSucc
    have h2 := hpos i.succ
    rw [Fin.val_castSucc] at h1
    rw [Fin.val_succ] at h2
    have hεsq : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> ring
    have hprod := mul_pos h1 h2
    have hpp : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have key : (ε * (-1 : ℝ) ^ (i : ℕ) * q.eval (x i.castSucc)) *
        (ε * (-1 : ℝ) ^ ((i : ℕ) + 1) * q.eval (x i.succ))
        = -(q.eval (x i.castSucc) * q.eval (x i.succ)) := by
      have hrw : (ε * (-1 : ℝ) ^ (i : ℕ) * q.eval (x i.castSucc)) *
          (ε * (-1 : ℝ) ^ ((i : ℕ) + 1) * q.eval (x i.succ))
          = (ε * ε) * ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) * (-1) *
            (q.eval (x i.castSucc) * q.eval (x i.succ)) := by
        rw [pow_succ]; ring
      rw [hrw, hεsq, hpp]; ring
    rw [key] at hprod
    linarith
  choose z hz1 hz2 hz3 using fun i : Fin n =>
    root_between (x i.castSucc) (x i.succ) (hxmono i.castSucc_lt_succ) (hopp i)
  refine ⟨z, ?_, fun i => hz3 i⟩
  intro i j hij
  have hijnat : (i : ℕ) < (j : ℕ) := hij
  have h1 : z i < x i.succ := hz2 i
  have h2 : x j.castSucc < z j := hz1 j
  have h3 : x i.succ ≤ x j.castSucc := hxmono.monotone (by
    rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    omega)
  linarith

end Part5
