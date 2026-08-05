import LeanCode.Vendor.E5.P5.Part5.Basic
import LeanCode.Vendor.E5.P5.Part5.SignChanges
import LeanCode.Vendor.E5.Defs





namespace Part5


theorem complex_split (q : Polynomial ℂ) (hq : q ≠ 0) :
    ∃ w : Fin q.natDegree → ℂ,
      q = Polynomial.C q.leadingCoeff * ∏ j, (Polynomial.X - Polynomial.C (w j)) := by
  have hcard : Multiset.card q.roots = q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  set l := q.roots.toList with hl
  have hlen : l.length = q.natDegree := by rw [hl, Multiset.length_toList, hcard]
  refine ⟨fun i => l.get (Fin.cast hlen.symm i), ?_⟩
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hprod : (∏ j : Fin q.natDegree,
        (Polynomial.X - Polynomial.C (l.get (Fin.cast hlen.symm j))))
      = (q.roots.map fun a => Polynomial.X - Polynomial.C a).prod := by
    have hcoe : q.roots = (l : Multiset ℂ) := (Multiset.coe_toList q.roots).symm
    rw [hcoe, Multiset.map_coe, Multiset.prod_coe]
    conv_rhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn, Fin.prod_ofFn]
    exact Fin.prod_congr'
      ((fun a => Polynomial.X - Polynomial.C a) ∘ l.get) hlen.symm
  rw [hprod]
  exact hfac.symm



theorem realrooted_bound (q : Polynomial ℝ) (hq : q ≠ 0) (hrr : RealRooted q)
    (z : ℂ) :
    |q.leadingCoeff| * |z.im| ^ q.natDegree ≤ ‖Polynomial.aeval z q‖ := by
  classical
  set Q : Polynomial ℂ := q.map (algebraMap ℝ ℂ) with hQ
  have hinj : Function.Injective (algebraMap ℝ ℂ) := by
    rw [Complex.coe_algebraMap]; exact Complex.ofReal_injective
  have hQne : Q ≠ 0 := by rw [hQ, Polynomial.map_ne_zero_iff hinj]; exact hq
  have hdeg : Q.natDegree = q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj q
  have hlc : Q.leadingCoeff = algebraMap ℝ ℂ q.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_injective hinj q
  have haeval : ∀ u : ℂ, Polynomial.aeval u q = Q.eval u := by
    intro u
    rw [Polynomial.aeval_def, hQ, Polynomial.eval_map]
  obtain ⟨w, hw⟩ := complex_split Q hQne
  have hroot : ∀ j, (w j).im = 0 := by
    intro j
    have hev : Q.eval (w j) = 0 := by
      rw [hw, Polynomial.eval_mul, Polynomial.eval_prod]
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      ring
    have hz0 : Polynomial.aeval (w j) q = 0 := by rw [haeval]; exact hev
    exact hrr (w j) hz0
  have hval : Polynomial.aeval z q = Q.leadingCoeff * ∏ j, (z - w j) := by
    rw [haeval]
    conv_lhs => rw [hw]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hval, norm_mul, Complex.norm_prod]
  have hnormlc : ‖Q.leadingCoeff‖ = |q.leadingCoeff| := by
    rw [hlc, Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs]
  rw [hnormlc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc |z.im| ^ q.natDegree
      = ∏ _j : Fin Q.natDegree, |z.im| := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hdeg]
    _ ≤ ∏ j, ‖z - w j‖ := by
        apply Finset.prod_le_prod
        · intro j _; exact abs_nonneg _
        · intro j _
          have him : (z - w j).im = z.im := by
            rw [Complex.sub_im, hroot j, sub_zero]
          calc |z.im| = |(z - w j).im| := by rw [him]
            _ ≤ ‖z - w j‖ := Complex.abs_im_le_norm _



theorem bound_realrooted (q : Polynomial ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hbd : ∀ z : ℂ, κ * |z.im| ^ n ≤ ‖Polynomial.aeval z q‖) :
    RealRooted q := by
  intro z hz
  by_contra him
  have h1 := hbd z
  rw [hz, norm_zero] at h1
  exact absurd h1 (not_le.mpr (mul_pos hκ (pow_pos (abs_pos.mpr him) n)))



theorem vieta {K : Type*} [CommRing K] (n : ℕ) (a : Fin n → K) :
    ∏ j, (Polynomial.X - Polynomial.C (a j))
      = ∑ m ∈ Finset.range (n + 1),
          Polynomial.C ((-1 : K) ^ m *
            ∑ t ∈ Finset.univ.powersetCard m, ∏ j ∈ t, a j) *
            Polynomial.X ^ (n - m) := by
  have hcard : Multiset.card ((Finset.univ : Finset (Fin n)).val.map a) = n := by
    rw [Multiset.card_map]; simp
  have hprod : (∏ j, (Polynomial.X - Polynomial.C (a j)))
      = (((Finset.univ : Finset (Fin n)).val.map a).map
          (fun t => Polynomial.X - Polynomial.C t)).prod := by
    rw [Multiset.map_map]; rfl
  rw [hprod, Multiset.prod_X_sub_X_eq_sum_esymm, hcard]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.esymm_map_val a Finset.univ m]
  rw [map_mul, map_pow, map_neg, map_one]
  ring



noncomputable def simpleApprox (n L : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.Icc 1 n, (Polynomial.X - Polynomial.C ((j : ℝ) / (L : ℝ)))

open Polynomial in
private theorem simpleApprox_monic (n L : ℕ) : (simpleApprox n L).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i _
  exact Polynomial.monic_X_sub_C _

open Polynomial in
private theorem simpleApprox_natDegree (n L : ℕ) :
    (simpleApprox n L).natDegree = n := by
  unfold simpleApprox
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C]
  simp

open Polynomial in


theorem coeff_convergence_zeros (n : ℕ) (hn : 1 ≤ n) (L : ℕ) (hL : 1 ≤ L) :
    (simpleApprox n L).natDegree = n ∧ (simpleApprox n L).leadingCoeff = 1 ∧
      ∃ r : Fin n → ℝ, StrictMono r ∧ ∀ i, (simpleApprox n L).IsRoot (r i) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  refine ⟨simpleApprox_natDegree n L, (simpleApprox_monic n L).leadingCoeff, ?_⟩
  refine ⟨fun i => ((i : ℕ) + 1 : ℝ) / (L : ℝ), ?_, ?_⟩
  · intro i j hij
    have hlt : (i : ℕ) < (j : ℕ) := hij
    have : ((i : ℕ) + 1 : ℝ) < ((j : ℕ) + 1 : ℝ) := by
      have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hlt
      linarith
    exact div_lt_div_of_pos_right this hLpos
  · intro i
    unfold simpleApprox Polynomial.IsRoot
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (i := (i : ℕ) + 1)
    · simp only [Finset.mem_Icc]
      constructor
      · omega
      · have := i.2; omega
    · simp

open Polynomial in
private theorem simpleApprox_coeff (n L k : ℕ) (hk : k ≤ n) :
    (simpleApprox n L).coeff k =
      (-1 : ℝ) ^ (n - k) * (1 / (L : ℝ)) ^ (n - k) *
        (((Finset.Icc 1 n).val.map (fun j : ℕ => (j : ℝ))).esymm (n - k)) := by
  unfold simpleApprox
  have hcard :
      Multiset.card ((Finset.Icc 1 n).val.map (fun j : ℕ => (j : ℝ) / (L : ℝ))) = n := by
    rw [Multiset.card_map, ← Finset.card_def]; simp [Nat.card_Icc]
  have hrw : (∏ j ∈ Finset.Icc 1 n, (Polynomial.X - Polynomial.C ((j : ℝ) / (L : ℝ))))
      = (((Finset.Icc 1 n).val.map (fun j : ℕ => (j : ℝ) / (L : ℝ))).map
          (fun t => Polynomial.X - Polynomial.C t)).prod := by
    rw [Multiset.map_map]; rfl
  rw [hrw, Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; exact hk), hcard]
  have hscale :
      (((Finset.Icc 1 n).val.map (fun j : ℕ => (j : ℝ) / (L : ℝ))).esymm (n - k))
        = (1 / (L : ℝ)) ^ (n - k) *
            (((Finset.Icc 1 n).val.map (fun j : ℕ => (j : ℝ))).esymm (n - k)) := by
    have key := Multiset.pow_smul_esymm (S := ℝ) (1 / (L : ℝ)) (n - k)
        ((Finset.Icc 1 n).val.map (fun j : ℕ => (j : ℝ)))
    rw [show ((Finset.Icc 1 n).val.map (fun j : ℕ => (j : ℝ))).map ((1 / (L : ℝ)) • ·)
          = (Finset.Icc 1 n).val.map (fun j : ℕ => (j : ℝ) / (L : ℝ)) by
      rw [Multiset.map_map]; congr 1; ext j; simp [smul_eq_mul]; ring] at key
    rw [← key, smul_eq_mul]
  rw [hscale]; ring

open Polynomial in


theorem coeff_convergence_limit (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    Filter.Tendsto (fun L : ℕ => (simpleApprox n L).coeff k) Filter.atTop
      (nhds ((Polynomial.X ^ n : Polynomial ℝ).coeff k)) := by
  rw [Polynomial.coeff_X_pow]
  rcases lt_trichotomy k n with hlt | heq | hgt
  · rw [if_neg (by omega)]
    have hfun : (fun L : ℕ => (simpleApprox n L).coeff k)
        = (fun L : ℕ => ((-1 : ℝ) ^ (n - k) *
            (((Finset.Icc 1 n).val.map (fun j : ℕ => (j : ℝ))).esymm (n - k))) *
            (1 / (L : ℝ)) ^ (n - k)) := by
      funext L; rw [simpleApprox_coeff n L k (le_of_lt hlt)]; ring
    rw [hfun]
    have hpow :
        Filter.Tendsto (fun L : ℕ => (1 / (L : ℝ)) ^ (n - k)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun L : ℕ => (1 / (L : ℝ))) Filter.atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h2 := h1.pow (n - k)
      simpa [zero_pow (by omega : n - k ≠ 0)] using h2
    have h3 := hpow.const_mul ((-1 : ℝ) ^ (n - k) *
        (((Finset.Icc 1 n).val.map (fun j : ℕ => (j : ℝ))).esymm (n - k)))
    simpa using h3
  · subst heq
    rw [if_pos rfl]
    have hconst : (fun L : ℕ => (simpleApprox k L).coeff k) = (fun _ : ℕ => (1 : ℝ)) := by
      funext L
      have hm := simpleApprox_monic k L
      unfold Polynomial.Monic Polynomial.leadingCoeff at hm
      rw [simpleApprox_natDegree k L] at hm
      exact hm
    rw [hconst]; exact tendsto_const_nhds
  · rw [if_neg (by omega)]
    have hconst : (fun L : ℕ => (simpleApprox n L).coeff k) = (fun _ : ℕ => (0 : ℝ)) := by
      funext L
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [simpleApprox_natDegree n L]; exact hgt
    rw [hconst]; exact tendsto_const_nhds

end Part5
