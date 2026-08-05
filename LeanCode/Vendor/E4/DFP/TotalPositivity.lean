import LeanCode.Vendor.E4.DFP.Defs

open Matrix
open scoped BigOperators

noncomputable section

namespace VendorE4


theorem strictlyAlternating_restrict_interval :
  forall {u : Int -> Real}, IsUniformlyAlternating u ->
    forall (a : Int) (n : Nat),
      IsStrictlyAlternatingFin (fun i : Fin n => u (a + (i.val : Int))) := by
  intro u hAlt a n
  constructor
  · intro i hzero
    have hzero' : u (a + (i.val : Int)) = 0 := hzero
    have hneg := hAlt (a + (i.val : Int))
    rw [hzero', zero_mul] at hneg
    exact not_lt_of_ge le_rfl hneg
  · intro i hi
    have hneg := hAlt (a + (i.val : Int))
    simpa [Nat.cast_add, add_assoc] using hneg


theorem isTotallyPositive_submatrix :
  forall {G : Int -> Int -> Real}, IsTotallyPositive G ->
    forall {n m : Nat} (rows : Fin n -> Int) (cols : Fin m -> Int),
      StrictMono rows -> StrictMono cols ->
        IsTotallyPositiveFinite (fun i j => G (rows i) (cols j)) := by
  intro G hG n m rows cols hrows hcols r i j hi hj
  exact hG r (fun p => rows (i p)) (fun p => cols (j p))
    (fun p q hpq => hrows (by exact_mod_cast hi hpq))
    (fun p q hpq => hcols (by exact_mod_cast hj hpq))




theorem cofactorVector_mul_eq_zero :
  forall {n : Nat} (C : Matrix (Fin (n + 1)) (Fin n) Real),
    (exists rows : Fin n -> Fin (n + 1),
      StrictMono (fun i => (rows i).val) /\
        (Matrix.of fun i j => C (rows i) j).det ≠ 0) ->
      exists c : Fin (n + 1) -> Real, c ≠ 0 /\
        forall t : Fin n, (∑ p : Fin (n + 1), c p * C p t) = 0 := by
  intro n C _hRank
  let L : (Fin (n + 1) -> Real) →ₗ[Real] (Fin n -> Real) :=
    { toFun := fun c t => ∑ p : Fin (n + 1), c p * C p t
      map_add' := by
        intro c d
        ext t
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        ext t
        simp [mul_assoc, Finset.mul_sum] }
  have hdim :
      Module.finrank Real (Fin n -> Real) <
        Module.finrank Real (Fin (n + 1) -> Real) := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  rcases (Submodule.ne_bot_iff (LinearMap.ker L)).mp hker with ⟨c, hcKer, hcNe⟩
  refine ⟨c, hcNe, ?_⟩
  intro t
  have hL : L c = 0 := LinearMap.mem_ker.mp hcKer
  exact congrFun hL t

private theorem strictlyAlternatingFin_checkerboard_adjacent_pos
    {n : Nat} {u : Fin n -> Real}
    (hAlt : IsStrictlyAlternatingFin u) (i : Fin n) (hi : i.val + 1 < n) :
    0 < (((-1 : Real) ^ i.val * u i) *
      ((-1 : Real) ^ (i.val + 1) * u ⟨i.val + 1, hi⟩)) := by
  have hneg := hAlt.2 i hi
  rcases neg_one_pow_eq_or Real i.val with hp | hp <;>
    simp [hp, pow_succ, hneg]

private theorem strictlyAlternatingFin_checkerboard_from_zero_pos
    {n : Nat} {u : Fin n -> Real}
    (hAlt : IsStrictlyAlternatingFin u) {p : Fin n} :
    0 < (((-1 : Real) ^ (0 : Nat) *
        u ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le p.val) p.isLt⟩) *
      ((-1 : Real) ^ p.val * u p)) := by
  let z0 : Fin n := ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le p.val) p.isLt⟩
  let v : Fin n -> Real := fun i => (-1 : Real) ^ i.val * u i
  have hmain : forall (m : Nat) (hm : m < n), 0 < v z0 * v ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero =>
        intro _hm
        have hv0_ne : v z0 ≠ 0 := by
          simp [v, z0, hAlt.1 z0]
        simpa [v, z0] using mul_self_pos.mpr hv0_ne
    | succ m ih =>
        intro hm_succ
        have hm : m < n := Nat.lt_trans (Nat.lt_succ_self m) hm_succ
        have hprev : 0 < v z0 * v ⟨m, hm⟩ := ih hm
        have hadj : 0 < v ⟨m, hm⟩ * v ⟨m + 1, hm_succ⟩ := by
          simpa [v] using
            strictlyAlternatingFin_checkerboard_adjacent_pos hAlt ⟨m, hm⟩ hm_succ
        have hmid_ne : v ⟨m, hm⟩ ≠ 0 := by
          simp [v, hAlt.1 ⟨m, hm⟩]
        have hsq : 0 < v ⟨m, hm⟩ * v ⟨m, hm⟩ := mul_self_pos.mpr hmid_ne
        have hprod :
            0 < (v z0 * v ⟨m, hm⟩) * (v ⟨m, hm⟩ * v ⟨m + 1, hm_succ⟩) :=
          mul_pos hprev hadj
        have hprod' :
            0 < (v z0 * v ⟨m + 1, hm_succ⟩) *
              (v ⟨m, hm⟩ * v ⟨m, hm⟩) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
        exact pos_of_mul_pos_left hprod' hsq.le
  simpa [v, z0] using hmain p.val p.isLt

private theorem sum_abs_eq_abs_sum_of_common_sign {ι : Type*} [Fintype ι]
    (t : ι -> Real) {r : Real} (hr : r ≠ 0)
    (h : forall i : ι, 0 <= r * t i) :
    (∑ i, |t i|) = |∑ i, t i| := by
  classical
  rcases lt_or_gt_of_ne hr.symm with hrpos | hrneg
  · have ht_nonneg : forall i : ι, 0 <= t i := fun i =>
      nonneg_of_mul_nonneg_right (h i) hrpos
    have hsum_nonneg : 0 <= (∑ i, t i) :=
      Finset.sum_nonneg (fun i _ => ht_nonneg i)
    calc
      (∑ i, |t i|) = ∑ i, t i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact abs_of_nonneg (ht_nonneg i)
      _ = |∑ i, t i| := by rw [abs_of_nonneg hsum_nonneg]
  · have ht_nonpos : forall i : ι, t i <= 0 := fun i =>
      nonpos_of_mul_nonneg_right (h i) hrneg
    have hsum_nonpos : (∑ i, t i) <= 0 :=
      Finset.sum_nonpos (fun i _ => ht_nonpos i)
    calc
      (∑ i, |t i|) = ∑ i, -t i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact abs_of_nonpos (ht_nonpos i)
      _ = -(∑ i, t i) := by rw [Finset.sum_neg_distrib]
      _ = |∑ i, t i| := by rw [abs_of_nonpos hsum_nonpos]




def signChangesFin {n : Nat} (u : Fin n -> Real) : Nat :=
  ((Finset.range (n - 1)).filter fun k =>
    if hk : k + 1 < n then
      u ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_of_lt hk)⟩ *
        u ⟨k + 1, hk⟩ < 0
    else
      False).card


theorem signChangesFin_le_pred :
  forall {n : Nat} (u : Fin n -> Real), signChangesFin u <= n - 1 := by
  intro n u
  let p : Nat -> Prop := fun k =>
    if hk : k + 1 < n then
      u ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_of_lt hk)⟩ *
        u ⟨k + 1, hk⟩ < 0
    else
      False
  change ((Finset.range (n - 1)).filter p).card <= n - 1
  simpa using (Finset.range (n - 1)).card_filter_le p


theorem signChangesFin_eq_pred_of_strictlyAlternating :
  forall {n : Nat} {u : Fin n -> Real},
    IsStrictlyAlternatingFin u -> signChangesFin u = n - 1 := by
  intro n u hAlt
  unfold signChangesFin
  have hfilter :
      (Finset.range (n - 1)).filter (fun k =>
        if hk : k + 1 < n then
          u ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_of_lt hk)⟩ *
            u ⟨k + 1, hk⟩ < 0
        else
          False) = Finset.range (n - 1) := by
    ext k
    constructor
    · intro hk
      exact (Finset.mem_filter.mp hk).1
    · intro hk
      rw [Finset.mem_filter]
      refine ⟨hk, ?_⟩
      have hklt : k < n - 1 := Finset.mem_range.mp hk
      have hk1 : k + 1 < n := by omega
      have hk0 : k < n :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_of_lt hk1)
      simpa [hk1] using hAlt.2 ⟨k, hk0⟩ hk1
  rw [hfilter]
  simp




def signVariationsFin {n : Nat} (u : Fin n -> Real) : Nat :=
  let signs := (List.ofFn fun i : Fin n => SignType.sign (u i))
  let nonzeroSigns := signs.filter (· ≠ 0)
  (nonzeroSigns.destutter (· ≠ ·)).length - 1



theorem signVariationsFin_le_pred :
  forall {n : Nat} (u : Fin n -> Real), signVariationsFin u <= n - 1 := by
  intro n u
  let signs : List SignType := List.ofFn fun i : Fin n => SignType.sign (u i)
  let nonzeroSigns : List SignType := signs.filter (· ≠ 0)
  have hdest :
      (nonzeroSigns.destutter (· ≠ ·)).length <= nonzeroSigns.length :=
    (List.destutter_sublist (fun a b : SignType => a ≠ b) nonzeroSigns).length_le
  have hfilter : nonzeroSigns.length <= signs.length :=
    (List.filter_sublist (p := fun s : SignType => decide (s ≠ 0))
      (l := signs)).length_le
  have hlen : (nonzeroSigns.destutter (· ≠ ·)).length <= n := by
    calc
      (nonzeroSigns.destutter (· ≠ ·)).length <= nonzeroSigns.length := hdest
      _ <= signs.length := hfilter
      _ = n := by simp [signs]
  simpa [signVariationsFin, signs, nonzeroSigns] using Nat.sub_le_sub_right hlen 1

private theorem sign_ne_of_mul_neg {a b : Real} (h : a * b < 0) :
    SignType.sign a ≠ SignType.sign b := by
  intro hs
  have hprod_nonneg : 0 <= a * b := by
    rcases lt_trichotomy a 0 with ha | ha | ha
    · have hb : b < 0 := by
        have hsa : SignType.sign a = -1 := sign_neg ha
        have hsb : SignType.sign b = -1 := by
          rw [hsa] at hs
          exact hs.symm
        exact sign_eq_neg_one_iff.mp hsb
      exact mul_nonneg_of_nonpos_of_nonpos ha.le hb.le
    · subst a
      simp
    · have hb : 0 < b := by
        have hsa : SignType.sign a = 1 := sign_pos ha
        have hsb : SignType.sign b = 1 := by
          rw [hsa] at hs
          exact hs.symm
        exact sign_eq_one_iff.mp hsb
      exact mul_nonneg ha.le hb.le
  exact not_lt_of_ge hprod_nonneg h




theorem signVariationsFin_eq_pred_of_strictlyAlternating :
  forall {n : Nat} {u : Fin n -> Real},
    IsStrictlyAlternatingFin u -> signVariationsFin u = n - 1 := by
  intro n u hAlt
  let signs : List SignType := List.ofFn fun i : Fin n => SignType.sign (u i)
  let nonzeroSigns : List SignType := signs.filter (· ≠ 0)
  have hfilter : nonzeroSigns = signs := by
    dsimp [nonzeroSigns, signs]
    rw [List.filter_eq_self]
    intro s hs
    rcases List.mem_ofFn.mp hs with ⟨i, rfl⟩
    exact decide_eq_true ((sign_ne_zero).2 (hAlt.1 i))
  have hchain : signs.IsChain (· ≠ ·) := by
    rw [List.isChain_iff_getElem]
    intro k hk
    have hk1 : k + 1 < n := by
      simpa [signs] using hk
    have hk0 : k < n :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_of_lt hk1)
    have hneq :
        SignType.sign (u ⟨k, hk0⟩) ≠ SignType.sign (u ⟨k + 1, hk1⟩) :=
      sign_ne_of_mul_neg (hAlt.2 ⟨k, hk0⟩ hk1)
    simpa [signs] using hneq
  have hdest : nonzeroSigns.destutter (· ≠ ·) = signs := by
    rw [hfilter]
    exact List.destutter_of_isChain (fun a b : SignType => a ≠ b) signs hchain
  have hlen : (nonzeroSigns.destutter (· ≠ ·)).length = n := by
    rw [hdest]
    simp [signs]
  unfold signVariationsFin
  change (nonzeroSigns.destutter (fun a b : SignType => a ≠ b)).length - 1 = n - 1
  rw [hlen]



theorem entry_nonneg_of_totallyPositiveFinite :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real},
    IsTotallyPositiveFinite B ->
    forall i : Fin n, forall j : Fin m, 0 <= B i j := by
  intro n m B hTP i j
  have hrows : StrictMono (fun _ : Fin 1 => i.val) := by
    intro a b hab
    fin_cases a
    fin_cases b
    simp at hab
  have hcols : StrictMono (fun _ : Fin 1 => j.val) := by
    intro a b hab
    fin_cases a
    fin_cases b
    simp at hab
  have hminor := hTP 1 (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) hrows hcols
  simpa using hminor



private theorem not_strictlyAlternating_image_of_cols_lt_two :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real} {x : Fin m -> Real},
    2 <= n ->
    m < 2 ->
    IsTotallyPositiveFinite B ->
      ¬ IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin m, B i j * x j) := by
  classical
  intro n m B x hn hm hTP hAlt
  interval_cases m
  · let i0 : Fin n := ⟨0, by omega⟩
    have hzero : (∑ j : Fin 0, B i0 j * x j) = 0 := by simp
    exact hAlt.1 i0 hzero
  · let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have hneg : (∑ j : Fin 1, B i0 j * x j) *
        (∑ j : Fin 1, B i1 j * x j) < 0 := by
      have hi0 : i0.val + 1 < n := by
        simp [i0]
        omega
      simpa [i0, i1] using hAlt.2 i0 hi0
    have hB0 : 0 <= B i0 0 := entry_nonneg_of_totallyPositiveFinite hTP i0 0
    have hB1 : 0 <= B i1 0 := entry_nonneg_of_totallyPositiveFinite hTP i1 0
    have hprod_nonneg :
        0 <= (∑ j : Fin 1, B i0 j * x j) *
          (∑ j : Fin 1, B i1 j * x j) := by
      have hBprod : 0 <= B i0 0 * B i1 0 := mul_nonneg hB0 hB1
      have hxprod : 0 <= x 0 * x 0 := mul_self_nonneg (x 0)
      have hrewrite :
          (∑ j : Fin 1, B i0 j * x j) *
            (∑ j : Fin 1, B i1 j * x j) =
            (B i0 0 * B i1 0) * (x 0 * x 0) := by
        simp
        ring
      rw [hrewrite]
      exact mul_nonneg hBprod hxprod
    exact not_lt_of_ge hprod_nonneg hneg




private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_two
    {m : Nat} {B : Matrix (Fin 2) (Fin m) Real} {x : Fin m -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 2 => ∑ j : Fin m, B i j * x j)) :
      exists cols : Fin 2 -> Fin m,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  let u0 : Real := ∑ j : Fin m, B 0 j * x j
  let u1 : Real := ∑ j : Fin m, B 1 j * x j
  have hneg : u0 * u1 < 0 := by
    simpa [u0, u1] using hAlt.2 0 (by norm_num)
  have hu0_ne : u0 ≠ 0 := by
    simpa [u0] using hAlt.1 0
  have hu1_ne : u1 ≠ 0 := by
    simpa [u1] using hAlt.1 1
  have hentry_nonneg : forall i : Fin 2, forall j : Fin m, 0 <= B i j := by
    intro i j
    have hrows : StrictMono (fun _ : Fin 1 => i.val) := by
      intro a b hab
      fin_cases a
      fin_cases b
      simp at hab
    have hcols : StrictMono (fun _ : Fin 1 => j.val) := by
      intro a b hab
      fin_cases a
      fin_cases b
      simp at hab
    have hminor := hTP 1 (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) hrows hcols
    simpa using hminor
  by_contra hnone
  have hdet_zero_cols :
      forall cols : Fin 2 -> Fin m, Function.Injective cols ->
        (Matrix.of fun i j => B i (cols j)).det = 0 := by
    intro cols hcols
    by_contra hdet
    exact hnone ⟨cols, hcols, hdet⟩
  have hrel : forall j k : Fin m, B 0 j * B 1 k = B 0 k * B 1 j := by
    intro j k
    by_cases hjk : j = k
    · subst k
      ring
    · let cols : Fin 2 -> Fin m := fun c => if c = 0 then j else k
      have hcols : Function.Injective cols := by
        have hkj : k ≠ j := fun h => hjk h.symm
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp [cols, hjk, hkj] at hab ⊢
      have hdet := hdet_zero_cols cols hcols
      have hformula :
          (Matrix.of fun i c => B i (cols c)).det =
            B 0 j * B 1 k - B 0 k * B 1 j := by
        rw [Matrix.det_fin_two]
        simp [cols]
      rw [hformula] at hdet
      nlinarith
  have hex_a : exists j : Fin m, B 0 j ≠ 0 := by
    by_contra hno
    have hzero : forall j : Fin m, B 0 j = 0 := by
      intro j
      by_contra hj
      exact hno ⟨j, hj⟩
    have hu0_zero : u0 = 0 := by
      simp [u0, hzero]
    exact hu0_ne hu0_zero
  rcases hex_a with ⟨j0, hB0_ne⟩
  have hB0_pos : 0 < B 0 j0 := lt_of_le_of_ne (hentry_nonneg 0 j0) (Ne.symm hB0_ne)
  have hB1_ne : B 1 j0 ≠ 0 := by
    intro hB1_zero
    have hrow1_zero : forall k : Fin m, B 1 k = 0 := by
      intro k
      have hprod : B 0 j0 * B 1 k = 0 := by
        simpa [hB1_zero] using hrel j0 k
      exact (mul_eq_zero.mp hprod).resolve_left hB0_ne
    have hu1_zero : u1 = 0 := by
      simp [u1, hrow1_zero]
    exact hu1_ne hu1_zero
  have hB1_pos : 0 < B 1 j0 := lt_of_le_of_ne (hentry_nonneg 1 j0) (Ne.symm hB1_ne)
  have hscale : u0 * B 1 j0 = B 0 j0 * u1 := by
    calc
      u0 * B 1 j0
          = ∑ j : Fin m, (B 0 j * x j) * B 1 j0 := by
              simp [u0, Finset.sum_mul]
      _ = ∑ j : Fin m, B 0 j0 * (B 1 j * x j) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              have h := hrel j j0
              calc
                (B 0 j * x j) * B 1 j0
                    = (B 0 j * B 1 j0) * x j := by ring
                _ = (B 0 j0 * B 1 j) * x j := by rw [h]
                _ = B 0 j0 * (B 1 j * x j) := by ring
      _ = B 0 j0 * u1 := by
              simp [u1, Finset.mul_sum]
  have hscaled_nonneg : 0 <= B 0 j0 * (u0 * u1) := by
    have hleft_nonneg : 0 <= (u0 * u0) * B 1 j0 :=
      mul_nonneg (mul_self_nonneg u0) hB1_pos.le
    have heq : B 0 j0 * (u0 * u1) = (u0 * u0) * B 1 j0 := by
      calc
        B 0 j0 * (u0 * u1)
            = u0 * (B 0 j0 * u1) := by ring
        _ = u0 * (u0 * B 1 j0) := by rw [← hscale]
        _ = (u0 * u0) * B 1 j0 := by ring
    simpa [heq] using hleft_nonneg
  have hprod_nonneg : 0 <= u0 * u1 :=
    nonneg_of_mul_nonneg_left
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled_nonneg) hB0_pos
  exact not_lt_of_ge hprod_nonneg hneg


private theorem adjugate_checkerboard_nonneg_of_totallyPositive :
  forall {n : Nat} {B : Matrix (Fin n) (Fin n) Real},
    IsTotallyPositiveFinite B ->
      forall p q : Fin n,
        0 <= ((-1 : Real) ^ (p.val + q.val)) * (B.adjugate q p) := by
  intro n B hTP p q
  cases n with
  | zero => exact Fin.elim0 p
  | succ k =>
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      have hrows : StrictMono (fun a : Fin k => ((p.succAbove a).val)) := by
        intro a b hab
        exact Fin.strictMono_succAbove p hab
      have hcols : StrictMono (fun a : Fin k => ((q.succAbove a).val)) := by
        intro a b hab
        exact Fin.strictMono_succAbove q hab
      have hminor : 0 <= (B.submatrix p.succAbove q.succAbove).det :=
        hTP k p.succAbove q.succAbove hrows hcols
      have heq : (-1 : Real) ^ (p.val + q.val) *
            ((-1 : Real) ^ (p.val + q.val) *
              (B.submatrix p.succAbove q.succAbove).det) =
          (B.submatrix p.succAbove q.succAbove).det := by
        rcases neg_one_pow_eq_or Real (p.val + q.val) with hs | hs <;>
          simp [hs]
      simpa [heq] using hminor



private theorem exists_nonzero_adjugate_col_two_of_alternating_image_fin_three
    {B : Matrix (Fin 3) (Fin 3) Real} {x : Fin 3 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 3 => ∑ j : Fin 3, B i j * x j)) :
    exists q : Fin 3, B.adjugate q 2 ≠ 0 := by
  classical
  let B01 : Matrix (Fin 2) (Fin 3) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP01 : IsTotallyPositiveFinite B01 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt01 :
      IsStrictlyAlternatingFin (fun i : Fin 2 => ∑ j : Fin 3, B01 i j * x j) := by
    constructor
    · intro i
      simpa [B01] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      fin_cases i
      · simpa [B01] using hAlt.2 0 (by norm_num)
      · norm_num at hi
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_two
      hTP01 hAlt01 with ⟨cols, hcols, hdet⟩
  have hne_val : (cols 0).val ≠ (cols 1).val := by
    intro hval
    have hsame_cols : cols 0 = cols 1 := Fin.ext hval
    have hsame_idx : (0 : Fin 2) = 1 := hcols hsame_cols
    norm_num at hsame_idx
  have hcases :
      ((cols 0).val = 0 ∧ (cols 1).val = 1) ∨
      ((cols 0).val = 0 ∧ (cols 1).val = 2) ∨
      ((cols 0).val = 1 ∧ (cols 1).val = 0) ∨
      ((cols 0).val = 1 ∧ (cols 1).val = 2) ∨
      ((cols 0).val = 2 ∧ (cols 1).val = 0) ∨
      ((cols 0).val = 2 ∧ (cols 1).val = 1) := by
    have h0lt : (cols 0).val < 3 := (cols 0).isLt
    have h1lt : (cols 1).val < 3 := (cols 1).isLt
    omega
  rcases hcases with
      ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ |
      ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine ⟨2, ?_⟩
    have hc0 : cols 0 = (0 : Fin 3) := Fin.ext h0
    have hc1 : cols 1 = (1 : Fin 3) := Fin.ext h1
    have hdetformula :
        (Matrix.of fun i j => B01 i (cols j)).det =
          B 0 0 * B 1 1 - B 0 1 * B 1 0 := by
      rw [Matrix.det_fin_two]
      simp [B01, hc0, hc1]
    have hadjformula :
        B.adjugate 2 2 = B 0 0 * B 1 1 - B 0 1 * B 1 0 := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      rw [Matrix.det_fin_two]
      simp [Fin.succAbove]
      ring_nf
    intro hadj
    exact hdet (by
      rw [hdetformula, ← hadjformula]
      exact hadj)
  · refine ⟨1, ?_⟩
    have hc0 : cols 0 = (0 : Fin 3) := Fin.ext h0
    have hc1 : cols 1 = (2 : Fin 3) := Fin.ext h1
    have hdetformula :
        (Matrix.of fun i j => B01 i (cols j)).det =
          B 0 0 * B 1 2 - B 0 2 * B 1 0 := by
      rw [Matrix.det_fin_two]
      simp [B01, hc0, hc1]
    have hadjformula :
        B.adjugate 1 2 = -(B 0 0 * B 1 2 - B 0 2 * B 1 0) := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      rw [Matrix.det_fin_two]
      simp [Fin.succAbove]
      ring_nf
    intro hadj
    have hminor_zero :
        B 0 0 * B 1 2 - B 0 2 * B 1 0 = 0 := by
      have hneg_zero :
          -(B 0 0 * B 1 2 - B 0 2 * B 1 0) = 0 := by
        rw [← hadjformula]
        exact hadj
      linarith
    exact hdet (by simp [hdetformula, hminor_zero])
  · refine ⟨2, ?_⟩
    have hc0 : cols 0 = (1 : Fin 3) := Fin.ext h0
    have hc1 : cols 1 = (0 : Fin 3) := Fin.ext h1
    have hdetformula :
        (Matrix.of fun i j => B01 i (cols j)).det =
          -(B 0 0 * B 1 1 - B 0 1 * B 1 0) := by
      rw [Matrix.det_fin_two]
      simp [B01, hc0, hc1]
    have hadjformula :
        B.adjugate 2 2 = B 0 0 * B 1 1 - B 0 1 * B 1 0 := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      rw [Matrix.det_fin_two]
      simp [Fin.succAbove]
      ring_nf
    intro hadj
    have hminor_zero :
        B 0 0 * B 1 1 - B 0 1 * B 1 0 = 0 := by
      rw [← hadjformula]
      exact hadj
    exact hdet (by simp [hdetformula, hminor_zero])
  · refine ⟨0, ?_⟩
    have hc0 : cols 0 = (1 : Fin 3) := Fin.ext h0
    have hc1 : cols 1 = (2 : Fin 3) := Fin.ext h1
    have hdetformula :
        (Matrix.of fun i j => B01 i (cols j)).det =
          B 0 1 * B 1 2 - B 0 2 * B 1 1 := by
      rw [Matrix.det_fin_two]
      simp [B01, hc0, hc1]
    have hadjformula :
        B.adjugate 0 2 = B 0 1 * B 1 2 - B 0 2 * B 1 1 := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      rw [Matrix.det_fin_two]
      simp [Fin.succAbove]
    intro hadj
    exact hdet (by
      rw [hdetformula, ← hadjformula]
      exact hadj)
  · refine ⟨1, ?_⟩
    have hc0 : cols 0 = (2 : Fin 3) := Fin.ext h0
    have hc1 : cols 1 = (0 : Fin 3) := Fin.ext h1
    have hdetformula :
        (Matrix.of fun i j => B01 i (cols j)).det =
          -(B 0 0 * B 1 2 - B 0 2 * B 1 0) := by
      rw [Matrix.det_fin_two]
      simp [B01, hc0, hc1]
    have hadjformula :
        B.adjugate 1 2 = -(B 0 0 * B 1 2 - B 0 2 * B 1 0) := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      rw [Matrix.det_fin_two]
      simp [Fin.succAbove]
      ring_nf
    intro hadj
    exact hdet (by
      rw [hdetformula, ← hadjformula]
      exact hadj)
  · refine ⟨0, ?_⟩
    have hc0 : cols 0 = (2 : Fin 3) := Fin.ext h0
    have hc1 : cols 1 = (1 : Fin 3) := Fin.ext h1
    have hdetformula :
        (Matrix.of fun i j => B01 i (cols j)).det =
          -(B 0 1 * B 1 2 - B 0 2 * B 1 1) := by
      rw [Matrix.det_fin_two]
      simp [B01, hc0, hc1]
    have hadjformula :
        B.adjugate 0 2 = B 0 1 * B 1 2 - B 0 2 * B 1 1 := by
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      rw [Matrix.det_fin_two]
      simp [Fin.succAbove]
    intro hadj
    have hminor_zero :
        B 0 1 * B 1 2 - B 0 2 * B 1 1 = 0 := by
      rw [← hadjformula]
      exact hadj
    exact hdet (by simp [hdetformula, hminor_zero])



private theorem det_ne_zero_of_totallyPositive_of_alternating_image_fin_three
    {B : Matrix (Fin 3) (Fin 3) Real} {x : Fin 3 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 3 => ∑ j : Fin 3, B i j * x j)) :
    B.det ≠ 0 := by
  classical
  intro hdet_zero
  let u : Fin 3 -> Real := fun i => ∑ j : Fin 3, B i j * x j
  rcases exists_nonzero_adjugate_col_two_of_alternating_image_fin_three
      hTP hAlt with ⟨q, hq_ne⟩
  let r : Real := (-1 : Real) ^ q.val * u 0
  have hchecker :
      forall i : Fin 3,
        0 <= ((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i) := by
    intro i
    exact adjugate_checkerboard_nonneg_of_totallyPositive hTP i q
  have hcommon_nonneg :
      forall i : Fin 3, 0 <= r * (B.adjugate q i * u i) := by
    intro i
    have hsign : 0 < u 0 * (((-1 : Real) ^ i.val) * u i) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := i)
    have heq : r * (B.adjugate q i * u i) =
        (u 0 * (((-1 : Real) ^ i.val) * u i)) *
          (((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real i.val with hi | hi <;>
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
      simp [hi, hq, mul_assoc, mul_comm]
    rw [heq]
    exact mul_nonneg hsign.le (hchecker i)
  have hcommon_pos_two : 0 < r * (B.adjugate q 2 * u 2) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (2 : Nat)) * u 2) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (2 : Fin 3))
    have hchecker_two_nonneg :
        0 <= ((-1 : Real) ^ ((2 : Fin 3).val + q.val)) * (B.adjugate q 2) :=
      hchecker 2
    have hchecker_two_ne :
        ((-1 : Real) ^ ((2 : Fin 3).val + q.val)) * (B.adjugate q 2) ≠ 0 := by
      exact mul_ne_zero
        (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hq_ne
    have hchecker_two_pos :
        0 < ((-1 : Real) ^ ((2 : Fin 3).val + q.val)) * (B.adjugate q 2) :=
      lt_of_le_of_ne hchecker_two_nonneg (Ne.symm hchecker_two_ne)
    have heq : r * (B.adjugate q 2 * u 2) =
        (u 0 * (((-1 : Real) ^ (2 : Nat)) * u 2)) *
          (((-1 : Real) ^ ((2 : Fin 3).val + q.val)) * (B.adjugate q 2)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
        simp [hq] <;> ring
    rw [heq]
    exact mul_pos hsign hchecker_two_pos
  have hsum_pos :
      0 < ∑ i : Fin 3, r * (B.adjugate q i * u i) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i : Fin 3 => r * (B.adjugate q i * u i))
        (fun i _ => hcommon_nonneg i)
        (Finset.mem_univ (2 : Fin 3))
    exact lt_of_lt_of_le hcommon_pos_two hle
  have hu : u = B *ᵥ x := by
    ext i
    simp [u, Matrix.mulVec, dotProduct]
  have hvec : B.adjugate *ᵥ u = 0 := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet_zero]
    ext i
    simp
  have hsum_zero : (∑ i : Fin 3, B.adjugate q i * u i) = 0 := by
    have hqvec := congrFun hvec q
    simpa [Matrix.mulVec, dotProduct] using hqvec
  have hsum_rewrite :
      (∑ i : Fin 3, r * (B.adjugate q i * u i)) =
        r * (∑ i : Fin 3, B.adjugate q i * u i) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hsum_zero, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos


private theorem linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_three
    {B : Matrix (Fin 3) (Fin 3) Real} {x : Fin 3 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 3 => ∑ j : Fin 3, B i j * x j)) :
    LinearIndependent Real (fun i : Fin 3 => fun j : Fin 3 => B i j) := by
  have hdet := det_ne_zero_of_totallyPositive_of_alternating_image_fin_three hTP hAlt
  have hunit : IsUnit B := Matrix.isUnit_iff_isUnit_det B |>.mpr (IsUnit.mk0 B.det hdet)
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr hunit




private theorem not_strictlyAlternating_image_fin_three_two
    {B : Matrix (Fin 3) (Fin 2) Real} {x : Fin 2 -> Real}
    (hTP : IsTotallyPositiveFinite B) :
      ¬ IsStrictlyAlternatingFin
        (fun i : Fin 3 => ∑ j : Fin 2, B i j * x j) := by
  classical
  intro hAlt
  let u0 : Real := ∑ j : Fin 2, B 0 j * x j
  let u1 : Real := ∑ j : Fin 2, B 1 j * x j
  let u2 : Real := ∑ j : Fin 2, B 2 j * x j
  let d01 : Real := B 0 0 * B 1 1 - B 0 1 * B 1 0
  let d02 : Real := B 0 0 * B 2 1 - B 0 1 * B 2 0
  let d12 : Real := B 1 0 * B 2 1 - B 1 1 * B 2 0
  have hTP01 :
      IsTotallyPositiveFinite
        (fun i : Fin 2 => fun j : Fin 2 => B ⟨i.val, by omega⟩ j) := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt01 :
      IsStrictlyAlternatingFin
        (fun i : Fin 2 =>
          ∑ j : Fin 2, (fun i : Fin 2 => fun j : Fin 2 => B ⟨i.val, by omega⟩ j) i j * x j) := by
    constructor
    · intro i
      simpa using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      fin_cases i
      · simpa [u0, u1] using hAlt.2 0 (by norm_num)
      · norm_num at hi
  have hd01_ne : d01 ≠ 0 := by
    rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_two
        hTP01 hAlt01 with ⟨cols, hcols, hdet⟩
    have hcols_cases :
        (cols 0 = 0 ∧ cols 1 = 1) ∨ (cols 0 = 1 ∧ cols 1 = 0) := by
      have hne_val : (cols 0).val ≠ (cols 1).val := by
        intro hval
        have hsame_cols : cols 0 = cols 1 := Fin.ext hval
        have hsame_idx : (0 : Fin 2) = 1 := hcols hsame_cols
        norm_num at hsame_idx
      have hvals :
          ((cols 0).val = 0 ∧ (cols 1).val = 1) ∨
            ((cols 0).val = 1 ∧ (cols 1).val = 0) := by
        omega
      rcases hvals with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inl ⟨Fin.ext h0, Fin.ext h1⟩
      · exact Or.inr ⟨Fin.ext h0, Fin.ext h1⟩
    rcases hcols_cases with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have hformula :
          (Matrix.of fun i j =>
            (fun i : Fin 2 => fun j : Fin 2 => B ⟨i.val, by omega⟩ j) i (cols j)).det =
              d01 := by
        rw [Matrix.det_fin_two]
        simp [d01, h0, h1]
      simpa [hformula] using hdet
    · have hformula :
          (Matrix.of fun i j =>
            (fun i : Fin 2 => fun j : Fin 2 => B ⟨i.val, by omega⟩ j) i (cols j)).det =
              -d01 := by
        rw [Matrix.det_fin_two]
        simp [d01, h0, h1]
      intro hd01
      exact hdet (by simp [hformula, hd01])
  have hd01_nonneg : 0 <= d01 := by
    have hrows : StrictMono (fun i : Fin 2 => (⟨i.val, by omega⟩ : Fin 3).val) := by
      intro a b hab
      exact hab
    have hcols : StrictMono (fun j : Fin 2 => j.val) := by
      intro a b hab
      exact hab
    have hminor := hTP 2 (fun i : Fin 2 => ⟨i.val, by omega⟩)
      (fun j : Fin 2 => j) hrows hcols
    simpa [d01, Matrix.det_fin_two] using hminor
  have hd01_pos : 0 < d01 := lt_of_le_of_ne hd01_nonneg (Ne.symm hd01_ne)
  have hd02_nonneg : 0 <= d02 := by
    let rows02 : Fin 2 -> Fin 3 := fun i => if i = 0 then 0 else 2
    have hrows : StrictMono (fun i : Fin 2 => (rows02 i).val) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp [rows02] at hab ⊢
    have hcols : StrictMono (fun j : Fin 2 => j.val) := by
      intro a b hab
      exact hab
    have hminor := hTP 2 rows02 (fun j : Fin 2 => j) hrows hcols
    simpa [d02, rows02, Matrix.det_fin_two] using hminor
  have hd12_nonneg : 0 <= d12 := by
    let rows12 : Fin 2 -> Fin 3 := fun i => ⟨i.val + 1, by omega⟩
    have hrows : StrictMono (fun i : Fin 2 => (rows12 i).val) := by
      intro a b hab
      exact Nat.add_lt_add_right hab 1
    have hcols : StrictMono (fun j : Fin 2 => j.val) := by
      intro a b hab
      exact hab
    have hminor := hTP 2 rows12 (fun j : Fin 2 => j) hrows hcols
    simpa [d12, rows12, Matrix.det_fin_two] using hminor
  have hidentity : d12 * u0 - d02 * u1 + d01 * u2 = 0 := by
    simp [d12, d02, d01, u0, u1, u2]
    ring
  have h01neg : u0 * u1 < 0 := by
    simpa [u0, u1] using hAlt.2 0 (by norm_num)
  have h12neg : u1 * u2 < 0 := by
    simpa [u1, u2] using hAlt.2 1 (by norm_num)
  have hu1_ne : u1 ≠ 0 := by
    simpa [u1] using hAlt.1 1
  rcases lt_or_gt_of_ne hu1_ne.symm with hu1_pos | hu1_neg
  · have hu0_neg : u0 < 0 := by
      rcases mul_neg_iff.mp h01neg with h | h
      · exact False.elim (not_lt_of_ge hu1_pos.le h.2)
      · exact h.1
    have hu2_neg : u2 < 0 := by
      rcases mul_neg_iff.mp h12neg with h | h
      · exact h.2
      · exact False.elim (not_lt_of_ge hu1_pos.le h.1)
    have hterm0 : d12 * u0 <= 0 := mul_nonpos_of_nonneg_of_nonpos hd12_nonneg hu0_neg.le
    have hterm1 : -d02 * u1 <= 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd02_nonneg) hu1_pos.le
    have hterm2 : d01 * u2 < 0 := mul_neg_of_pos_of_neg hd01_pos hu2_neg
    have hsum_neg : d12 * u0 - d02 * u1 + d01 * u2 < 0 := by
      nlinarith
    rw [hidentity] at hsum_neg
    linarith
  · have hu0_pos : 0 < u0 := by
      rcases mul_neg_iff.mp h01neg with h | h
      · exact h.1
      · exact False.elim (not_lt_of_ge hu1_neg.le h.2)
    have hu2_pos : 0 < u2 := by
      rcases mul_neg_iff.mp h12neg with h | h
      · exact False.elim (not_lt_of_ge hu1_neg.le h.1)
      · exact h.2
    have hterm0 : 0 <= d12 * u0 := mul_nonneg hd12_nonneg hu0_pos.le
    have hterm1 : 0 <= -d02 * u1 := by
      have hnonneg : 0 <= d02 * (-u1) :=
        mul_nonneg hd02_nonneg (neg_nonneg.mpr hu1_neg.le)
      nlinarith
    have hterm2 : 0 < d01 * u2 := mul_pos hd01_pos hu2_pos
    have hsum_pos : 0 < d12 * u0 - d02 * u1 + d01 * u2 := by
      nlinarith
    rw [hidentity] at hsum_pos
    linarith



private theorem not_strictlyAlternating_image_of_cols_eq_two :
  forall {n : Nat} {B : Matrix (Fin n) (Fin 2) Real} {x : Fin 2 -> Real},
    3 <= n ->
    IsTotallyPositiveFinite B ->
      ¬ IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin 2, B i j * x j) := by
  classical
  intro n B x hn hTP hAlt
  let B3 : Matrix (Fin 3) (Fin 2) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP3 : IsTotallyPositiveFinite B3 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt3 :
      IsStrictlyAlternatingFin (fun i : Fin 3 => ∑ j : Fin 2, B3 i j * x j) := by
    constructor
    · intro i
      simpa [B3] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < n := by omega
      simpa [B3] using hAlt.2 ⟨i.val, by omega⟩ hi'
  exact (not_strictlyAlternating_image_fin_three_two hTP3) hAlt3




private theorem not_strictlyAlternating_image_fin_four_three
    {B : Matrix (Fin 4) (Fin 3) Real} {x : Fin 3 -> Real}
    (hTP : IsTotallyPositiveFinite B) :
      ¬ IsStrictlyAlternatingFin
        (fun i : Fin 4 => ∑ j : Fin 3, B i j * x j) := by
  classical
  intro hAlt
  let u0 : Real := ∑ j : Fin 3, B 0 j * x j
  let u1 : Real := ∑ j : Fin 3, B 1 j * x j
  let u2 : Real := ∑ j : Fin 3, B 2 j * x j
  let u3 : Real := ∑ j : Fin 3, B 3 j * x j
  let d0 : Real := (B.submatrix (Fin.succAbove (0 : Fin 4)) (fun j : Fin 3 => j)).det
  let d1 : Real := (B.submatrix (Fin.succAbove (1 : Fin 4)) (fun j : Fin 3 => j)).det
  let d2 : Real := (B.submatrix (Fin.succAbove (2 : Fin 4)) (fun j : Fin 3 => j)).det
  let d3 : Real := (B.submatrix (Fin.succAbove (3 : Fin 4)) (fun j : Fin 3 => j)).det
  have hminor_nonneg :
      forall p : Fin 4, 0 <= (B.submatrix (Fin.succAbove p) (fun j : Fin 3 => j)).det := by
    intro p
    have hrows : StrictMono (fun i : Fin 3 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    have hcols : StrictMono (fun j : Fin 3 => j.val) := by
      intro a b hab
      exact hab
    exact hTP 3 (Fin.succAbove p) (fun j : Fin 3 => j) hrows hcols
  have hd0_nonneg : 0 <= d0 := by simpa [d0] using hminor_nonneg 0
  have hd1_nonneg : 0 <= d1 := by simpa [d1] using hminor_nonneg 1
  have hd2_nonneg : 0 <= d2 := by simpa [d2] using hminor_nonneg 2
  have hd3_nonneg : 0 <= d3 := by simpa [d3] using hminor_nonneg 3
  let B012 : Matrix (Fin 3) (Fin 3) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP012 : IsTotallyPositiveFinite B012 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt012 :
      IsStrictlyAlternatingFin (fun i : Fin 3 => ∑ j : Fin 3, B012 i j * x j) := by
    constructor
    · intro i
      simpa [B012] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 4 := by omega
      simpa [B012] using hAlt.2 ⟨i.val, by omega⟩ hi'
  have hd3_ne : d3 ≠ 0 := by
    have hLI :=
      linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_three
        hTP012 hAlt012
    have hunit : IsUnit B012 := Matrix.linearIndependent_rows_iff_isUnit.mp hLI
    have hdetUnit : IsUnit B012.det := (Matrix.isUnit_iff_isUnit_det B012).mp hunit
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (3 : Fin 4)) (fun j : Fin 3 => j) = B012 := by
      ext i j
      fin_cases i <;> rfl
    have hd3_eq : d3 = B012.det := by
      simp [d3, hmatrix_eq]
    exact fun hd3_zero => hdetUnit.ne_zero (by simpa [← hd3_eq] using hd3_zero)
  have hd3_pos : 0 < d3 := lt_of_le_of_ne hd3_nonneg (Ne.symm hd3_ne)
  have hidentity : d0 * u0 - d1 * u1 + d2 * u2 - d3 * u3 = 0 := by
    simp [d0, d1, d2, d3, u0, u1, u2, u3, Matrix.det_fin_three,
      Fin.succAbove, Fin.sum_univ_three]
    ring
  have h01neg : u0 * u1 < 0 := by
    simpa [u0, u1] using hAlt.2 0 (by norm_num)
  have h12neg : u1 * u2 < 0 := by
    simpa [u1, u2] using hAlt.2 1 (by norm_num)
  have h23neg : u2 * u3 < 0 := by
    simpa [u2, u3] using hAlt.2 2 (by norm_num)
  have hu0_ne : u0 ≠ 0 := by
    simpa [u0] using hAlt.1 0
  rcases lt_or_gt_of_ne hu0_ne.symm with hu0_pos | hu0_neg
  · have hu1_neg : u1 < 0 := by
      rcases mul_neg_iff.mp h01neg with h | h
      · exact h.2
      · exact False.elim (not_lt_of_ge hu0_pos.le h.1)
    have hu2_pos : 0 < u2 := by
      rcases mul_neg_iff.mp h12neg with h | h
      · exact False.elim (not_lt_of_ge hu1_neg.le h.1)
      · exact h.2
    have hu3_neg : u3 < 0 := by
      rcases mul_neg_iff.mp h23neg with h | h
      · exact h.2
      · exact False.elim (not_lt_of_ge hu2_pos.le h.1)
    have hterm0 : 0 <= d0 * u0 := mul_nonneg hd0_nonneg hu0_pos.le
    have hterm1 : 0 <= -d1 * u1 :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hd1_nonneg) hu1_neg.le
    have hterm2 : 0 <= d2 * u2 := mul_nonneg hd2_nonneg hu2_pos.le
    have hterm3 : 0 < -d3 * u3 :=
      mul_pos_of_neg_of_neg (neg_lt_zero.mpr hd3_pos) hu3_neg
    have hsum_pos : 0 < d0 * u0 - d1 * u1 + d2 * u2 - d3 * u3 := by
      nlinarith
    rw [hidentity] at hsum_pos
    linarith
  · have hu1_pos : 0 < u1 := by
      rcases mul_neg_iff.mp h01neg with h | h
      · exact False.elim (not_lt_of_ge hu0_neg.le h.1)
      · exact h.2
    have hu2_neg : u2 < 0 := by
      rcases mul_neg_iff.mp h12neg with h | h
      · exact h.2
      · exact False.elim (not_lt_of_ge hu1_pos.le h.1)
    have hu3_pos : 0 < u3 := by
      rcases mul_neg_iff.mp h23neg with h | h
      · exact False.elim (not_lt_of_ge hu2_neg.le h.1)
      · exact h.2
    have hterm0 : d0 * u0 <= 0 := mul_nonpos_of_nonneg_of_nonpos hd0_nonneg hu0_neg.le
    have hterm1 : -d1 * u1 <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd1_nonneg) hu1_pos.le
    have hterm2 : d2 * u2 <= 0 := mul_nonpos_of_nonneg_of_nonpos hd2_nonneg hu2_neg.le
    have hterm3 : -d3 * u3 < 0 :=
      mul_neg_of_neg_of_pos (neg_lt_zero.mpr hd3_pos) hu3_pos
    have hsum_neg : d0 * u0 - d1 * u1 + d2 * u2 - d3 * u3 < 0 := by
      nlinarith
    rw [hidentity] at hsum_neg
    linarith



private theorem not_strictlyAlternating_image_of_cols_eq_three :
  forall {n : Nat} {B : Matrix (Fin n) (Fin 3) Real} {x : Fin 3 -> Real},
    4 <= n ->
    IsTotallyPositiveFinite B ->
      ¬ IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin 3, B i j * x j) := by
  classical
  intro n B x hn hTP hAlt
  let B4 : Matrix (Fin 4) (Fin 3) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP4 : IsTotallyPositiveFinite B4 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt4 :
      IsStrictlyAlternatingFin (fun i : Fin 4 => ∑ j : Fin 3, B4 i j * x j) := by
    constructor
    · intro i
      simpa [B4] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < n := by omega
      simpa [B4] using hAlt.2 ⟨i.val, by omega⟩ hi'
  exact (not_strictlyAlternating_image_fin_four_three hTP4) hAlt4



private theorem exists_positive_ordered_two_minor_first_two_rows_fin_three_four
    {B : Matrix (Fin 3) (Fin 4) Real} {x : Fin 4 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 3 => ∑ j : Fin 4, B i j * x j)) :
    exists a b : Fin 4,
      a.val < b.val /\
        0 < B 0 a * B 1 b - B 0 b * B 1 a := by
  classical
  let B01 : Matrix (Fin 2) (Fin 4) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP01 : IsTotallyPositiveFinite B01 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt01 :
      IsStrictlyAlternatingFin (fun i : Fin 2 => ∑ j : Fin 4, B01 i j * x j) := by
    constructor
    · intro i
      simpa [B01] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      fin_cases i
      · simpa [B01] using hAlt.2 0 (by norm_num)
      · norm_num at hi
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_two
      hTP01 hAlt01 with ⟨cols, hcols, hdet⟩
  have hne_val : (cols 0).val ≠ (cols 1).val := by
    intro hval
    have hsame_cols : cols 0 = cols 1 := Fin.ext hval
    have hsame_idx : (0 : Fin 2) = 1 := hcols hsame_cols
    norm_num at hsame_idx
  by_cases hlt : (cols 0).val < (cols 1).val
  · let a : Fin 4 := cols 0
    let b : Fin 4 := cols 1
    have hdet_eq :
        (Matrix.of fun i j => B01 i (cols j)).det =
          B 0 a * B 1 b - B 0 b * B 1 a := by
      rw [Matrix.det_fin_two]
      simp [B01, a, b]
    have hminor_nonneg : 0 <= B 0 a * B 1 b - B 0 b * B 1 a := by
      let colsAB : Fin 2 -> Fin 4 := fun j => if j = 0 then a else b
      have hrows : StrictMono (fun i : Fin 2 => (⟨i.val, by omega⟩ : Fin 3).val) := by
        intro i j hij
        exact hij
      have hcolsAB : StrictMono (fun j : Fin 2 => (colsAB j).val) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp [colsAB, a, b, hlt] at hij ⊢
      have hminor := hTP 2 (fun i : Fin 2 => ⟨i.val, by omega⟩) colsAB hrows hcolsAB
      simpa [colsAB, a, b, Matrix.det_fin_two] using hminor
    have hminor_ne : B 0 a * B 1 b - B 0 b * B 1 a ≠ 0 := by
      intro hzero
      exact hdet (by simp [hdet_eq, hzero])
    exact ⟨a, b, hlt, lt_of_le_of_ne hminor_nonneg (Ne.symm hminor_ne)⟩
  · have hgt : (cols 1).val < (cols 0).val := by omega
    let a : Fin 4 := cols 1
    let b : Fin 4 := cols 0
    have hdet_eq :
        (Matrix.of fun i j => B01 i (cols j)).det =
          -(B 0 a * B 1 b - B 0 b * B 1 a) := by
      rw [Matrix.det_fin_two]
      simp [B01, a, b]
    have hminor_nonneg : 0 <= B 0 a * B 1 b - B 0 b * B 1 a := by
      let colsAB : Fin 2 -> Fin 4 := fun j => if j = 0 then a else b
      have hrows : StrictMono (fun i : Fin 2 => (⟨i.val, by omega⟩ : Fin 3).val) := by
        intro i j hij
        exact hij
      have hcolsAB : StrictMono (fun j : Fin 2 => (colsAB j).val) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp [colsAB, a, b, hgt] at hij ⊢
      have hminor := hTP 2 (fun i : Fin 2 => ⟨i.val, by omega⟩) colsAB hrows hcolsAB
      simpa [colsAB, a, b, Matrix.det_fin_two] using hminor
    have hminor_ne : B 0 a * B 1 b - B 0 b * B 1 a ≠ 0 := by
      intro hzero
      exact hdet (by simp [hdet_eq, hzero])
    exact ⟨a, b, hgt, lt_of_le_of_ne hminor_nonneg (Ne.symm hminor_ne)⟩



private theorem exists_positive_ordered_two_minor_first_two_rows_fin_three
    {m : Nat} {B : Matrix (Fin 3) (Fin m) Real} {x : Fin m -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 3 => ∑ j : Fin m, B i j * x j)) :
    exists a b : Fin m,
      a.val < b.val /\
        0 < B 0 a * B 1 b - B 0 b * B 1 a := by
  classical
  let B01 : Matrix (Fin 2) (Fin m) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP01 : IsTotallyPositiveFinite B01 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt01 :
      IsStrictlyAlternatingFin (fun i : Fin 2 => ∑ j : Fin m, B01 i j * x j) := by
    constructor
    · intro i
      simpa [B01] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      fin_cases i
      · simpa [B01] using hAlt.2 0 (by norm_num)
      · norm_num at hi
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_two
      hTP01 hAlt01 with ⟨cols, hcols, hdet⟩
  have hne_val : (cols 0).val ≠ (cols 1).val := by
    intro hval
    have hsame_cols : cols 0 = cols 1 := Fin.ext hval
    have hsame_idx : (0 : Fin 2) = 1 := hcols hsame_cols
    norm_num at hsame_idx
  by_cases hlt : (cols 0).val < (cols 1).val
  · let a : Fin m := cols 0
    let b : Fin m := cols 1
    have hdet_eq :
        (Matrix.of fun i j => B01 i (cols j)).det =
          B 0 a * B 1 b - B 0 b * B 1 a := by
      rw [Matrix.det_fin_two]
      simp [B01, a, b]
    have hminor_nonneg : 0 <= B 0 a * B 1 b - B 0 b * B 1 a := by
      let colsAB : Fin 2 -> Fin m := fun j => if j = 0 then a else b
      have hrows : StrictMono (fun i : Fin 2 => (⟨i.val, by omega⟩ : Fin 3).val) := by
        intro i j hij
        exact hij
      have hcolsAB : StrictMono (fun j : Fin 2 => (colsAB j).val) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp [colsAB, a, b, hlt] at hij ⊢
      have hminor := hTP 2 (fun i : Fin 2 => ⟨i.val, by omega⟩) colsAB hrows hcolsAB
      simpa [colsAB, a, b, Matrix.det_fin_two] using hminor
    have hminor_ne : B 0 a * B 1 b - B 0 b * B 1 a ≠ 0 := by
      intro hzero
      exact hdet (by simp [hdet_eq, hzero])
    exact ⟨a, b, hlt, lt_of_le_of_ne hminor_nonneg (Ne.symm hminor_ne)⟩
  · have hgt : (cols 1).val < (cols 0).val := by omega
    let a : Fin m := cols 1
    let b : Fin m := cols 0
    have hdet_eq :
        (Matrix.of fun i j => B01 i (cols j)).det =
          -(B 0 a * B 1 b - B 0 b * B 1 a) := by
      rw [Matrix.det_fin_two]
      simp [B01, a, b]
    have hminor_nonneg : 0 <= B 0 a * B 1 b - B 0 b * B 1 a := by
      let colsAB : Fin 2 -> Fin m := fun j => if j = 0 then a else b
      have hrows : StrictMono (fun i : Fin 2 => (⟨i.val, by omega⟩ : Fin 3).val) := by
        intro i j hij
        exact hij
      have hcolsAB : StrictMono (fun j : Fin 2 => (colsAB j).val) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp [colsAB, a, b, hgt] at hij ⊢
      have hminor := hTP 2 (fun i : Fin 2 => ⟨i.val, by omega⟩) colsAB hrows hcolsAB
      simpa [colsAB, a, b, Matrix.det_fin_two] using hminor
    have hminor_ne : B 0 a * B 1 b - B 0 b * B 1 a ≠ 0 := by
      intro hzero
      exact hdet (by simp [hdet_eq, hzero])
    exact ⟨a, b, hgt, lt_of_le_of_ne hminor_nonneg (Ne.symm hminor_ne)⟩



private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_three_cols
    {m : Nat} {B : Matrix (Fin 3) (Fin m) Real} {x : Fin m -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 3 => ∑ j : Fin m, B i j * x j)) :
      exists cols : Fin 3 -> Fin m,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  by_contra hnone
  have hdet_zero_cols :
      forall cols : Fin 3 -> Fin m, Function.Injective cols ->
        (Matrix.of fun i j => B i (cols j)).det = 0 := by
    intro cols hcols
    by_contra hdet
    exact hnone ⟨cols, hcols, hdet⟩
  let u0 : Real := ∑ j : Fin m, B 0 j * x j
  let u1 : Real := ∑ j : Fin m, B 1 j * x j
  let u2 : Real := ∑ j : Fin m, B 2 j * x j
  rcases exists_positive_ordered_two_minor_first_two_rows_fin_three
      hTP hAlt with ⟨a, b, hab, hd_pos⟩
  let d : Real := B 0 a * B 1 b - B 0 b * B 1 a
  let e : Real := B 1 a * B 2 b - B 1 b * B 2 a
  let f : Real := B 0 a * B 2 b - B 0 b * B 2 a
  have hd_pos' : 0 < d := by simpa [d] using hd_pos
  have he_nonneg : 0 <= e := by
    let rows12 : Fin 2 -> Fin 3 := fun i => ⟨i.val + 1, by omega⟩
    let colsAB : Fin 2 -> Fin m := fun j => if j = 0 then a else b
    have hrows : StrictMono (fun i : Fin 2 => (rows12 i).val) := by
      intro i j hij
      exact Nat.add_lt_add_right hij 1
    have hcols : StrictMono (fun j : Fin 2 => (colsAB j).val) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [colsAB, hab] at hij ⊢
    have hminor := hTP 2 rows12 colsAB hrows hcols
    simpa [e, rows12, colsAB, Matrix.det_fin_two] using hminor
  have hf_nonneg : 0 <= f := by
    let rows02 : Fin 2 -> Fin 3 := fun i => if i = 0 then 0 else 2
    let colsAB : Fin 2 -> Fin m := fun j => if j = 0 then a else b
    have hrows : StrictMono (fun i : Fin 2 => (rows02 i).val) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [rows02] at hij ⊢
    have hcols : StrictMono (fun j : Fin 2 => (colsAB j).val) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [colsAB, hab] at hij ⊢
    have hminor := hTP 2 rows02 colsAB hrows hcols
    simpa [f, rows02, colsAB, Matrix.det_fin_two] using hminor
  have hrel_col : forall k : Fin m, e * B 0 k - f * B 1 k + d * B 2 k = 0 := by
    intro k
    by_cases hka : k = a
    · subst k
      simp [d, e, f]
      ring
    by_cases hkb : k = b
    · subst k
      simp [d, e, f]
      ring
    let cols3 : Fin 3 -> Fin m := fun j => if j = 0 then a else if j = 1 then b else k
    have hcols3 : Function.Injective cols3 := by
      have hab_ne : a ≠ b := by
        intro h
        have hv : a.val = b.val := congrArg Fin.val h
        omega
      have hba_ne : b ≠ a := fun h => hab_ne h.symm
      have hak : a ≠ k := fun h => hka h.symm
      have hbk : b ≠ k := fun h => hkb h.symm
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [cols3, hab_ne, hba_ne, hka, hkb, hak, hbk] at hij ⊢
    have hdet0 := hdet_zero_cols cols3 hcols3
    have hdet_formula :
        (Matrix.of fun i j => B i (cols3 j)).det =
          e * B 0 k - f * B 1 k + d * B 2 k := by
      rw [Matrix.det_fin_three]
      simp [cols3, d, e, f]
      ring
    simpa [hdet_formula] using hdet0
  have hidentity : e * u0 - f * u1 + d * u2 = 0 := by
    have hsum_zero : (∑ k : Fin m, (e * B 0 k - f * B 1 k + d * B 2 k) * x k) = 0 := by
      simp [hrel_col]
    have hrewrite :
        e * u0 - f * u1 + d * u2 =
          ∑ k : Fin m, (e * B 0 k - f * B 1 k + d * B 2 k) * x k := by
      simp [u0, u1, u2, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [hrewrite, hsum_zero]
  have h01neg : u0 * u1 < 0 := by
    simpa [u0, u1] using hAlt.2 0 (by norm_num)
  have h12neg : u1 * u2 < 0 := by
    simpa [u1, u2] using hAlt.2 1 (by norm_num)
  have hu1_ne : u1 ≠ 0 := by
    simpa [u1] using hAlt.1 1
  rcases lt_or_gt_of_ne hu1_ne.symm with hu1_pos | hu1_neg
  · have hu0_neg : u0 < 0 := by
      rcases mul_neg_iff.mp h01neg with h | h
      · exact False.elim (not_lt_of_ge hu1_pos.le h.2)
      · exact h.1
    have hu2_neg : u2 < 0 := by
      rcases mul_neg_iff.mp h12neg with h | h
      · exact h.2
      · exact False.elim (not_lt_of_ge hu1_pos.le h.1)
    have hterm0 : e * u0 <= 0 := mul_nonpos_of_nonneg_of_nonpos he_nonneg hu0_neg.le
    have hterm1 : -f * u1 <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hf_nonneg) hu1_pos.le
    have hterm2 : d * u2 < 0 := mul_neg_of_pos_of_neg hd_pos' hu2_neg
    have hsum_neg : e * u0 - f * u1 + d * u2 < 0 := by
      nlinarith
    rw [hidentity] at hsum_neg
    linarith
  · have hu0_pos : 0 < u0 := by
      rcases mul_neg_iff.mp h01neg with h | h
      · exact h.1
      · exact False.elim (not_lt_of_ge hu1_neg.le h.2)
    have hu2_pos : 0 < u2 := by
      rcases mul_neg_iff.mp h12neg with h | h
      · exact False.elim (not_lt_of_ge hu1_neg.le h.1)
      · exact h.2
    have hterm0 : 0 <= e * u0 := mul_nonneg he_nonneg hu0_pos.le
    have hterm1 : 0 <= -f * u1 := by
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hf_nonneg) hu1_neg.le
    have hterm2 : 0 < d * u2 := mul_pos hd_pos' hu2_pos
    have hsum_pos : 0 < e * u0 - f * u1 + d * u2 := by
      nlinarith
    rw [hidentity] at hsum_pos
    linarith



private theorem exists_positive_ordered_three_minor_first_three_rows_fin_four_five
    {B : Matrix (Fin 4) (Fin 5) Real} {x : Fin 5 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 4 => ∑ j : Fin 5, B i j * x j)) :
    exists cols : Fin 3 -> Fin 5,
      StrictMono (fun j => (cols j).val) /\
        0 < (Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols j)).det := by
  classical
  let Btop : Matrix (Fin 3) (Fin 5) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 3 => ∑ j : Fin 5, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 4 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_three_cols
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin 5) := Finset.image cols Finset.univ
  have hS_card : S.card = 3 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 3))) hcols
  let colsOrd : Fin 3 -> Fin 5 := fun j => S.orderEmbOfFin hS_card j
  have hcolsOrd_strict : StrictMono (fun j => (colsOrd j).val) := by
    intro a b hab
    exact (S.orderEmbOfFin hS_card).strictMono hab
  have hminor_nonneg :
      0 <= (Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)).det := by
    have hrows : StrictMono (fun i : Fin 3 => (⟨i.val, by omega⟩ : Fin 4).val) := by
      intro i j hij
      exact hij
    exact hTP 3 (fun i : Fin 3 => ⟨i.val, by omega⟩) colsOrd hrows hcolsOrd_strict
  have hcols_ne_ord :
      forall j : Fin 3, cols j ∈ S := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  let colsSub : Fin 3 -> S := fun j => ⟨cols j, hcols_ne_ord j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hS_card]⟩
  let colsEquiv : Fin 3 ≃ S := Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 3) := colsEquiv.trans (S.orderIsoOfFin hS_card).symm
  have hcolsOrd_sigma : forall j : Fin 3, colsOrd (sigma j) = cols j := by
    intro j
    have hsub : S.orderIsoOfFin hS_card (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 3) (Fin 3) Real :=
    Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    simp [M, Btop, hcolsOrd_sigma j]
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  exact ⟨colsOrd, hcolsOrd_strict, lt_of_le_of_ne hminor_nonneg (Ne.symm hM_ne)⟩



private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_four_five
    {B : Matrix (Fin 4) (Fin 5) Real} {x : Fin 5 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 4 => ∑ j : Fin 5, B i j * x j)) :
      exists cols : Fin 4 -> Fin 5,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  by_contra hnone
  have hdet_zero_cols :
      forall cols : Fin 4 -> Fin 5, Function.Injective cols ->
        (Matrix.of fun i j => B i (cols j)).det = 0 := by
    intro cols hcols
    by_contra hdet
    exact hnone ⟨cols, hcols, hdet⟩
  let u : Fin 4 -> Real := fun i => ∑ j : Fin 5, B i j * x j
  rcases exists_positive_ordered_three_minor_first_three_rows_fin_four_five
      hTP hAlt with ⟨cols3, hcols3_strict, hdet3_pos⟩
  let d : Fin 4 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) cols3).det
  have hminor_nonneg : forall p : Fin 4, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 3 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    exact hTP 3 (Fin.succAbove p) cols3 hrows hcols3_strict
  have hd3_pos : 0 < d (3 : Fin 4) := by
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (3 : Fin 4)) cols3 =
          Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols3 j) := by
      ext i j
      fin_cases i <;> rfl
    simpa [d, hmatrix_eq] using hdet3_pos
  let S : Finset (Fin 5) := Finset.image cols3 Finset.univ
  have hcols3_inj : Function.Injective cols3 := by
    intro a b h
    apply hcols3_strict.injective
    exact congrArg Fin.val h
  have hidentity_cols :
      forall t : Fin 5,
        (∑ p : Fin 4, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    let A : Matrix (Fin 4) (Fin 4) Real := fun i j =>
      if hj : j.val < 3 then B i (cols3 ⟨j.val, hj⟩) else B i t
    have hdetA_zero : A.det = 0 := by
      by_cases htS : t ∈ S
      · rcases Finset.mem_image.mp htS with ⟨j0, _hj0mem, hj0⟩
        have hcol_eq : forall i : Fin 4, A i (Fin.castSucc j0) = A i (3 : Fin 4) := by
          intro i
          simp [A, Fin.castSucc, hj0]
        have hne : (Fin.castSucc j0 : Fin 4) ≠ (3 : Fin 4) := by
          intro h
          have hv := congrArg Fin.val h
          simp [Fin.castSucc] at hv
          have hj0lt : j0.val < 3 := j0.isLt
          omega
        exact Matrix.det_zero_of_column_eq hne hcol_eq
      · let cols4 : Fin 4 -> Fin 5 := fun j =>
          if hj : j.val < 3 then cols3 ⟨j.val, hj⟩ else t
        have h01 : cols3 0 ≠ cols3 1 := by
          intro h
          have hidx : (0 : Fin 3) = 1 := hcols3_inj h
          norm_num at hidx
        have h02 : cols3 0 ≠ cols3 2 := by
          intro h
          have hidx : (0 : Fin 3) = 2 := hcols3_inj h
          have hval := congrArg Fin.val hidx
          norm_num at hval
        have h12 : cols3 1 ≠ cols3 2 := by
          intro h
          have hidx : (1 : Fin 3) = 2 := hcols3_inj h
          have hval := congrArg Fin.val hidx
          norm_num at hval
        have h0t : cols3 0 ≠ t := by
          intro h
          exact htS (Finset.mem_image.mpr ⟨(0 : Fin 3), Finset.mem_univ _, h⟩)
        have h1t : cols3 1 ≠ t := by
          intro h
          exact htS (Finset.mem_image.mpr ⟨(1 : Fin 3), Finset.mem_univ _, h⟩)
        have h2t : cols3 2 ≠ t := by
          intro h
          exact htS (Finset.mem_image.mpr ⟨(2 : Fin 3), Finset.mem_univ _, h⟩)
        have hcols4 : Function.Injective cols4 := by
          intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp [cols4, h01, h02, h12, h01.symm, h02.symm, h12.symm,
              h0t, h1t, h2t, h0t.symm, h1t.symm, h2t.symm] at hij ⊢
        have hdet0 := hdet_zero_cols cols4 hcols4
        have hA_eq : A = Matrix.of fun i j => B i (cols4 j) := by
          ext i j
          by_cases hj : j.val < 3 <;> simp [A, cols4, hj]
        rw [hA_eq]
        exact hdet0
    have hdet_exp := Matrix.det_succ_column A (3 : Fin 4)
    rw [hdet_exp] at hdetA_zero
    have hterm_eq : forall p : Fin 4,
        (-1 : Real) ^ p.val * d p * B p t =
          - ((-1 : Real) ^ ((p : Nat) + ((3 : Fin 4) : Nat)) *
              A p (3 : Fin 4) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (3 : Fin 4))).det) := by
      intro p
      have hA3 : A p (3 : Fin 4) = B p t := by
        simp [A]
      have hsub :
          A.submatrix (Fin.succAbove p) (Fin.succAbove (3 : Fin 4)) =
            B.submatrix (Fin.succAbove p) cols3 := by
        ext i j
        fin_cases j <;> simp [A, Fin.succAbove]
      rw [hA3, hsub]
      have hsign :
          (-1 : Real) ^ ((p : Nat) + ((3 : Fin 4) : Nat)) =
            -((-1 : Real) ^ p.val) := by
        rw [pow_add]
        norm_num
      rw [hsign]
      simp [d]
      ring
    calc
      (∑ p : Fin 4, (-1 : Real) ^ p.val * d p * B p t)
          =
        ∑ p : Fin 4,
          - ((-1 : Real) ^ ((p : Nat) + ((3 : Fin 4) : Nat)) *
              A p (3 : Fin 4) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (3 : Fin 4))).det) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        exact hterm_eq p
      _ = 0 := by
        rw [Finset.sum_neg_distrib, hdetA_zero, neg_zero]
  have hidentity : (∑ p : Fin 4, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 4, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 4, ∑ j : Fin 5,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin 5, (∑ p : Fin 4,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 4, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_three :
      0 < r * (((-1 : Real) ^ (3 : Fin 4).val * d (3 : Fin 4)) * u (3 : Fin 4)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (3 : Nat)) * u (3 : Fin 4)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (3 : Fin 4))
    have heq :
        r * (((-1 : Real) ^ (3 : Fin 4).val * d (3 : Fin 4)) * u (3 : Fin 4)) =
          (u 0 * (((-1 : Real) ^ (3 : Nat)) * u (3 : Fin 4))) * d (3 : Fin 4) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd3_pos
  have hsum_pos :
      0 < ∑ p : Fin 4, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 4)))
        (f := fun p : Fin 4 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (3 : Fin 4))
    exact lt_of_lt_of_le hcommon_pos_three hle
  have hsum_rewrite :
      (∑ p : Fin 4, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 4, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem exists_positive_ordered_three_minor_first_three_rows_fin_four
    {m : Nat} {B : Matrix (Fin 4) (Fin m) Real} {x : Fin m -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 4 => ∑ j : Fin m, B i j * x j)) :
    exists cols : Fin 3 -> Fin m,
      StrictMono (fun j => (cols j).val) /\
        0 < (Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols j)).det := by
  classical
  let Btop : Matrix (Fin 3) (Fin m) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 3 => ∑ j : Fin m, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 4 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_three_cols
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin m) := Finset.image cols Finset.univ
  have hS_card : S.card = 3 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 3))) hcols
  let colsOrd : Fin 3 -> Fin m := fun j => S.orderEmbOfFin hS_card j
  have hcolsOrd_strict : StrictMono (fun j => (colsOrd j).val) := by
    intro a b hab
    exact (S.orderEmbOfFin hS_card).strictMono hab
  have hminor_nonneg :
      0 <= (Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)).det := by
    have hrows : StrictMono (fun i : Fin 3 => (⟨i.val, by omega⟩ : Fin 4).val) := by
      intro i j hij
      exact hij
    exact hTP 3 (fun i : Fin 3 => ⟨i.val, by omega⟩) colsOrd hrows hcolsOrd_strict
  have hcols_ne_ord :
      forall j : Fin 3, cols j ∈ S := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  let colsSub : Fin 3 -> S := fun j => ⟨cols j, hcols_ne_ord j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hS_card]⟩
  let colsEquiv : Fin 3 ≃ S := Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 3) := colsEquiv.trans (S.orderIsoOfFin hS_card).symm
  have hcolsOrd_sigma : forall j : Fin 3, colsOrd (sigma j) = cols j := by
    intro j
    have hsub : S.orderIsoOfFin hS_card (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 3) (Fin 3) Real :=
    Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    simp [M, Btop, hcolsOrd_sigma j]
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  exact ⟨colsOrd, hcolsOrd_strict, lt_of_le_of_ne hminor_nonneg (Ne.symm hM_ne)⟩



private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_four_cols
    {m : Nat} {B : Matrix (Fin 4) (Fin m) Real} {x : Fin m -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 4 => ∑ j : Fin m, B i j * x j)) :
      exists cols : Fin 4 -> Fin m,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  by_contra hnone
  have hdet_zero_cols :
      forall cols : Fin 4 -> Fin m, Function.Injective cols ->
        (Matrix.of fun i j => B i (cols j)).det = 0 := by
    intro cols hcols
    by_contra hdet
    exact hnone ⟨cols, hcols, hdet⟩
  let u : Fin 4 -> Real := fun i => ∑ j : Fin m, B i j * x j
  rcases exists_positive_ordered_three_minor_first_three_rows_fin_four
      hTP hAlt with ⟨cols3, hcols3_strict, hdet3_pos⟩
  let d : Fin 4 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) cols3).det
  have hminor_nonneg : forall p : Fin 4, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 3 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    exact hTP 3 (Fin.succAbove p) cols3 hrows hcols3_strict
  have hd3_pos : 0 < d (3 : Fin 4) := by
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (3 : Fin 4)) cols3 =
          Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols3 j) := by
      ext i j
      fin_cases i <;> rfl
    simpa [d, hmatrix_eq] using hdet3_pos
  let S : Finset (Fin m) := Finset.image cols3 Finset.univ
  have hcols3_inj : Function.Injective cols3 := by
    intro a b h
    apply hcols3_strict.injective
    exact congrArg Fin.val h
  have hidentity_cols :
      forall t : Fin m,
        (∑ p : Fin 4, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    let A : Matrix (Fin 4) (Fin 4) Real := fun i j =>
      if hj : j.val < 3 then B i (cols3 ⟨j.val, hj⟩) else B i t
    have hdetA_zero : A.det = 0 := by
      by_cases htS : t ∈ S
      · rcases Finset.mem_image.mp htS with ⟨j0, _hj0mem, hj0⟩
        have hcol_eq : forall i : Fin 4, A i (Fin.castSucc j0) = A i (3 : Fin 4) := by
          intro i
          simp [A, Fin.castSucc, hj0]
        have hne : (Fin.castSucc j0 : Fin 4) ≠ (3 : Fin 4) := by
          intro h
          have hv := congrArg Fin.val h
          simp [Fin.castSucc] at hv
          have hj0lt : j0.val < 3 := j0.isLt
          omega
        exact Matrix.det_zero_of_column_eq hne hcol_eq
      · let cols4 : Fin 4 -> Fin m := fun j =>
          if hj : j.val < 3 then cols3 ⟨j.val, hj⟩ else t
        have hcols4 : Function.Injective cols4 := by
          intro i j hij
          by_cases hi : i.val < 3
          · by_cases hj : j.val < 3
            · have hcols_eq : cols3 ⟨i.val, hi⟩ = cols3 ⟨j.val, hj⟩ := by
                simpa [cols4, hi, hj] using hij
              have hidx : (⟨i.val, hi⟩ : Fin 3) = ⟨j.val, hj⟩ :=
                hcols3_inj hcols_eq
              exact Fin.ext (by simpa using congrArg Fin.val hidx)
            · have hit : cols3 ⟨i.val, hi⟩ = t := by
                simpa [cols4, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨i.val, hi⟩, Finset.mem_univ _, hit⟩))
          · by_cases hj : j.val < 3
            · have htj : t = cols3 ⟨j.val, hj⟩ := by
                simpa [cols4, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨j.val, hj⟩, Finset.mem_univ _, htj.symm⟩))
            · exact Fin.ext (by omega)
        have hdet0 := hdet_zero_cols cols4 hcols4
        have hA_eq : A = Matrix.of fun i j => B i (cols4 j) := by
          ext i j
          by_cases hj : j.val < 3 <;> simp [A, cols4, hj]
        rw [hA_eq]
        exact hdet0
    have hdet_exp := Matrix.det_succ_column A (3 : Fin 4)
    rw [hdet_exp] at hdetA_zero
    have hterm_eq : forall p : Fin 4,
        (-1 : Real) ^ p.val * d p * B p t =
          - ((-1 : Real) ^ ((p : Nat) + ((3 : Fin 4) : Nat)) *
              A p (3 : Fin 4) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (3 : Fin 4))).det) := by
      intro p
      have hA3 : A p (3 : Fin 4) = B p t := by
        simp [A]
      have hsub :
          A.submatrix (Fin.succAbove p) (Fin.succAbove (3 : Fin 4)) =
            B.submatrix (Fin.succAbove p) cols3 := by
        ext i j
        fin_cases j <;> simp [A, Fin.succAbove]
      rw [hA3, hsub]
      have hsign :
          (-1 : Real) ^ ((p : Nat) + ((3 : Fin 4) : Nat)) =
            -((-1 : Real) ^ p.val) := by
        rw [pow_add]
        norm_num
      rw [hsign]
      simp [d]
      ring
    calc
      (∑ p : Fin 4, (-1 : Real) ^ p.val * d p * B p t)
          =
        ∑ p : Fin 4,
          - ((-1 : Real) ^ ((p : Nat) + ((3 : Fin 4) : Nat)) *
              A p (3 : Fin 4) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (3 : Fin 4))).det) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        exact hterm_eq p
      _ = 0 := by
        rw [Finset.sum_neg_distrib, hdetA_zero, neg_zero]
  have hidentity : (∑ p : Fin 4, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 4, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 4, ∑ j : Fin m,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin m, (∑ p : Fin 4,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 4, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_three :
      0 < r * (((-1 : Real) ^ (3 : Fin 4).val * d (3 : Fin 4)) * u (3 : Fin 4)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (3 : Nat)) * u (3 : Fin 4)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (3 : Fin 4))
    have heq :
        r * (((-1 : Real) ^ (3 : Fin 4).val * d (3 : Fin 4)) * u (3 : Fin 4)) =
          (u 0 * (((-1 : Real) ^ (3 : Nat)) * u (3 : Fin 4))) * d (3 : Fin 4) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd3_pos
  have hsum_pos :
      0 < ∑ p : Fin 4, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 4)))
        (f := fun p : Fin 4 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (3 : Fin 4))
    exact lt_of_lt_of_le hcommon_pos_three hle
  have hsum_rewrite :
      (∑ p : Fin 4, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 4, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem exists_positive_ordered_four_minor_first_four_rows_fin_five_six
    {B : Matrix (Fin 5) (Fin 6) Real} {x : Fin 6 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 5 => ∑ j : Fin 6, B i j * x j)) :
    exists cols : Fin 4 -> Fin 6,
      StrictMono (fun j => (cols j).val) /\
        0 < (Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols j)).det := by
  classical
  let Btop : Matrix (Fin 4) (Fin 6) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 4 => ∑ j : Fin 6, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 5 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_four_cols
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin 6) := Finset.image cols Finset.univ
  have hS_card : S.card = 4 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 4))) hcols
  let colsOrd : Fin 4 -> Fin 6 := fun j => S.orderEmbOfFin hS_card j
  have hcolsOrd_strict : StrictMono (fun j => (colsOrd j).val) := by
    intro a b hab
    exact (S.orderEmbOfFin hS_card).strictMono hab
  have hminor_nonneg :
      0 <= (Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)).det := by
    have hrows : StrictMono (fun i : Fin 4 => (⟨i.val, by omega⟩ : Fin 5).val) := by
      intro i j hij
      exact hij
    exact hTP 4 (fun i : Fin 4 => ⟨i.val, by omega⟩) colsOrd hrows hcolsOrd_strict
  have hcols_ne_ord :
      forall j : Fin 4, cols j ∈ S := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  let colsSub : Fin 4 -> S := fun j => ⟨cols j, hcols_ne_ord j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hS_card]⟩
  let colsEquiv : Fin 4 ≃ S := Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 4) := colsEquiv.trans (S.orderIsoOfFin hS_card).symm
  have hcolsOrd_sigma : forall j : Fin 4, colsOrd (sigma j) = cols j := by
    intro j
    have hsub : S.orderIsoOfFin hS_card (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 4) (Fin 4) Real :=
    Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    simp [M, Btop, hcolsOrd_sigma j]
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  exact ⟨colsOrd, hcolsOrd_strict, lt_of_le_of_ne hminor_nonneg (Ne.symm hM_ne)⟩



private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_five_six
    {B : Matrix (Fin 5) (Fin 6) Real} {x : Fin 6 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 5 => ∑ j : Fin 6, B i j * x j)) :
      exists cols : Fin 5 -> Fin 6,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  by_contra hnone
  have hdet_zero_cols :
      forall cols : Fin 5 -> Fin 6, Function.Injective cols ->
        (Matrix.of fun i j => B i (cols j)).det = 0 := by
    intro cols hcols
    by_contra hdet
    exact hnone ⟨cols, hcols, hdet⟩
  let u : Fin 5 -> Real := fun i => ∑ j : Fin 6, B i j * x j
  rcases exists_positive_ordered_four_minor_first_four_rows_fin_five_six
      hTP hAlt with ⟨cols4, hcols4_strict, hdet4_pos⟩
  let d : Fin 5 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) cols4).det
  have hminor_nonneg : forall p : Fin 5, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 4 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    exact hTP 4 (Fin.succAbove p) cols4 hrows hcols4_strict
  have hd4_pos : 0 < d (4 : Fin 5) := by
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (4 : Fin 5)) cols4 =
          Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols4 j) := by
      ext i j
      fin_cases i <;> rfl
    simpa [d, hmatrix_eq] using hdet4_pos
  let S : Finset (Fin 6) := Finset.image cols4 Finset.univ
  have hcols4_inj : Function.Injective cols4 := by
    intro a b h
    apply hcols4_strict.injective
    exact congrArg Fin.val h
  have hidentity_cols :
      forall t : Fin 6,
        (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    let A : Matrix (Fin 5) (Fin 5) Real := fun i j =>
      if hj : j.val < 4 then B i (cols4 ⟨j.val, hj⟩) else B i t
    have hdetA_zero : A.det = 0 := by
      by_cases htS : t ∈ S
      · rcases Finset.mem_image.mp htS with ⟨j0, _hj0mem, hj0⟩
        have hcol_eq : forall i : Fin 5, A i (Fin.castSucc j0) = A i (4 : Fin 5) := by
          intro i
          simp [A, Fin.castSucc, hj0]
        have hne : (Fin.castSucc j0 : Fin 5) ≠ (4 : Fin 5) := by
          intro h
          have hv := congrArg Fin.val h
          simp [Fin.castSucc] at hv
          have hj0lt : j0.val < 4 := j0.isLt
          omega
        exact Matrix.det_zero_of_column_eq hne hcol_eq
      · let cols5 : Fin 5 -> Fin 6 := fun j =>
          if hj : j.val < 4 then cols4 ⟨j.val, hj⟩ else t
        have hcols5 : Function.Injective cols5 := by
          intro i j hij
          by_cases hi : i.val < 4
          · by_cases hj : j.val < 4
            · have hcols_eq : cols4 ⟨i.val, hi⟩ = cols4 ⟨j.val, hj⟩ := by
                simpa [cols5, hi, hj] using hij
              have hidx : (⟨i.val, hi⟩ : Fin 4) = ⟨j.val, hj⟩ :=
                hcols4_inj hcols_eq
              exact Fin.ext (by simpa using congrArg Fin.val hidx)
            · have hit : cols4 ⟨i.val, hi⟩ = t := by
                simpa [cols5, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨i.val, hi⟩, Finset.mem_univ _, hit⟩))
          · by_cases hj : j.val < 4
            · have htj : t = cols4 ⟨j.val, hj⟩ := by
                simpa [cols5, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨j.val, hj⟩, Finset.mem_univ _, htj.symm⟩))
            · exact Fin.ext (by omega)
        have hdet0 := hdet_zero_cols cols5 hcols5
        have hA_eq : A = Matrix.of fun i j => B i (cols5 j) := by
          ext i j
          by_cases hj : j.val < 4 <;> simp [A, cols5, hj]
        rw [hA_eq]
        exact hdet0
    have hdet_exp := Matrix.det_succ_column A (4 : Fin 5)
    rw [hdet_exp] at hdetA_zero
    have hterm_eq : forall p : Fin 5,
        (-1 : Real) ^ p.val * d p * B p t =
          (-1 : Real) ^ ((p : Nat) + ((4 : Fin 5) : Nat)) *
              A p (4 : Fin 5) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (4 : Fin 5))).det := by
      intro p
      have hA4 : A p (4 : Fin 5) = B p t := by
        simp [A]
      have hsub :
          A.submatrix (Fin.succAbove p) (Fin.succAbove (4 : Fin 5)) =
            B.submatrix (Fin.succAbove p) cols4 := by
        ext i j
        fin_cases j <;> simp [A, Fin.succAbove]
      rw [hA4, hsub]
      have hsign :
          (-1 : Real) ^ ((p : Nat) + ((4 : Fin 5) : Nat)) =
            (-1 : Real) ^ p.val := by
        rw [pow_add]
        norm_num
      rw [hsign]
      simp [d]
      ring
    calc
      (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * B p t)
          =
        ∑ p : Fin 5,
          (-1 : Real) ^ ((p : Nat) + ((4 : Fin 5) : Nat)) *
              A p (4 : Fin 5) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (4 : Fin 5))).det := by
        refine Finset.sum_congr rfl ?_
        intro p _
        exact hterm_eq p
      _ = 0 := hdetA_zero
  have hidentity : (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 5, ∑ j : Fin 6,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin 6, (∑ p : Fin 5,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 5, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_four :
      0 < r * (((-1 : Real) ^ (4 : Fin 5).val * d (4 : Fin 5)) * u (4 : Fin 5)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (4 : Nat)) * u (4 : Fin 5)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (4 : Fin 5))
    have heq :
        r * (((-1 : Real) ^ (4 : Fin 5).val * d (4 : Fin 5)) * u (4 : Fin 5)) =
          (u 0 * (((-1 : Real) ^ (4 : Nat)) * u (4 : Fin 5))) * d (4 : Fin 5) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd4_pos
  have hsum_pos :
      0 < ∑ p : Fin 5, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 5)))
        (f := fun p : Fin 5 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (4 : Fin 5))
    exact lt_of_lt_of_le hcommon_pos_four hle
  have hsum_rewrite :
      (∑ p : Fin 5, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem exists_positive_ordered_four_minor_first_four_rows_fin_five_cols
    {m : Nat} {B : Matrix (Fin 5) (Fin m) Real} {x : Fin m -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 5 => ∑ j : Fin m, B i j * x j)) :
    exists cols : Fin 4 -> Fin m,
      StrictMono (fun j => (cols j).val) /\
        0 < (Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols j)).det := by
  classical
  let Btop : Matrix (Fin 4) (Fin m) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 4 => ∑ j : Fin m, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 5 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_four_cols
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin m) := Finset.image cols Finset.univ
  have hS_card : S.card = 4 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 4))) hcols
  let colsOrd : Fin 4 -> Fin m := fun j => S.orderEmbOfFin hS_card j
  have hcolsOrd_strict : StrictMono (fun j => (colsOrd j).val) := by
    intro a b hab
    exact (S.orderEmbOfFin hS_card).strictMono hab
  have hminor_nonneg :
      0 <= (Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)).det := by
    have hrows : StrictMono (fun i : Fin 4 => (⟨i.val, by omega⟩ : Fin 5).val) := by
      intro i j hij
      exact hij
    exact hTP 4 (fun i : Fin 4 => ⟨i.val, by omega⟩) colsOrd hrows hcolsOrd_strict
  have hcols_ne_ord :
      forall j : Fin 4, cols j ∈ S := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  let colsSub : Fin 4 -> S := fun j => ⟨cols j, hcols_ne_ord j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hS_card]⟩
  let colsEquiv : Fin 4 ≃ S := Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 4) := colsEquiv.trans (S.orderIsoOfFin hS_card).symm
  have hcolsOrd_sigma : forall j : Fin 4, colsOrd (sigma j) = cols j := by
    intro j
    have hsub : S.orderIsoOfFin hS_card (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 4) (Fin 4) Real :=
    Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    simp [M, Btop, hcolsOrd_sigma j]
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  exact ⟨colsOrd, hcolsOrd_strict, lt_of_le_of_ne hminor_nonneg (Ne.symm hM_ne)⟩



private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_five_cols
    {m : Nat} {B : Matrix (Fin 5) (Fin m) Real} {x : Fin m -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 5 => ∑ j : Fin m, B i j * x j)) :
      exists cols : Fin 5 -> Fin m,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  by_contra hnone
  have hdet_zero_cols :
      forall cols : Fin 5 -> Fin m, Function.Injective cols ->
        (Matrix.of fun i j => B i (cols j)).det = 0 := by
    intro cols hcols
    by_contra hdet
    exact hnone ⟨cols, hcols, hdet⟩
  let u : Fin 5 -> Real := fun i => ∑ j : Fin m, B i j * x j
  rcases exists_positive_ordered_four_minor_first_four_rows_fin_five_cols
      hTP hAlt with ⟨cols4, hcols4_strict, hdet4_pos⟩
  let d : Fin 5 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) cols4).det
  have hminor_nonneg : forall p : Fin 5, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 4 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    exact hTP 4 (Fin.succAbove p) cols4 hrows hcols4_strict
  have hd4_pos : 0 < d (4 : Fin 5) := by
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (4 : Fin 5)) cols4 =
          Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols4 j) := by
      ext i j
      fin_cases i <;> rfl
    simpa [d, hmatrix_eq] using hdet4_pos
  let S : Finset (Fin m) := Finset.image cols4 Finset.univ
  have hcols4_inj : Function.Injective cols4 := by
    intro a b h
    apply hcols4_strict.injective
    exact congrArg Fin.val h
  have hidentity_cols :
      forall t : Fin m,
        (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    let A : Matrix (Fin 5) (Fin 5) Real := fun i j =>
      if hj : j.val < 4 then B i (cols4 ⟨j.val, hj⟩) else B i t
    have hdetA_zero : A.det = 0 := by
      by_cases htS : t ∈ S
      · rcases Finset.mem_image.mp htS with ⟨j0, _hj0mem, hj0⟩
        have hcol_eq : forall i : Fin 5, A i (Fin.castSucc j0) = A i (4 : Fin 5) := by
          intro i
          simp [A, Fin.castSucc, hj0]
        have hne : (Fin.castSucc j0 : Fin 5) ≠ (4 : Fin 5) := by
          intro h
          have hv := congrArg Fin.val h
          simp [Fin.castSucc] at hv
          have hj0lt : j0.val < 4 := j0.isLt
          omega
        exact Matrix.det_zero_of_column_eq hne hcol_eq
      · let cols5 : Fin 5 -> Fin m := fun j =>
          if hj : j.val < 4 then cols4 ⟨j.val, hj⟩ else t
        have hcols5 : Function.Injective cols5 := by
          intro i j hij
          by_cases hi : i.val < 4
          · by_cases hj : j.val < 4
            · have hcols_eq : cols4 ⟨i.val, hi⟩ = cols4 ⟨j.val, hj⟩ := by
                simpa [cols5, hi, hj] using hij
              have hidx : (⟨i.val, hi⟩ : Fin 4) = ⟨j.val, hj⟩ :=
                hcols4_inj hcols_eq
              exact Fin.ext (by simpa using congrArg Fin.val hidx)
            · have hit : cols4 ⟨i.val, hi⟩ = t := by
                simpa [cols5, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨i.val, hi⟩, Finset.mem_univ _, hit⟩))
          · by_cases hj : j.val < 4
            · have htj : t = cols4 ⟨j.val, hj⟩ := by
                simpa [cols5, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨j.val, hj⟩, Finset.mem_univ _, htj.symm⟩))
            · exact Fin.ext (by omega)
        have hdet0 := hdet_zero_cols cols5 hcols5
        have hA_eq : A = Matrix.of fun i j => B i (cols5 j) := by
          ext i j
          by_cases hj : j.val < 4 <;> simp [A, cols5, hj]
        rw [hA_eq]
        exact hdet0
    have hdet_exp := Matrix.det_succ_column A (4 : Fin 5)
    rw [hdet_exp] at hdetA_zero
    have hterm_eq : forall p : Fin 5,
        (-1 : Real) ^ p.val * d p * B p t =
          (-1 : Real) ^ ((p : Nat) + ((4 : Fin 5) : Nat)) *
              A p (4 : Fin 5) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (4 : Fin 5))).det := by
      intro p
      have hA4 : A p (4 : Fin 5) = B p t := by
        simp [A]
      have hsub :
          A.submatrix (Fin.succAbove p) (Fin.succAbove (4 : Fin 5)) =
            B.submatrix (Fin.succAbove p) cols4 := by
        ext i j
        fin_cases j <;> simp [A, Fin.succAbove]
      rw [hA4, hsub]
      have hsign :
          (-1 : Real) ^ ((p : Nat) + ((4 : Fin 5) : Nat)) =
            (-1 : Real) ^ p.val := by
        rw [pow_add]
        norm_num
      rw [hsign]
      simp [d]
      ring
    calc
      (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * B p t)
          =
        ∑ p : Fin 5,
          (-1 : Real) ^ ((p : Nat) + ((4 : Fin 5) : Nat)) *
              A p (4 : Fin 5) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (4 : Fin 5))).det := by
        refine Finset.sum_congr rfl ?_
        intro p _
        exact hterm_eq p
      _ = 0 := hdetA_zero
  have hidentity : (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 5, ∑ j : Fin m,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin m, (∑ p : Fin 5,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 5, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_four :
      0 < r * (((-1 : Real) ^ (4 : Fin 5).val * d (4 : Fin 5)) * u (4 : Fin 5)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (4 : Nat)) * u (4 : Fin 5)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (4 : Fin 5))
    have heq :
        r * (((-1 : Real) ^ (4 : Fin 5).val * d (4 : Fin 5)) * u (4 : Fin 5)) =
          (u 0 * (((-1 : Real) ^ (4 : Nat)) * u (4 : Fin 5))) * d (4 : Fin 5) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd4_pos
  have hsum_pos :
      0 < ∑ p : Fin 5, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 5)))
        (f := fun p : Fin 5 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (4 : Fin 5))
    exact lt_of_lt_of_le hcommon_pos_four hle
  have hsum_rewrite :
      (∑ p : Fin 5, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem exists_positive_ordered_five_minor_first_five_rows_fin_six_cols
    {m : Nat} {B : Matrix (Fin 6) (Fin m) Real} {x : Fin m -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 6 => ∑ j : Fin m, B i j * x j)) :
    exists cols : Fin 5 -> Fin m,
      StrictMono (fun j => (cols j).val) /\
        0 < (Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols j)).det := by
  classical
  let Btop : Matrix (Fin 5) (Fin m) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 5 => ∑ j : Fin m, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 6 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_five_cols
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin m) := Finset.image cols Finset.univ
  have hS_card : S.card = 5 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 5))) hcols
  let colsOrd : Fin 5 -> Fin m := fun j => S.orderEmbOfFin hS_card j
  have hcolsOrd_strict : StrictMono (fun j => (colsOrd j).val) := by
    intro a b hab
    exact (S.orderEmbOfFin hS_card).strictMono hab
  have hminor_nonneg :
      0 <= (Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)).det := by
    have hrows : StrictMono (fun i : Fin 5 => (⟨i.val, by omega⟩ : Fin 6).val) := by
      intro i j hij
      exact hij
    exact hTP 5 (fun i : Fin 5 => ⟨i.val, by omega⟩) colsOrd hrows hcolsOrd_strict
  have hcols_ne_ord :
      forall j : Fin 5, cols j ∈ S := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  let colsSub : Fin 5 -> S := fun j => ⟨cols j, hcols_ne_ord j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hS_card]⟩
  let colsEquiv : Fin 5 ≃ S := Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 5) := colsEquiv.trans (S.orderIsoOfFin hS_card).symm
  have hcolsOrd_sigma : forall j : Fin 5, colsOrd (sigma j) = cols j := by
    intro j
    have hsub : S.orderIsoOfFin hS_card (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 5) (Fin 5) Real :=
    Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    simp [M, Btop, hcolsOrd_sigma j]
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  exact ⟨colsOrd, hcolsOrd_strict, lt_of_le_of_ne hminor_nonneg (Ne.symm hM_ne)⟩



private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_six_cols
    {m : Nat} {B : Matrix (Fin 6) (Fin m) Real} {x : Fin m -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 6 => ∑ j : Fin m, B i j * x j)) :
      exists cols : Fin 6 -> Fin m,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  by_contra hnone
  have hdet_zero_cols :
      forall cols : Fin 6 -> Fin m, Function.Injective cols ->
        (Matrix.of fun i j => B i (cols j)).det = 0 := by
    intro cols hcols
    by_contra hdet
    exact hnone ⟨cols, hcols, hdet⟩
  let u : Fin 6 -> Real := fun i => ∑ j : Fin m, B i j * x j
  rcases exists_positive_ordered_five_minor_first_five_rows_fin_six_cols
      hTP hAlt with ⟨cols5, hcols5_strict, hdet5_pos⟩
  let d : Fin 6 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) cols5).det
  have hminor_nonneg : forall p : Fin 6, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 5 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    exact hTP 5 (Fin.succAbove p) cols5 hrows hcols5_strict
  have hd5_pos : 0 < d (5 : Fin 6) := by
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (5 : Fin 6)) cols5 =
          Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols5 j) := by
      ext i j
      fin_cases i <;> rfl
    simpa [d, hmatrix_eq] using hdet5_pos
  let S : Finset (Fin m) := Finset.image cols5 Finset.univ
  have hcols5_inj : Function.Injective cols5 := by
    intro a b h
    apply hcols5_strict.injective
    exact congrArg Fin.val h
  have hidentity_cols :
      forall t : Fin m,
        (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    let A : Matrix (Fin 6) (Fin 6) Real := fun i j =>
      if hj : j.val < 5 then B i (cols5 ⟨j.val, hj⟩) else B i t
    have hdetA_zero : A.det = 0 := by
      by_cases htS : t ∈ S
      · rcases Finset.mem_image.mp htS with ⟨j0, _hj0mem, hj0⟩
        have hcol_eq : forall i : Fin 6, A i (Fin.castSucc j0) = A i (5 : Fin 6) := by
          intro i
          simp [A, Fin.castSucc, hj0]
        have hne : (Fin.castSucc j0 : Fin 6) ≠ (5 : Fin 6) := by
          intro h
          have hv := congrArg Fin.val h
          simp [Fin.castSucc] at hv
          have hj0lt : j0.val < 5 := j0.isLt
          omega
        exact Matrix.det_zero_of_column_eq hne hcol_eq
      · let cols6 : Fin 6 -> Fin m := fun j =>
          if hj : j.val < 5 then cols5 ⟨j.val, hj⟩ else t
        have hcols6 : Function.Injective cols6 := by
          intro i j hij
          by_cases hi : i.val < 5
          · by_cases hj : j.val < 5
            · have hcols_eq : cols5 ⟨i.val, hi⟩ = cols5 ⟨j.val, hj⟩ := by
                simpa [cols6, hi, hj] using hij
              have hidx : (⟨i.val, hi⟩ : Fin 5) = ⟨j.val, hj⟩ :=
                hcols5_inj hcols_eq
              exact Fin.ext (by simpa using congrArg Fin.val hidx)
            · have hit : cols5 ⟨i.val, hi⟩ = t := by
                simpa [cols6, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨i.val, hi⟩, Finset.mem_univ _, hit⟩))
          · by_cases hj : j.val < 5
            · have htj : t = cols5 ⟨j.val, hj⟩ := by
                simpa [cols6, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨j.val, hj⟩, Finset.mem_univ _, htj.symm⟩))
            · exact Fin.ext (by omega)
        have hdet0 := hdet_zero_cols cols6 hcols6
        have hA_eq : A = Matrix.of fun i j => B i (cols6 j) := by
          ext i j
          by_cases hj : j.val < 5 <;> simp [A, cols6, hj]
        rw [hA_eq]
        exact hdet0
    have hdet_exp := Matrix.det_succ_column A (5 : Fin 6)
    rw [hdet_exp] at hdetA_zero
    have hterm_eq : forall p : Fin 6,
        (-1 : Real) ^ p.val * d p * B p t =
          - ((-1 : Real) ^ ((p : Nat) + ((5 : Fin 6) : Nat)) *
              A p (5 : Fin 6) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (5 : Fin 6))).det) := by
      intro p
      have hA5 : A p (5 : Fin 6) = B p t := by
        simp [A]
      have hsub :
          A.submatrix (Fin.succAbove p) (Fin.succAbove (5 : Fin 6)) =
            B.submatrix (Fin.succAbove p) cols5 := by
        ext i j
        fin_cases j <;> simp [A, Fin.succAbove]
      rw [hA5, hsub]
      have hsign :
          (-1 : Real) ^ ((p : Nat) + ((5 : Fin 6) : Nat)) =
            -((-1 : Real) ^ p.val) := by
        rw [pow_add]
        norm_num
      rw [hsign]
      simp [d]
      ring
    calc
      (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * B p t)
          =
        ∑ p : Fin 6,
          - ((-1 : Real) ^ ((p : Nat) + ((5 : Fin 6) : Nat)) *
              A p (5 : Fin 6) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (5 : Fin 6))).det) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        exact hterm_eq p
      _ = 0 := by
        rw [Finset.sum_neg_distrib, hdetA_zero, neg_zero]
  have hidentity : (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 6, ∑ j : Fin m,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin m, (∑ p : Fin 6,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 6, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_five :
      0 < r * (((-1 : Real) ^ (5 : Fin 6).val * d (5 : Fin 6)) * u (5 : Fin 6)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (5 : Nat)) * u (5 : Fin 6)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (5 : Fin 6))
    have heq :
        r * (((-1 : Real) ^ (5 : Fin 6).val * d (5 : Fin 6)) * u (5 : Fin 6)) =
          (u 0 * (((-1 : Real) ^ (5 : Nat)) * u (5 : Fin 6))) * d (5 : Fin 6) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd5_pos
  have hsum_pos :
      0 < ∑ p : Fin 6, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 6)))
        (f := fun p : Fin 6 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (5 : Fin 6))
    exact lt_of_lt_of_le hcommon_pos_five hle
  have hsum_rewrite :
      (∑ p : Fin 6, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem exists_nonzero_adjugate_col_five_of_alternating_image_fin_six
    {B : Matrix (Fin 6) (Fin 6) Real} {x : Fin 6 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 6 => ∑ j : Fin 6, B i j * x j)) :
    exists q : Fin 6, B.adjugate q 5 ≠ 0 := by
  classical
  let Btop : Matrix (Fin 5) (Fin 6) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 5 => ∑ j : Fin 6, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 6 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_five_six
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin 6) := Finset.image cols Finset.univ
  have hS_card : S.card = 5 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 5))) hcols
  have hS_lt_univ : S.card < (Finset.univ : Finset (Fin 6)).card := by
    simp [hS_card]
  rcases Finset.exists_mem_notMem_of_card_lt_card hS_lt_univ with ⟨q, _hqmem, hqnot⟩
  refine ⟨q, ?_⟩
  have hcols_ne_q : forall j : Fin 5, cols j ≠ q := by
    intro j hj
    exact hqnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩)
  let colsSub : Fin 5 -> {j : Fin 6 // j ≠ q} :=
    fun j => ⟨cols j, hcols_ne_q j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcard_sub : Fintype.card {j : Fin 6 // j ≠ q} = 5 := by
    simp
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hcard_sub]⟩
  let colsEquiv : Fin 5 ≃ {j : Fin 6 // j ≠ q} :=
    Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 5) := colsEquiv.trans (finSuccAboveEquiv q).symm
  have hsucc_sigma : forall j : Fin 5, q.succAbove (sigma j) = cols j := by
    intro j
    have hsub : finSuccAboveEquiv q (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 5) (Fin 5) Real :=
    B.submatrix (Fin.succAbove (5 : Fin 6)) (Fin.succAbove q)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    fin_cases i
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 0 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 1 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 2 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 3 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 4 c) (hsucc_sigma j)
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  have hadj_formula :
      B.adjugate q (5 : Fin 6) =
        (-1 : Real) ^ ((5 : Fin 6).val + q.val) * M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [hadj_formula]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hM_ne



private theorem det_ne_zero_of_totallyPositive_of_alternating_image_fin_six
    {B : Matrix (Fin 6) (Fin 6) Real} {x : Fin 6 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 6 => ∑ j : Fin 6, B i j * x j)) :
    B.det ≠ 0 := by
  classical
  intro hdet_zero
  let u : Fin 6 -> Real := fun i => ∑ j : Fin 6, B i j * x j
  rcases exists_nonzero_adjugate_col_five_of_alternating_image_fin_six
      hTP hAlt with ⟨q, hq_ne⟩
  let r : Real := (-1 : Real) ^ q.val * u 0
  have hchecker :
      forall i : Fin 6,
        0 <= ((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i) := by
    intro i
    exact adjugate_checkerboard_nonneg_of_totallyPositive hTP i q
  have hcommon_nonneg :
      forall i : Fin 6, 0 <= r * (B.adjugate q i * u i) := by
    intro i
    have hsign : 0 < u 0 * (((-1 : Real) ^ i.val) * u i) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := i)
    have heq : r * (B.adjugate q i * u i) =
        (u 0 * (((-1 : Real) ^ i.val) * u i)) *
          (((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real i.val with hi | hi <;>
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
      simp [hi, hq, mul_assoc, mul_comm]
    rw [heq]
    exact mul_nonneg hsign.le (hchecker i)
  have hcommon_pos_five : 0 < r * (B.adjugate q 5 * u 5) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (5 : Nat)) * u 5) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (5 : Fin 6))
    have hchecker_five_nonneg :
        0 <= ((-1 : Real) ^ ((5 : Fin 6).val + q.val)) * (B.adjugate q 5) :=
      hchecker 5
    have hchecker_five_ne :
        ((-1 : Real) ^ ((5 : Fin 6).val + q.val)) * (B.adjugate q 5) ≠ 0 := by
      exact mul_ne_zero
        (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hq_ne
    have hchecker_five_pos :
        0 < ((-1 : Real) ^ ((5 : Fin 6).val + q.val)) * (B.adjugate q 5) :=
      lt_of_le_of_ne hchecker_five_nonneg (Ne.symm hchecker_five_ne)
    have heq : r * (B.adjugate q 5 * u 5) =
        (u 0 * (((-1 : Real) ^ (5 : Nat)) * u 5)) *
          (((-1 : Real) ^ ((5 : Fin 6).val + q.val)) * (B.adjugate q 5)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
        simp [hq] <;> ring
    rw [heq]
    exact mul_pos hsign hchecker_five_pos
  have hsum_pos :
      0 < ∑ i : Fin 6, r * (B.adjugate q i * u i) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 6)))
        (f := fun i : Fin 6 => r * (B.adjugate q i * u i))
        (fun i _ => hcommon_nonneg i)
        (Finset.mem_univ (5 : Fin 6))
    exact lt_of_lt_of_le hcommon_pos_five hle
  have hu : u = B *ᵥ x := by
    ext i
    simp [u, Matrix.mulVec, dotProduct]
  have hvec : B.adjugate *ᵥ u = 0 := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet_zero]
    ext i
    simp
  have hsum_zero : (∑ i : Fin 6, B.adjugate q i * u i) = 0 := by
    have hqvec := congrFun hvec q
    simpa [Matrix.mulVec, dotProduct] using hqvec
  have hsum_rewrite :
      (∑ i : Fin 6, r * (B.adjugate q i * u i)) =
        r * (∑ i : Fin 6, B.adjugate q i * u i) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hsum_zero, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos


private theorem linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_six
    {B : Matrix (Fin 6) (Fin 6) Real} {x : Fin 6 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 6 => ∑ j : Fin 6, B i j * x j)) :
    LinearIndependent Real (fun i : Fin 6 => fun j : Fin 6 => B i j) := by
  have hdet := det_ne_zero_of_totallyPositive_of_alternating_image_fin_six hTP hAlt
  have hunit : IsUnit B := Matrix.isUnit_iff_isUnit_det B |>.mpr (IsUnit.mk0 B.det hdet)
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr hunit



private theorem exists_nonzero_adjugate_col_four_of_alternating_image_fin_five
    {B : Matrix (Fin 5) (Fin 5) Real} {x : Fin 5 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 5 => ∑ j : Fin 5, B i j * x j)) :
    exists q : Fin 5, B.adjugate q 4 ≠ 0 := by
  classical
  let Btop : Matrix (Fin 4) (Fin 5) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 4 => ∑ j : Fin 5, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 5 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_four_five
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin 5) := Finset.image cols Finset.univ
  have hS_card : S.card = 4 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 4))) hcols
  have hS_lt_univ : S.card < (Finset.univ : Finset (Fin 5)).card := by
    simp [hS_card]
  rcases Finset.exists_mem_notMem_of_card_lt_card hS_lt_univ with ⟨q, _hqmem, hqnot⟩
  refine ⟨q, ?_⟩
  have hcols_ne_q : forall j : Fin 4, cols j ≠ q := by
    intro j hj
    exact hqnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩)
  let colsSub : Fin 4 -> {j : Fin 5 // j ≠ q} :=
    fun j => ⟨cols j, hcols_ne_q j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcard_sub : Fintype.card {j : Fin 5 // j ≠ q} = 4 := by
    simp
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hcard_sub]⟩
  let colsEquiv : Fin 4 ≃ {j : Fin 5 // j ≠ q} :=
    Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 4) := colsEquiv.trans (finSuccAboveEquiv q).symm
  have hsucc_sigma : forall j : Fin 4, q.succAbove (sigma j) = cols j := by
    intro j
    have hsub : finSuccAboveEquiv q (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 4) (Fin 4) Real :=
    B.submatrix (Fin.succAbove (4 : Fin 5)) (Fin.succAbove q)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    fin_cases i
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 0 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 1 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 2 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 3 c) (hsucc_sigma j)
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  have hadj_formula :
      B.adjugate q (4 : Fin 5) =
        (-1 : Real) ^ ((4 : Fin 5).val + q.val) * M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [hadj_formula]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hM_ne



private theorem det_ne_zero_of_totallyPositive_of_alternating_image_fin_five
    {B : Matrix (Fin 5) (Fin 5) Real} {x : Fin 5 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 5 => ∑ j : Fin 5, B i j * x j)) :
    B.det ≠ 0 := by
  classical
  intro hdet_zero
  let u : Fin 5 -> Real := fun i => ∑ j : Fin 5, B i j * x j
  rcases exists_nonzero_adjugate_col_four_of_alternating_image_fin_five
      hTP hAlt with ⟨q, hq_ne⟩
  let r : Real := (-1 : Real) ^ q.val * u 0
  have hchecker :
      forall i : Fin 5,
        0 <= ((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i) := by
    intro i
    exact adjugate_checkerboard_nonneg_of_totallyPositive hTP i q
  have hcommon_nonneg :
      forall i : Fin 5, 0 <= r * (B.adjugate q i * u i) := by
    intro i
    have hsign : 0 < u 0 * (((-1 : Real) ^ i.val) * u i) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := i)
    have heq : r * (B.adjugate q i * u i) =
        (u 0 * (((-1 : Real) ^ i.val) * u i)) *
          (((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real i.val with hi | hi <;>
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
      simp [hi, hq, mul_assoc, mul_comm]
    rw [heq]
    exact mul_nonneg hsign.le (hchecker i)
  have hcommon_pos_four : 0 < r * (B.adjugate q 4 * u 4) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (4 : Nat)) * u 4) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (4 : Fin 5))
    have hchecker_four_nonneg :
        0 <= ((-1 : Real) ^ ((4 : Fin 5).val + q.val)) * (B.adjugate q 4) :=
      hchecker 4
    have hchecker_four_ne :
        ((-1 : Real) ^ ((4 : Fin 5).val + q.val)) * (B.adjugate q 4) ≠ 0 := by
      exact mul_ne_zero
        (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hq_ne
    have hchecker_four_pos :
        0 < ((-1 : Real) ^ ((4 : Fin 5).val + q.val)) * (B.adjugate q 4) :=
      lt_of_le_of_ne hchecker_four_nonneg (Ne.symm hchecker_four_ne)
    have heq : r * (B.adjugate q 4 * u 4) =
        (u 0 * (((-1 : Real) ^ (4 : Nat)) * u 4)) *
          (((-1 : Real) ^ ((4 : Fin 5).val + q.val)) * (B.adjugate q 4)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
        simp [hq] <;> ring
    rw [heq]
    exact mul_pos hsign hchecker_four_pos
  have hsum_pos :
      0 < ∑ i : Fin 5, r * (B.adjugate q i * u i) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 5)))
        (f := fun i : Fin 5 => r * (B.adjugate q i * u i))
        (fun i _ => hcommon_nonneg i)
        (Finset.mem_univ (4 : Fin 5))
    exact lt_of_lt_of_le hcommon_pos_four hle
  have hu : u = B *ᵥ x := by
    ext i
    simp [u, Matrix.mulVec, dotProduct]
  have hvec : B.adjugate *ᵥ u = 0 := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet_zero]
    ext i
    simp
  have hsum_zero : (∑ i : Fin 5, B.adjugate q i * u i) = 0 := by
    have hqvec := congrFun hvec q
    simpa [Matrix.mulVec, dotProduct] using hqvec
  have hsum_rewrite :
      (∑ i : Fin 5, r * (B.adjugate q i * u i)) =
        r * (∑ i : Fin 5, B.adjugate q i * u i) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hsum_zero, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos


private theorem linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_five
    {B : Matrix (Fin 5) (Fin 5) Real} {x : Fin 5 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 5 => ∑ j : Fin 5, B i j * x j)) :
    LinearIndependent Real (fun i : Fin 5 => fun j : Fin 5 => B i j) := by
  have hdet := det_ne_zero_of_totallyPositive_of_alternating_image_fin_five hTP hAlt
  have hunit : IsUnit B := Matrix.isUnit_iff_isUnit_det B |>.mpr (IsUnit.mk0 B.det hdet)
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr hunit



private theorem cofactor_identity_fin_six_five
    {B : Matrix (Fin 6) (Fin 5) Real} (t : Fin 5) :
    (∑ p : Fin 6,
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) (fun j : Fin 5 => j)).det * B p t) = 0 := by
  classical
  let A : Matrix (Fin 6) (Fin 6) Real := fun i j =>
    if hj : j.val < 5 then B i ⟨j.val, hj⟩ else B i t
  have hcol_eq : forall i : Fin 6, A i (Fin.castSucc t) = A i (5 : Fin 6) := by
    intro i
    simp [A, Fin.castSucc]
  have hne : (Fin.castSucc t : Fin 6) ≠ (5 : Fin 6) := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.castSucc] at hv
    have ht : t.val < 5 := t.isLt
    omega
  have hdet_zero : A.det = 0 := Matrix.det_zero_of_column_eq hne hcol_eq
  have hdet_exp := Matrix.det_succ_column A (5 : Fin 6)
  rw [hdet_exp] at hdet_zero
  have hterm_eq : forall p : Fin 6,
      (-1 : Real) ^ p.val *
          (B.submatrix (Fin.succAbove p) (fun j : Fin 5 => j)).det * B p t =
        - ((-1 : Real) ^ ((p : Nat) + ((5 : Fin 6) : Nat)) *
          A p (5 : Fin 6) *
          (A.submatrix (Fin.succAbove p) (Fin.succAbove (5 : Fin 6))).det) := by
    intro p
    have hA5 : A p (5 : Fin 6) = B p t := by
      simp [A]
    have hsub :
        A.submatrix (Fin.succAbove p) (Fin.succAbove (5 : Fin 6)) =
          B.submatrix (Fin.succAbove p) (fun j : Fin 5 => j) := by
      ext i j
      fin_cases j <;> simp [A, Fin.succAbove]
    rw [hA5, hsub]
    have hsign :
        (-1 : Real) ^ ((p : Nat) + ((5 : Fin 6) : Nat)) =
          -((-1 : Real) ^ p.val) := by
      rw [pow_add]
      norm_num
    rw [hsign]
    ring
  calc
    (∑ p : Fin 6,
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) (fun j : Fin 5 => j)).det * B p t)
        =
      ∑ p : Fin 6,
        - ((-1 : Real) ^ ((p : Nat) + ((5 : Fin 6) : Nat)) *
          A p (5 : Fin 6) *
          (A.submatrix (Fin.succAbove p) (Fin.succAbove (5 : Fin 6))).det) := by
      refine Finset.sum_congr rfl ?_
      intro p _
      exact hterm_eq p
    _ = 0 := by
      rw [Finset.sum_neg_distrib, hdet_zero, neg_zero]



private theorem not_strictlyAlternating_image_fin_six_five
    {B : Matrix (Fin 6) (Fin 5) Real} {x : Fin 5 -> Real}
    (hTP : IsTotallyPositiveFinite B) :
      ¬ IsStrictlyAlternatingFin
        (fun i : Fin 6 => ∑ j : Fin 5, B i j * x j) := by
  classical
  intro hAlt
  let u : Fin 6 -> Real := fun i => ∑ j : Fin 5, B i j * x j
  let d : Fin 6 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) (fun j : Fin 5 => j)).det
  have hminor_nonneg : forall p : Fin 6, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 5 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    have hcols : StrictMono (fun j : Fin 5 => j.val) := by
      intro a b hab
      exact hab
    dsimp [d]
    change 0 <= (Matrix.of fun i j => B (Fin.succAbove p i) j).det
    exact hTP 5 (Fin.succAbove p) (fun j : Fin 5 => j) hrows hcols
  let Btop : Matrix (Fin 5) (Fin 5) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 5 => ∑ j : Fin 5, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 6 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  have hd5_ne : d (5 : Fin 6) ≠ 0 := by
    have hLI :=
      linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_five
        hTPtop hAlttop
    have hunit : IsUnit Btop := Matrix.linearIndependent_rows_iff_isUnit.mp hLI
    have hdetUnit : IsUnit Btop.det := (Matrix.isUnit_iff_isUnit_det Btop).mp hunit
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (5 : Fin 6)) (fun j : Fin 5 => j) = Btop := by
      ext i j
      fin_cases i <;> rfl
    have hd5_eq : d (5 : Fin 6) = Btop.det := by
      simp [d, hmatrix_eq]
    exact fun hd5_zero => hdetUnit.ne_zero (by simpa [← hd5_eq] using hd5_zero)
  have hd5_pos : 0 < d (5 : Fin 6) :=
    lt_of_le_of_ne (hminor_nonneg 5) (Ne.symm hd5_ne)
  have hidentity_cols :
      forall t : Fin 5,
        (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    simpa [d] using cofactor_identity_fin_six_five (B := B) t
  have hidentity : (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 6, ∑ j : Fin 5,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin 5, (∑ p : Fin 6,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 6, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_five :
      0 < r * (((-1 : Real) ^ (5 : Fin 6).val * d (5 : Fin 6)) * u (5 : Fin 6)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (5 : Nat)) * u (5 : Fin 6)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (5 : Fin 6))
    have heq :
        r * (((-1 : Real) ^ (5 : Fin 6).val * d (5 : Fin 6)) * u (5 : Fin 6)) =
          (u 0 * (((-1 : Real) ^ (5 : Nat)) * u (5 : Fin 6))) * d (5 : Fin 6) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd5_pos
  have hsum_pos :
      0 < ∑ p : Fin 6, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 6)))
        (f := fun p : Fin 6 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (5 : Fin 6))
    exact lt_of_lt_of_le hcommon_pos_five hle
  have hsum_rewrite :
      (∑ p : Fin 6, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem not_strictlyAlternating_image_of_cols_eq_five :
  forall {n : Nat} {B : Matrix (Fin n) (Fin 5) Real} {x : Fin 5 -> Real},
    6 <= n ->
    IsTotallyPositiveFinite B ->
      ¬ IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin 5, B i j * x j) := by
  classical
  intro n B x hn hTP hAlt
  let B6 : Matrix (Fin 6) (Fin 5) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP6 : IsTotallyPositiveFinite B6 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt6 :
      IsStrictlyAlternatingFin (fun i : Fin 6 => ∑ j : Fin 5, B6 i j * x j) := by
    constructor
    · intro i
      simpa [B6] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < n := by omega
      simpa [B6] using hAlt.2 ⟨i.val, by omega⟩ hi'
  exact (not_strictlyAlternating_image_fin_six_five hTP6) hAlt6



private theorem cofactor_identity_fin_seven_six
    {B : Matrix (Fin 7) (Fin 6) Real} (t : Fin 6) :
    (∑ p : Fin 7,
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) (fun j : Fin 6 => j)).det * B p t) = 0 := by
  classical
  let A : Matrix (Fin 7) (Fin 7) Real := fun i j =>
    if hj : j.val < 6 then B i ⟨j.val, hj⟩ else B i t
  have hcol_eq : forall i : Fin 7, A i (Fin.castSucc t) = A i (6 : Fin 7) := by
    intro i
    simp [A, Fin.castSucc]
  have hne : (Fin.castSucc t : Fin 7) ≠ (6 : Fin 7) := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.castSucc] at hv
    have ht : t.val < 6 := t.isLt
    omega
  have hdet_zero : A.det = 0 := Matrix.det_zero_of_column_eq hne hcol_eq
  have hdet_exp := Matrix.det_succ_column A (6 : Fin 7)
  rw [hdet_exp] at hdet_zero
  have hterm_eq : forall p : Fin 7,
      (-1 : Real) ^ p.val *
          (B.submatrix (Fin.succAbove p) (fun j : Fin 6 => j)).det * B p t =
        (-1 : Real) ^ ((p : Nat) + ((6 : Fin 7) : Nat)) *
          A p (6 : Fin 7) *
          (A.submatrix (Fin.succAbove p) (Fin.succAbove (6 : Fin 7))).det := by
    intro p
    have hA6 : A p (6 : Fin 7) = B p t := by
      simp [A]
    have hsub :
        A.submatrix (Fin.succAbove p) (Fin.succAbove (6 : Fin 7)) =
          B.submatrix (Fin.succAbove p) (fun j : Fin 6 => j) := by
      ext i j
      fin_cases j <;> simp [A, Fin.succAbove]
    rw [hA6, hsub]
    have hsign :
        (-1 : Real) ^ ((p : Nat) + ((6 : Fin 7) : Nat)) =
          (-1 : Real) ^ p.val := by
      rw [pow_add]
      norm_num
    rw [hsign]
    ring
  calc
    (∑ p : Fin 7,
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) (fun j : Fin 6 => j)).det * B p t)
        =
      ∑ p : Fin 7,
        (-1 : Real) ^ ((p : Nat) + ((6 : Fin 7) : Nat)) *
          A p (6 : Fin 7) *
          (A.submatrix (Fin.succAbove p) (Fin.succAbove (6 : Fin 7))).det := by
      refine Finset.sum_congr rfl ?_
      intro p _
      exact hterm_eq p
    _ = 0 := hdet_zero



private theorem not_strictlyAlternating_image_fin_seven_six
    {B : Matrix (Fin 7) (Fin 6) Real} {x : Fin 6 -> Real}
    (hTP : IsTotallyPositiveFinite B) :
      ¬ IsStrictlyAlternatingFin
        (fun i : Fin 7 => ∑ j : Fin 6, B i j * x j) := by
  classical
  intro hAlt
  let u : Fin 7 -> Real := fun i => ∑ j : Fin 6, B i j * x j
  let d : Fin 7 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) (fun j : Fin 6 => j)).det
  have hminor_nonneg : forall p : Fin 7, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 6 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    have hcols : StrictMono (fun j : Fin 6 => j.val) := by
      intro a b hab
      exact hab
    dsimp [d]
    change 0 <= (Matrix.of fun i j => B (Fin.succAbove p i) j).det
    exact hTP 6 (Fin.succAbove p) (fun j : Fin 6 => j) hrows hcols
  let Btop : Matrix (Fin 6) (Fin 6) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 6 => ∑ j : Fin 6, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 7 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  have hd6_ne : d (6 : Fin 7) ≠ 0 := by
    have hLI :=
      linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_six
        hTPtop hAlttop
    have hunit : IsUnit Btop := Matrix.linearIndependent_rows_iff_isUnit.mp hLI
    have hdetUnit : IsUnit Btop.det := (Matrix.isUnit_iff_isUnit_det Btop).mp hunit
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (6 : Fin 7)) (fun j : Fin 6 => j) = Btop := by
      ext i j
      fin_cases i <;> rfl
    have hd6_eq : d (6 : Fin 7) = Btop.det := by
      simp [d, hmatrix_eq]
    exact fun hd6_zero => hdetUnit.ne_zero (by simpa [← hd6_eq] using hd6_zero)
  have hd6_pos : 0 < d (6 : Fin 7) :=
    lt_of_le_of_ne (hminor_nonneg 6) (Ne.symm hd6_ne)
  have hidentity_cols :
      forall t : Fin 6,
        (∑ p : Fin 7, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    simpa [d] using cofactor_identity_fin_seven_six (B := B) t
  have hidentity : (∑ p : Fin 7, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 7, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 7, ∑ j : Fin 6,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin 6, (∑ p : Fin 7,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 7, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_six :
      0 < r * (((-1 : Real) ^ (6 : Fin 7).val * d (6 : Fin 7)) * u (6 : Fin 7)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (6 : Nat)) * u (6 : Fin 7)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (6 : Fin 7))
    have heq :
        r * (((-1 : Real) ^ (6 : Fin 7).val * d (6 : Fin 7)) * u (6 : Fin 7)) =
          (u 0 * (((-1 : Real) ^ (6 : Nat)) * u (6 : Fin 7))) * d (6 : Fin 7) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd6_pos
  have hsum_pos :
      0 < ∑ p : Fin 7, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 7)))
        (f := fun p : Fin 7 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (6 : Fin 7))
    exact lt_of_lt_of_le hcommon_pos_six hle
  have hsum_rewrite :
      (∑ p : Fin 7, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 7, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem not_strictlyAlternating_image_of_cols_eq_six :
  forall {n : Nat} {B : Matrix (Fin n) (Fin 6) Real} {x : Fin 6 -> Real},
    7 <= n ->
    IsTotallyPositiveFinite B ->
      ¬ IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin 6, B i j * x j) := by
  classical
  intro n B x hn hTP hAlt
  let B7 : Matrix (Fin 7) (Fin 6) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP7 : IsTotallyPositiveFinite B7 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt7 :
      IsStrictlyAlternatingFin (fun i : Fin 7 => ∑ j : Fin 6, B7 i j * x j) := by
    constructor
    · intro i
      simpa [B7] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < n := by omega
      simpa [B7] using hAlt.2 ⟨i.val, by omega⟩ hi'
  exact (not_strictlyAlternating_image_fin_seven_six hTP7) hAlt7



private theorem exists_positive_ordered_five_minor_first_five_rows_fin_six_seven
    {B : Matrix (Fin 6) (Fin 7) Real} {x : Fin 7 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 6 => ∑ j : Fin 7, B i j * x j)) :
    exists cols : Fin 5 -> Fin 7,
      StrictMono (fun j => (cols j).val) /\
        0 < (Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols j)).det := by
  classical
  let Btop : Matrix (Fin 5) (Fin 7) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 5 => ∑ j : Fin 7, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 6 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_five_cols
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin 7) := Finset.image cols Finset.univ
  have hS_card : S.card = 5 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 5))) hcols
  let colsOrd : Fin 5 -> Fin 7 := fun j => S.orderEmbOfFin hS_card j
  have hcolsOrd_strict : StrictMono (fun j => (colsOrd j).val) := by
    intro a b hab
    exact (S.orderEmbOfFin hS_card).strictMono hab
  have hminor_nonneg :
      0 <= (Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)).det := by
    have hrows : StrictMono (fun i : Fin 5 => (⟨i.val, by omega⟩ : Fin 6).val) := by
      intro i j hij
      exact hij
    exact hTP 5 (fun i : Fin 5 => ⟨i.val, by omega⟩) colsOrd hrows hcolsOrd_strict
  have hcols_ne_ord :
      forall j : Fin 5, cols j ∈ S := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  let colsSub : Fin 5 -> S := fun j => ⟨cols j, hcols_ne_ord j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hS_card]⟩
  let colsEquiv : Fin 5 ≃ S := Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 5) := colsEquiv.trans (S.orderIsoOfFin hS_card).symm
  have hcolsOrd_sigma : forall j : Fin 5, colsOrd (sigma j) = cols j := by
    intro j
    have hsub : S.orderIsoOfFin hS_card (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 5) (Fin 5) Real :=
    Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    simp [M, Btop, hcolsOrd_sigma j]
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  exact ⟨colsOrd, hcolsOrd_strict, lt_of_le_of_ne hminor_nonneg (Ne.symm hM_ne)⟩



private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_six_seven
    {B : Matrix (Fin 6) (Fin 7) Real} {x : Fin 7 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 6 => ∑ j : Fin 7, B i j * x j)) :
      exists cols : Fin 6 -> Fin 7,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  by_contra hnone
  have hdet_zero_cols :
      forall cols : Fin 6 -> Fin 7, Function.Injective cols ->
        (Matrix.of fun i j => B i (cols j)).det = 0 := by
    intro cols hcols
    by_contra hdet
    exact hnone ⟨cols, hcols, hdet⟩
  let u : Fin 6 -> Real := fun i => ∑ j : Fin 7, B i j * x j
  rcases exists_positive_ordered_five_minor_first_five_rows_fin_six_seven
      hTP hAlt with ⟨cols5, hcols5_strict, hdet5_pos⟩
  let d : Fin 6 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) cols5).det
  have hminor_nonneg : forall p : Fin 6, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 5 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    exact hTP 5 (Fin.succAbove p) cols5 hrows hcols5_strict
  have hd5_pos : 0 < d (5 : Fin 6) := by
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (5 : Fin 6)) cols5 =
          Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols5 j) := by
      ext i j
      fin_cases i <;> rfl
    simpa [d, hmatrix_eq] using hdet5_pos
  let S : Finset (Fin 7) := Finset.image cols5 Finset.univ
  have hcols5_inj : Function.Injective cols5 := by
    intro a b h
    apply hcols5_strict.injective
    exact congrArg Fin.val h
  have hidentity_cols :
      forall t : Fin 7,
        (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    let A : Matrix (Fin 6) (Fin 6) Real := fun i j =>
      if hj : j.val < 5 then B i (cols5 ⟨j.val, hj⟩) else B i t
    have hdetA_zero : A.det = 0 := by
      by_cases htS : t ∈ S
      · rcases Finset.mem_image.mp htS with ⟨j0, _hj0mem, hj0⟩
        have hcol_eq : forall i : Fin 6, A i (Fin.castSucc j0) = A i (5 : Fin 6) := by
          intro i
          simp [A, Fin.castSucc, hj0]
        have hne : (Fin.castSucc j0 : Fin 6) ≠ (5 : Fin 6) := by
          intro h
          have hv := congrArg Fin.val h
          simp [Fin.castSucc] at hv
          have hj0lt : j0.val < 5 := j0.isLt
          omega
        exact Matrix.det_zero_of_column_eq hne hcol_eq
      · let cols6 : Fin 6 -> Fin 7 := fun j =>
          if hj : j.val < 5 then cols5 ⟨j.val, hj⟩ else t
        have hcols6 : Function.Injective cols6 := by
          intro i j hij
          by_cases hi : i.val < 5
          · by_cases hj : j.val < 5
            · have hcols_eq : cols5 ⟨i.val, hi⟩ = cols5 ⟨j.val, hj⟩ := by
                simpa [cols6, hi, hj] using hij
              have hidx : (⟨i.val, hi⟩ : Fin 5) = ⟨j.val, hj⟩ :=
                hcols5_inj hcols_eq
              exact Fin.ext (by simpa using congrArg Fin.val hidx)
            · have hit : cols5 ⟨i.val, hi⟩ = t := by
                simpa [cols6, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨i.val, hi⟩, Finset.mem_univ _, hit⟩))
          · by_cases hj : j.val < 5
            · have htj : t = cols5 ⟨j.val, hj⟩ := by
                simpa [cols6, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨j.val, hj⟩, Finset.mem_univ _, htj.symm⟩))
            · exact Fin.ext (by omega)
        have hdet0 := hdet_zero_cols cols6 hcols6
        have hA_eq : A = Matrix.of fun i j => B i (cols6 j) := by
          ext i j
          by_cases hj : j.val < 5 <;> simp [A, cols6, hj]
        rw [hA_eq]
        exact hdet0
    have hdet_exp := Matrix.det_succ_column A (5 : Fin 6)
    rw [hdet_exp] at hdetA_zero
    have hterm_eq : forall p : Fin 6,
        (-1 : Real) ^ p.val * d p * B p t =
          - ((-1 : Real) ^ ((p : Nat) + ((5 : Fin 6) : Nat)) *
              A p (5 : Fin 6) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (5 : Fin 6))).det) := by
      intro p
      have hA5 : A p (5 : Fin 6) = B p t := by
        simp [A]
      have hsub :
          A.submatrix (Fin.succAbove p) (Fin.succAbove (5 : Fin 6)) =
            B.submatrix (Fin.succAbove p) cols5 := by
        ext i j
        fin_cases j <;> simp [A, Fin.succAbove]
      rw [hA5, hsub]
      have hsign :
          (-1 : Real) ^ ((p : Nat) + ((5 : Fin 6) : Nat)) =
            -((-1 : Real) ^ p.val) := by
        rw [pow_add]
        norm_num
      rw [hsign]
      simp [d]
      ring
    calc
      (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * B p t)
          =
        ∑ p : Fin 6,
          - ((-1 : Real) ^ ((p : Nat) + ((5 : Fin 6) : Nat)) *
              A p (5 : Fin 6) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (5 : Fin 6))).det) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        exact hterm_eq p
      _ = 0 := by
        rw [Finset.sum_neg_distrib, hdetA_zero, neg_zero]
  have hidentity : (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 6, ∑ j : Fin 7,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin 7, (∑ p : Fin 6,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 6, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_five :
      0 < r * (((-1 : Real) ^ (5 : Fin 6).val * d (5 : Fin 6)) * u (5 : Fin 6)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (5 : Nat)) * u (5 : Fin 6)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (5 : Fin 6))
    have heq :
        r * (((-1 : Real) ^ (5 : Fin 6).val * d (5 : Fin 6)) * u (5 : Fin 6)) =
          (u 0 * (((-1 : Real) ^ (5 : Nat)) * u (5 : Fin 6))) * d (5 : Fin 6) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd5_pos
  have hsum_pos :
      0 < ∑ p : Fin 6, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 6)))
        (f := fun p : Fin 6 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (5 : Fin 6))
    exact lt_of_lt_of_le hcommon_pos_five hle
  have hsum_rewrite :
      (∑ p : Fin 6, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 6, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem exists_nonzero_adjugate_col_six_of_alternating_image_fin_seven
    {B : Matrix (Fin 7) (Fin 7) Real} {x : Fin 7 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 7 => ∑ j : Fin 7, B i j * x j)) :
    exists q : Fin 7, B.adjugate q 6 ≠ 0 := by
  classical
  let Btop : Matrix (Fin 6) (Fin 7) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 6 => ∑ j : Fin 7, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 7 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_six_seven
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin 7) := Finset.image cols Finset.univ
  have hS_card : S.card = 6 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 6))) hcols
  have hS_lt_univ : S.card < (Finset.univ : Finset (Fin 7)).card := by
    simp [hS_card]
  rcases Finset.exists_mem_notMem_of_card_lt_card hS_lt_univ with ⟨q, _hqmem, hqnot⟩
  refine ⟨q, ?_⟩
  have hcols_ne_q : forall j : Fin 6, cols j ≠ q := by
    intro j hj
    exact hqnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩)
  let colsSub : Fin 6 -> {j : Fin 7 // j ≠ q} :=
    fun j => ⟨cols j, hcols_ne_q j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcard_sub : Fintype.card {j : Fin 7 // j ≠ q} = 6 := by
    simp
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hcard_sub]⟩
  let colsEquiv : Fin 6 ≃ {j : Fin 7 // j ≠ q} :=
    Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 6) := colsEquiv.trans (finSuccAboveEquiv q).symm
  have hsucc_sigma : forall j : Fin 6, q.succAbove (sigma j) = cols j := by
    intro j
    have hsub : finSuccAboveEquiv q (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 6) (Fin 6) Real :=
    B.submatrix (Fin.succAbove (6 : Fin 7)) (Fin.succAbove q)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    fin_cases i
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 0 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 1 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 2 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 3 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 4 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 5 c) (hsucc_sigma j)
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  have hadj_formula :
      B.adjugate q (6 : Fin 7) =
        (-1 : Real) ^ ((6 : Fin 7).val + q.val) * M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [hadj_formula]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hM_ne



private theorem det_ne_zero_of_totallyPositive_of_alternating_image_fin_seven
    {B : Matrix (Fin 7) (Fin 7) Real} {x : Fin 7 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 7 => ∑ j : Fin 7, B i j * x j)) :
    B.det ≠ 0 := by
  classical
  intro hdet_zero
  let u : Fin 7 -> Real := fun i => ∑ j : Fin 7, B i j * x j
  rcases exists_nonzero_adjugate_col_six_of_alternating_image_fin_seven
      hTP hAlt with ⟨q, hq_ne⟩
  let r : Real := (-1 : Real) ^ q.val * u 0
  have hchecker :
      forall i : Fin 7,
        0 <= ((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i) := by
    intro i
    exact adjugate_checkerboard_nonneg_of_totallyPositive hTP i q
  have hcommon_nonneg :
      forall i : Fin 7, 0 <= r * (B.adjugate q i * u i) := by
    intro i
    have hsign : 0 < u 0 * (((-1 : Real) ^ i.val) * u i) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := i)
    have heq : r * (B.adjugate q i * u i) =
        (u 0 * (((-1 : Real) ^ i.val) * u i)) *
          (((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real i.val with hi | hi <;>
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
      simp [hi, hq, mul_assoc, mul_comm]
    rw [heq]
    exact mul_nonneg hsign.le (hchecker i)
  have hcommon_pos_six : 0 < r * (B.adjugate q 6 * u 6) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (6 : Nat)) * u 6) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (6 : Fin 7))
    have hchecker_six_nonneg :
        0 <= ((-1 : Real) ^ ((6 : Fin 7).val + q.val)) * (B.adjugate q 6) :=
      hchecker 6
    have hchecker_six_ne :
        ((-1 : Real) ^ ((6 : Fin 7).val + q.val)) * (B.adjugate q 6) ≠ 0 := by
      exact mul_ne_zero
        (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hq_ne
    have hchecker_six_pos :
        0 < ((-1 : Real) ^ ((6 : Fin 7).val + q.val)) * (B.adjugate q 6) :=
      lt_of_le_of_ne hchecker_six_nonneg (Ne.symm hchecker_six_ne)
    have heq : r * (B.adjugate q 6 * u 6) =
        (u 0 * (((-1 : Real) ^ (6 : Nat)) * u 6)) *
          (((-1 : Real) ^ ((6 : Fin 7).val + q.val)) * (B.adjugate q 6)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
        simp [hq] <;> ring
    rw [heq]
    exact mul_pos hsign hchecker_six_pos
  have hsum_pos :
      0 < ∑ i : Fin 7, r * (B.adjugate q i * u i) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 7)))
        (f := fun i : Fin 7 => r * (B.adjugate q i * u i))
        (fun i _ => hcommon_nonneg i)
        (Finset.mem_univ (6 : Fin 7))
    exact lt_of_lt_of_le hcommon_pos_six hle
  have hu : u = B *ᵥ x := by
    ext i
    simp [u, Matrix.mulVec, dotProduct]
  have hvec : B.adjugate *ᵥ u = 0 := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet_zero]
    ext i
    simp
  have hsum_zero : (∑ i : Fin 7, B.adjugate q i * u i) = 0 := by
    have hqvec := congrFun hvec q
    simpa [Matrix.mulVec, dotProduct] using hqvec
  have hsum_rewrite :
      (∑ i : Fin 7, r * (B.adjugate q i * u i)) =
        r * (∑ i : Fin 7, B.adjugate q i * u i) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hsum_zero, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos


private theorem linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_seven
    {B : Matrix (Fin 7) (Fin 7) Real} {x : Fin 7 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 7 => ∑ j : Fin 7, B i j * x j)) :
    LinearIndependent Real (fun i : Fin 7 => fun j : Fin 7 => B i j) := by
  have hdet := det_ne_zero_of_totallyPositive_of_alternating_image_fin_seven hTP hAlt
  have hunit : IsUnit B := Matrix.isUnit_iff_isUnit_det B |>.mpr (IsUnit.mk0 B.det hdet)
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr hunit



private theorem cofactor_identity_fin_eight_seven
    {B : Matrix (Fin 8) (Fin 7) Real} (t : Fin 7) :
    (∑ p : Fin 8,
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) (fun j : Fin 7 => j)).det * B p t) = 0 := by
  classical
  let A : Matrix (Fin 8) (Fin 8) Real := fun i j =>
    if hj : j.val < 7 then B i ⟨j.val, hj⟩ else B i t
  have hcol_eq : forall i : Fin 8, A i (Fin.castSucc t) = A i (7 : Fin 8) := by
    intro i
    simp [A, Fin.castSucc]
  have hne : (Fin.castSucc t : Fin 8) ≠ (7 : Fin 8) := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.castSucc] at hv
    have ht : t.val < 7 := t.isLt
    omega
  have hdet_zero : A.det = 0 := Matrix.det_zero_of_column_eq hne hcol_eq
  have hdet_exp := Matrix.det_succ_column A (7 : Fin 8)
  rw [hdet_exp] at hdet_zero
  have hterm_eq : forall p : Fin 8,
      (-1 : Real) ^ p.val *
          (B.submatrix (Fin.succAbove p) (fun j : Fin 7 => j)).det * B p t =
        - ((-1 : Real) ^ ((p : Nat) + ((7 : Fin 8) : Nat)) *
          A p (7 : Fin 8) *
          (A.submatrix (Fin.succAbove p) (Fin.succAbove (7 : Fin 8))).det) := by
    intro p
    have hA7 : A p (7 : Fin 8) = B p t := by
      simp [A]
    have hsub :
        A.submatrix (Fin.succAbove p) (Fin.succAbove (7 : Fin 8)) =
          B.submatrix (Fin.succAbove p) (fun j : Fin 7 => j) := by
      ext i j
      fin_cases j <;> simp [A, Fin.succAbove]
    rw [hA7, hsub]
    have hsign :
        (-1 : Real) ^ ((p : Nat) + ((7 : Fin 8) : Nat)) =
          -((-1 : Real) ^ p.val) := by
      rw [pow_add]
      norm_num
    rw [hsign]
    simp
    ring
  calc
    (∑ p : Fin 8,
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) (fun j : Fin 7 => j)).det * B p t)
        =
      ∑ p : Fin 8,
        - ((-1 : Real) ^ ((p : Nat) + ((7 : Fin 8) : Nat)) *
          A p (7 : Fin 8) *
          (A.submatrix (Fin.succAbove p) (Fin.succAbove (7 : Fin 8))).det) := by
      refine Finset.sum_congr rfl ?_
      intro p _
      exact hterm_eq p
    _ = 0 := by
      rw [Finset.sum_neg_distrib, hdet_zero, neg_zero]



private theorem not_strictlyAlternating_image_fin_eight_seven
    {B : Matrix (Fin 8) (Fin 7) Real} {x : Fin 7 -> Real}
    (hTP : IsTotallyPositiveFinite B) :
      ¬ IsStrictlyAlternatingFin
        (fun i : Fin 8 => ∑ j : Fin 7, B i j * x j) := by
  classical
  intro hAlt
  let u : Fin 8 -> Real := fun i => ∑ j : Fin 7, B i j * x j
  let d : Fin 8 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) (fun j : Fin 7 => j)).det
  have hminor_nonneg : forall p : Fin 8, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 7 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    have hcols : StrictMono (fun j : Fin 7 => j.val) := by
      intro a b hab
      exact hab
    dsimp [d]
    change 0 <= (Matrix.of fun i j => B (Fin.succAbove p i) j).det
    exact hTP 7 (Fin.succAbove p) (fun j : Fin 7 => j) hrows hcols
  let Btop : Matrix (Fin 7) (Fin 7) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 7 => ∑ j : Fin 7, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 8 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  have hd7_ne : d (7 : Fin 8) ≠ 0 := by
    have hLI :=
      linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_seven
        hTPtop hAlttop
    have hunit : IsUnit Btop := Matrix.linearIndependent_rows_iff_isUnit.mp hLI
    have hdetUnit : IsUnit Btop.det := (Matrix.isUnit_iff_isUnit_det Btop).mp hunit
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (7 : Fin 8)) (fun j : Fin 7 => j) = Btop := by
      ext i j
      fin_cases i <;> rfl
    have hd7_eq : d (7 : Fin 8) = Btop.det := by
      simp [d, hmatrix_eq]
    exact fun hd7_zero => hdetUnit.ne_zero (by simpa [← hd7_eq] using hd7_zero)
  have hd7_pos : 0 < d (7 : Fin 8) :=
    lt_of_le_of_ne (hminor_nonneg 7) (Ne.symm hd7_ne)
  have hidentity_cols :
      forall t : Fin 7,
        (∑ p : Fin 8, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    simpa [d] using cofactor_identity_fin_eight_seven (B := B) t
  have hidentity : (∑ p : Fin 8, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 8, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 8, ∑ j : Fin 7,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin 7, (∑ p : Fin 8,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 8, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_seven :
      0 < r * (((-1 : Real) ^ (7 : Fin 8).val * d (7 : Fin 8)) * u (7 : Fin 8)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (7 : Nat)) * u (7 : Fin 8)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (7 : Fin 8))
    have heq :
        r * (((-1 : Real) ^ (7 : Fin 8).val * d (7 : Fin 8)) * u (7 : Fin 8)) =
          (u 0 * (((-1 : Real) ^ (7 : Nat)) * u (7 : Fin 8))) * d (7 : Fin 8) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd7_pos
  have hsum_pos :
      0 < ∑ p : Fin 8, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 8)))
        (f := fun p : Fin 8 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (7 : Fin 8))
    exact lt_of_lt_of_le hcommon_pos_seven hle
  have hsum_rewrite :
      (∑ p : Fin 8, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 8, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem not_strictlyAlternating_image_of_cols_eq_seven :
  forall {n : Nat} {B : Matrix (Fin n) (Fin 7) Real} {x : Fin 7 -> Real},
    8 <= n ->
    IsTotallyPositiveFinite B ->
      ¬ IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin 7, B i j * x j) := by
  classical
  intro n B x hn hTP hAlt
  let B8 : Matrix (Fin 8) (Fin 7) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP8 : IsTotallyPositiveFinite B8 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt8 :
      IsStrictlyAlternatingFin (fun i : Fin 8 => ∑ j : Fin 7, B8 i j * x j) := by
    constructor
    · intro i
      simpa [B8] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < n := by omega
      simpa [B8] using hAlt.2 ⟨i.val, by omega⟩ hi'
  exact (not_strictlyAlternating_image_fin_eight_seven hTP8) hAlt8



private theorem exists_positive_ordered_six_minor_first_six_rows_fin_seven_eight
    {B : Matrix (Fin 7) (Fin 8) Real} {x : Fin 8 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 7 => ∑ j : Fin 8, B i j * x j)) :
    exists cols : Fin 6 -> Fin 8,
      StrictMono (fun j => (cols j).val) /\
        0 < (Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols j)).det := by
  classical
  let Btop : Matrix (Fin 6) (Fin 8) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 6 => ∑ j : Fin 8, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 7 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_six_cols
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin 8) := Finset.image cols Finset.univ
  have hS_card : S.card = 6 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 6))) hcols
  let colsOrd : Fin 6 -> Fin 8 := fun j => S.orderEmbOfFin hS_card j
  have hcolsOrd_strict : StrictMono (fun j => (colsOrd j).val) := by
    intro a b hab
    exact (S.orderEmbOfFin hS_card).strictMono hab
  have hminor_nonneg :
      0 <= (Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)).det := by
    have hrows : StrictMono (fun i : Fin 6 => (⟨i.val, by omega⟩ : Fin 7).val) := by
      intro i j hij
      exact hij
    exact hTP 6 (fun i : Fin 6 => ⟨i.val, by omega⟩) colsOrd hrows hcolsOrd_strict
  have hcols_ne_ord :
      forall j : Fin 6, cols j ∈ S := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  let colsSub : Fin 6 -> S := fun j => ⟨cols j, hcols_ne_ord j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hS_card]⟩
  let colsEquiv : Fin 6 ≃ S := Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 6) := colsEquiv.trans (S.orderIsoOfFin hS_card).symm
  have hcolsOrd_sigma : forall j : Fin 6, colsOrd (sigma j) = cols j := by
    intro j
    have hsub : S.orderIsoOfFin hS_card (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 6) (Fin 6) Real :=
    Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    simp [M, Btop, hcolsOrd_sigma j]
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  exact ⟨colsOrd, hcolsOrd_strict, lt_of_le_of_ne hminor_nonneg (Ne.symm hM_ne)⟩



private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_seven_eight
    {B : Matrix (Fin 7) (Fin 8) Real} {x : Fin 8 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 7 => ∑ j : Fin 8, B i j * x j)) :
      exists cols : Fin 7 -> Fin 8,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  by_contra hnone
  have hdet_zero_cols :
      forall cols : Fin 7 -> Fin 8, Function.Injective cols ->
        (Matrix.of fun i j => B i (cols j)).det = 0 := by
    intro cols hcols
    by_contra hdet
    exact hnone ⟨cols, hcols, hdet⟩
  let u : Fin 7 -> Real := fun i => ∑ j : Fin 8, B i j * x j
  rcases exists_positive_ordered_six_minor_first_six_rows_fin_seven_eight
      hTP hAlt with ⟨cols6, hcols6_strict, hdet6_pos⟩
  let d : Fin 7 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) cols6).det
  have hminor_nonneg : forall p : Fin 7, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 6 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    exact hTP 6 (Fin.succAbove p) cols6 hrows hcols6_strict
  have hd6_pos : 0 < d (6 : Fin 7) := by
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (6 : Fin 7)) cols6 =
          Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols6 j) := by
      ext i j
      fin_cases i <;> rfl
    simpa [d, hmatrix_eq] using hdet6_pos
  let S : Finset (Fin 8) := Finset.image cols6 Finset.univ
  have hcols6_inj : Function.Injective cols6 := by
    intro a b h
    apply hcols6_strict.injective
    exact congrArg Fin.val h
  have hidentity_cols :
      forall t : Fin 8,
        (∑ p : Fin 7, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    let A : Matrix (Fin 7) (Fin 7) Real := fun i j =>
      if hj : j.val < 6 then B i (cols6 ⟨j.val, hj⟩) else B i t
    have hdetA_zero : A.det = 0 := by
      by_cases htS : t ∈ S
      · rcases Finset.mem_image.mp htS with ⟨j0, _hj0mem, hj0⟩
        have hcol_eq : forall i : Fin 7, A i (Fin.castSucc j0) = A i (6 : Fin 7) := by
          intro i
          simp [A, Fin.castSucc, hj0]
        have hne : (Fin.castSucc j0 : Fin 7) ≠ (6 : Fin 7) := by
          intro h
          have hv := congrArg Fin.val h
          simp [Fin.castSucc] at hv
          have hj0lt : j0.val < 6 := j0.isLt
          omega
        exact Matrix.det_zero_of_column_eq hne hcol_eq
      · let cols7 : Fin 7 -> Fin 8 := fun j =>
          if hj : j.val < 6 then cols6 ⟨j.val, hj⟩ else t
        have hcols7 : Function.Injective cols7 := by
          intro i j hij
          by_cases hi : i.val < 6
          · by_cases hj : j.val < 6
            · have hcols_eq : cols6 ⟨i.val, hi⟩ = cols6 ⟨j.val, hj⟩ := by
                simpa [cols7, hi, hj] using hij
              have hidx : (⟨i.val, hi⟩ : Fin 6) = ⟨j.val, hj⟩ :=
                hcols6_inj hcols_eq
              exact Fin.ext (by simpa using congrArg Fin.val hidx)
            · have hit : cols6 ⟨i.val, hi⟩ = t := by
                simpa [cols7, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨i.val, hi⟩, Finset.mem_univ _, hit⟩))
          · by_cases hj : j.val < 6
            · have htj : t = cols6 ⟨j.val, hj⟩ := by
                simpa [cols7, hi, hj] using hij
              exact False.elim
                (htS (Finset.mem_image.mpr
                  ⟨⟨j.val, hj⟩, Finset.mem_univ _, htj.symm⟩))
            · exact Fin.ext (by omega)
        have hdet0 := hdet_zero_cols cols7 hcols7
        have hA_eq : A = Matrix.of fun i j => B i (cols7 j) := by
          ext i j
          by_cases hj : j.val < 6 <;> simp [A, cols7, hj]
        rw [hA_eq]
        exact hdet0
    have hdet_exp := Matrix.det_succ_column A (6 : Fin 7)
    rw [hdet_exp] at hdetA_zero
    have hterm_eq : forall p : Fin 7,
        (-1 : Real) ^ p.val * d p * B p t =
          (-1 : Real) ^ ((p : Nat) + ((6 : Fin 7) : Nat)) *
              A p (6 : Fin 7) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (6 : Fin 7))).det := by
      intro p
      have hA6 : A p (6 : Fin 7) = B p t := by
        simp [A]
      have hsub :
          A.submatrix (Fin.succAbove p) (Fin.succAbove (6 : Fin 7)) =
            B.submatrix (Fin.succAbove p) cols6 := by
        ext i j
        fin_cases j <;> simp [A, Fin.succAbove]
      rw [hA6, hsub]
      have hsign :
          (-1 : Real) ^ ((p : Nat) + ((6 : Fin 7) : Nat)) =
            (-1 : Real) ^ p.val := by
        rw [pow_add]
        norm_num
      rw [hsign]
      simp [d]
      ring
    calc
      (∑ p : Fin 7, (-1 : Real) ^ p.val * d p * B p t)
          =
        ∑ p : Fin 7,
          (-1 : Real) ^ ((p : Nat) + ((6 : Fin 7) : Nat)) *
              A p (6 : Fin 7) *
              (A.submatrix (Fin.succAbove p) (Fin.succAbove (6 : Fin 7))).det := by
        refine Finset.sum_congr rfl ?_
        intro p _
        exact hterm_eq p
      _ = 0 := hdetA_zero
  have hidentity : (∑ p : Fin 7, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 7, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 7, ∑ j : Fin 8,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin 8, (∑ p : Fin 7,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 7, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_six :
      0 < r * (((-1 : Real) ^ (6 : Fin 7).val * d (6 : Fin 7)) * u (6 : Fin 7)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (6 : Nat)) * u (6 : Fin 7)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (6 : Fin 7))
    have heq :
        r * (((-1 : Real) ^ (6 : Fin 7).val * d (6 : Fin 7)) * u (6 : Fin 7)) =
          (u 0 * (((-1 : Real) ^ (6 : Nat)) * u (6 : Fin 7))) * d (6 : Fin 7) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd6_pos
  have hsum_pos :
      0 < ∑ p : Fin 7, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 7)))
        (f := fun p : Fin 7 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (6 : Fin 7))
    exact lt_of_lt_of_le hcommon_pos_six hle
  have hsum_rewrite :
      (∑ p : Fin 7, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 7, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem exists_nonzero_adjugate_col_seven_of_alternating_image_fin_eight
    {B : Matrix (Fin 8) (Fin 8) Real} {x : Fin 8 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 8 => ∑ j : Fin 8, B i j * x j)) :
    exists q : Fin 8, B.adjugate q 7 ≠ 0 := by
  classical
  let Btop : Matrix (Fin 7) (Fin 8) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 7 => ∑ j : Fin 8, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 8 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_seven_eight
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin 8) := Finset.image cols Finset.univ
  have hS_card : S.card = 7 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 7))) hcols
  have hS_lt_univ : S.card < (Finset.univ : Finset (Fin 8)).card := by
    simp [hS_card]
  rcases Finset.exists_mem_notMem_of_card_lt_card hS_lt_univ with ⟨q, _hqmem, hqnot⟩
  refine ⟨q, ?_⟩
  have hcols_ne_q : forall j : Fin 7, cols j ≠ q := by
    intro j hj
    exact hqnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩)
  let colsSub : Fin 7 -> {j : Fin 8 // j ≠ q} :=
    fun j => ⟨cols j, hcols_ne_q j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcard_sub : Fintype.card {j : Fin 8 // j ≠ q} = 7 := by
    simp
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hcard_sub]⟩
  let colsEquiv : Fin 7 ≃ {j : Fin 8 // j ≠ q} :=
    Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 7) := colsEquiv.trans (finSuccAboveEquiv q).symm
  have hsucc_sigma : forall j : Fin 7, q.succAbove (sigma j) = cols j := by
    intro j
    have hsub : finSuccAboveEquiv q (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 7) (Fin 7) Real :=
    B.submatrix (Fin.succAbove (7 : Fin 8)) (Fin.succAbove q)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    fin_cases i
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 0 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 1 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 2 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 3 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 4 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 5 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 6 c) (hsucc_sigma j)
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  have hadj_formula :
      B.adjugate q (7 : Fin 8) =
        (-1 : Real) ^ ((7 : Fin 8).val + q.val) * M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [hadj_formula]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hM_ne



private theorem det_ne_zero_of_totallyPositive_of_alternating_image_fin_eight
    {B : Matrix (Fin 8) (Fin 8) Real} {x : Fin 8 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 8 => ∑ j : Fin 8, B i j * x j)) :
    B.det ≠ 0 := by
  classical
  intro hdet_zero
  let u : Fin 8 -> Real := fun i => ∑ j : Fin 8, B i j * x j
  rcases exists_nonzero_adjugate_col_seven_of_alternating_image_fin_eight
      hTP hAlt with ⟨q, hq_ne⟩
  let r : Real := (-1 : Real) ^ q.val * u 0
  have hchecker :
      forall i : Fin 8,
        0 <= ((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i) := by
    intro i
    exact adjugate_checkerboard_nonneg_of_totallyPositive hTP i q
  have hcommon_nonneg :
      forall i : Fin 8, 0 <= r * (B.adjugate q i * u i) := by
    intro i
    have hsign : 0 < u 0 * (((-1 : Real) ^ i.val) * u i) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := i)
    have heq : r * (B.adjugate q i * u i) =
        (u 0 * (((-1 : Real) ^ i.val) * u i)) *
          (((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real i.val with hi | hi <;>
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
      simp [hi, hq, mul_assoc, mul_comm]
    rw [heq]
    exact mul_nonneg hsign.le (hchecker i)
  have hcommon_pos_seven : 0 < r * (B.adjugate q 7 * u 7) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (7 : Nat)) * u 7) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (7 : Fin 8))
    have hchecker_seven_nonneg :
        0 <= ((-1 : Real) ^ ((7 : Fin 8).val + q.val)) * (B.adjugate q 7) :=
      hchecker 7
    have hchecker_seven_ne :
        ((-1 : Real) ^ ((7 : Fin 8).val + q.val)) * (B.adjugate q 7) ≠ 0 := by
      exact mul_ne_zero
        (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hq_ne
    have hchecker_seven_pos :
        0 < ((-1 : Real) ^ ((7 : Fin 8).val + q.val)) * (B.adjugate q 7) :=
      lt_of_le_of_ne hchecker_seven_nonneg (Ne.symm hchecker_seven_ne)
    have heq : r * (B.adjugate q 7 * u 7) =
        (u 0 * (((-1 : Real) ^ (7 : Nat)) * u 7)) *
          (((-1 : Real) ^ ((7 : Fin 8).val + q.val)) * (B.adjugate q 7)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
        simp [hq] <;> ring
    rw [heq]
    exact mul_pos hsign hchecker_seven_pos
  have hsum_pos :
      0 < ∑ i : Fin 8, r * (B.adjugate q i * u i) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 8)))
        (f := fun i : Fin 8 => r * (B.adjugate q i * u i))
        (fun i _ => hcommon_nonneg i)
        (Finset.mem_univ (7 : Fin 8))
    exact lt_of_lt_of_le hcommon_pos_seven hle
  have hu : u = B *ᵥ x := by
    ext i
    simp [u, Matrix.mulVec, dotProduct]
  have hvec : B.adjugate *ᵥ u = 0 := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet_zero]
    ext i
    simp
  have hsum_zero : (∑ i : Fin 8, B.adjugate q i * u i) = 0 := by
    have hqvec := congrFun hvec q
    simpa [Matrix.mulVec, dotProduct] using hqvec
  have hsum_rewrite :
      (∑ i : Fin 8, r * (B.adjugate q i * u i)) =
        r * (∑ i : Fin 8, B.adjugate q i * u i) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hsum_zero, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos


private theorem linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_eight
    {B : Matrix (Fin 8) (Fin 8) Real} {x : Fin 8 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 8 => ∑ j : Fin 8, B i j * x j)) :
    LinearIndependent Real (fun i : Fin 8 => fun j : Fin 8 => B i j) := by
  have hdet := det_ne_zero_of_totallyPositive_of_alternating_image_fin_eight hTP hAlt
  have hunit : IsUnit B := Matrix.isUnit_iff_isUnit_det B |>.mpr (IsUnit.mk0 B.det hdet)
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr hunit



private theorem cofactor_identity_fin_nine_eight
    {B : Matrix (Fin 9) (Fin 8) Real} (t : Fin 8) :
    (∑ p : Fin 9,
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) (fun j : Fin 8 => j)).det * B p t) = 0 := by
  classical
  let A : Matrix (Fin 9) (Fin 9) Real := fun i j =>
    if hj : j.val < 8 then B i ⟨j.val, hj⟩ else B i t
  have hcol_eq : forall i : Fin 9, A i (Fin.castSucc t) = A i (8 : Fin 9) := by
    intro i
    simp [A, Fin.castSucc]
  have hne : (Fin.castSucc t : Fin 9) ≠ (8 : Fin 9) := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.castSucc] at hv
    have ht : t.val < 8 := t.isLt
    omega
  have hdet_zero : A.det = 0 := Matrix.det_zero_of_column_eq hne hcol_eq
  have hdet_exp := Matrix.det_succ_column A (8 : Fin 9)
  rw [hdet_exp] at hdet_zero
  have hterm_eq : forall p : Fin 9,
      (-1 : Real) ^ p.val *
          (B.submatrix (Fin.succAbove p) (fun j : Fin 8 => j)).det * B p t =
        (-1 : Real) ^ ((p : Nat) + ((8 : Fin 9) : Nat)) *
          A p (8 : Fin 9) *
          (A.submatrix (Fin.succAbove p) (Fin.succAbove (8 : Fin 9))).det := by
    intro p
    have hA8 : A p (8 : Fin 9) = B p t := by
      simp [A]
    have hsub :
        A.submatrix (Fin.succAbove p) (Fin.succAbove (8 : Fin 9)) =
          B.submatrix (Fin.succAbove p) (fun j : Fin 8 => j) := by
      ext i j
      fin_cases j <;> simp [A, Fin.succAbove]
    rw [hA8, hsub]
    have hsign :
        (-1 : Real) ^ ((p : Nat) + ((8 : Fin 9) : Nat)) =
          (-1 : Real) ^ p.val := by
      rw [pow_add]
      norm_num
    rw [hsign]
    ring
  calc
    (∑ p : Fin 9,
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) (fun j : Fin 8 => j)).det * B p t)
        =
      ∑ p : Fin 9,
        (-1 : Real) ^ ((p : Nat) + ((8 : Fin 9) : Nat)) *
          A p (8 : Fin 9) *
          (A.submatrix (Fin.succAbove p) (Fin.succAbove (8 : Fin 9))).det := by
      refine Finset.sum_congr rfl ?_
      intro p _
      exact hterm_eq p
    _ = 0 := hdet_zero



private theorem not_strictlyAlternating_image_fin_nine_eight
    {B : Matrix (Fin 9) (Fin 8) Real} {x : Fin 8 -> Real}
    (hTP : IsTotallyPositiveFinite B) :
      ¬ IsStrictlyAlternatingFin
        (fun i : Fin 9 => ∑ j : Fin 8, B i j * x j) := by
  classical
  intro hAlt
  let u : Fin 9 -> Real := fun i => ∑ j : Fin 8, B i j * x j
  let d : Fin 9 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) (fun j : Fin 8 => j)).det
  have hminor_nonneg : forall p : Fin 9, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 8 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    have hcols : StrictMono (fun j : Fin 8 => j.val) := by
      intro a b hab
      exact hab
    dsimp [d]
    change 0 <= (Matrix.of fun i j => B (Fin.succAbove p i) j).det
    exact hTP 8 (Fin.succAbove p) (fun j : Fin 8 => j) hrows hcols
  let Btop : Matrix (Fin 8) (Fin 8) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 8 => ∑ j : Fin 8, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 9 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  have hd8_ne : d (8 : Fin 9) ≠ 0 := by
    have hLI :=
      linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_eight
        hTPtop hAlttop
    have hunit : IsUnit Btop := Matrix.linearIndependent_rows_iff_isUnit.mp hLI
    have hdetUnit : IsUnit Btop.det := (Matrix.isUnit_iff_isUnit_det Btop).mp hunit
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (8 : Fin 9)) (fun j : Fin 8 => j) = Btop := by
      ext i j
      fin_cases i <;> rfl
    have hd8_eq : d (8 : Fin 9) = Btop.det := by
      simp [d, hmatrix_eq]
    exact fun hd8_zero => hdetUnit.ne_zero (by simpa [← hd8_eq] using hd8_zero)
  have hd8_pos : 0 < d (8 : Fin 9) :=
    lt_of_le_of_ne (hminor_nonneg 8) (Ne.symm hd8_ne)
  have hidentity_cols :
      forall t : Fin 8,
        (∑ p : Fin 9, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    simpa [d] using cofactor_identity_fin_nine_eight (B := B) t
  have hidentity : (∑ p : Fin 9, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 9, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 9, ∑ j : Fin 8,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin 8, (∑ p : Fin 9,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 9, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_eight :
      0 < r * (((-1 : Real) ^ (8 : Fin 9).val * d (8 : Fin 9)) * u (8 : Fin 9)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (8 : Nat)) * u (8 : Fin 9)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (8 : Fin 9))
    have heq :
        r * (((-1 : Real) ^ (8 : Fin 9).val * d (8 : Fin 9)) * u (8 : Fin 9)) =
          (u 0 * (((-1 : Real) ^ (8 : Nat)) * u (8 : Fin 9))) * d (8 : Fin 9) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd8_pos
  have hsum_pos :
      0 < ∑ p : Fin 9, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 9)))
        (f := fun p : Fin 9 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (8 : Fin 9))
    exact lt_of_lt_of_le hcommon_pos_eight hle
  have hsum_rewrite :
      (∑ p : Fin 9, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 9, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem not_strictlyAlternating_image_of_cols_eq_eight :
  forall {n : Nat} {B : Matrix (Fin n) (Fin 8) Real} {x : Fin 8 -> Real},
    9 <= n ->
    IsTotallyPositiveFinite B ->
      ¬ IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin 8, B i j * x j) := by
  classical
  intro n B x hn hTP hAlt
  let B9 : Matrix (Fin 9) (Fin 8) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP9 : IsTotallyPositiveFinite B9 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt9 :
      IsStrictlyAlternatingFin (fun i : Fin 9 => ∑ j : Fin 8, B9 i j * x j) := by
    constructor
    · intro i
      simpa [B9] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < n := by omega
      simpa [B9] using hAlt.2 ⟨i.val, by omega⟩ hi'
  exact (not_strictlyAlternating_image_fin_nine_eight hTP9) hAlt9



private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_three_four
    {B : Matrix (Fin 3) (Fin 4) Real} {x : Fin 4 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 3 => ∑ j : Fin 4, B i j * x j)) :
      exists cols : Fin 3 -> Fin 4,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  by_contra hnone
  have hdet_zero_cols :
      forall cols : Fin 3 -> Fin 4, Function.Injective cols ->
        (Matrix.of fun i j => B i (cols j)).det = 0 := by
    intro cols hcols
    by_contra hdet
    exact hnone ⟨cols, hcols, hdet⟩
  let u0 : Real := ∑ j : Fin 4, B 0 j * x j
  let u1 : Real := ∑ j : Fin 4, B 1 j * x j
  let u2 : Real := ∑ j : Fin 4, B 2 j * x j
  rcases exists_positive_ordered_two_minor_first_two_rows_fin_three_four
      hTP hAlt with ⟨a, b, hab, hd_pos⟩
  let d : Real := B 0 a * B 1 b - B 0 b * B 1 a
  let e : Real := B 1 a * B 2 b - B 1 b * B 2 a
  let f : Real := B 0 a * B 2 b - B 0 b * B 2 a
  have hd_pos' : 0 < d := by simpa [d] using hd_pos
  have he_nonneg : 0 <= e := by
    let rows12 : Fin 2 -> Fin 3 := fun i => ⟨i.val + 1, by omega⟩
    let colsAB : Fin 2 -> Fin 4 := fun j => if j = 0 then a else b
    have hrows : StrictMono (fun i : Fin 2 => (rows12 i).val) := by
      intro i j hij
      exact Nat.add_lt_add_right hij 1
    have hcols : StrictMono (fun j : Fin 2 => (colsAB j).val) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [colsAB, hab] at hij ⊢
    have hminor := hTP 2 rows12 colsAB hrows hcols
    simpa [e, rows12, colsAB, Matrix.det_fin_two] using hminor
  have hf_nonneg : 0 <= f := by
    let rows02 : Fin 2 -> Fin 3 := fun i => if i = 0 then 0 else 2
    let colsAB : Fin 2 -> Fin 4 := fun j => if j = 0 then a else b
    have hrows : StrictMono (fun i : Fin 2 => (rows02 i).val) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [rows02] at hij ⊢
    have hcols : StrictMono (fun j : Fin 2 => (colsAB j).val) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [colsAB, hab] at hij ⊢
    have hminor := hTP 2 rows02 colsAB hrows hcols
    simpa [f, rows02, colsAB, Matrix.det_fin_two] using hminor
  have hrel_col : forall k : Fin 4, e * B 0 k - f * B 1 k + d * B 2 k = 0 := by
    intro k
    by_cases hka : k = a
    · subst k
      simp [d, e, f]
      ring
    by_cases hkb : k = b
    · subst k
      simp [d, e, f]
      ring
    let cols3 : Fin 3 -> Fin 4 := fun j => if j = 0 then a else if j = 1 then b else k
    have hcols3 : Function.Injective cols3 := by
      have hab_ne : a ≠ b := by
        intro h
        have hv : a.val = b.val := congrArg Fin.val h
        omega
      have hba_ne : b ≠ a := fun h => hab_ne h.symm
      have hak : a ≠ k := fun h => hka h.symm
      have hbk : b ≠ k := fun h => hkb h.symm
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [cols3, hab_ne, hba_ne, hka, hkb, hak, hbk] at hij ⊢
    have hdet0 := hdet_zero_cols cols3 hcols3
    have hdet_formula :
        (Matrix.of fun i j => B i (cols3 j)).det =
          e * B 0 k - f * B 1 k + d * B 2 k := by
      rw [Matrix.det_fin_three]
      simp [cols3, d, e, f]
      ring
    simpa [hdet_formula] using hdet0
  have hidentity : e * u0 - f * u1 + d * u2 = 0 := by
    have hsum_zero : (∑ k : Fin 4, (e * B 0 k - f * B 1 k + d * B 2 k) * x k) = 0 := by
      simp [hrel_col]
    have hrewrite :
        e * u0 - f * u1 + d * u2 =
          ∑ k : Fin 4, (e * B 0 k - f * B 1 k + d * B 2 k) * x k := by
      simp [u0, u1, u2, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [hrewrite, hsum_zero]
  have h01neg : u0 * u1 < 0 := by
    simpa [u0, u1] using hAlt.2 0 (by norm_num)
  have h12neg : u1 * u2 < 0 := by
    simpa [u1, u2] using hAlt.2 1 (by norm_num)
  have hu1_ne : u1 ≠ 0 := by
    simpa [u1] using hAlt.1 1
  rcases lt_or_gt_of_ne hu1_ne.symm with hu1_pos | hu1_neg
  · have hu0_neg : u0 < 0 := by
      rcases mul_neg_iff.mp h01neg with h | h
      · exact False.elim (not_lt_of_ge hu1_pos.le h.2)
      · exact h.1
    have hu2_neg : u2 < 0 := by
      rcases mul_neg_iff.mp h12neg with h | h
      · exact h.2
      · exact False.elim (not_lt_of_ge hu1_pos.le h.1)
    have hterm0 : e * u0 <= 0 := mul_nonpos_of_nonneg_of_nonpos he_nonneg hu0_neg.le
    have hterm1 : -f * u1 <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hf_nonneg) hu1_pos.le
    have hterm2 : d * u2 < 0 := mul_neg_of_pos_of_neg hd_pos' hu2_neg
    have hsum_neg : e * u0 - f * u1 + d * u2 < 0 := by
      nlinarith
    rw [hidentity] at hsum_neg
    linarith
  · have hu0_pos : 0 < u0 := by
      rcases mul_neg_iff.mp h01neg with h | h
      · exact h.1
      · exact False.elim (not_lt_of_ge hu1_neg.le h.2)
    have hu2_pos : 0 < u2 := by
      rcases mul_neg_iff.mp h12neg with h | h
      · exact False.elim (not_lt_of_ge hu1_neg.le h.1)
      · exact h.2
    have hterm0 : 0 <= e * u0 := mul_nonneg he_nonneg hu0_pos.le
    have hterm1 : 0 <= -f * u1 := by
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hf_nonneg) hu1_neg.le
    have hterm2 : 0 < d * u2 := mul_pos hd_pos' hu2_pos
    have hsum_pos : 0 < e * u0 - f * u1 + d * u2 := by
      nlinarith
    rw [hidentity] at hsum_pos
    linarith



private theorem exists_nonzero_adjugate_col_three_of_alternating_image_fin_four
    {B : Matrix (Fin 4) (Fin 4) Real} {x : Fin 4 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 4 => ∑ j : Fin 4, B i j * x j)) :
    exists q : Fin 4, B.adjugate q 3 ≠ 0 := by
  classical
  let Btop : Matrix (Fin 3) (Fin 4) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 3 => ∑ j : Fin 4, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 4 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_three_four
      hTPtop hAlttop with ⟨cols, hcols, hdet⟩
  let S : Finset (Fin 4) := Finset.image cols Finset.univ
  have hS_card : S.card = 3 := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin 3))) hcols
  have hS_lt_univ : S.card < (Finset.univ : Finset (Fin 4)).card := by
    simp [hS_card]
  rcases Finset.exists_mem_notMem_of_card_lt_card hS_lt_univ with ⟨q, _hqmem, hqnot⟩
  refine ⟨q, ?_⟩
  have hcols_ne_q : forall j : Fin 3, cols j ≠ q := by
    intro j hj
    exact hqnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩)
  let colsSub : Fin 3 -> {j : Fin 4 // j ≠ q} :=
    fun j => ⟨cols j, hcols_ne_q j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcard_sub : Fintype.card {j : Fin 4 // j ≠ q} = 3 := by
    simp
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hcard_sub]⟩
  let colsEquiv : Fin 3 ≃ {j : Fin 4 // j ≠ q} :=
    Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin 3) := colsEquiv.trans (finSuccAboveEquiv q).symm
  have hsucc_sigma : forall j : Fin 3, q.succAbove (sigma j) = cols j := by
    intro j
    have hsub : finSuccAboveEquiv q (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin 3) (Fin 3) Real :=
    B.submatrix (Fin.succAbove (3 : Fin 4)) (Fin.succAbove q)
  have hmatrix_eq :
      M.submatrix id sigma = Matrix.of fun i j => Btop i (cols j) := by
    ext i j
    fin_cases i
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 0 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 1 c) (hsucc_sigma j)
    · simpa [M, Btop, Fin.succAbove] using congrArg (fun c => B 2 c) (hsucc_sigma j)
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  have hadj_formula :
      B.adjugate q (3 : Fin 4) =
        (-1 : Real) ^ ((3 : Fin 4).val + q.val) * M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [hadj_formula]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hM_ne



private theorem det_ne_zero_of_totallyPositive_of_alternating_image_fin_four
    {B : Matrix (Fin 4) (Fin 4) Real} {x : Fin 4 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 4 => ∑ j : Fin 4, B i j * x j)) :
    B.det ≠ 0 := by
  classical
  intro hdet_zero
  let u : Fin 4 -> Real := fun i => ∑ j : Fin 4, B i j * x j
  rcases exists_nonzero_adjugate_col_three_of_alternating_image_fin_four
      hTP hAlt with ⟨q, hq_ne⟩
  let r : Real := (-1 : Real) ^ q.val * u 0
  have hchecker :
      forall i : Fin 4,
        0 <= ((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i) := by
    intro i
    exact adjugate_checkerboard_nonneg_of_totallyPositive hTP i q
  have hcommon_nonneg :
      forall i : Fin 4, 0 <= r * (B.adjugate q i * u i) := by
    intro i
    have hsign : 0 < u 0 * (((-1 : Real) ^ i.val) * u i) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := i)
    have heq : r * (B.adjugate q i * u i) =
        (u 0 * (((-1 : Real) ^ i.val) * u i)) *
          (((-1 : Real) ^ (i.val + q.val)) * (B.adjugate q i)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real i.val with hi | hi <;>
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
      simp [hi, hq, mul_assoc, mul_comm]
    rw [heq]
    exact mul_nonneg hsign.le (hchecker i)
  have hcommon_pos_three : 0 < r * (B.adjugate q 3 * u 3) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (3 : Nat)) * u 3) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (3 : Fin 4))
    have hchecker_three_nonneg :
        0 <= ((-1 : Real) ^ ((3 : Fin 4).val + q.val)) * (B.adjugate q 3) :=
      hchecker 3
    have hchecker_three_ne :
        ((-1 : Real) ^ ((3 : Fin 4).val + q.val)) * (B.adjugate q 3) ≠ 0 := by
      exact mul_ne_zero
        (pow_ne_zero _ (by norm_num : (-1 : Real) ≠ 0)) hq_ne
    have hchecker_three_pos :
        0 < ((-1 : Real) ^ ((3 : Fin 4).val + q.val)) * (B.adjugate q 3) :=
      lt_of_le_of_ne hchecker_three_nonneg (Ne.symm hchecker_three_ne)
    have heq : r * (B.adjugate q 3 * u 3) =
        (u 0 * (((-1 : Real) ^ (3 : Nat)) * u 3)) *
          (((-1 : Real) ^ ((3 : Fin 4).val + q.val)) * (B.adjugate q 3)) := by
      dsimp [r]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
        simp [hq] <;> ring
    rw [heq]
    exact mul_pos hsign hchecker_three_pos
  have hsum_pos :
      0 < ∑ i : Fin 4, r * (B.adjugate q i * u i) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 4)))
        (f := fun i : Fin 4 => r * (B.adjugate q i * u i))
        (fun i _ => hcommon_nonneg i)
        (Finset.mem_univ (3 : Fin 4))
    exact lt_of_lt_of_le hcommon_pos_three hle
  have hu : u = B *ᵥ x := by
    ext i
    simp [u, Matrix.mulVec, dotProduct]
  have hvec : B.adjugate *ᵥ u = 0 := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet_zero]
    ext i
    simp
  have hsum_zero : (∑ i : Fin 4, B.adjugate q i * u i) = 0 := by
    have hqvec := congrFun hvec q
    simpa [Matrix.mulVec, dotProduct] using hqvec
  have hsum_rewrite :
      (∑ i : Fin 4, r * (B.adjugate q i * u i)) =
        r * (∑ i : Fin 4, B.adjugate q i * u i) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hsum_zero, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos


private theorem linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_four
    {B : Matrix (Fin 4) (Fin 4) Real} {x : Fin 4 -> Real}
    (hTP : IsTotallyPositiveFinite B)
    (hAlt : IsStrictlyAlternatingFin
      (fun i : Fin 4 => ∑ j : Fin 4, B i j * x j)) :
    LinearIndependent Real (fun i : Fin 4 => fun j : Fin 4 => B i j) := by
  have hdet := det_ne_zero_of_totallyPositive_of_alternating_image_fin_four hTP hAlt
  have hunit : IsUnit B := Matrix.isUnit_iff_isUnit_det B |>.mpr (IsUnit.mk0 B.det hdet)
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr hunit



private theorem cofactor_identity_fin_five_four
    {B : Matrix (Fin 5) (Fin 4) Real} (t : Fin 4) :
    (∑ p : Fin 5,
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) (fun j : Fin 4 => j)).det * B p t) = 0 := by
  classical
  let A : Matrix (Fin 5) (Fin 5) Real := fun i j =>
    if hj : j.val < 4 then B i ⟨j.val, hj⟩ else B i t
  have hcol_eq : forall i : Fin 5, A i (Fin.castSucc t) = A i (4 : Fin 5) := by
    intro i
    simp [A, Fin.castSucc]
  have hne : (Fin.castSucc t : Fin 5) ≠ (4 : Fin 5) := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.castSucc] at hv
    have ht : t.val < 4 := t.isLt
    omega
  have hdet_zero : A.det = 0 := Matrix.det_zero_of_column_eq hne hcol_eq
  have hdet_exp := Matrix.det_succ_column A (4 : Fin 5)
  rw [hdet_exp] at hdet_zero
  have hterm_eq : forall p : Fin 5,
      (-1 : Real) ^ p.val *
          (B.submatrix (Fin.succAbove p) (fun j : Fin 4 => j)).det * B p t =
        (-1 : Real) ^ ((p : Nat) + ((4 : Fin 5) : Nat)) *
          A p (4 : Fin 5) *
          (A.submatrix (Fin.succAbove p) (Fin.succAbove (4 : Fin 5))).det := by
    intro p
    have hA4 : A p (4 : Fin 5) = B p t := by
      simp [A]
    have hsub :
        A.submatrix (Fin.succAbove p) (Fin.succAbove (4 : Fin 5)) =
          B.submatrix (Fin.succAbove p) (fun j : Fin 4 => j) := by
      ext i j
      fin_cases j <;> simp [A, Fin.succAbove]
    rw [hA4, hsub]
    have hsign :
        (-1 : Real) ^ ((p : Nat) + ((4 : Fin 5) : Nat)) =
          (-1 : Real) ^ p.val := by
      rw [pow_add]
      norm_num
    rw [hsign]
    ring
  calc
    (∑ p : Fin 5,
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) (fun j : Fin 4 => j)).det * B p t)
        =
      ∑ p : Fin 5,
        (-1 : Real) ^ ((p : Nat) + ((4 : Fin 5) : Nat)) *
          A p (4 : Fin 5) *
          (A.submatrix (Fin.succAbove p) (Fin.succAbove (4 : Fin 5))).det := by
      refine Finset.sum_congr rfl ?_
      intro p _
      exact hterm_eq p
    _ = 0 := hdet_zero



private theorem not_strictlyAlternating_image_fin_five_four
    {B : Matrix (Fin 5) (Fin 4) Real} {x : Fin 4 -> Real}
    (hTP : IsTotallyPositiveFinite B) :
      ¬ IsStrictlyAlternatingFin
        (fun i : Fin 5 => ∑ j : Fin 4, B i j * x j) := by
  classical
  intro hAlt
  let u : Fin 5 -> Real := fun i => ∑ j : Fin 4, B i j * x j
  let d : Fin 5 -> Real :=
    fun p => (B.submatrix (Fin.succAbove p) (fun j : Fin 4 => j)).det
  have hminor_nonneg : forall p : Fin 5, 0 <= d p := by
    intro p
    have hrows : StrictMono (fun i : Fin 4 => ((Fin.succAbove p i).val)) := by
      intro a b hab
      exact Fin.strictMono_succAbove p hab
    have hcols : StrictMono (fun j : Fin 4 => j.val) := by
      intro a b hab
      exact hab
    dsimp [d]
    change 0 <= (Matrix.of fun i j => B (Fin.succAbove p i) j).det
    exact hTP 4 (Fin.succAbove p) (fun j : Fin 4 => j) hrows hcols
  let Btop : Matrix (Fin 4) (Fin 4) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTPtop : IsTotallyPositiveFinite Btop := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlttop :
      IsStrictlyAlternatingFin (fun i : Fin 4 => ∑ j : Fin 4, Btop i j * x j) := by
    constructor
    · intro i
      simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < 5 := by omega
      simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
  have hd4_ne : d (4 : Fin 5) ≠ 0 := by
    have hLI :=
      linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_four
        hTPtop hAlttop
    have hunit : IsUnit Btop := Matrix.linearIndependent_rows_iff_isUnit.mp hLI
    have hdetUnit : IsUnit Btop.det := (Matrix.isUnit_iff_isUnit_det Btop).mp hunit
    have hmatrix_eq :
        B.submatrix (Fin.succAbove (4 : Fin 5)) (fun j : Fin 4 => j) = Btop := by
      ext i j
      fin_cases i <;> rfl
    have hd4_eq : d (4 : Fin 5) = Btop.det := by
      simp [d, hmatrix_eq]
    exact fun hd4_zero => hdetUnit.ne_zero (by simpa [← hd4_eq] using hd4_zero)
  have hd4_pos : 0 < d (4 : Fin 5) :=
    lt_of_le_of_ne (hminor_nonneg 4) (Ne.symm hd4_ne)
  have hidentity_cols :
      forall t : Fin 4,
        (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * B p t) = 0 := by
    intro t
    simpa [d] using cofactor_identity_fin_five_four (B := B) t
  have hidentity : (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin 5, ∑ j : Fin 4,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin 4, (∑ p : Fin 5,
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hidentity_cols]
  let r : Real := u 0
  have hcommon_nonneg :
      forall p : Fin 5, 0 <= r * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : r * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hminor_nonneg p)
  have hcommon_pos_four :
      0 < r * (((-1 : Real) ^ (4 : Fin 5).val * d (4 : Fin 5)) * u (4 : Fin 5)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (4 : Nat)) * u (4 : Fin 5)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := (4 : Fin 5))
    have heq :
        r * (((-1 : Real) ^ (4 : Fin 5).val * d (4 : Fin 5)) * u (4 : Fin 5)) =
          (u 0 * (((-1 : Real) ^ (4 : Nat)) * u (4 : Fin 5))) * d (4 : Fin 5) := by
      dsimp [r]
      ring
    rw [heq]
    exact mul_pos hsign hd4_pos
  have hsum_pos :
      0 < ∑ p : Fin 5, r * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 5)))
        (f := fun p : Fin 5 => r * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (4 : Fin 5))
    exact lt_of_lt_of_le hcommon_pos_four hle
  have hsum_rewrite :
      (∑ p : Fin 5, r * (((-1 : Real) ^ p.val * d p) * u p)) =
        r * (∑ p : Fin 5, (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos



private theorem not_strictlyAlternating_image_of_cols_eq_four :
  forall {n : Nat} {B : Matrix (Fin n) (Fin 4) Real} {x : Fin 4 -> Real},
    5 <= n ->
    IsTotallyPositiveFinite B ->
      ¬ IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin 4, B i j * x j) := by
  classical
  intro n B x hn hTP hAlt
  let B5 : Matrix (Fin 5) (Fin 4) Real := fun i j => B ⟨i.val, by omega⟩ j
  have hTP5 : IsTotallyPositiveFinite B5 := by
    intro r rows cols hrows hcols
    exact hTP r
      (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
      cols
      (by
        intro p q hpq
        exact hrows hpq)
      hcols
  have hAlt5 :
      IsStrictlyAlternatingFin (fun i : Fin 5 => ∑ j : Fin 4, B5 i j * x j) := by
    constructor
    · intro i
      simpa [B5] using hAlt.1 ⟨i.val, by omega⟩
    · intro i hi
      have hi' : i.val + 1 < n := by omega
      simpa [B5] using hAlt.2 ⟨i.val, by omega⟩ hi'
  exact (not_strictlyAlternating_image_fin_five_four hTP5) hAlt5



theorem exists_nonzero_minor_of_linearIndependent_rows :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real},
    LinearIndependent Real (fun i : Fin n => fun j : Fin m => B i j) ->
      exists cols : Fin n -> Fin m,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  intro n m B hrows
  have hrank : B.rank = n := by
    simpa using (LinearIndependent.rank_matrix (M := B) hrows)
  have hdim : Module.finrank Real (Submodule.span Real (Set.range B.col)) = n := by
    rw [← Matrix.rank_eq_finrank_span_cols B, hrank]
  rcases Submodule.exists_fun_fin_finrank_span_eq Real (Set.range B.col) with
    ⟨f, hfmem, _hfspan, hfLI⟩
  let castIdx : Fin n -> Fin (Module.finrank Real (Submodule.span Real (Set.range B.col))) :=
    fun i => Fin.cast hdim.symm i
  let fN : Fin n -> (Fin n -> Real) := fun i => f (castIdx i)
  have hcast_inj : Function.Injective castIdx := by
    intro a b h
    exact Fin.ext (by simpa [castIdx] using congrArg Fin.val h)
  have hfNLI : LinearIndependent Real fN := hfLI.comp castIdx hcast_inj
  let cols : Fin n -> Fin m := fun i => Classical.choose (hfmem (castIdx i))
  have hcol_eq : forall i : Fin n, B.col (cols i) = fN i := by
    intro i
    exact Classical.choose_spec (hfmem (castIdx i))
  have hcolsLI : LinearIndependent Real (fun i : Fin n => B.col (cols i)) := by
    convert hfNLI using 1
    funext i
    exact hcol_eq i
  have hcolsLI' : LinearIndependent Real (fun j : Fin n => fun i : Fin n => B i (cols j)) := by
    convert hcolsLI using 2
    ext i
    rfl
  have hcols_inj : Function.Injective cols := by
    intro a b hab
    apply hcolsLI.injective
    ext i
    simp [Matrix.col, hab]
  let C : Matrix (Fin n) (Fin n) Real := Matrix.of fun i j => B i (cols j)
  have hCcols : LinearIndependent Real C.col := by
    change LinearIndependent Real (fun j : Fin n => fun i : Fin n => C i j)
    simpa [C] using hcolsLI'
  have hunit : IsUnit C := Matrix.linearIndependent_cols_iff_isUnit.mp hCcols
  have hdetUnit : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hunit
  refine ⟨cols, hcols_inj, ?_⟩
  simpa [C] using hdetUnit.ne_zero


private theorem linearIndependent_rows_of_exists_nonzero_minor :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real},
    (exists cols : Fin n -> Fin m,
      Function.Injective cols /\
      (Matrix.of fun i j => B i (cols j)).det ≠ 0) ->
      LinearIndependent Real (fun i : Fin n => fun j : Fin m => B i j) := by
  classical
  intro n m B hminor
  rcases hminor with ⟨cols, _hcols, hdet⟩
  let C : Matrix (Fin n) (Fin n) Real := Matrix.of fun i j => B i (cols j)
  have hunit : IsUnit C :=
    Matrix.isUnit_iff_isUnit_det C |>.mpr (IsUnit.mk0 C.det (by simpa [C] using hdet))
  have hLI_C : LinearIndependent Real (fun i : Fin n => fun j : Fin n => C i j) :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr hunit
  let restrictCols : (Fin m -> Real) →ₗ[Real] (Fin n -> Real) :=
    { toFun := fun row j => row (cols j)
      map_add' := by
        intro a b
        ext j
        rfl
      map_smul' := by
        intro a row
        ext j
        rfl }
  have hLI_image :
      LinearIndependent Real
        (fun i : Fin n => restrictCols (fun j : Fin m => B i j)) := by
    simpa [restrictCols, C] using hLI_C
  exact hLI_image.of_comp restrictCols



private theorem exists_positive_ordered_minor_first_rows_of_nonzero :
  forall {r m : Nat} {B : Matrix (Fin (r + 1)) (Fin m) Real}
    (_ : IsTotallyPositiveFinite B) {cols : Fin r -> Fin m},
      Function.Injective cols ->
      (Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols j)).det ≠ 0 ->
        exists colsOrd : Fin r -> Fin m,
          StrictMono (fun j => (colsOrd j).val) /\
            0 < (Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)).det := by
  classical
  intro r m B hTP cols hcols hdet
  let S : Finset (Fin m) := Finset.image cols Finset.univ
  have hS_card : S.card = r := by
    simpa [S] using Finset.card_image_of_injective
      (s := (Finset.univ : Finset (Fin r))) hcols
  let colsOrd : Fin r -> Fin m := fun j => S.orderEmbOfFin hS_card j
  have hcolsOrd_strict : StrictMono (fun j => (colsOrd j).val) := by
    intro a b hab
    exact (S.orderEmbOfFin hS_card).strictMono hab
  have hminor_nonneg :
      0 <= (Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)).det := by
    have hrows : StrictMono (fun i : Fin r => (⟨i.val, by omega⟩ : Fin (r + 1)).val) := by
      intro i j hij
      exact hij
    exact hTP r (fun i : Fin r => ⟨i.val, by omega⟩) colsOrd hrows hcolsOrd_strict
  have hcols_mem : forall j : Fin r, cols j ∈ S := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  let colsSub : Fin r -> S := fun j => ⟨cols j, hcols_mem j⟩
  have hcolsSub_inj : Function.Injective colsSub := by
    intro i j hij
    apply hcols
    exact congrArg Subtype.val hij
  have hcolsSub_bij : Function.Bijective colsSub :=
    (Fintype.bijective_iff_injective_and_card colsSub).2
      ⟨hcolsSub_inj, by simp [hS_card]⟩
  let colsEquiv : Fin r ≃ S := Equiv.ofBijective colsSub hcolsSub_bij
  let sigma : Equiv.Perm (Fin r) := colsEquiv.trans (S.orderIsoOfFin hS_card).symm
  have hcolsOrd_sigma : forall j : Fin r, colsOrd (sigma j) = cols j := by
    intro j
    have hsub : S.orderIsoOfFin hS_card (sigma j) = colsSub j := by
      simp [sigma, colsEquiv, colsSub]
    exact congrArg Subtype.val hsub
  let M : Matrix (Fin r) (Fin r) Real :=
    Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j)
  have hmatrix_eq :
      M.submatrix id sigma =
        Matrix.of fun i j => B ⟨i.val, by omega⟩ (cols j) := by
    ext i j
    simp [M, hcolsOrd_sigma j]
  have hperm_ne : (M.submatrix id sigma).det ≠ 0 := by
    simpa [hmatrix_eq] using hdet
  have hM_ne : M.det ≠ 0 := by
    intro hM_zero
    have hperm_zero : (M.submatrix id sigma).det = 0 := by
      rw [Matrix.det_permute', hM_zero, mul_zero]
    exact hperm_ne hperm_zero
  exact ⟨colsOrd, hcolsOrd_strict, lt_of_le_of_ne hminor_nonneg (Ne.symm hM_ne)⟩

private theorem neg_one_pow_mul_add_cancel (a b : Nat) :
    (-1 : Real) ^ b * ((-1 : Real) ^ (a + b)) = (-1 : Real) ^ a := by
  rw [pow_add]
  rcases neg_one_pow_eq_or Real b with hb | hb
  · simp [hb]
  · simp [hb]




private theorem cofactor_relation_of_vanishing_maximal_minors :
  forall {r m : Nat} {B : Matrix (Fin (r + 1)) (Fin m) Real}
    {cols : Fin r -> Fin m},
      Function.Injective cols ->
      (forall colsAll : Fin (r + 1) -> Fin m,
        Function.Injective colsAll ->
          (Matrix.of fun i j => B i (colsAll j)).det = 0) ->
      forall t : Fin m,
        (∑ p : Fin (r + 1),
          (-1 : Real) ^ p.val *
            (B.submatrix (Fin.succAbove p) cols).det * B p t) = 0 := by
  classical
  intro r m B cols hcols hdet_zero_cols t
  let last : Fin (r + 1) := Fin.last r
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) Real := fun i j =>
    if hj : j.val < r then B i (cols ⟨j.val, hj⟩) else B i t
  let S : Finset (Fin m) := Finset.image cols Finset.univ
  have hdetA_zero : A.det = 0 := by
    by_cases htS : t ∈ S
    · rcases Finset.mem_image.mp htS with ⟨j0, _hj0mem, hj0⟩
      have hcol_eq : forall i : Fin (r + 1), A i (Fin.castSucc j0) = A i last := by
        intro i
        simp [A, last, Fin.castSucc, hj0]
      have hne : (Fin.castSucc j0 : Fin (r + 1)) ≠ last := by
        intro h
        have hv := congrArg Fin.val h
        simp [last, Fin.castSucc] at hv
        have hj0lt := j0.isLt
        omega
      exact Matrix.det_zero_of_column_eq hne hcol_eq
    · let colsAll : Fin (r + 1) -> Fin m := fun j =>
        if hj : j.val < r then cols ⟨j.val, hj⟩ else t
      have hcolsAll : Function.Injective colsAll := by
        intro i j hij
        by_cases hi : i.val < r
        · by_cases hj : j.val < r
          · have hcols_eq : cols ⟨i.val, hi⟩ = cols ⟨j.val, hj⟩ := by
              simpa [colsAll, hi, hj] using hij
            have hidx : (⟨i.val, hi⟩ : Fin r) = ⟨j.val, hj⟩ :=
              hcols hcols_eq
            exact Fin.ext (by simpa using congrArg Fin.val hidx)
          · have hit : cols ⟨i.val, hi⟩ = t := by
              simpa [colsAll, hi, hj] using hij
            exact False.elim
              (htS (Finset.mem_image.mpr
                ⟨⟨i.val, hi⟩, Finset.mem_univ _, hit⟩))
        · by_cases hj : j.val < r
          · have htj : t = cols ⟨j.val, hj⟩ := by
              simpa [colsAll, hi, hj] using hij
            exact False.elim
              (htS (Finset.mem_image.mpr
                ⟨⟨j.val, hj⟩, Finset.mem_univ _, htj.symm⟩))
          · exact Fin.ext (by omega)
      have hdet0 := hdet_zero_cols colsAll hcolsAll
      have hA_eq : A = Matrix.of fun i j => B i (colsAll j) := by
        ext i j
        by_cases hj : j.val < r <;> simp [A, colsAll, hj]
      rw [hA_eq]
      exact hdet0
  have hdet_exp := Matrix.det_succ_column A last
  rw [hdet_exp] at hdetA_zero
  let factor : Real := (-1 : Real) ^ r
  have hterm_eq : forall p : Fin (r + 1),
      (-1 : Real) ^ p.val *
          (B.submatrix (Fin.succAbove p) cols).det * B p t =
        factor *
          ((-1 : Real) ^ ((p : Nat) + (last : Nat)) *
            A p last *
            (A.submatrix (Fin.succAbove p) (Fin.succAbove last)).det) := by
    intro p
    have hA_last : A p last = B p t := by
      simp [A, last]
    have hsub :
        A.submatrix (Fin.succAbove p) (Fin.succAbove last) =
          B.submatrix (Fin.succAbove p) cols := by
      ext i j
      simp [A, last, Fin.succAbove_last]
    rw [hA_last, hsub]
    have hlast_val : (last : Nat) = r := by simp [last]
    rw [hlast_val]
    have hpow :
        factor * ((-1 : Real) ^ ((p : Nat) + r)) = (-1 : Real) ^ p.val := by
      simpa [factor] using neg_one_pow_mul_add_cancel p.val r
    rw [← hpow]
    ring
  calc
    (∑ p : Fin (r + 1),
      (-1 : Real) ^ p.val *
        (B.submatrix (Fin.succAbove p) cols).det * B p t)
        =
      ∑ p : Fin (r + 1),
        factor *
          ((-1 : Real) ^ ((p : Nat) + (last : Nat)) *
            A p last *
            (A.submatrix (Fin.succAbove p) (Fin.succAbove last)).det) := by
      refine Finset.sum_congr rfl ?_
      intro p _
      exact hterm_eq p
    _ = factor *
        (∑ p : Fin (r + 1),
          (-1 : Real) ^ ((p : Nat) + (last : Nat)) *
            A p last *
            (A.submatrix (Fin.succAbove p) (Fin.succAbove last)).det) := by
      rw [Finset.mul_sum]
    _ = 0 := by
      rw [hdetA_zero, mul_zero]




private theorem contradiction_of_positive_cofactor_relation :
  forall {r m : Nat} {B : Matrix (Fin (r + 1)) (Fin m) Real} {x : Fin m -> Real}
    {d : Fin (r + 1) -> Real},
      IsStrictlyAlternatingFin (fun i : Fin (r + 1) => ∑ j : Fin m, B i j * x j) ->
      (forall p : Fin (r + 1), 0 <= d p) ->
      0 < d (Fin.last r) ->
      (forall t : Fin m,
        (∑ p : Fin (r + 1), (-1 : Real) ^ p.val * d p * B p t) = 0) ->
      False := by
  classical
  intro r m B x d hAlt hnonneg hdlast_pos hcols
  let u : Fin (r + 1) -> Real := fun i => ∑ j : Fin m, B i j * x j
  have hidentity : (∑ p : Fin (r + 1), (-1 : Real) ^ p.val * d p * u p) = 0 := by
    calc
      (∑ p : Fin (r + 1), (-1 : Real) ^ p.val * d p * u p)
          = ∑ p : Fin (r + 1), ∑ j : Fin m,
              ((-1 : Real) ^ p.val * d p * B p j) * x j := by
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [u, Finset.mul_sum, mul_assoc]
      _ = ∑ j : Fin m, (∑ p : Fin (r + 1),
              (-1 : Real) ^ p.val * d p * B p j) * x j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.sum_mul]
      _ = 0 := by
        simp [hcols]
  let c : Real := u 0
  have hcommon_nonneg :
      forall p : Fin (r + 1), 0 <= c * (((-1 : Real) ^ p.val * d p) * u p) := by
    intro p
    have hsign : 0 < u 0 * (((-1 : Real) ^ p.val) * u p) := by
      simpa [u] using strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have heq : c * (((-1 : Real) ^ p.val * d p) * u p) =
        (u 0 * (((-1 : Real) ^ p.val) * u p)) * d p := by
      dsimp [c]
      ring
    rw [heq]
    exact mul_nonneg hsign.le (hnonneg p)
  have hcommon_pos_last :
      0 < c * (((-1 : Real) ^ (Fin.last r).val * d (Fin.last r)) * u (Fin.last r)) := by
    have hsign : 0 < u 0 * (((-1 : Real) ^ (Fin.last r).val) * u (Fin.last r)) := by
      simpa [u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := Fin.last r)
    have heq :
        c * (((-1 : Real) ^ (Fin.last r).val * d (Fin.last r)) * u (Fin.last r)) =
          (u 0 * (((-1 : Real) ^ (Fin.last r).val) * u (Fin.last r))) *
            d (Fin.last r) := by
      dsimp [c]
      ring
    rw [heq]
    exact mul_pos hsign hdlast_pos
  have hsum_pos :
      0 < ∑ p : Fin (r + 1), c * (((-1 : Real) ^ p.val * d p) * u p) := by
    have hle :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin (r + 1))))
        (f := fun p : Fin (r + 1) => c * (((-1 : Real) ^ p.val * d p) * u p))
        (fun p _ => hcommon_nonneg p)
        (Finset.mem_univ (Fin.last r))
    exact lt_of_lt_of_le hcommon_pos_last hle
  have hsum_rewrite :
      (∑ p : Fin (r + 1), c * (((-1 : Real) ^ p.val * d p) * u p)) =
        c * (∑ p : Fin (r + 1), (-1 : Real) ^ p.val * d p * u p) := by
    rw [Finset.mul_sum]
  rw [hsum_rewrite, hidentity, mul_zero] at hsum_pos
  exact (lt_irrefl (0 : Real)) hsum_pos




private theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image_induction :
  forall (n : Nat) {m : Nat} {B : Matrix (Fin n) (Fin m) Real} {x : Fin m -> Real},
    IsTotallyPositiveFinite B ->
    IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin m, B i j * x j) ->
      exists cols : Fin n -> Fin m,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  intro n
  induction n with
  | zero =>
      intro m B x _hTP _hAlt
      refine ⟨fun i : Fin 0 => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp
  | succ n ih =>
      intro m B x hTP hAlt
      cases n with
      | zero =>
          have hsum_ne :
              (∑ j : Fin m, B 0 j * x j) ≠ 0 := by
            simpa using hAlt.1 0
          have hex : exists j : Fin m, B 0 j * x j ≠ 0 := by
            by_contra hnone
            have hzero : forall j : Fin m, B 0 j * x j = 0 := by
              intro j
              by_contra hj
              exact hnone ⟨j, hj⟩
            have hsum_zero : (∑ j : Fin m, B 0 j * x j) = 0 := by
              simp [hzero]
            exact hsum_ne hsum_zero
          rcases hex with ⟨j0, hj0⟩
          have hB0 : B 0 j0 ≠ 0 := by
            intro hB
            exact hj0 (by simp [hB])
          refine ⟨fun _ : Fin 1 => j0, ?_, ?_⟩
          · intro a b _hab
            exact Fin.ext (by omega)
          · simpa using hB0
      | succ r =>
          let Btop : Matrix (Fin (r + 1)) (Fin m) Real :=
            fun i j => B ⟨i.val, by omega⟩ j
          have hTPtop : IsTotallyPositiveFinite Btop := by
            intro k rows cols hrows hcols
            exact hTP k
              (fun p => ⟨(rows p).val, by have := (rows p).isLt; omega⟩)
              cols
              (by
                intro p q hpq
                exact hrows hpq)
              hcols
          have hAlttop :
              IsStrictlyAlternatingFin
                (fun i : Fin (r + 1) => ∑ j : Fin m, Btop i j * x j) := by
            constructor
            · intro i
              simpa [Btop] using hAlt.1 ⟨i.val, by omega⟩
            · intro i hi
              have hi' : i.val + 1 < r + 2 := by omega
              simpa [Btop] using hAlt.2 ⟨i.val, by omega⟩ hi'
          rcases ih (m := m) (B := Btop) (x := x) hTPtop hAlttop with
            ⟨colsTop, hcolsTop, hdetTop⟩
          rcases exists_positive_ordered_minor_first_rows_of_nonzero
              (B := B) hTP hcolsTop (by simpa [Btop] using hdetTop) with
            ⟨colsOrd, hcolsOrd_strict, hdetOrd_pos⟩
          have hcolsOrd_inj : Function.Injective colsOrd := by
            intro a b hab
            exact hcolsOrd_strict.injective (congrArg Fin.val hab)
          by_contra hnone
          have hdet_zero_cols :
              forall colsAll : Fin (r + 2) -> Fin m, Function.Injective colsAll ->
                (Matrix.of fun i j => B i (colsAll j)).det = 0 := by
            intro colsAll hcolsAll
            by_contra hdet
            exact hnone ⟨colsAll, hcolsAll, hdet⟩
          let d : Fin (r + 2) -> Real :=
            fun p => (B.submatrix (Fin.succAbove p) colsOrd).det
          have hminor_nonneg : forall p : Fin (r + 2), 0 <= d p := by
            intro p
            have hrows : StrictMono (fun i : Fin (r + 1) => ((Fin.succAbove p i).val)) := by
              intro a b hab
              exact Fin.strictMono_succAbove p hab
            exact hTP (r + 1) (Fin.succAbove p) colsOrd hrows hcolsOrd_strict
          have hdlast_pos : 0 < d (Fin.last (r + 1)) := by
            have hmatrix_eq :
                B.submatrix (Fin.succAbove (Fin.last (r + 1))) colsOrd =
                  Matrix.of fun i j => B ⟨i.val, by omega⟩ (colsOrd j) := by
              ext i j
              simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last]
              apply congrArg (fun q => B q (colsOrd j))
              exact Fin.ext (by simp [Fin.castSucc, Fin.castAdd])
            change 0 < (B.submatrix (Fin.succAbove (Fin.last (r + 1))) colsOrd).det
            rw [hmatrix_eq]
            exact hdetOrd_pos
          have hidentity_cols :
              forall t : Fin m,
                (∑ p : Fin (r + 2), (-1 : Real) ^ p.val * d p * B p t) = 0 := by
            intro t
            simpa [d] using
              cofactor_relation_of_vanishing_maximal_minors
                (cols := colsOrd) hcolsOrd_inj hdet_zero_cols t
          exact contradiction_of_positive_cofactor_relation
            (B := B) (x := x) (d := d) hAlt hminor_nonneg hdlast_pos hidentity_cols




theorem linearIndependent_rows_of_totallyPositive_of_alternating_image_core :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real} {x : Fin m -> Real},
    3 <= n ->
    3 <= m ->
    m <= n ->
    4 <= n ->
    9 <= m ->
    9 <= n ->
    IsTotallyPositiveFinite B ->
    IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin m, B i j * x j) ->
      LinearIndependent Real (fun i : Fin n => fun j : Fin m => B i j) := by
  intro n m B x _hn3 _hm3 _hmle _hn4 _hm9 _hn9 hTP hAlt
  exact linearIndependent_rows_of_exists_nonzero_minor
    (exists_nonzero_minor_of_totallyPositive_of_alternating_image_induction
      n (m := m) (B := B) (x := x) hTP hAlt)




theorem exists_nonzero_minor_of_totallyPositive_of_alternating_image :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real} {x : Fin m -> Real},
    m <= n ->
    IsTotallyPositiveFinite B ->
    IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin m, B i j * x j) ->
      exists cols : Fin n -> Fin m,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 := by
  classical
  intro n m B x hmle hTP hAlt
  by_cases hcore : 3 <= n
  · by_cases hm2 : 2 <= m
    · by_cases hm_eq_two : m = 2
      · subst m
        exact False.elim
          (not_strictlyAlternating_image_of_cols_eq_two hcore hTP hAlt)
      · have hm3 : 3 <= m := by omega
        by_cases hn3 : n = 3
        · subst n
          have hm3eq : m = 3 := by omega
          subst m
          exact exists_nonzero_minor_of_linearIndependent_rows
            (linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_three
              hTP hAlt)
        · have hn4 : 4 <= n := by omega
          by_cases hm_eq_three : m = 3
          · subst m
            exact False.elim
              (not_strictlyAlternating_image_of_cols_eq_three hn4 hTP hAlt)
          · have hm4 : 4 <= m := by omega
            by_cases hn_eq_four : n = 4
            · subst n
              have hm4eq : m = 4 := by omega
              subst m
              exact exists_nonzero_minor_of_linearIndependent_rows
                (linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_four
                  hTP hAlt)
            · have hn5 : 5 <= n := by omega
              by_cases hm_eq_four : m = 4
              · subst m
                exact False.elim
                  (not_strictlyAlternating_image_of_cols_eq_four hn5 hTP hAlt)
              · have hm5 : 5 <= m := by omega
                by_cases hn_eq_five : n = 5
                · subst n
                  have hm5eq : m = 5 := by omega
                  subst m
                  exact exists_nonzero_minor_of_linearIndependent_rows
                    (linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_five
                      hTP hAlt)
                · have hn6 : 6 <= n := by omega
                  by_cases hm_eq_five : m = 5
                  · subst m
                    exact False.elim
                      (not_strictlyAlternating_image_of_cols_eq_five hn6 hTP hAlt)
                  · have hm6 : 6 <= m := by omega
                    by_cases hn_eq_six : n = 6
                    · subst n
                      have hm6eq : m = 6 := by omega
                      subst m
                      exact exists_nonzero_minor_of_linearIndependent_rows
                        (linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_six
                          hTP hAlt)
                    · have hn7 : 7 <= n := by omega
                      by_cases hm_eq_six : m = 6
                      · subst m
                        exact False.elim
                          (not_strictlyAlternating_image_of_cols_eq_six hn7 hTP hAlt)
                      · have hm7 : 7 <= m := by omega
                        by_cases hn_eq_seven : n = 7
                        · subst n
                          have hm7eq : m = 7 := by omega
                          subst m
                          exact exists_nonzero_minor_of_linearIndependent_rows
                            (linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_seven
                              hTP hAlt)
                        · have hn8 : 8 <= n := by omega
                          by_cases hm_eq_seven : m = 7
                          · subst m
                            exact False.elim
                              (not_strictlyAlternating_image_of_cols_eq_seven hn8 hTP hAlt)
                          · have hm8 : 8 <= m := by omega
                            by_cases hn_eq_eight : n = 8
                            · subst n
                              have hm8eq : m = 8 := by omega
                              subst m
                              exact exists_nonzero_minor_of_linearIndependent_rows
                                (linearIndependent_rows_of_totallyPositive_of_alternating_image_fin_eight
                                  hTP hAlt)
                            · have hn9 : 9 <= n := by omega
                              by_cases hm_eq_eight : m = 8
                              · subst m
                                exact False.elim
                                  (not_strictlyAlternating_image_of_cols_eq_eight hn9 hTP hAlt)
                              · have hm9 : 9 <= m := by omega
                                exact exists_nonzero_minor_of_linearIndependent_rows
                                  (linearIndependent_rows_of_totallyPositive_of_alternating_image_core
                                    hcore hm3 hmle hn4 hm9 hn9 hTP hAlt)
    · exact False.elim
        (not_strictlyAlternating_image_of_cols_lt_two
          (by omega) (Nat.lt_of_not_ge hm2) hTP hAlt)
  · have hnlt : n < 3 := Nat.lt_of_not_ge hcore
    interval_cases n
    · refine ⟨fun i : Fin 0 => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp
    · have hsum_ne :
          (∑ j : Fin m, B 0 j * x j) ≠ 0 := by
        simpa using hAlt.1 0
      have hex : exists j : Fin m, B 0 j * x j ≠ 0 := by
        by_contra hnone
        have hzero : forall j : Fin m, B 0 j * x j = 0 := by
          intro j
          by_contra hj
          exact hnone ⟨j, hj⟩
        have hsum_zero : (∑ j : Fin m, B 0 j * x j) = 0 := by
          simp [hzero]
        exact hsum_ne hsum_zero
      rcases hex with ⟨j0, hj0⟩
      have hB0 : B 0 j0 ≠ 0 := by
        intro hB
        exact hj0 (by simp [hB])
      refine ⟨fun _ : Fin 1 => j0, ?_, ?_⟩
      · intro a b _hab
        exact Subsingleton.elim a b
      · simpa using hB0
    · exact exists_nonzero_minor_of_totallyPositive_of_alternating_image_fin_two
        hTP hAlt



theorem rank_eq_rows_of_totallyPositive_of_alternating_image :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real} {x : Fin m -> Real},
    m <= n ->
    IsTotallyPositiveFinite B ->
    IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin m, B i j * x j) ->
      LinearIndependent Real (fun i : Fin n => fun j : Fin m => B i j) := by
  intro n m B x hmle hTP hAlt
  rcases exists_nonzero_minor_of_totallyPositive_of_alternating_image hmle hTP hAlt with
    ⟨cols, _hcolsInj, hdet⟩
  let C : Matrix (Fin n) (Fin n) Real := Matrix.of fun i j => B i (cols j)
  have hCrows : LinearIndependent Real C.row := by
    apply Matrix.linearIndependent_rows_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det C).mpr
    exact IsUnit.mk0 C.det (by simpa [C] using hdet)
  let P : (Fin m -> Real) →ₗ[Real] (Fin n -> Real) := LinearMap.funLeft Real Real cols
  have hcomp : (P ∘ fun i : Fin n => fun j : Fin m => B i j) = C.row := by
    funext i j
    rfl
  have hProws : LinearIndependent Real (P ∘ fun i : Fin n => fun j : Fin m => B i j) := by
    simpa [hcomp]
  exact LinearIndependent.of_comp P hProws



theorem inverse_checkerboard_nonneg_of_totallyPositive :
  forall {n : Nat} {B : Matrix (Fin n) (Fin n) Real},
    IsTotallyPositiveFinite B -> B.det ≠ 0 ->
      0 < B.det /\
        forall p q : Fin n,
          0 <= ((-1 : Real) ^ (p.val + q.val)) * (B⁻¹ q p) := by
  intro n B hTP hdet
  have hstrict_id : StrictMono (fun i : Fin n => i.val) := by
    intro a b h
    exact h
  have hdetNonneg : 0 <= B.det := by
    change 0 <= (Matrix.of fun p q => B p q).det
    exact hTP n (fun i : Fin n => i) (fun i : Fin n => i) hstrict_id hstrict_id
  have hdetPos : 0 < B.det := lt_of_le_of_ne hdetNonneg (Ne.symm hdet)
  constructor
  · exact hdetPos
  · intro p q
    cases n with
    | zero => exact Fin.elim0 p
    | succ k =>
        rw [Matrix.inv_def, Ring.inverse_eq_inv]
        rw [Matrix.smul_apply]
        change 0 <= (-1 : Real) ^ (p.val + q.val) * (B.det⁻¹ * B.adjugate q p)
        rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
        have hrows : StrictMono (fun a : Fin k => ((p.succAbove a).val)) := by
          intro a b hab
          exact Fin.strictMono_succAbove p hab
        have hcols : StrictMono (fun a : Fin k => ((q.succAbove a).val)) := by
          intro a b hab
          exact Fin.strictMono_succAbove q hab
        have hminor : 0 <= (B.submatrix p.succAbove q.succAbove).det :=
          hTP k p.succAbove q.succAbove hrows hcols
        have hinvNonneg : 0 <= B.det⁻¹ := inv_nonneg.mpr hdetPos.le
        have heq : (-1 : Real) ^ (p.val + q.val) *
              (B.det⁻¹ * ((-1 : Real) ^ (p.val + q.val) *
                (B.submatrix p.succAbove q.succAbove).det)) =
            B.det⁻¹ * (B.submatrix p.succAbove q.succAbove).det := by
          rcases neg_one_pow_eq_or Real (p.val + q.val) with hs | hs <;>
            simp [hs]
        rw [heq]
        exact mul_nonneg hinvNonneg hminor



theorem abs_inverse_mul_alternating_eq_abs :
  forall {n : Nat} {B : Matrix (Fin n) (Fin n) Real} {w : Fin n -> Real},
    IsTotallyPositiveFinite B -> B.det ≠ 0 ->
    IsStrictlyAlternatingFin (fun i : Fin n => ∑ j : Fin n, B i j * w j) ->
      forall q : Fin n,
        (∑ p : Fin n,
          |B⁻¹ q p| * |(∑ j : Fin n, B p j * w j)|) = |w q| := by
  intro n B w hTP hdet hAlt q
  let u : Fin n -> Real := fun i => ∑ j : Fin n, B i j * w j
  change (∑ p : Fin n, |B⁻¹ q p| * |u p|) = |w q|
  rcases inverse_checkerboard_nonneg_of_totallyPositive hTP hdet with ⟨_hdetPos, hchecker⟩
  let z0 : Fin n := ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le q.val) q.isLt⟩
  let v : Fin n -> Real := fun i => (-1 : Real) ^ i.val * u i
  let r : Real := (-1 : Real) ^ q.val * v z0
  have hr : r ≠ 0 := by
    have hsign_ne : (-1 : Real) ^ q.val ≠ 0 := pow_ne_zero q.val (by norm_num)
    have hv0_ne : v z0 ≠ 0 := by
      simp [v, z0, u, hAlt.1 z0]
    exact mul_ne_zero hsign_ne hv0_ne
  have hcommon : forall p : Fin n, 0 <= r * (B⁻¹ q p * u p) := by
    intro p
    have hsign : 0 < v z0 * v p := by
      simpa [v, z0, u] using
        strictlyAlternatingFin_checkerboard_from_zero_pos hAlt (p := p)
    have hchecker_p : 0 <= ((-1 : Real) ^ (p.val + q.val)) * (B⁻¹ q p) :=
      hchecker p q
    have heq : r * (B⁻¹ q p * u p) =
        (v z0 * v p) * (((-1 : Real) ^ (p.val + q.val)) * (B⁻¹ q p)) := by
      dsimp [r, v]
      rw [pow_add]
      rcases neg_one_pow_eq_or Real p.val with hp | hp <;>
      rcases neg_one_pow_eq_or Real q.val with hq | hq <;>
      simp [hp, hq, mul_assoc, mul_left_comm, mul_comm]
    rw [heq]
    exact mul_nonneg hsign.le hchecker_p
  have habs := sum_abs_eq_abs_sum_of_common_sign
    (fun p : Fin n => B⁻¹ q p * u p) hr hcommon
  have hvec : B⁻¹ *ᵥ u = w := by
    have hu : u = B *ᵥ w := by
      ext i
      simp [u, Matrix.mulVec, dotProduct]
    rw [hu]
    have hunit : IsUnit B.det := IsUnit.mk0 B.det hdet
    calc
      B⁻¹ *ᵥ (B *ᵥ w) = (B⁻¹ * B) *ᵥ w := by
        rw [Matrix.mulVec_mulVec]
      _ = 1 *ᵥ w := by rw [Matrix.nonsing_inv_mul B hunit]
      _ = w := by rw [Matrix.one_mulVec]
  have hq : (∑ p : Fin n, B⁻¹ q p * u p) = w q := by
    exact congrFun hvec q
  calc
    (∑ p : Fin n, |B⁻¹ q p| * |u p|)
        = ∑ p : Fin n, |B⁻¹ q p * u p| := by
          simp [abs_mul]
    _ = |∑ p : Fin n, B⁻¹ q p * u p| := habs
    _ = |w q| := by rw [hq]

end VendorE4
