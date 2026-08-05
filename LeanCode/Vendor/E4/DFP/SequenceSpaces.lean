import LeanCode.Vendor.E4.DFP.Defs

open scoped BigOperators
open Filter Topology

noncomputable section

namespace VendorE4


def intWindow (N : Nat) : Finset Int :=
  Finset.Icc (-(N : Int)) (N : Int)


theorem intWindow_mono :
  forall N : Nat, intWindow N <= intWindow (N + 1) := by
  intro N k hk
  rw [intWindow, Finset.mem_Icc] at hk ⊢
  constructor <;> omega


theorem intWindow_cover :
  forall k : Int, exists N : Nat, k ∈ intWindow N := by
  intro k
  refine ⟨k.natAbs, ?_⟩
  rw [intWindow, Finset.mem_Icc]
  constructor
  · have h : -k <= (k.natAbs : Int) := by
      simpa [Int.natAbs_neg] using (Int.le_natAbs (a := -k))
    omega
  · exact Int.le_natAbs


theorem intWindow_card :
  forall N : Nat, (intWindow N).card = 2 * N + 1 := by
  intro N
  rw [intWindow, Int.card_Icc]
  omega



theorem intWindow_orderEmbOfFin_eq :
  forall (N : Nat),
    (fun i : Fin ((intWindow N).card) =>
        (intWindow N).orderEmbOfFin rfl i) =
      fun i : Fin ((intWindow N).card) => (-(N : Int) + (i.val : Int)) := by
  intro N
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    simp only [intWindow, Finset.mem_Icc]
    have hi : i.val < (intWindow N).card := i.isLt
    have hcard : (intWindow N).card = 2 * N + 1 := intWindow_card N
    constructor <;> omega
  · intro a b hab
    simp at hab ⊢
    exact_mod_cast hab


theorem pairing_abs_le_mul_norm :
  forall {y s : Int -> Real}, IsBoundedSequence y -> IsL1Sequence s ->
    Summable (fun k : Int => |y k * s k|) := by
  intro y s hy hs
  rcases hy with ⟨M, hMpos, hM⟩
  exact (hs.mul_left M).of_nonneg_of_le
    (fun k => abs_nonneg (y k * s k))
    (fun k => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hM k) (abs_nonneg (s k)))




theorem pairing_row_eq_matVec :
  forall (G : Int -> Int -> Real) (y : Int -> Real) (i : Int),
    pairing y (fun j : Int => G i j) = MatVec G y i := by
  intro G y i
  simp [pairing, MatVec, mul_comm]



theorem uniformlyBoundedFromBelow_restrict_interval :
  forall {u : Int -> Real}, IsUniformlyBoundedFromBelow u ->
    forall (a : Int) (n : Nat),
      exists delta : Real, 0 < delta /\
        forall i : Fin n, delta <= |u (a + (i.val : Int))| := by
  intro u hbelow a n
  rcases hbelow with ⟨delta, hdelta_pos, hdelta⟩
  refine ⟨delta, hdelta_pos, ?_⟩
  intro i
  exact hdelta (a + (i.val : Int))


theorem truncation_l1_norm_le :
  forall (K : Finset Int) {s : Int -> Real}, IsL1Sequence s ->
    IsL1Sequence (truncation K s) /\
      l1Norm (truncation K s) <= l1Norm s := by
  intro K s hs
  have htrunc : IsL1Sequence (truncation K s) := by
    exact summable_of_hasFiniteSupport <|
      K.finite_toSet.subset (by
        intro k hk
        by_contra hkK
        have hkK' : k ∉ K := by
          simpa using hkK
        have hzero : |truncation K s k| = 0 := by
          simp [truncation, hkK']
        exact hk hzero)
  constructor
  · exact htrunc
  · exact Summable.tsum_le_tsum
      (fun k => by
        by_cases hk : k ∈ K
        · simp [truncation, hk]
        · simp [truncation, hk])
      htrunc hs



theorem sum_orderEmbOfFin_eq {α β : Type*} [LinearOrder α] [AddCommMonoid β]
    (S : Finset α) {k : Nat} (hS : S.card = k) (f : α -> β) :
    (∑ i : Fin k, f (S.orderEmbOfFin hS i)) = ∑ x ∈ S, f x := by
  classical
  have hsumImage :
      (Finset.image (S.orderEmbOfFin hS) Finset.univ).sum f =
        ∑ i : Fin k, f (S.orderEmbOfFin hS i) := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact (S.orderEmbOfFin hS).injective hab
  calc
    (∑ i : Fin k, f (S.orderEmbOfFin hS i))
        = (Finset.image (S.orderEmbOfFin hS) Finset.univ).sum f := hsumImage.symm
    _ = ∑ x ∈ S, f x := by
      change (Finset.image (S.orderEmbOfFin hS) Finset.univ).sum f = S.sum f
      exact congrArg (fun T : Finset α => T.sum f)
        (Finset.image_orderEmbOfFin_univ S hS)



theorem pairing_truncation_eq_sum_orderEmb
    (K : Finset Int) (x s : Int -> Real) :
    pairing x (truncation K s) =
      ∑ k : Fin K.card, x (K.orderEmbOfFin rfl k) * s (K.orderEmbOfFin rfl k) := by
  classical
  have htsum :
      (∑' j : Int, x j * truncation K s j) =
        ∑ j ∈ K, x j * truncation K s j := by
    exact tsum_eq_sum (s := K) (f := fun j : Int => x j * truncation K s j)
      (fun j hj => by
        simp [truncation, hj])
  have hsumK :
      (∑ j ∈ K, x j * truncation K s j) = ∑ j ∈ K, x j * s j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [truncation, hj]
  calc
    pairing x (truncation K s)
        = ∑ j ∈ K, x j * truncation K s j := htsum
    _ = ∑ j ∈ K, x j * s j := hsumK
    _ = ∑ k : Fin K.card, x (K.orderEmbOfFin rfl k) * s (K.orderEmbOfFin rfl k) := by
        exact (sum_orderEmbOfFin_eq K rfl (fun j : Int => x j * s j)).symm


theorem truncation_l1_tendsto :
  forall {K : Nat -> Finset Int} {s : Int -> Real},
    IsL1Sequence s ->
    (forall n : Nat, K n <= K (n + 1)) ->
    (forall k : Int, exists n : Nat, k ∈ K n) ->
      Filter.Tendsto (fun n : Nat => l1Norm (fun k => s k - truncation (K n) s k))
        Filter.atTop (nhds 0) := by
  intro K s _hs hmono hcover
  have hKmono : Monotone K := monotone_nat_of_le_succ hmono
  have hKtendsto : Filter.Tendsto K Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_finset_of_monotone hKmono hcover
  have htail :=
    (tendsto_tsum_compl_atTop_zero (fun k : Int => |s k|)).comp hKtendsto
  convert htail using 1
  ext n
  simp only [Function.comp_apply]
  rw [l1Norm]
  change (∑' k : Int, |s k - truncation (K n) s k|) =
    ∑' a : ((((K n : Finset Int) : Set Int)ᶜ) : Set Int), |s a|
  rw [tsum_subtype ((((K n : Finset Int) : Set Int)ᶜ) : Set Int)
    (fun k : Int => |s k|)]
  apply tsum_congr
  intro k
  by_cases hk : k ∈ K n
  · simp [truncation, hk]
  · have hkCompl : k ∈ ((K n : Set Int)ᶜ) := by
      simpa using hk
    simp [truncation, hk, hkCompl]



theorem abs_pairing_sub_pairing_truncation_le :
  forall (K : Finset Int) {x s : Int -> Real} {M : Real},
    0 <= M ->
    (forall k : Int, |x k| <= M) ->
    IsL1Sequence s ->
      |pairing x s - pairing x (truncation K s)| <=
        M * l1Norm (fun k : Int => s k - truncation K s k) := by
  intro K x s M _hM hx hs
  rcases truncation_l1_norm_le K hs with ⟨htrunc, _htrunc_le⟩
  let tail : Int -> Real := fun k => s k - truncation K s k
  have htail : IsL1Sequence tail := by
    exact (hs.add htrunc).of_nonneg_of_le
      (fun k => abs_nonneg (tail k))
      (fun k => by
        dsimp [tail]
        exact abs_sub (s k) (truncation K s k))
  have hprodS_abs : Summable (fun k : Int => |x k * s k|) := by
    exact (hs.mul_left M).of_nonneg_of_le
      (fun k => abs_nonneg (x k * s k))
      (fun k => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hx k) (abs_nonneg (s k)))
  have hprodT_abs : Summable (fun k : Int => |x k * truncation K s k|) := by
    exact (htrunc.mul_left M).of_nonneg_of_le
      (fun k => abs_nonneg (x k * truncation K s k))
      (fun k => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hx k) (abs_nonneg (truncation K s k)))
  have hprodTail_abs : Summable (fun k : Int => |x k * tail k|) := by
    exact (htail.mul_left M).of_nonneg_of_le
      (fun k => abs_nonneg (x k * tail k))
      (fun k => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hx k) (abs_nonneg (tail k)))
  have hprodS : Summable (fun k : Int => x k * s k) := by
    exact Summable.of_norm (by simpa [Real.norm_eq_abs] using hprodS_abs)
  have hprodT : Summable (fun k : Int => x k * truncation K s k) := by
    exact Summable.of_norm (by simpa [Real.norm_eq_abs] using hprodT_abs)
  have hdiff :
      pairing x s - pairing x (truncation K s) =
        ∑' k : Int, x k * tail k := by
    calc
      pairing x s - pairing x (truncation K s)
          = (∑' k : Int, x k * s k) -
              (∑' k : Int, x k * truncation K s k) := by
              rfl
      _ = ∑' k : Int, (x k * s k - x k * truncation K s k) := by
              exact (hprodS.tsum_sub hprodT).symm
      _ = ∑' k : Int, x k * tail k := by
              apply tsum_congr
              intro k
              simp [tail, mul_sub]
  calc
    |pairing x s - pairing x (truncation K s)|
        = ‖∑' k : Int, x k * tail k‖ := by
            rw [hdiff, Real.norm_eq_abs]
    _ <= ∑' k : Int, ‖x k * tail k‖ := by
            exact norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hprodTail_abs)
    _ = ∑' k : Int, |x k * tail k| := by
            simp [Real.norm_eq_abs]
    _ <= ∑' k : Int, M * |tail k| := by
            exact Summable.tsum_le_tsum
              (fun k => by
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_right (hx k) (abs_nonneg (tail k)))
              hprodTail_abs (htail.mul_left M)
    _ = M * l1Norm tail := by
            rw [Summable.tsum_mul_left M htail]
            rfl



theorem pairing_truncation_tendsto :
  forall {K : Nat -> Finset Int} {x s : Int -> Real},
    IsBoundedSequence x ->
    IsL1Sequence s ->
    (forall n : Nat, K n <= K (n + 1)) ->
    (forall k : Int, exists n : Nat, k ∈ K n) ->
      Filter.Tendsto (fun n : Nat => pairing x (truncation (K n) s))
        Filter.atTop (nhds (pairing x s)) := by
  intro K x s hx hs hmono hcover
  rcases hx with ⟨M, hMpos, hxM⟩
  have htail :=
    truncation_l1_tendsto (K := K) (s := s) hs hmono hcover
  have hright :
      Filter.Tendsto
        (fun n : Nat => M * l1Norm (fun k : Int => s k - truncation (K n) s k))
        Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto (fun _ : Nat => M) Filter.atTop (nhds M) :=
      tendsto_const_nhds
    have hmul := hconst.mul htail
    simpa using hmul
  apply tendsto_iff_dist_tendsto_zero.2
  exact squeeze_zero
    (fun n : Nat => dist_nonneg)
    (fun n : Nat => by
      have hle := abs_pairing_sub_pairing_truncation_le (K n)
        (le_of_lt hMpos) hxM hs
      simpa [Real.dist_eq, abs_sub_comm] using hle)
    hright



theorem row_pairing_truncation_tendsto_of_uniformlySummableRows :
  forall {K : Nat -> Finset Int} {G : Int -> Int -> Real} {x : Int -> Real}
      (i : Int),
    UniformlySummableRows G ->
    IsBoundedSequence x ->
    (forall n : Nat, K n <= K (n + 1)) ->
    (forall k : Int, exists n : Nat, k ∈ K n) ->
      Filter.Tendsto
        (fun n : Nat => pairing x (truncation (K n) (fun j : Int => G i j)))
        Filter.atTop (nhds (pairing x (fun j : Int => G i j))) := by
  intro K G x i hG hx hmono hcover
  rcases hG with ⟨_M, _hMpos, hrow⟩
  exact pairing_truncation_tendsto hx (hrow i).1 hmono hcover



theorem eventually_strictlyAlternatingFin_of_tendsto :
  forall {n : Nat} {uN : Nat -> Fin n -> Real} {u : Fin n -> Real},
    IsStrictlyAlternatingFin u ->
    (forall i : Fin n,
      Filter.Tendsto (fun N : Nat => uN N i) Filter.atTop (nhds (u i))) ->
      ∀ᶠ N : Nat in Filter.atTop, IsStrictlyAlternatingFin (uN N) := by
  intro n uN u hAlt hcoord
  have hnonzero : ∀ᶠ N : Nat in Filter.atTop, forall i : Fin n, uN N i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (hcoord i).eventually_ne (hAlt.1 i)
  have hadj : ∀ᶠ N : Nat in Filter.atTop,
      forall i : Fin n, forall h : i.val + 1 < n,
        uN N i * uN N ⟨i.val + 1, h⟩ < 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i.val + 1 < n
    · have hlim : Filter.Tendsto
          (fun N : Nat => uN N i * uN N ⟨i.val + 1, hi⟩)
          Filter.atTop (nhds (u i * u ⟨i.val + 1, hi⟩)) :=
        (hcoord i).mul (hcoord ⟨i.val + 1, hi⟩)
      have hev : ∀ᶠ N : Nat in Filter.atTop,
          uN N i * uN N ⟨i.val + 1, hi⟩ < 0 := by
        exact hlim.eventually_lt tendsto_const_nhds (hAlt.2 i hi)
      exact hev.mono (fun N hN h => by
        have hfin : (⟨i.val + 1, h⟩ : Fin n) = ⟨i.val + 1, hi⟩ := by
          exact Fin.ext rfl
        simpa [hfin] using hN)
    · exact Eventually.of_forall (fun _N h => (hi h).elim)
  exact (hnonzero.and hadj).mono (fun _N h => ⟨h.1, h.2⟩)



theorem eventually_abs_ge_half_of_tendsto_nonzero_fin :
  forall {n : Nat} {uN : Nat -> Fin n -> Real} {u : Fin n -> Real},
    (forall i : Fin n, u i ≠ 0) ->
    (forall i : Fin n,
      Filter.Tendsto (fun N : Nat => uN N i) Filter.atTop (nhds (u i))) ->
      ∀ᶠ N : Nat in Filter.atTop,
        forall i : Fin n, |u i| / 2 <= |uN N i| := by
  intro n uN u hu hcoord
  rw [Filter.eventually_all]
  intro i
  have habs : Filter.Tendsto (fun N : Nat => |uN N i|)
      Filter.atTop (nhds |u i|) := by
    simpa [Function.comp_def] using (continuous_abs.tendsto (u i)).comp (hcoord i)
  have hhalf : |u i| / 2 < |u i| := half_lt_self (abs_pos.mpr (hu i))
  exact (Filter.Tendsto.eventually_const_lt hhalf habs).mono
    (fun _N hN => le_of_lt hN)




theorem weightedSupNormFin_le_two_of_abs_lower :
  forall {n : Nat} [Nonempty (Fin n)] {v u w : Fin n -> Real},
    (forall i : Fin n, u i ≠ 0) ->
    (forall i : Fin n, |u i| / 2 <= |w i|) ->
      weightedSupNormFin v w <= 2 * weightedSupNormFin v u := by
  intro n _ v u w hu hlower
  let beta : Real := weightedSupNormFin v u
  apply csSup_le
  · exact Set.range_nonempty _
  · intro b hb
    rcases hb with ⟨i, rfl⟩
    have hupos : 0 < |u i| := abs_pos.mpr (hu i)
    have hdiv : |v i / w i| <= 2 * |v i / u i| := by
      rw [abs_div, abs_div]
      have hstep : |v i| / |w i| <= |v i| / (|u i| / 2) := by
        exact div_le_div_of_nonneg_left (abs_nonneg (v i)) (half_pos hupos) (hlower i)
      have hrewrite : |v i| / (|u i| / 2) = 2 * (|v i| / |u i|) := by
        field_simp [hupos.ne']
      calc
        |v i| / |w i| <= |v i| / (|u i| / 2) := hstep
        _ = 2 * (|v i| / |u i|) := hrewrite
    have hterm_le_beta : |v i / u i| <= beta := by
      exact le_csSup (Finite.bddAbove_range fun k : Fin n => |v k / u k|)
        (Set.mem_range_self i)
    calc
      |v i / w i| <= 2 * |v i / u i| := hdiv
      _ <= 2 * beta := by
        exact mul_le_mul_of_nonneg_left hterm_le_beta (by norm_num)



theorem weightedSupNormFin_le_of_abs_bounds :
  forall {n : Nat} [Nonempty (Fin n)] {v u : Fin n -> Real} {M delta : Real},
    0 <= M ->
    0 < delta ->
    (forall i : Fin n, |v i| <= M) ->
    (forall i : Fin n, delta <= |u i|) ->
      weightedSupNormFin v u <= M / delta := by
  intro n _ v u M delta hM hdelta_pos hv hu
  apply csSup_le
  · exact Set.range_nonempty _
  · intro b hb
    rcases hb with ⟨i, rfl⟩
    calc
      |v i / u i| = |v i| / |u i| := by
        rw [abs_div]
      _ <= M / |u i| := by
        exact div_le_div_of_nonneg_right (hv i) (abs_nonneg (u i))
      _ <= M / delta := by
        exact div_le_div_of_nonneg_left hM hdelta_pos (hu i)



theorem eventually_weightedSupNormFin_le_two_of_tendsto_nonzero_fin :
  forall {n : Nat} [Nonempty (Fin n)] {v u : Fin n -> Real}
      {uN : Nat -> Fin n -> Real},
    (forall i : Fin n, u i ≠ 0) ->
    (forall i : Fin n,
      Filter.Tendsto (fun N : Nat => uN N i) Filter.atTop (nhds (u i))) ->
      ∀ᶠ N : Nat in Filter.atTop,
        weightedSupNormFin v (uN N) <= 2 * weightedSupNormFin v u := by
  intro n _ v u uN hu hcoord
  exact (eventually_abs_ge_half_of_tendsto_nonzero_fin hu hcoord).mono
    (fun _N hN => weightedSupNormFin_le_two_of_abs_lower hu hN)



theorem matVec_isBounded_of_uniformlySummableRows :
  forall {G : Int -> Int -> Real} {y : Int -> Real},
    UniformlySummableRows G -> IsBoundedSequence y ->
      IsBoundedSequence (MatVec G y) := by
  intro G y hG hy
  rcases hG with ⟨M, hMpos, hrow⟩
  rcases hy with ⟨B, hBpos, hyB⟩
  refine ⟨M * B, mul_pos hMpos hBpos, ?_⟩
  intro i
  rcases hrow i with ⟨hsumRow, hrowBound⟩
  have hsumProd : Summable fun j : Int => |G i j * y j| := by
    exact (hsumRow.mul_right B).of_nonneg_of_le
      (fun j => abs_nonneg (G i j * y j))
      (fun j => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hyB j) (abs_nonneg (G i j)))
  have hnorm :
      ‖MatVec G y i‖ <= ∑' j : Int, ‖G i j * y j‖ := by
    exact norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hsumProd)
  have hleTsum :
      (∑' j : Int, |G i j * y j|) <=
        (∑' j : Int, |G i j| * B) := by
    exact Summable.tsum_le_tsum
      (fun j => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hyB j) (abs_nonneg (G i j)))
      hsumProd (hsumRow.mul_right B)
  have hmul :
      (∑' j : Int, |G i j| * B) <= M * B := by
    rw [hsumRow.tsum_mul_right B]
    exact mul_le_mul_of_nonneg_right hrowBound (le_of_lt hBpos)
  calc
    |MatVec G y i| = ‖MatVec G y i‖ := by rw [Real.norm_eq_abs]
    _ <= ∑' j : Int, ‖G i j * y j‖ := hnorm
    _ = ∑' j : Int, |G i j * y j| := by simp [Real.norm_eq_abs]
    _ <= ∑' j : Int, |G i j| * B := hleTsum
    _ <= M * B := hmul



theorem boundedSequence_subseq_pairing_tendsto :
  forall {ys : Nat -> Int -> Real} {M : Real},
    0 <= M ->
    (forall n : Nat, forall k : Int, |ys n k| <= M) ->
      exists phi : Nat -> Nat, StrictMono phi /\
        exists y : Int -> Real, (forall k : Int, |y k| <= M) /\
          IsBoundedSequence y /\
          forall s : Int -> Real, IsL1Sequence s ->
            Filter.Tendsto (fun n : Nat => pairing (ys (phi n)) s)
              Filter.atTop (nhds (pairing y s)) := by
  intro ys M hM hys
  let ysBounded : Nat -> Int -> Set.Icc (-M) M := fun n k =>
    ⟨ys n k, by
      exact abs_le.mp (hys n k)⟩
  obtain ⟨z, phi, hphi, hz⟩ := CompactSpace.tendsto_subseq ysBounded
  let y : Int -> Real := fun k => (z k : Real)
  refine ⟨phi, hphi, y, ?_, ?_, ?_⟩
  · intro k
    have hzmem : (z k : Real) ∈ Set.Icc (-M) M := (z k).property
    exact abs_le.mpr hzmem
  · refine ⟨M + 1, by positivity, ?_⟩
    intro k
    have hzmem : (z k : Real) ∈ Set.Icc (-M) M := (z k).property
    have hzabs : |(z k : Real)| <= M := abs_le.mpr hzmem
    exact hzabs.trans (by linarith)
  · intro s hs
    have hsumBound : Summable (fun k : Int => M * |s k|) := hs.mul_left M
    have hcoord : forall k : Int,
        Filter.Tendsto (fun n : Nat => ys (phi n) k * s k)
          Filter.atTop (nhds (y k * s k)) := by
      intro k
      have hsub : Filter.Tendsto (fun n : Nat => ysBounded (phi n) k)
          Filter.atTop (nhds (z k)) := (tendsto_pi_nhds.mp hz) k
      have hreal : Filter.Tendsto (fun n : Nat => (ysBounded (phi n) k : Real))
          Filter.atTop (nhds ((z k : Set.Icc (-M) M) : Real)) :=
        (continuous_subtype_val.tendsto (z k)).comp hsub
      simpa [ysBounded, y] using hreal.mul tendsto_const_nhds
    have hdom : forall n : Nat, forall k : Int,
        ‖ys (phi n) k * s k‖ <= M * |s k| := by
      intro n k
      calc
        ‖ys (phi n) k * s k‖ = |ys (phi n) k * s k| := by
          rw [Real.norm_eq_abs]
        _ = |ys (phi n) k| * |s k| := by rw [abs_mul]
        _ <= M * |s k| :=
          mul_le_mul_of_nonneg_right (hys (phi n) k) (abs_nonneg (s k))
    have ht := tendsto_tsum_of_dominated_convergence
      (𝓕 := Filter.atTop)
      (f := fun n k => ys (phi n) k * s k)
      (g := fun k => y k * s k)
      (bound := fun k => M * |s k|)
      hsumBound hcoord (Eventually.of_forall hdom)
    simpa [pairing] using ht

end VendorE4
