import LeanCode.Vendor.E4.DFP.FiniteCore

open scoped BigOperators

noncomputable section

namespace VendorE4



theorem truncatedRowData_tendsto :
  forall {n : Nat} {G : Int -> Int -> Real} {rows : Fin n -> Int}
      {x : Int -> Real} {u : Fin n -> Real},
    UniformlySummableRows G ->
    IsBoundedSequence x ->
    (forall i : Fin n, u i = pairing x (fun j : Int => G (rows i) j)) ->
      forall i : Fin n,
        Filter.Tendsto
          (fun N : Nat =>
            pairing x (truncation (intWindow N) (fun j : Int => G (rows i) j)))
          Filter.atTop (nhds (u i)) := by
  intro n G rows x u hG hx hu i
  have h := row_pairing_truncation_tendsto_of_uniformlySummableRows
    (K := intWindow) (G := G) (x := x) (rows i) hG hx intWindow_mono intWindow_cover
  simpa [hu i] using h



theorem eventually_strictlyAlternatingFin_truncatedRowData :
  forall {n : Nat} {G : Int -> Int -> Real} {rows : Fin n -> Int}
      {x : Int -> Real} {u : Fin n -> Real},
    UniformlySummableRows G ->
    IsBoundedSequence x ->
    (forall i : Fin n, u i = pairing x (fun j : Int => G (rows i) j)) ->
    IsStrictlyAlternatingFin u ->
      ∀ᶠ N : Nat in Filter.atTop,
        IsStrictlyAlternatingFin
          (fun i : Fin n =>
            pairing x (truncation (intWindow N) (fun j : Int => G (rows i) j))) := by
  intro n G rows x u hG hx hu hAlt
  exact eventually_strictlyAlternatingFin_of_tendsto hAlt
    (truncatedRowData_tendsto hG hx hu)



theorem eventually_abs_truncatedRowData_ge_half :
  forall {n : Nat} {G : Int -> Int -> Real} {rows : Fin n -> Int}
      {x : Int -> Real} {u : Fin n -> Real},
    UniformlySummableRows G ->
    IsBoundedSequence x ->
    (forall i : Fin n, u i = pairing x (fun j : Int => G (rows i) j)) ->
    IsStrictlyAlternatingFin u ->
      ∀ᶠ N : Nat in Filter.atTop,
        forall i : Fin n,
          |u i| / 2 <=
            |pairing x (truncation (intWindow N) (fun j : Int => G (rows i) j))| := by
  intro n G rows x u hG hx hu hAlt
  exact eventually_abs_ge_half_of_tendsto_nonzero_fin hAlt.1
    (truncatedRowData_tendsto hG hx hu)



theorem eventually_weightedSupNorm_truncatedRowData_le_two :
  forall {n : Nat} [Nonempty (Fin n)] {G : Int -> Int -> Real}
      {rows : Fin n -> Int} {x : Int -> Real} {u v : Fin n -> Real},
    UniformlySummableRows G ->
    IsBoundedSequence x ->
    (forall i : Fin n, u i = pairing x (fun j : Int => G (rows i) j)) ->
    IsStrictlyAlternatingFin u ->
      ∀ᶠ N : Nat in Filter.atTop,
        weightedSupNormFin v
          (fun i : Fin n =>
            pairing x (truncation (intWindow N) (fun j : Int => G (rows i) j))) <=
          2 * weightedSupNormFin v u := by
  intro n _ G rows x u v hG hx hu hAlt
  exact eventually_weightedSupNormFin_le_two_of_tendsto_nonzero_fin hAlt.1
    (truncatedRowData_tendsto hG hx hu)




theorem isTotallyPositive_intWindow_submatrix :
  forall {n : Nat} {G : Int -> Int -> Real} {rows : Fin n -> Int},
    IsTotallyPositive G ->
    StrictMono rows ->
      forall N : Nat,
        IsTotallyPositiveFinite
          (fun i : Fin n => fun k : Fin (intWindow N).card =>
            G (rows i) ((intWindow N).orderEmbOfFin rfl k)) := by
  intro n G rows hTP hrows N
  exact isTotallyPositive_submatrix hTP rows
    ((intWindow N).orderEmbOfFin rfl) hrows
    ((intWindow N).orderEmbOfFin rfl).strictMono





theorem finite_window_rows_surjective :
  forall {n : Nat} {G : Int -> Int -> Real} {rows : Fin n -> Int}
      {x : Int -> Real} (K : Finset Int),
    IsTotallyPositiveFinite
      (fun i : Fin n => fun k : Fin K.card =>
        G (rows i) (K.orderEmbOfFin rfl k)) ->
    IsStrictlyAlternatingFin
      (fun i : Fin n =>
        pairing x (truncation K (fun j : Int => G (rows i) j))) ->
      forall v : Fin n -> Real,
        exists y : Int -> Real,
          IsBoundedSequence y /\
          (forall i : Fin n,
            pairing y (truncation K (fun j : Int => G (rows i) j)) = v i) /\
          forall j : Int,
            |y j| <=
              weightedSupNormFin v
                (fun i : Fin n =>
                  pairing x (truncation K (fun j : Int => G (rows i) j))) *
                sSup (Set.range fun k : Fin K.card => |x (K.orderEmbOfFin rfl k)|) := by
  classical
  intro n G rows x K hTP hAlt v
  let emb : Fin K.card -> Int := K.orderEmbOfFin rfl
  let B : Matrix (Fin n) (Fin K.card) Real := fun i k => G (rows i) (emb k)
  let xK : Fin K.card -> Real := fun k => x (emb k)
  let uK : Fin n -> Real := fun i =>
    pairing x (truncation K (fun j : Int => G (rows i) j))
  have hxsol : forall i : Fin n, (∑ k : Fin K.card, B i k * xK k) = uK i := by
    intro i
    calc
      (∑ k : Fin K.card, B i k * xK k)
          = ∑ k : Fin K.card, x (emb k) * G (rows i) (emb k) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              ring
      _ = uK i := by
              symm
              simpa [uK, emb] using
                pairing_truncation_eq_sum_orderEmb K x (fun j : Int => G (rows i) j)
  rcases finite_rows_finite_columns_surjective (B := B) (x := xK) (u := uK)
      (by simpa [B, emb] using hTP) (by simpa [uK] using hAlt) hxsol v with
    ⟨yK, hyK, hyKbd⟩
  let C : Real :=
    weightedSupNormFin v uK *
      sSup (Set.range fun k : Fin K.card => |xK k|)
  have hbeta_nonneg : 0 <= weightedSupNormFin v uK := by
    exact Real.sSup_nonneg (Set.forall_mem_range.2 (fun i => abs_nonneg _))
  have hM_nonneg : 0 <= sSup (Set.range fun k : Fin K.card => |xK k|) := by
    exact Real.sSup_nonneg (Set.forall_mem_range.2 (fun k => abs_nonneg _))
  have hC_nonneg : 0 <= C := mul_nonneg hbeta_nonneg hM_nonneg
  let y : Int -> Real := fun j =>
    if h : j ∈ Set.range emb then yK (Classical.choose h) else 0
  have hyEmb : forall k : Fin K.card, y (emb k) = yK k := by
    intro k
    have hrange : emb k ∈ Set.range emb := ⟨k, rfl⟩
    have hchoose : emb (Classical.choose hrange) = emb k :=
      Classical.choose_spec hrange
    have hck : Classical.choose hrange = k :=
      (K.orderEmbOfFin rfl).injective hchoose
    rw [show y (emb k) = yK (Classical.choose hrange) by
      dsimp [y]
      rw [dif_pos hrange]]
    exact congrArg yK hck
  have hyBound : forall j : Int, |y j| <= C := by
    intro j
    by_cases hj : j ∈ Set.range emb
    · have hbd := hyKbd (Classical.choose hj)
      rw [show y j = yK (Classical.choose hj) by
        dsimp [y]
        rw [dif_pos hj]]
      simpa [C] using hbd
    · rw [show y j = 0 by
        dsimp [y]
        rw [dif_neg hj]]
      simpa using hC_nonneg
  refine ⟨y, ?_, ?_, ?_⟩
  · refine ⟨C + 1, by linarith, ?_⟩
    intro j
    exact (hyBound j).trans (by linarith)
  · intro i
    calc
      pairing y (truncation K (fun j : Int => G (rows i) j))
          = ∑ k : Fin K.card, y (emb k) * G (rows i) (emb k) := by
              simpa [emb] using
                pairing_truncation_eq_sum_orderEmb K y (fun j : Int => G (rows i) j)
      _ = ∑ k : Fin K.card, B i k * yK k := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [hyEmb k]
              ring
      _ = v i := hyK i
  · intro j
    simpa [C, uK, xK] using hyBound j




theorem finite_row_surjectivity_implies_rows_injective :
  forall {n : Nat} {G : Int -> Int -> Real} {rows : Fin n -> Int},
    (forall v : Fin n -> Real,
      exists y : Int -> Real,
        IsBoundedSequence y /\
          forall i : Fin n, pairing y (fun j : Int => G (rows i) j) = v i) ->
      Function.Injective rows := by
  intro n G rows hsurj p q hpq
  by_contra hpne
  let v : Fin n -> Real := fun i => if i = p then 0 else 1
  rcases hsurj v with ⟨y, _hy, hyrows⟩
  have hp : pairing y (fun j : Int => G (rows p) j) = 0 := by
    simpa [v] using hyrows p
  have hq : pairing y (fun j : Int => G (rows q) j) = 1 := by
    have hqp : q ≠ p := fun h => hpne h.symm
    simpa [v, hqp] using hyrows q
  have hpair :
      pairing y (fun j : Int => G (rows p) j) =
        pairing y (fun j : Int => G (rows q) j) := by
    rw [hpq]
  have hzero_one : (0 : Real) = 1 := by
    rw [← hp, hpair, hq]
  norm_num at hzero_one





theorem finite_rows_all_columns_surjective_bounded :
  forall {n : Nat} {G : Int -> Int -> Real} {rows : Fin n -> Int}
      {x : Int -> Real} {u : Fin n -> Real} {Mx : Real},
    IsTotallyPositive G ->
    UniformlySummableRows G ->
    0 < Mx ->
    (forall k : Int, |x k| <= Mx) ->
    StrictMono rows ->
    (forall i : Fin n, u i = pairing x (fun j : Int => G (rows i) j)) ->
    IsStrictlyAlternatingFin u ->
      forall v : Fin n -> Real,
        exists y : Int -> Real,
          IsBoundedSequence y /\
            (forall i : Fin n, pairing y (fun j : Int => G (rows i) j) = v i) /\
            forall j : Int, |y j| <= 2 * weightedSupNormFin v u * Mx := by
  classical
  intro n G rows x u Mx hTP hG hMxpos hxM hrows hu hAlt v
  by_cases hn : n = 0
  · subst n
    refine ⟨fun _ : Int => 0, ?_, ?_, ?_⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro k
      simp
    · intro i
      exact Fin.elim0 i
    · intro j
      have hbeta_nonneg : 0 <= weightedSupNormFin v u := by
        exact Real.sSup_nonneg (Set.forall_mem_range.2 (fun i => abs_nonneg _))
      have hbound_nonneg : 0 <= 2 * weightedSupNormFin v u * Mx := by
        nlinarith [hbeta_nonneg, le_of_lt hMxpos]
      simpa using hbound_nonneg
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  let hx' : IsBoundedSequence x := ⟨Mx, hMxpos, hxM⟩
  rcases hG with ⟨R, hRpos, hrow⟩
  let hG' : UniformlySummableRows G := ⟨R, hRpos, hrow⟩
  let uN : Nat -> Fin n -> Real := fun N i =>
    pairing x (truncation (intWindow N) (fun j : Int => G (rows i) j))
  have hbeta_nonneg : 0 <= weightedSupNormFin v u := by
    exact Real.sSup_nonneg (Set.forall_mem_range.2 (fun i => abs_nonneg _))
  have hCtop_nonneg : 0 <= 2 * weightedSupNormFin v u := by
    nlinarith
  have hSupX_le : forall N : Nat,
      sSup
        (Set.range fun k : Fin (intWindow N).card =>
          |x ((intWindow N).orderEmbOfFin rfl k)|) <= Mx := by
    intro N
    have hmem0 : (0 : Int) ∈ intWindow N := by
      rw [intWindow, Finset.mem_Icc]
      constructor <;> omega
    have hcardpos : 0 < (intWindow N).card :=
      Finset.card_pos.mpr ⟨0, hmem0⟩
    have hnonempty :
        (Set.range fun k : Fin (intWindow N).card =>
          |x ((intWindow N).orderEmbOfFin rfl k)|).Nonempty := by
      let k0 : Fin (intWindow N).card := ⟨0, hcardpos⟩
      exact ⟨|x ((intWindow N).orderEmbOfFin rfl k0)|, Set.mem_range_self k0⟩
    exact csSup_le hnonempty (by
      intro b hb
      rcases hb with ⟨k, rfl⟩
      exact hxM _)
  have hAltEv : ∀ᶠ N : Nat in Filter.atTop, IsStrictlyAlternatingFin (uN N) := by
    simpa [uN] using
      eventually_strictlyAlternatingFin_truncatedRowData
        (G := G) (rows := rows) (x := x) (u := u) hG' hx' hu hAlt
  have hWeightEv : ∀ᶠ N : Nat in Filter.atTop,
      weightedSupNormFin v (uN N) <= 2 * weightedSupNormFin v u := by
    simpa [uN] using
      eventually_weightedSupNorm_truncatedRowData_le_two
        (G := G) (rows := rows) (x := x) (u := u) (v := v) hG' hx' hu hAlt
  rcases Filter.eventually_atTop.1 (hAltEv.and hWeightEv) with ⟨N0, hN0⟩
  let C0 : Real := 2 * weightedSupNormFin v u * Mx
  have hC0_nonneg : 0 <= C0 := by
    dsimp [C0]
    nlinarith [hbeta_nonneg, le_of_lt hMxpos]
  have hsol : forall t : Nat,
      exists y : Int -> Real,
        IsBoundedSequence y /\
        (forall i : Fin n,
          pairing y
            (truncation (intWindow (N0 + t)) (fun j : Int => G (rows i) j)) = v i) /\
        forall j : Int, |y j| <= C0 := by
    intro t
    let N : Nat := N0 + t
    have hNge : N0 <= N := Nat.le_add_right N0 t
    have hAltN : IsStrictlyAlternatingFin (uN N) := (hN0 N hNge).1
    have hWeightN : weightedSupNormFin v (uN N) <= 2 * weightedSupNormFin v u :=
      (hN0 N hNge).2
    rcases finite_window_rows_surjective (G := G) (rows := rows) (x := x)
        (K := intWindow N)
        (isTotallyPositive_intWindow_submatrix hTP hrows N)
        (by simpa [uN, N] using hAltN) v with
      ⟨y, hyBounded, hyEq, hyRawBound⟩
    refine ⟨y, hyBounded, ?_, ?_⟩
    · intro i
      simpa [N] using hyEq i
    · intro j
      have hSupN_nonneg : 0 <=
          sSup
            (Set.range fun k : Fin (intWindow N).card =>
              |x ((intWindow N).orderEmbOfFin rfl k)|) := by
        exact Real.sSup_nonneg (Set.forall_mem_range.2 (fun k => abs_nonneg _))
      calc
        |y j| <=
            weightedSupNormFin v (uN N) *
              sSup
                (Set.range fun k : Fin (intWindow N).card =>
                  |x ((intWindow N).orderEmbOfFin rfl k)|) := by
              simpa [uN, N] using hyRawBound j
        _ <= (2 * weightedSupNormFin v u) * Mx := by
              exact mul_le_mul hWeightN (hSupX_le N) hSupN_nonneg hCtop_nonneg
        _ = C0 := by
              ring
  let ys : Nat -> Int -> Real := fun t => Classical.choose (hsol t)
  have hys_bound : forall t : Nat, forall j : Int, |ys t j| <= C0 := by
    intro t
    exact (Classical.choose_spec (hsol t)).2.2
  rcases boundedSequence_subseq_pairing_tendsto (ys := ys) (M := C0)
      hC0_nonneg hys_bound with
    ⟨phi, hphi, hlimit⟩
  rcases hlimit with ⟨y, hdata⟩
  have hyBounded : IsBoundedSequence y := hdata.2.1
  have hpair_tendsto :
      forall s : Int -> Real, IsL1Sequence s ->
        Filter.Tendsto (fun n : Nat => pairing (ys (phi n)) s)
          Filter.atTop (nhds (pairing y s)) := hdata.2.2
  refine ⟨y, hyBounded, ?_, ?_⟩
  · intro i
    have hrowL1 : IsL1Sequence (fun j : Int => G (rows i) j) :=
      (hrow (rows i)).1
    have hNphi : Filter.Tendsto (fun t : Nat => N0 + phi t)
        Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      rcases Filter.tendsto_atTop_atTop.mp hphi.tendsto_atTop b with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      intro t ht
      exact (ha t ht).trans (Nat.le_add_left (phi t) N0)
    have htail :=
      truncation_l1_tendsto
        (K := intWindow) (s := fun j : Int => G (rows i) j)
        hrowL1 intWindow_mono intWindow_cover
    have htail_sub :
        Filter.Tendsto
          (fun t : Nat =>
            l1Norm
              (fun k : Int =>
                G (rows i) k -
                  truncation (intWindow (N0 + phi t)) (fun j : Int => G (rows i) j) k))
          Filter.atTop (nhds 0) := by
      simpa [Function.comp_def] using htail.comp hNphi
    have hright :
        Filter.Tendsto
          (fun t : Nat =>
            C0 *
              l1Norm
                (fun k : Int =>
                  G (rows i) k -
                    truncation (intWindow (N0 + phi t)) (fun j : Int => G (rows i) j) k))
          Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul htail_sub)
    have hto_v :
        Filter.Tendsto
          (fun t : Nat => pairing (ys (phi t)) (fun j : Int => G (rows i) j))
          Filter.atTop (nhds (v i)) := by
      apply tendsto_iff_dist_tendsto_zero.2
      exact squeeze_zero
        (fun t : Nat => dist_nonneg)
        (fun t : Nat => by
          have hspec := Classical.choose_spec (hsol (phi t))
          have htrunc_eq :
              pairing (ys (phi t))
                (truncation (intWindow (N0 + phi t)) (fun j : Int => G (rows i) j)) =
                v i := hspec.2.1 i
          have herr :=
            abs_pairing_sub_pairing_truncation_le
              (intWindow (N0 + phi t)) (M := C0) hC0_nonneg
              (hys_bound (phi t)) hrowL1
          simpa [Real.dist_eq, htrunc_eq, abs_sub_comm] using herr)
        hright
    have hto_y :
        Filter.Tendsto
          (fun t : Nat => pairing (ys (phi t)) (fun j : Int => G (rows i) j))
          Filter.atTop (nhds (pairing y (fun j : Int => G (rows i) j))) :=
      hpair_tendsto (fun j : Int => G (rows i) j) hrowL1
    exact tendsto_nhds_unique hto_y hto_v
  · intro j
    simpa [C0] using hdata.1 j



theorem finite_rows_all_columns_surjective :
  forall {n : Nat} {G : Int -> Int -> Real} {rows : Fin n -> Int}
      {x : Int -> Real} {u : Fin n -> Real},
    IsTotallyPositive G ->
    UniformlySummableRows G ->
    IsBoundedSequence x ->
    StrictMono rows ->
    (forall i : Fin n, u i = pairing x (fun j : Int => G (rows i) j)) ->
    IsStrictlyAlternatingFin u ->
      forall v : Fin n -> Real,
        exists y : Int -> Real,
          IsBoundedSequence y /\
            forall i : Fin n, pairing y (fun j : Int => G (rows i) j) = v i := by
  intro n G rows x u hTP hG hx hrows hu hAlt v
  rcases hx with ⟨Mx, hMxpos, hxM⟩
  rcases finite_rows_all_columns_surjective_bounded
      (G := G) (rows := rows) (x := x) (u := u) (Mx := Mx)
      hTP hG hMxpos hxM hrows hu hAlt v with
    ⟨y, hyBounded, hyRows, _hyBound⟩
  exact ⟨y, hyBounded, hyRows⟩




theorem dfp_surjective_of_uniformly_summable_rows :
  forall (G : Int -> Int -> Real),
    IsTotallyPositive G ->
    UniformlySummableRows G ->
    forall {c : Int -> Real},
      IsBoundedSequence c ->
      IsUniformlyAlternating (MatVec G c) ->
      IsUniformlyBoundedFromBelow (MatVec G c) ->
        forall x : Int -> Real, IsBoundedSequence x ->
          exists y : Int -> Real, IsBoundedSequence y /\ MatVec G y = x := by
  classical
  intro G hTP hG c hc hAlt hBelow x hx
  rcases hc with ⟨Mc, hMcpos, hcM⟩
  let hc' : IsBoundedSequence c := ⟨Mc, hMcpos, hcM⟩
  rcases hx with ⟨Mx, hMxpos, hxM⟩
  rcases hBelow with ⟨delta, hdelta_pos, hdelta⟩
  rcases hG with ⟨R, hRpos, hrow⟩
  let hG' : UniformlySummableRows G := ⟨R, hRpos, hrow⟩
  let C : Real := 2 * (Mx / delta) * Mc
  have hMx_nonneg : 0 <= Mx := le_of_lt hMxpos
  have hC_nonneg : 0 <= C := by
    dsimp [C]
    positivity
  have hsol : forall N : Nat,
      exists y : Int -> Real,
        IsBoundedSequence y /\
        (forall i : Int, i ∈ intWindow N ->
          pairing y (fun j : Int => G i j) = x i) /\
        forall j : Int, |y j| <= C := by
    intro N
    let rows : Fin (intWindow N).card -> Int :=
      fun i => (intWindow N).orderEmbOfFin rfl i
    let u : Fin (intWindow N).card -> Real :=
      fun i => pairing c (fun j : Int => G (rows i) j)
    let v : Fin (intWindow N).card -> Real := fun i => x (rows i)
    have hmem0 : (0 : Int) ∈ intWindow N := by
      rw [intWindow, Finset.mem_Icc]
      constructor <;> omega
    have hcardpos : 0 < (intWindow N).card :=
      Finset.card_pos.mpr ⟨0, hmem0⟩
    haveI : Nonempty (Fin (intWindow N).card) := ⟨⟨0, hcardpos⟩⟩
    have hrows : StrictMono rows := (intWindow N).orderEmbOfFin rfl |>.strictMono
    have hu : forall i : Fin (intWindow N).card,
        u i = pairing c (fun j : Int => G (rows i) j) := by
      intro i
      rfl
    have hrows_eq :
        rows = fun i : Fin (intWindow N).card => (-(N : Int) + (i.val : Int)) := by
      simpa [rows] using intWindow_orderEmbOfFin_eq N
    have hAltFin : IsStrictlyAlternatingFin u := by
      have hbase :=
        strictlyAlternating_restrict_interval
          (u := MatVec G c) hAlt (-(N : Int)) (intWindow N).card
      convert hbase using 1
      ext i
      have hirow := congrFun hrows_eq i
      calc
        u i = pairing c (fun j : Int => G (rows i) j) := rfl
        _ = MatVec G c (rows i) := pairing_row_eq_matVec G c (rows i)
        _ = MatVec G c (-(N : Int) + (i.val : Int)) := by rw [hirow]
    rcases finite_rows_all_columns_surjective_bounded
        (G := G) (rows := rows) (x := c) (u := u) (Mx := Mc)
        hTP hG' hMcpos hcM hrows hu hAltFin v with
      ⟨y, hyBounded, hyRows, hyBoundRaw⟩
    have hweight :
        weightedSupNormFin v u <= Mx / delta := by
      apply weightedSupNormFin_le_of_abs_bounds
      · exact hMx_nonneg
      · exact hdelta_pos
      · intro i
        exact hxM (rows i)
      · intro i
        have hrow_eq : u i = MatVec G c (rows i) := by
          calc
            u i = pairing c (fun j : Int => G (rows i) j) := rfl
            _ = MatVec G c (rows i) := pairing_row_eq_matVec G c (rows i)
        simpa [hrow_eq] using hdelta (rows i)
    have hyBound : forall j : Int, |y j| <= C := by
      intro j
      calc
        |y j| <= 2 * weightedSupNormFin v u * Mc := hyBoundRaw j
        _ <= 2 * (Mx / delta) * Mc := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hweight (by norm_num))
            (le_of_lt hMcpos)
        _ = C := by ring
    refine ⟨y, hyBounded, ?_, hyBound⟩
    intro i hi
    have hset : i ∈ ((intWindow N : Finset Int) : Set Int) := by
      simpa using hi
    rw [← Finset.range_orderEmbOfFin (intWindow N) rfl] at hset
    rcases hset with ⟨p, hp⟩
    have hp' : rows p = i := by
      simpa [rows] using hp
    have hy := hyRows p
    simpa [v, hp'] using hy
  let ys : Nat -> Int -> Real := fun N => Classical.choose (hsol N)
  have hys_bound : forall N : Nat, forall j : Int, |ys N j| <= C := by
    intro N
    exact (Classical.choose_spec (hsol N)).2.2
  rcases boundedSequence_subseq_pairing_tendsto (ys := ys) (M := C)
      hC_nonneg hys_bound with
    ⟨phi, hphi, hlimit⟩
  rcases hlimit with ⟨y, hdata⟩
  have hyBounded : IsBoundedSequence y := hdata.2.1
  have hpair_tendsto :
      forall s : Int -> Real, IsL1Sequence s ->
        Filter.Tendsto (fun n : Nat => pairing (ys (phi n)) s)
          Filter.atTop (nhds (pairing y s)) := hdata.2.2
  refine ⟨y, hyBounded, ?_⟩
  funext i
  have hrowL1 : IsL1Sequence (fun j : Int => G i j) := (hrow i).1
  have hEventually_eq :
      ∀ᶠ t : Nat in Filter.atTop,
        pairing (ys (phi t)) (fun j : Int => G i j) = x i := by
    rcases intWindow_cover i with ⟨N0, hiN0⟩
    have hmono : Monotone intWindow := monotone_nat_of_le_succ intWindow_mono
    rcases Filter.tendsto_atTop_atTop.mp hphi.tendsto_atTop N0 with ⟨a, ha⟩
    rw [Filter.eventually_atTop]
    refine ⟨a, ?_⟩
    intro t ht
    have hNle : N0 <= phi t := ha t ht
    have hiMem : i ∈ intWindow (phi t) := hmono hNle hiN0
    have hspec := Classical.choose_spec (hsol (phi t))
    exact hspec.2.1 i hiMem
  have hto_x :
      Filter.Tendsto
        (fun t : Nat => pairing (ys (phi t)) (fun j : Int => G i j))
        Filter.atTop (nhds (x i)) :=
    Filter.Tendsto.congr'
      (hEventually_eq.mono (fun _ h => h.symm)) tendsto_const_nhds
  have hto_y :
      Filter.Tendsto
        (fun t : Nat => pairing (ys (phi t)) (fun j : Int => G i j))
        Filter.atTop (nhds (pairing y (fun j : Int => G i j))) :=
    hpair_tendsto (fun j : Int => G i j) hrowL1
  have hpair_eq : pairing y (fun j : Int => G i j) = x i :=
    tendsto_nhds_unique hto_y hto_x
  rw [← hpair_eq]
  exact (pairing_row_eq_matVec G y i).symm

end VendorE4
