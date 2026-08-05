import LeanCode.Vendor.E4.DFP.SequenceSpaces
import LeanCode.Vendor.E4.DFP.TotalPositivity

open Matrix
open scoped BigOperators

noncomputable section

namespace VendorE4



theorem exists_nonzero_kernel_vector_supported_on_card_succ :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real} {L : Finset (Fin m)},
    L.card = n + 1 ->
      exists c : Fin m -> Real, c ≠ 0 /\
        (forall j : Fin m, j ∉ L -> c j = 0) /\
        forall i : Fin n, (∑ j : Fin m, c j * B i j) = 0 := by
  classical
  intro n m B L hcard
  let T : (L -> Real) →ₗ[Real] (Fin n -> Real) :=
    { toFun := fun c i => ∑ j : L, c j * B i j
      map_add' := by
        intro c d
        ext i
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        ext i
        simp [mul_assoc, Finset.mul_sum] }
  have hdim : Module.finrank Real (Fin n -> Real) < Module.finrank Real (L -> Real) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, hcard]
    simp
  have hker : LinearMap.ker T ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  rcases (Submodule.ne_bot_iff (LinearMap.ker T)).mp hker with ⟨cL, hcKer, hcNe⟩
  let c : Fin m -> Real := fun j => if h : j ∈ L then cL ⟨j, h⟩ else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · intro hc
    apply hcNe
    ext j
    have hzero := congrFun hc j.1
    simpa [c, j.2] using hzero
  · intro j hj
    simp [c, hj]
  · intro i
    have hT : T cL = 0 := LinearMap.mem_ker.mp hcKer
    have hTi : (∑ j : L, cL j * B i j) = 0 := congrFun hT i
    let f : Fin m -> Real := fun j => c j * B i j
    have hsum_subset : L.sum f = Finset.univ.sum f :=
      Finset.sum_subset (by simp) (fun j _hj_univ hjL => by simp [c, hjL])
    have hsum_subtype : L.sum f = ∑ j : L, cL j * B i j := by
      rw [Finset.sum_subtype L (fun x => Iff.rfl) f]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [f, c, j.2]
    calc
      (∑ j : Fin m, c j * B i j) = L.sum f := by
        exact hsum_subset.symm
      _ = ∑ j : L, cL j * B i j := hsum_subtype
      _ = 0 := hTi



theorem kernel_direction_preserves_zero_coordinates :
  forall {m : Nat} {L : Finset (Fin m)} {w c : Fin m -> Real},
    (forall j : Fin m, j ∉ L -> c j = 0) ->
    (forall j : Fin m, j ∈ L -> w j ≠ 0) ->
      forall t : Real, forall j : Fin m, w j = 0 -> w j + t * c j = 0 := by
  intro m L w c hcSupport hwL t j hwj
  have hjnot : j ∉ L := by
    intro hjL
    exact hwL j hjL hwj
  simp [hwj, hcSupport j hjnot]



theorem exists_kernel_breakpoint :
  forall {m : Nat} {L : Finset (Fin m)} {w c : Fin m -> Real},
    c ≠ 0 ->
    (forall j : Fin m, j ∉ L -> c j = 0) ->
    (forall j : Fin m, j ∈ L -> w j ≠ 0) ->
      exists t : Real,
        (forall j : Fin m, w j = 0 -> w j + t * c j = 0) /\
        (exists j : Fin m, w j ≠ 0 /\ w j + t * c j = 0) := by
  classical
  intro m L w c hcNe hcSupport hwL
  have hexists : exists j : Fin m, c j ≠ 0 := by
    by_contra h
    apply hcNe
    funext j
    by_contra hcj
    exact h ⟨j, hcj⟩
  rcases hexists with ⟨j0, hj0c⟩
  have hj0L : j0 ∈ L := by
    by_contra hj0not
    exact hj0c (hcSupport j0 hj0not)
  refine ⟨-w j0 / c j0, ?_, ?_⟩
  · exact kernel_direction_preserves_zero_coordinates hcSupport hwL (-w j0 / c j0)
  · refine ⟨j0, hwL j0 hj0L, ?_⟩
    calc
      w j0 + (-w j0 / c j0) * c j0
          = w j0 + (-w j0) := by field_simp [hj0c]
      _ = 0 := by ring




theorem weighted_abs_affine_eq_weighted_root {w c s t : Real} (hc : c ≠ 0) :
    |w + t * c| * |s| = (|c| * |s|) * |t - (-w / c)| := by
  have h : w + t * c = c * (t - (-w / c)) := by
    field_simp [hc]
    ring
  rw [h, abs_mul]
  ring


theorem weighted_abs_affine_eq_const_of_slope_zero {w c s t : Real} (hc : c = 0) :
    |w + t * c| * |s| = |w| * |s| := by
  simp [hc]




theorem weighted_distance_root_bound_of_negative_side {m : Nat} {r a : Fin m -> Real}
    {A : Finset (Fin m)}
    (ha_zero : forall j : Fin m, j ∉ A -> a j = 0)
    (hnozero : forall j : Fin m, j ∈ A -> r j ≠ 0)
    {jn : Fin m}
    (hjN : jn ∈ A.filter (fun j => r j < 0))
    (hmax : MaximalFor (fun j => j ∈ A.filter (fun j => r j < 0)) r jn)
    (hWPleWN : (∑ j ∈ A.filter (fun j => 0 < r j), a j) <=
      ∑ j ∈ A.filter (fun j => r j < 0), a j) :
    (∑ j : Fin m, a j * |r jn - r j|) <=
      (∑ j : Fin m, a j * |0 - r j|) := by
  let N : Finset (Fin m) := A.filter (fun j => r j < 0)
  let P : Finset (Fin m) := A.filter (fun j => 0 < r j)
  have hjn_neg : r jn < 0 := (Finset.mem_filter.mp hjN).2
  have hnotNeg_eq_pos : A.filter (fun j => ¬ r j < 0) = P := by
    ext j
    constructor
    · intro hj
      have hjA : j ∈ A := (Finset.mem_filter.mp hj).1
      have hnlt : ¬ r j < 0 := (Finset.mem_filter.mp hj).2
      have h0le : 0 <= r j := le_of_not_gt hnlt
      have hpos : 0 < r j := lt_of_le_of_ne h0le (Ne.symm (hnozero j hjA))
      exact Finset.mem_filter.mpr ⟨hjA, hpos⟩
    · intro hj
      have hjA : j ∈ A := (Finset.mem_filter.mp hj).1
      have hpos : 0 < r j := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨hjA, not_lt_of_ge (le_of_lt hpos)⟩
  have hsplit (f : Fin m -> Real) :
      (∑ j ∈ A, f j) = (∑ j ∈ N, f j) + (∑ j ∈ P, f j) := by
    rw [← Finset.sum_filter_add_sum_filter_not A (fun j => r j < 0) f]
    rw [hnotNeg_eq_pos]
  have htotal (f : Fin m -> Real) :
      (∑ j : Fin m, a j * f j) = ∑ j ∈ A, a j * f j := by
    symm
    exact Finset.sum_subset (by simp) (fun j _ hj => by simp [ha_zero j hj])
  have hmax_le : forall j : Fin m, j ∈ N -> r j <= r jn := by
    intro j hj
    exact hmax.le (by simpa [N] using hj)
  have hLN : (∑ j ∈ N, a j * |r jn - r j|) =
      ∑ j ∈ N, a j * (r jn - r j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [abs_of_nonneg]
    exact sub_nonneg.mpr (hmax_le j hj)
  have hLP : (∑ j ∈ P, a j * |r jn - r j|) =
      ∑ j ∈ P, a j * (r j - r jn) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hp : 0 < r j := by simpa [P] using (Finset.mem_filter.mp hj).2
    have hnonpos : r jn - r j <= 0 := by linarith
    calc
      a j * |r jn - r j| = a j * (-(r jn - r j)) := by
        rw [abs_of_nonpos hnonpos]
      _ = a j * (r j - r jn) := by ring
  have hRN : (∑ j ∈ N, a j * |0 - r j|) = ∑ j ∈ N, a j * (-r j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hn : r j < 0 := by simpa [N] using (Finset.mem_filter.mp hj).2
    have hnonneg : 0 <= 0 - r j := by linarith
    calc
      a j * |0 - r j| = a j * (0 - r j) := by rw [abs_of_nonneg hnonneg]
      _ = a j * (-r j) := by ring
  have hRP : (∑ j ∈ P, a j * |0 - r j|) = ∑ j ∈ P, a j * r j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hp : 0 < r j := by simpa [P] using (Finset.mem_filter.mp hj).2
    have hnonpos : 0 - r j <= 0 := by linarith
    calc
      a j * |0 - r j| = a j * (-(0 - r j)) := by rw [abs_of_nonpos hnonpos]
      _ = a j * r j := by ring
  have hterm : r jn * ((∑ j ∈ N, a j) - (∑ j ∈ P, a j)) <= 0 := by
    have hdiff_nonneg : 0 <= (∑ j ∈ N, a j) - (∑ j ∈ P, a j) := by
      exact sub_nonneg.mpr (by simpa [N, P] using hWPleWN)
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hjn_neg) hdiff_nonneg
  rw [htotal (fun j => |r jn - r j|), htotal (fun j => |0 - r j|)]
  rw [hsplit (fun j => a j * |r jn - r j|), hsplit (fun j => a j * |0 - r j|)]
  rw [hLN, hLP, hRN, hRP]
  simp_rw [mul_sub, mul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hterm' : (∑ j ∈ N, a j) * r jn - (∑ j ∈ P, a j) * r jn <= 0 := by
    nlinarith [hterm]
  nlinarith [hterm']




theorem weighted_distance_root_bound_of_positive_side {m : Nat} {r a : Fin m -> Real}
    {A : Finset (Fin m)}
    (ha_zero : forall j : Fin m, j ∉ A -> a j = 0)
    (hnozero : forall j : Fin m, j ∈ A -> r j ≠ 0)
    {jp : Fin m}
    (hjP : jp ∈ A.filter (fun j => 0 < r j))
    (hmin : MinimalFor (fun j => j ∈ A.filter (fun j => 0 < r j)) r jp)
    (hWNleWP : (∑ j ∈ A.filter (fun j => r j < 0), a j) <=
      ∑ j ∈ A.filter (fun j => 0 < r j), a j) :
    (∑ j : Fin m, a j * |r jp - r j|) <=
      (∑ j : Fin m, a j * |0 - r j|) := by
  let N : Finset (Fin m) := A.filter (fun j => r j < 0)
  let P : Finset (Fin m) := A.filter (fun j => 0 < r j)
  have hjp_pos : 0 < r jp := (Finset.mem_filter.mp hjP).2
  have hnotNeg_eq_pos : A.filter (fun j => ¬ r j < 0) = P := by
    ext j
    constructor
    · intro hj
      have hjA : j ∈ A := (Finset.mem_filter.mp hj).1
      have hnlt : ¬ r j < 0 := (Finset.mem_filter.mp hj).2
      have h0le : 0 <= r j := le_of_not_gt hnlt
      have hpos : 0 < r j := lt_of_le_of_ne h0le (Ne.symm (hnozero j hjA))
      exact Finset.mem_filter.mpr ⟨hjA, hpos⟩
    · intro hj
      have hjA : j ∈ A := (Finset.mem_filter.mp hj).1
      have hpos : 0 < r j := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨hjA, not_lt_of_ge (le_of_lt hpos)⟩
  have hsplit (f : Fin m -> Real) :
      (∑ j ∈ A, f j) = (∑ j ∈ N, f j) + (∑ j ∈ P, f j) := by
    rw [← Finset.sum_filter_add_sum_filter_not A (fun j => r j < 0) f]
    rw [hnotNeg_eq_pos]
  have htotal (f : Fin m -> Real) :
      (∑ j : Fin m, a j * f j) = ∑ j ∈ A, a j * f j := by
    symm
    exact Finset.sum_subset (by simp) (fun j _ hj => by simp [ha_zero j hj])
  have hmin_le : forall j : Fin m, j ∈ P -> r jp <= r j := by
    intro j hj
    exact hmin.le (by simpa [P] using hj)
  have hLN : (∑ j ∈ N, a j * |r jp - r j|) =
      ∑ j ∈ N, a j * (r jp - r j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hn : r j < 0 := by simpa [N] using (Finset.mem_filter.mp hj).2
    have hnonneg : 0 <= r jp - r j := by linarith
    rw [abs_of_nonneg hnonneg]
  have hLP : (∑ j ∈ P, a j * |r jp - r j|) =
      ∑ j ∈ P, a j * (r j - r jp) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hnonpos : r jp - r j <= 0 := sub_nonpos.mpr (hmin_le j hj)
    calc
      a j * |r jp - r j| = a j * (-(r jp - r j)) := by
        rw [abs_of_nonpos hnonpos]
      _ = a j * (r j - r jp) := by ring
  have hRN : (∑ j ∈ N, a j * |0 - r j|) = ∑ j ∈ N, a j * (-r j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hn : r j < 0 := by simpa [N] using (Finset.mem_filter.mp hj).2
    have hnonneg : 0 <= 0 - r j := by linarith
    calc
      a j * |0 - r j| = a j * (0 - r j) := by rw [abs_of_nonneg hnonneg]
      _ = a j * (-r j) := by ring
  have hRP : (∑ j ∈ P, a j * |0 - r j|) = ∑ j ∈ P, a j * r j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hp : 0 < r j := by simpa [P] using (Finset.mem_filter.mp hj).2
    have hnonpos : 0 - r j <= 0 := by linarith
    calc
      a j * |0 - r j| = a j * (-(0 - r j)) := by rw [abs_of_nonpos hnonpos]
      _ = a j * r j := by ring
  have hterm : r jp * ((∑ j ∈ N, a j) - (∑ j ∈ P, a j)) <= 0 := by
    have hdiff_nonpos : (∑ j ∈ N, a j) - (∑ j ∈ P, a j) <= 0 := by
      exact sub_nonpos.mpr (by simpa [N, P] using hWNleWP)
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hjp_pos) hdiff_nonpos
  rw [htotal (fun j => |r jp - r j|), htotal (fun j => |0 - r j|)]
  rw [hsplit (fun j => a j * |r jp - r j|), hsplit (fun j => a j * |0 - r j|)]
  rw [hLN, hLP, hRN, hRP]
  simp_rw [mul_sub, mul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hterm' : (∑ j ∈ N, a j) * r jp - (∑ j ∈ P, a j) * r jp <= 0 := by
    nlinarith [hterm]
  nlinarith [hterm']




theorem exists_weighted_distance_root_bound :
  forall {m : Nat} {r a : Fin m -> Real} {A : Finset (Fin m)},
    A.Nonempty ->
    (forall j : Fin m, 0 <= a j) ->
    (forall j : Fin m, j ∉ A -> a j = 0) ->
      exists j0 : Fin m,
        j0 ∈ A /\
        (∑ j : Fin m, a j * |r j0 - r j|) <=
          (∑ j : Fin m, a j * |0 - r j|) := by
  classical
  intro m r a A hAne ha_nonneg ha_zero
  by_cases hzero : exists j : Fin m, j ∈ A /\ r j = 0
  · rcases hzero with ⟨j0, hj0A, hj0r⟩
    refine ⟨j0, hj0A, ?_⟩
    simp [hj0r]
  · have hnozero : forall j : Fin m, j ∈ A -> r j ≠ 0 := by
      intro j hjA hrj
      exact hzero ⟨j, hjA, hrj⟩
    let N : Finset (Fin m) := A.filter (fun j => r j < 0)
    let P : Finset (Fin m) := A.filter (fun j => 0 < r j)
    have hside : N.Nonempty ∨ P.Nonempty := by
      rcases hAne with ⟨j, hjA⟩
      rcases lt_or_gt_of_ne (hnozero j hjA) with hneg | hpos
      · exact Or.inl ⟨j, by simp [N, hjA, hneg]⟩
      · exact Or.inr ⟨j, by simp [P, hjA, hpos]⟩
    by_cases hN : N.Nonempty
    · by_cases hWPleWN : (∑ j ∈ P, a j) <= ∑ j ∈ N, a j
      · rcases Finset.exists_maximalFor r N hN with ⟨jn, hmax⟩
        have hjN : jn ∈ A.filter (fun j => r j < 0) := by simpa [N] using hmax.1
        refine ⟨jn, (Finset.mem_filter.mp hjN).1, ?_⟩
        exact weighted_distance_root_bound_of_negative_side (r := r) (a := a) (A := A)
          ha_zero hnozero hjN hmax (by simpa [N, P] using hWPleWN)
      · have hWNleWP : (∑ j ∈ N, a j) <= ∑ j ∈ P, a j := le_of_not_ge hWPleWN
        have hP : P.Nonempty := by
          by_contra hPempty
          have hP_eq_empty : P = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro j hj
            exact hPempty ⟨j, hj⟩
          have hWP_zero : (∑ j ∈ P, a j) = 0 := by simp [hP_eq_empty]
          have hWN_nonneg : 0 <= ∑ j ∈ N, a j := by
            exact Finset.sum_nonneg (fun j hj => ha_nonneg j)
          exact hWPleWN (by simpa [hWP_zero] using hWN_nonneg)
        rcases Finset.exists_minimalFor r P hP with ⟨jp, hmin⟩
        have hjP : jp ∈ A.filter (fun j => 0 < r j) := by simpa [P] using hmin.1
        refine ⟨jp, (Finset.mem_filter.mp hjP).1, ?_⟩
        exact weighted_distance_root_bound_of_positive_side (r := r) (a := a) (A := A)
          ha_zero hnozero hjP hmin (by simpa [N, P] using hWNleWP)
    · have hP : P.Nonempty := by
        rcases hside with hN' | hP'
        · exact (hN hN').elim
        · exact hP'
      have hWNleWP : (∑ j ∈ N, a j) <= ∑ j ∈ P, a j := by
        have hN_eq_empty : N = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro j hj
          exact hN ⟨j, hj⟩
        have hWN_zero : (∑ j ∈ N, a j) = 0 := by simp [hN_eq_empty]
        have hWP_nonneg : 0 <= ∑ j ∈ P, a j := by
          exact Finset.sum_nonneg (fun j hj => ha_nonneg j)
        simpa [hWN_zero] using hWP_nonneg
      rcases Finset.exists_minimalFor r P hP with ⟨jp, hmin⟩
      have hjP : jp ∈ A.filter (fun j => 0 < r j) := by simpa [P] using hmin.1
      refine ⟨jp, (Finset.mem_filter.mp hjP).1, ?_⟩
      exact weighted_distance_root_bound_of_positive_side (r := r) (a := a) (A := A)
        ha_zero hnozero hjP hmin (by simpa [N, P] using hWNleWP)




theorem exists_weighted_affine_breakpoint_bound :
  forall {m : Nat} {w s c : Fin m -> Real},
    c ≠ 0 ->
      exists j0 : Fin m,
        c j0 ≠ 0 /\
        (∑ j : Fin m, |w j + (-w j0 / c j0) * c j| * |s j|) <=
          (∑ j : Fin m, |w j| * |s j|) := by
  classical
  intro m w s c hcNe
  let A : Finset (Fin m) := Finset.univ.filter (fun j => c j ≠ 0)
  let r : Fin m -> Real := fun j => if h : c j ≠ 0 then -w j / c j else 0
  let a : Fin m -> Real := fun j => |c j| * |s j|
  have hAne : A.Nonempty := by
    have hexists : exists j : Fin m, c j ≠ 0 := by
      by_contra h
      apply hcNe
      funext j
      by_contra hcj
      exact h ⟨j, hcj⟩
    rcases hexists with ⟨j, hj⟩
    exact ⟨j, by simp [A, hj]⟩
  have ha_nonneg : forall j : Fin m, 0 <= a j := by
    intro j
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have ha_zero : forall j : Fin m, j ∉ A -> a j = 0 := by
    intro j hjA
    have hcj : c j = 0 := by
      by_contra hcjne
      exact hjA (by simp [A, hcjne])
    simp [a, hcj]
  rcases exists_weighted_distance_root_bound (r := r) (a := a) (A := A)
      hAne ha_nonneg ha_zero with ⟨j0, hj0A, hmedian⟩
  have hj0c : c j0 ≠ 0 := by
    simpa [A] using hj0A
  refine ⟨j0, hj0c, ?_⟩
  let lhs : Fin m -> Real := fun j => |w j + (-w j0 / c j0) * c j| * |s j|
  let rhs : Fin m -> Real := fun j => |w j| * |s j|
  let distL : Fin m -> Real := fun j => a j * |r j0 - r j|
  let distR : Fin m -> Real := fun j => a j * |0 - r j|
  let I : Finset (Fin m) := Finset.univ.filter (fun j => ¬ c j ≠ 0)
  have hL_active : forall j : Fin m, j ∈ A -> lhs j = distL j := by
    intro j hjA
    have hcj : c j ≠ 0 := by simpa [A] using hjA
    have hrj0 : r j0 = -w j0 / c j0 := by simp [r, hj0c]
    have hrj : r j = -w j / c j := by simp [r, hcj]
    calc
      lhs j = (|c j| * |s j|) * |(-w j0 / c j0) - (-w j / c j)| := by
        simpa [lhs] using weighted_abs_affine_eq_weighted_root (w := w j) (c := c j)
          (s := s j) (t := -w j0 / c j0) hcj
      _ = distL j := by simp [distL, a, hrj0, hrj, mul_assoc]
  have hR_active : forall j : Fin m, j ∈ A -> rhs j = distR j := by
    intro j hjA
    have hcj : c j ≠ 0 := by simpa [A] using hjA
    have hrj : r j = -w j / c j := by simp [r, hcj]
    calc
      rhs j = (|c j| * |s j|) * |(0 : Real) - (-w j / c j)| := by
        simpa [rhs, zero_mul] using weighted_abs_affine_eq_weighted_root (w := w j)
          (c := c j) (s := s j) (t := 0) hcj
      _ = distR j := by simp [distR, a, hrj, mul_assoc]
  have h_inactive : forall j : Fin m, j ∉ A -> lhs j = rhs j := by
    intro j hjA
    have hcj : c j = 0 := by
      by_contra hcjne
      exact hjA (by simp [A, hcjne])
    simp [lhs, rhs, hcj]
  have hsumL : (∑ j : Fin m, lhs j) = (∑ j ∈ A, lhs j) + (∑ j ∈ I, lhs j) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => c j ≠ 0) lhs]
  have hsumR : (∑ j : Fin m, rhs j) = (∑ j ∈ A, rhs j) + (∑ j ∈ I, rhs j) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => c j ≠ 0) rhs]
  have hdistL : (∑ j ∈ A, lhs j) = ∑ j ∈ A, distL j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact hL_active j hj
  have hdistR : (∑ j ∈ A, rhs j) = ∑ j ∈ A, distR j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact hR_active j hj
  have hcomp : (∑ j ∈ I, lhs j) = ∑ j ∈ I, rhs j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjA : j ∉ A := by
      have : ¬ c j ≠ 0 := by simpa [I] using hj
      intro hja
      exact this (by simpa [A] using hja)
    exact h_inactive j hjA
  have hmedianA : (∑ j ∈ A, distL j) <= ∑ j ∈ A, distR j := by
    have hDL_zero : forall j : Fin m, j ∉ A -> distL j = 0 := by
      intro j hj
      simp [distL, ha_zero j hj]
    have hDR_zero : forall j : Fin m, j ∉ A -> distR j = 0 := by
      intro j hj
      simp [distR, ha_zero j hj]
    have hDL : (∑ j : Fin m, distL j) = ∑ j ∈ A, distL j := by
      symm
      exact Finset.sum_subset (by simp) (fun j _ hj => hDL_zero j hj)
    have hDR : (∑ j : Fin m, distR j) = ∑ j ∈ A, distR j := by
      symm
      exact Finset.sum_subset (by simp) (fun j _ hj => hDR_zero j hj)
    have hmedian' : (∑ j : Fin m, distL j) <= ∑ j : Fin m, distR j := by
      simpa [distL, distR, sub_eq_add_neg, abs_neg] using hmedian
    rwa [hDL, hDR] at hmedian'
  rw [hsumL, hsumR, hdistL, hdistR, hcomp]
  exact add_le_add hmedianA le_rfl



theorem exists_weighted_kernel_pivot_bound :
  forall {m : Nat} {L : Finset (Fin m)} {w s c : Fin m -> Real},
    c ≠ 0 ->
    (forall j : Fin m, j ∉ L -> c j = 0) ->
    (forall j : Fin m, j ∈ L -> w j ≠ 0) ->
      exists t : Real,
        (exists j : Fin m, w j ≠ 0 /\ w j + t * c j = 0) /\
        (∑ j : Fin m, |w j + t * c j| * |s j|) <=
          (∑ j : Fin m, |w j| * |s j|) := by
  intro m L w s c hcNe hcSupport hwL
  rcases exists_weighted_affine_breakpoint_bound (w := w) (s := s) (c := c) hcNe with
    ⟨j0, hj0c, hbound⟩
  have hj0L : j0 ∈ L := by
    by_contra hj0not
    exact hj0c (hcSupport j0 hj0not)
  refine ⟨-w j0 / c j0, ?_, hbound⟩
  refine ⟨j0, hwL j0 hj0L, ?_⟩
  calc
    w j0 + (-w j0 / c j0) * c j0
        = w j0 + (-w j0) := by field_simp [hj0c]
    _ = 0 := by ring


theorem exists_weighted_kernel_pivot :
  forall {m : Nat} {L : Finset (Fin m)} {w s c : Fin m -> Real},
    c ≠ 0 ->
    (forall j : Fin m, j ∉ L -> c j = 0) ->
    (forall j : Fin m, j ∈ L -> w j ≠ 0) ->
      exists t : Real,
        (forall j : Fin m, w j = 0 -> w j + t * c j = 0) /\
        (exists j : Fin m, w j ≠ 0 /\ w j + t * c j = 0) /\
        (∑ j : Fin m, |w j + t * c j| * |s j|) <=
          (∑ j : Fin m, |w j| * |s j|) := by
  intro m L w s c hcNe hcSupport hwL
  rcases exists_weighted_kernel_pivot_bound (L := L) (w := w) (s := s) (c := c)
      hcNe hcSupport hwL with ⟨t, htKill, htWeight⟩
  exact ⟨t, kernel_direction_preserves_zero_coordinates hcSupport hwL t, htKill, htWeight⟩



theorem exists_smaller_support_solution_weighted_sum_le :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real}
      {u : Fin n -> Real} {w s : Fin m -> Real},
    (forall i : Fin n, (∑ j : Fin m, B i j * w j) = u i) ->
    (exists L : Finset (Fin m), L.card = n + 1 /\ forall j : Fin m, j ∈ L -> w j ≠ 0) ->
      exists w' : Fin m -> Real,
        (forall i : Fin n, (∑ j : Fin m, B i j * w' j) = u i) /\
        (forall j : Fin m, w j = 0 -> w' j = 0) /\
        (exists j : Fin m, w j ≠ 0 /\ w' j = 0) /\
        (∑ j : Fin m, |w' j| * |s j|) <=
          (∑ j : Fin m, |w j| * |s j|) := by
  classical
  intro n m B u w s hsol hL
  rcases hL with ⟨L, hLcard, hLnonzero⟩
  rcases exists_nonzero_kernel_vector_supported_on_card_succ (B := B) hLcard with
    ⟨c, hcNe, hcSupport, hcKer⟩
  rcases exists_weighted_kernel_pivot (L := L) (w := w) (s := s) (c := c)
      hcNe hcSupport hLnonzero with ⟨t, htSupport, htKill, htWeight⟩
  let w' : Fin m -> Real := fun j => w j + t * c j
  refine ⟨w', ?_, ?_, ?_, ?_⟩
  · intro i
    calc
      (∑ j : Fin m, B i j * w' j)
          = ∑ j : Fin m, (B i j * w j + t * (c j * B i j)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              simp [w', mul_add, mul_left_comm, mul_comm]
      _ = (∑ j : Fin m, B i j * w j) + t * (∑ j : Fin m, c j * B i j) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = u i := by
              rw [hsol i, hcKer i, mul_zero, add_zero]
  · intro j hj
    exact htSupport j hj
  · rcases htKill with ⟨j, hwj, hkill⟩
    exact ⟨j, hwj, hkill⟩
  · simpa [w'] using htWeight




theorem exists_solution_support_card_le_weighted_sum_le :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real}
      {u : Fin n -> Real} {w s : Fin m -> Real},
    (forall i : Fin n, (∑ j : Fin m, B i j * w j) = u i) ->
      exists w' : Fin m -> Real,
        (forall i : Fin n, (∑ j : Fin m, B i j * w' j) = u i) /\
        (forall j : Fin m, w j = 0 -> w' j = 0) /\
        (Finset.univ.filter (fun j : Fin m => w' j ≠ 0)).card <= n /\
        (∑ j : Fin m, |w' j| * |s j|) <=
          (∑ j : Fin m, |w j| * |s j|) := by
  classical
  intro n m B u w s hsol
  let support : (Fin m -> Real) -> Finset (Fin m) :=
    fun z => Finset.univ.filter (fun j : Fin m => z j ≠ 0)
  let P : Finset (Fin m) -> Prop := fun S =>
    forall z : Fin m -> Real,
      support z = S ->
      (forall i : Fin n, (∑ j : Fin m, B i j * z j) = u i) ->
        exists z' : Fin m -> Real,
          (forall i : Fin n, (∑ j : Fin m, B i j * z' j) = u i) /\
          (forall j : Fin m, z j = 0 -> z' j = 0) /\
          (support z').card <= n /\
          (∑ j : Fin m, |z' j| * |s j|) <=
            (∑ j : Fin m, |z j| * |s j|)
  have hP : forall S : Finset (Fin m), P S := by
    intro S
    refine S.strongInductionOn ?_
    intro S ih z hzS hzsol
    by_cases hsmall : S.card <= n
    · refine ⟨z, hzsol, ?_, ?_, le_rfl⟩
      · intro j hj
        exact hj
      · simpa [hzS]
    · have hlarge : n + 1 <= S.card := Nat.succ_le_of_lt (lt_of_not_ge hsmall)
      rcases Finset.exists_subset_card_eq (s := S) hlarge with ⟨L, hLS, hLcard⟩
      have hLnonzero : forall j : Fin m, j ∈ L -> z j ≠ 0 := by
        intro j hjL
        have hjS : j ∈ support z := by
          rw [hzS]
          exact hLS hjL
        exact (Finset.mem_filter.mp hjS).2
      rcases exists_smaller_support_solution_weighted_sum_le (B := B) (u := u) (w := z)
          (s := s) hzsol ⟨L, hLcard, hLnonzero⟩ with
        ⟨z1, hz1sol, hz1_no_new, hz1_kills, hz1_weight⟩
      have hsupp1_subset : support z1 ⊆ S := by
        intro j hj
        have hz1j : z1 j ≠ 0 := (Finset.mem_filter.mp hj).2
        by_contra hjS
        have hzj_zero : z j = 0 := by
          by_contra hzj
          exact hjS (by
            rw [← hzS]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hzj⟩)
        exact hz1j (hz1_no_new j hzj_zero)
      have hsupp1_ssubset : support z1 ⊂ S := by
        refine ⟨hsupp1_subset, ?_⟩
        intro hreverse
        rcases hz1_kills with ⟨j, hzj, hz1j⟩
        have hjS : j ∈ S := by
          rw [← hzS]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hzj⟩
        have hjSupp1 : j ∈ support z1 := hreverse hjS
        exact (Finset.mem_filter.mp hjSupp1).2 hz1j
      rcases ih (support z1) hsupp1_ssubset z1 rfl hz1sol with
        ⟨z2, hz2sol, hz2_no_new, hz2_card, hz2_weight⟩
      refine ⟨z2, hz2sol, ?_, hz2_card, ?_⟩
      · intro j hzj
        exact hz2_no_new j (hz1_no_new j hzj)
      · exact hz2_weight.trans hz1_weight
  exact hP (support w) w rfl hsol

private theorem sum_orderEmbOfFin {α β : Type*} [LinearOrder α] [AddCommMonoid β]
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

private theorem sum_eq_sum_support_mul {m : Nat} (w f : Fin m -> Real) :
    (∑ j : Fin m, f j * w j) =
      ∑ j ∈ (Finset.univ.filter (fun j : Fin m => w j ≠ 0)), f j * w j := by
  classical
  symm
  exact Finset.sum_subset (by simp) (fun j _ hj => by
    have hwj : w j = 0 := by
      by_contra hwj
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hwj⟩)
    simp [hwj])

private theorem abs_le_weightedSupNormFin_mul_abs :
  forall {n : Nat} {v u : Fin n -> Real},
    (forall i : Fin n, u i ≠ 0) ->
      forall i : Fin n, |v i| <= weightedSupNormFin v u * |u i| := by
  intro n v u hu i
  let beta : Real := weightedSupNormFin v u
  have hle : |v i / u i| <= beta := by
    exact le_csSup (Finite.bddAbove_range fun k : Fin n => |v k / u k|)
      (Set.mem_range_self i)
  have hrewrite : |v i| = |v i / u i| * |u i| := by
    have hv : (v i / u i) * u i = v i := by
      field_simp [hu i]
    calc
      |v i| = |(v i / u i) * u i| := by rw [hv]
      _ = |v i / u i| * |u i| := by rw [abs_mul]
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg (u i))






theorem exists_good_basis :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real}
      {x s : Fin m -> Real} {v u : Fin n -> Real},
    IsTotallyPositiveFinite B ->
    IsStrictlyAlternatingFin u ->
    (forall i : Fin n, (∑ j : Fin m, B i j * x j) = u i) ->
      exists cols : Fin n -> Fin m,
        Function.Injective cols /\
        (Matrix.of fun i j => B i (cols j)).det ≠ 0 /\
        (∑ k : Fin n,
          |(∑ i : Fin n, ((Matrix.of fun r c => B r (cols c))⁻¹ k i) * v i)| *
            |s (cols k)|) <=
          weightedSupNormFin v u * (∑ j : Fin m, |x j| * |s j|)
    := by
  classical
  intro n m B x s v u hTP hAlt hxsol
  rcases exists_solution_support_card_le_weighted_sum_le (B := B) (u := u) (w := x)
      (s := s) hxsol with ⟨w, hwsol, hw_no_new, hw_card_le, hw_weight⟩
  let S : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => w j ≠ 0)
  have hS_card_le : S.card <= n := by
    simpa [S] using hw_card_le
  let colsS : Fin S.card -> Fin m := S.orderEmbOfFin rfl
  let Bsub : Matrix (Fin n) (Fin S.card) Real := fun i k => B i (colsS k)
  let wS : Fin S.card -> Real := fun k => w (colsS k)
  have hTPsub : IsTotallyPositiveFinite Bsub := by
    intro r rows cols hrows hcols
    have hcols' : StrictMono (fun q : Fin r => ((colsS (cols q)).val)) := by
      intro a b hab
      exact (S.orderEmbOfFin rfl).strictMono (hcols hab)
    exact hTP r rows (fun q => colsS (cols q)) hrows hcols'
  have hsubSol : forall i : Fin n, (∑ k : Fin S.card, Bsub i k * wS k) = u i := by
    intro i
    calc
      (∑ k : Fin S.card, Bsub i k * wS k)
          = ∑ j ∈ S, B i j * w j := by
              simpa [Bsub, wS, colsS] using
                sum_orderEmbOfFin S rfl (fun j : Fin m => B i j * w j)
      _ = ∑ j : Fin m, B i j * w j := by
              symm
              simpa [S] using sum_eq_sum_support_mul w (fun j : Fin m => B i j)
      _ = u i := hwsol i
  have hAltSub : IsStrictlyAlternatingFin
      (fun i : Fin n => ∑ k : Fin S.card, Bsub i k * wS k) := by
    have hvec : (fun i : Fin n => ∑ k : Fin S.card, Bsub i k * wS k) = u := by
      funext i
      exact hsubSol i
    simpa [hvec] using hAlt
  have hLI_sub : LinearIndependent Real
      (fun i : Fin n => fun j : Fin S.card => Bsub i j) :=
    rank_eq_rows_of_totallyPositive_of_alternating_image (B := Bsub) (x := wS)
      hS_card_le hTPsub hAltSub
  have hn_le_card : n <= S.card := by
    have hdim := hLI_sub.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using hdim
  have hS_card : S.card = n := le_antisymm hS_card_le hn_le_card
  let cols : Fin n -> Fin m := S.orderEmbOfFin hS_card
  let C : Matrix (Fin n) (Fin n) Real := Matrix.of fun i k => B i (cols k)
  let wC : Fin n -> Real := fun k => w (cols k)
  have hTP_C : IsTotallyPositiveFinite C := by
    intro r rows cols' hrows hcols
    have hcols' : StrictMono (fun q : Fin r => ((cols (cols' q)).val)) := by
      intro a b hab
      exact (S.orderEmbOfFin hS_card).strictMono (hcols hab)
    exact hTP r rows (fun q => cols (cols' q)) hrows hcols'
  have hCsol : forall i : Fin n, (∑ k : Fin n, C i k * wC k) = u i := by
    intro i
    calc
      (∑ k : Fin n, C i k * wC k)
          = ∑ j ∈ S, B i j * w j := by
              simpa [C, wC, cols] using
                sum_orderEmbOfFin S hS_card (fun j : Fin m => B i j * w j)
      _ = ∑ j : Fin m, B i j * w j := by
              symm
              simpa [S] using sum_eq_sum_support_mul w (fun j : Fin m => B i j)
      _ = u i := hwsol i
  have hAltC : IsStrictlyAlternatingFin
      (fun i : Fin n => ∑ k : Fin n, C i k * wC k) := by
    have hvec : (fun i : Fin n => ∑ k : Fin n, C i k * wC k) = u := by
      funext i
      exact hCsol i
    simpa [hvec] using hAlt
  have hLI_C : LinearIndependent Real C.row :=
    rank_eq_rows_of_totallyPositive_of_alternating_image (B := C) (x := wC)
      (le_refl n) hTP_C hAltC
  have hdet : C.det ≠ 0 := by
    have hUnitMatrix : IsUnit C := Matrix.linearIndependent_rows_iff_isUnit.mp hLI_C
    have hUnitDet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hUnitMatrix
    exact IsUnit.ne_zero hUnitDet
  let beta : Real := weightedSupNormFin v u
  have hbeta_nonneg : 0 <= beta := by
    exact Real.sSup_nonneg (Set.forall_mem_range.2 (fun i => abs_nonneg _))
  let yb : Fin n -> Real := fun k => ∑ i : Fin n, C⁻¹ k i * v i
  have hv_bound : forall i : Fin n, |v i| <= beta * |u i| := by
    intro i
    simpa [beta] using abs_le_weightedSupNormFin_mul_abs hAlt.1 i
  have hyb_bound : forall k : Fin n, |yb k| <= beta * |wC k| := by
    intro k
    have hsum_abs :
        (∑ i : Fin n, |C⁻¹ k i * v i|) =
          ∑ i : Fin n, |C⁻¹ k i| * |v i| := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [abs_mul]
    have hsum_le :
        (∑ i : Fin n, |C⁻¹ k i| * |v i|) <=
          ∑ i : Fin n, |C⁻¹ k i| * (beta * |u i|) := by
      refine Finset.sum_le_sum ?_
      intro i _
      exact mul_le_mul_of_nonneg_left (hv_bound i) (abs_nonneg _)
    have hpull :
        (∑ i : Fin n, |C⁻¹ k i| * (beta * |u i|)) =
          beta * (∑ i : Fin n, |C⁻¹ k i| * |u i|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have hinv :
        (∑ i : Fin n, |C⁻¹ k i| * |u i|) = |wC k| := by
      have hinvRaw :
          (∑ i : Fin n,
            |C⁻¹ k i| * |(∑ j : Fin n, C i j * wC j)|) = |wC k| :=
        abs_inverse_mul_alternating_eq_abs (B := C) (w := wC) hTP_C hdet hAltC k
      calc
        (∑ i : Fin n, |C⁻¹ k i| * |u i|)
            = ∑ i : Fin n, |C⁻¹ k i| * |(∑ j : Fin n, C i j * wC j)| := by
                refine Finset.sum_congr rfl ?_
                intro i _
                rw [hCsol i]
        _ = |wC k| := hinvRaw
    calc
      |yb k| <= ∑ i : Fin n, |C⁻¹ k i * v i| := by
        simpa [yb] using Finset.abs_sum_le_sum_abs
          (fun i : Fin n => C⁻¹ k i * v i) Finset.univ
      _ = ∑ i : Fin n, |C⁻¹ k i| * |v i| := hsum_abs
      _ <= ∑ i : Fin n, |C⁻¹ k i| * (beta * |u i|) := hsum_le
      _ = beta * (∑ i : Fin n, |C⁻¹ k i| * |u i|) := hpull
      _ = beta * |wC k| := by rw [hinv]
  have hsupport_weight :
      (∑ k : Fin n, |wC k| * |s (cols k)|) =
        ∑ j : Fin m, |w j| * |s j| := by
    calc
      (∑ k : Fin n, |wC k| * |s (cols k)|)
          = ∑ j ∈ S, |w j| * |s j| := by
              simpa [wC, cols] using
                sum_orderEmbOfFin S hS_card (fun j : Fin m => |w j| * |s j|)
      _ = ∑ j : Fin m, |w j| * |s j| := by
              exact Finset.sum_subset (by simp) (fun j _ hj => by
                have hwj : w j = 0 := by
                  by_contra hwj
                  exact hj (by
                    simp [S, hwj])
                simp [hwj])
  have hsum_yb :
      (∑ k : Fin n, |yb k| * |s (cols k)|) <=
        beta * (∑ j : Fin m, |w j| * |s j|) := by
    calc
      (∑ k : Fin n, |yb k| * |s (cols k)|)
          <= ∑ k : Fin n, (beta * |wC k|) * |s (cols k)| := by
              refine Finset.sum_le_sum ?_
              intro k _
              exact mul_le_mul_of_nonneg_right (hyb_bound k) (abs_nonneg _)
      _ = beta * (∑ k : Fin n, |wC k| * |s (cols k)|) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro k _
              ring
      _ = beta * (∑ j : Fin m, |w j| * |s j|) := by
              rw [hsupport_weight]
  refine ⟨cols, (S.orderEmbOfFin hS_card).injective, ?_, ?_⟩
  · simpa [C, cols] using hdet
  · have hfinal :
        (∑ k : Fin n, |yb k| * |s (cols k)|) <=
          beta * (∑ j : Fin m, |x j| * |s j|) := by
      exact hsum_yb.trans (mul_le_mul_of_nonneg_left hw_weight hbeta_nonneg)
    simpa [yb, C, cols, beta] using hfinal



theorem exists_vector_representing_bounded_functional_on_l1_fin :
  forall {n : Nat} (F : (Fin n -> Real) →L[Real] Real) (beta : Real),
    0 <= beta ->
    (forall a : Fin n -> Real, |F a| <= beta * (∑ k : Fin n, |a k|)) ->
      exists y : Fin n -> Real,
        (forall k : Fin n, |y k| <= beta) /\
          forall a : Fin n -> Real, (∑ k : Fin n, y k * a k) = F a := by
  intro n F beta hbeta hF
  refine ⟨fun k => F (Pi.single k 1), ?_, ?_⟩
  · intro k
    have hsingle : (∑ i : Fin n, |Pi.single k (1 : Real) i|) = 1 := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik
        simp [Pi.single_eq_of_ne hik]
      · intro hk
        simp at hk
    simpa [hsingle] using hF (Pi.single k (1 : Real))
  · intro a
    have hdecomp : (∑ k : Fin n, a k • Pi.single k (1 : Real)) = a := by
      ext i
      simp [Pi.single_apply]
    calc
      (∑ k : Fin n, F (Pi.single k (1 : Real)) * a k)
          = ∑ k : Fin n, F (a k • Pi.single k (1 : Real)) := by
              refine Finset.sum_congr rfl ?_
              intro k _
              rw [F.map_smul]
              simp [mul_comm]
      _ = F (∑ k : Fin n, a k • Pi.single k (1 : Real)) := by
              rw [map_sum]
      _ = F a := by rw [hdecomp]




theorem finite_linf_duality_surjective :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real} {v : Fin n -> Real} {C : Real},
    0 <= C ->
    (forall a : Fin n -> Real,
      |(∑ i : Fin n, a i * v i)| <=
        C * (∑ j : Fin m, |(∑ i : Fin n, a i * B i j)|)) ->
      exists y : Fin m -> Real,
        (forall i : Fin n, (∑ j : Fin m, B i j * y j) = v i) /\
        forall j : Fin m, |y j| <= C := by
  classical
  intro n m B v C hC hdual
  let L : (Fin n -> Real) →ₗ[Real] (Fin m -> Real) :=
    { toFun := fun a j => ∑ i : Fin n, a i * B i j
      map_add' := by
        intro a b
        ext j
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext j
        simp [mul_assoc, Finset.mul_sum] }
  let Fv : (Fin n -> Real) →ₗ[Real] Real :=
    { toFun := fun a => ∑ i : Fin n, a i * v i
      map_add' := by
        intro a b
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp [mul_assoc, Finset.mul_sum] }
  have hwell : forall a b : Fin n -> Real, L a = L b -> Fv a = Fv b := by
    intro a b hab
    have hdiffL : forall j : Fin m, (∑ i : Fin n, (a i - b i) * B i j) = 0 := by
      intro j
      have hcomp := congrFun hab j
      simpa [L, sub_mul, Finset.sum_sub_distrib] using sub_eq_zero.mpr hcomp
    have h := hdual (fun i => a i - b i)
    have hzero_sum : (∑ j : Fin m, |(∑ i : Fin n, (a i - b i) * B i j)|) = 0 := by
      simp [hdiffL]
    have hF_abs : |(∑ i : Fin n, (a i - b i) * v i)| <= 0 := by
      simpa [hzero_sum] using h
    have hF_zero : (∑ i : Fin n, (a i - b i) * v i) = 0 := abs_nonpos_iff.mp hF_abs
    have : Fv (a - b) = 0 := by
      simpa [Fv, Pi.sub_apply, sub_mul] using hF_zero
    have hsub : Fv a - Fv b = 0 := by
      simpa using congrArg id this
    exact sub_eq_zero.mp hsub
  let f : (Fin m -> Real) →ₗ.[Real] Real :=
    { domain := LinearMap.range L
      toFun :=
        { toFun := fun z => Fv (Classical.choose ((LinearMap.mem_range).mp z.2))
          map_add' := by
            intro z w
            let az : Fin n -> Real := Classical.choose ((LinearMap.mem_range).mp z.2)
            let aw : Fin n -> Real := Classical.choose ((LinearMap.mem_range).mp w.2)
            let azw : Fin n -> Real := Classical.choose ((LinearMap.mem_range).mp (z + w).2)
            have hz : L az = z := Classical.choose_spec ((LinearMap.mem_range).mp z.2)
            have hw : L aw = w := Classical.choose_spec ((LinearMap.mem_range).mp w.2)
            have hzw : L azw = z + w := Classical.choose_spec ((LinearMap.mem_range).mp (z + w).2)
            have hLsum : L azw = L (az + aw) := by
              rw [hzw, map_add, hz, hw]
            have hF := hwell azw (az + aw) hLsum
            rw [hF]
            exact Fv.map_add az aw
          map_smul' := by
            intro c z
            let az : Fin n -> Real := Classical.choose ((LinearMap.mem_range).mp z.2)
            let acz : Fin n -> Real := Classical.choose ((LinearMap.mem_range).mp (c • z).2)
            have hz : L az = z := Classical.choose_spec ((LinearMap.mem_range).mp z.2)
            have hcz : L acz = c • z := Classical.choose_spec ((LinearMap.mem_range).mp (c • z).2)
            have hLsmul : L acz = L (c • az) := by
              rw [hcz, map_smul, hz]
            have hF := hwell acz (c • az) hLsmul
            rw [hF]
            exact Fv.map_smul c az } }
  let N : (Fin m -> Real) -> Real := fun s => C * (∑ j : Fin m, |s j|)
  have N_hom : forall c : Real, 0 < c -> forall s : Fin m -> Real, N (c • s) = c * N s := by
    intro c hc s
    have hsum : (∑ j : Fin m, |c * s j|) = c * (∑ j : Fin m, |s j|) := by
      calc
        (∑ j : Fin m, |c * s j|) = ∑ j : Fin m, c * |s j| := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simp [abs_mul, abs_of_pos hc]
        _ = c * (∑ j : Fin m, |s j|) := by rw [Finset.mul_sum]
    dsimp [N]
    rw [hsum]
    ring
  have N_add : forall s t : Fin m -> Real, N (s + t) <= N s + N t := by
    intro s t
    have hsum : (∑ j : Fin m, |(s + t) j|) <= (∑ j : Fin m, |s j|) + (∑ j : Fin m, |t j|) := by
      calc
        (∑ j : Fin m, |(s + t) j|) <= ∑ j : Fin m, (|s j| + |t j|) := by
          refine Finset.sum_le_sum ?_
          intro j _
          simpa using abs_add_le (s j) (t j)
        _ = (∑ j : Fin m, |s j|) + (∑ j : Fin m, |t j|) := by
          rw [Finset.sum_add_distrib]
    dsimp [N]
    calc
      C * (∑ j : Fin m, |(s + t) j|) <= C * ((∑ j : Fin m, |s j|) + (∑ j : Fin m, |t j|)) := by
        exact mul_le_mul_of_nonneg_left hsum hC
      _ = C * (∑ j : Fin m, |s j|) + C * (∑ j : Fin m, |t j|) := by ring
  have hf_bound : forall z : f.domain, f z <= N z := by
    intro z
    let a : Fin n -> Real := Classical.choose ((LinearMap.mem_range).mp z.2)
    have hz : L a = z := Classical.choose_spec ((LinearMap.mem_range).mp z.2)
    have h := hdual a
    have hF_abs : |Fv a| <= N z := by
      have h' : |Fv a| <= C * (∑ j : Fin m, |(L a) j|) := by
        simpa [Fv, L] using h
      have hsum_eq : (∑ j : Fin m, |(L a) j|) = ∑ j : Fin m, |(z : Fin m -> Real) j| := by
        rw [hz]
      simpa [N, hsum_eq] using h'
    have hf_eq : f z = Fv a := by rfl
    rw [hf_eq]
    exact le_trans (le_abs_self _) hF_abs
  rcases exists_extension_of_le_sublinear f N N_hom N_add hf_bound with ⟨g, hg_ext, hg_bound⟩
  have hg_abs : forall s : Fin m -> Real, |g s| <= N s := by
    intro s
    have hpos : g s <= N s := hg_bound s
    have hneg : -g s <= N s := by
      have h := hg_bound (-s)
      have hNneg : N (-s) = N s := by
        simp [N]
      simpa [map_neg, hNneg] using h
    have hleft : -N s <= g s := by linarith
    exact abs_le.mpr ⟨hleft, hpos⟩
  let y : Fin m -> Real := fun j => g (Pi.single j 1)
  have hy_bound : forall j : Fin m, |y j| <= C := by
    intro j
    have h := hg_abs (Pi.single j (1 : Real))
    have hsingle : (∑ i : Fin m, |Pi.single j (1 : Real) i|) = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij]
      · intro hj
        simp at hj
    simpa [y, N, hsingle] using h
  refine ⟨y, ?_, hy_bound⟩
  intro i
  let ei : Fin n -> Real := Pi.single i 1
  let row : Fin m -> Real := fun j => B i j
  have hrow_mem : row ∈ LinearMap.range L := by
    refine (LinearMap.mem_range).mpr ⟨ei, ?_⟩
    ext j
    change (∑ k : Fin n, ei k * B k j) = row j
    rw [Finset.sum_eq_single i]
    · simp [ei, row]
    · intro k _ hki
      simp [ei, Pi.single_eq_of_ne hki]
    · intro hi
      simp at hi
  have hrow_ext : g row = f ⟨row, hrow_mem⟩ := by
    exact hg_ext ⟨row, hrow_mem⟩
  have hf_row : f ⟨row, hrow_mem⟩ = v i := by
    have hchoose := Classical.choose_spec ((LinearMap.mem_range).mp hrow_mem)
    let arow : Fin n -> Real := Classical.choose ((LinearMap.mem_range).mp hrow_mem)
    have hwellrow : Fv arow = Fv ei := by
      apply hwell
      exact hchoose.trans (by
        ext j
        change row j = (∑ k : Fin n, ei k * B k j)
        symm
        rw [Finset.sum_eq_single i]
        · simp [ei, row]
        · intro k _ hki
          simp [ei, Pi.single_eq_of_ne hki]
        · intro hi
          simp at hi)
    calc
      f ⟨row, hrow_mem⟩ = Fv arow := by rfl
      _ = Fv ei := hwellrow
      _ = v i := by
        change (∑ k : Fin n, ei k * v k) = v i
        rw [Finset.sum_eq_single i]
        · simp [ei]
        · intro k _ hki
          simp [ei, Pi.single_eq_of_ne hki]
        · intro hi
          simp at hi
  have hrepr : (∑ j : Fin m, y j * row j) = g row := by
    have hdecomp : (∑ j : Fin m, row j • Pi.single j (1 : Real)) = row := by
      ext k
      simp [Pi.single_apply]
    calc
      (∑ j : Fin m, y j * row j) = ∑ j : Fin m, g (row j • Pi.single j (1 : Real)) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [map_smul]
        simp [y, mul_comm]
      _ = g (∑ j : Fin m, row j • Pi.single j (1 : Real)) := by
        rw [map_sum]
      _ = g row := by rw [hdecomp]
  calc
    (∑ j : Fin m, B i j * y j) = ∑ j : Fin m, y j * row j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [row, mul_comm]
    _ = g row := hrepr
    _ = f ⟨row, hrow_mem⟩ := hrow_ext
    _ = v i := hf_row




theorem finite_rows_finite_columns_surjective :
  forall {n m : Nat} {B : Matrix (Fin n) (Fin m) Real}
      {x : Fin m -> Real} {u : Fin n -> Real},
    IsTotallyPositiveFinite B ->
    IsStrictlyAlternatingFin u ->
    (forall i : Fin n, (∑ j : Fin m, B i j * x j) = u i) ->
      forall v : Fin n -> Real,
        exists y : Fin m -> Real,
          (forall i : Fin n, (∑ j : Fin m, B i j * y j) = v i) /\
          forall j : Fin m,
            |y j| <= weightedSupNormFin v u *
              sSup (Set.range fun k : Fin m => |x k|) := by
  classical
  intro n m B x u hTP hAlt hxsol v
  let beta : Real := weightedSupNormFin v u
  let M : Real := sSup (Set.range fun k : Fin m => |x k|)
  have hbeta_nonneg : 0 <= beta := by
    exact Real.sSup_nonneg (Set.forall_mem_range.2 (fun i => abs_nonneg _))
  have hM_nonneg : 0 <= M := by
    exact Real.sSup_nonneg (Set.forall_mem_range.2 (fun i => abs_nonneg _))
  have hx_le_M : forall j : Fin m, |x j| <= M := by
    intro j
    exact le_csSup (Finite.bddAbove_range fun k : Fin m => |x k|) (Set.mem_range_self j)
  have hdual : forall a : Fin n -> Real,
      |(∑ i : Fin n, a i * v i)| <=
        (beta * M) * (∑ j : Fin m, |(∑ i : Fin n, a i * B i j)|) := by
    intro a
    let s : Fin m -> Real := fun j => ∑ i : Fin n, a i * B i j
    rcases exists_good_basis (B := B) (x := x) (s := s) (v := v) (u := u)
        hTP hAlt hxsol with ⟨cols, _hcolsInj, hdet, hgood⟩
    let Cmat : Matrix (Fin n) (Fin n) Real := Matrix.of fun i k => B i (cols k)
    let yb : Fin n -> Real := fun k => ∑ i : Fin n, Cmat⁻¹ k i * v i
    have hCmul : forall i : Fin n, (∑ k : Fin n, Cmat i k * yb k) = v i := by
      intro i
      have hunit : IsUnit Cmat.det := IsUnit.mk0 Cmat.det (by simpa [Cmat] using hdet)
      calc
        (∑ k : Fin n, Cmat i k * yb k) = (Cmat *ᵥ (Cmat⁻¹ *ᵥ v)) i := by
          simp [Matrix.mulVec, dotProduct, yb]
        _ = ((Cmat * Cmat⁻¹) *ᵥ v) i := by
          rw [Matrix.mulVec_mulVec]
        _ = v i := by
          rw [Matrix.mul_nonsing_inv Cmat hunit, Matrix.one_mulVec]
    have hdot_eq : (∑ i : Fin n, a i * v i) = ∑ k : Fin n, yb k * s (cols k) := by
      calc
        (∑ i : Fin n, a i * v i) = ∑ i : Fin n, a i * (∑ k : Fin n, Cmat i k * yb k) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hCmul i]
        _ = ∑ i : Fin n, ∑ k : Fin n, a i * (Cmat i k * yb k) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
        _ = ∑ k : Fin n, ∑ i : Fin n, a i * (Cmat i k * yb k) := by
          rw [Finset.sum_comm]
        _ = ∑ k : Fin n, yb k * (∑ i : Fin n, a i * Cmat i k) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
        _ = ∑ k : Fin n, yb k * s (cols k) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          simp [s, Cmat]
    have habs_le_basis : |(∑ i : Fin n, a i * v i)| <=
        ∑ k : Fin n, |yb k| * |s (cols k)| := by
      calc
        |(∑ i : Fin n, a i * v i)| = |∑ k : Fin n, yb k * s (cols k)| := by
          rw [hdot_eq]
        _ <= ∑ k : Fin n, |yb k * s (cols k)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |yb k| * |s (cols k)| := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [abs_mul]
    have hgood' : (∑ k : Fin n, |yb k| * |s (cols k)|) <=
        beta * (∑ j : Fin m, |x j| * |s j|) := by
      simpa [beta, yb, Cmat] using hgood
    have hsum_x_le : (∑ j : Fin m, |x j| * |s j|) <= ∑ j : Fin m, M * |s j| := by
      refine Finset.sum_le_sum ?_
      intro j _
      exact mul_le_mul_of_nonneg_right (hx_le_M j) (abs_nonneg _)
    have hscale : beta * (∑ j : Fin m, |x j| * |s j|) <=
        (beta * M) * (∑ j : Fin m, |s j|) := by
      calc
        beta * (∑ j : Fin m, |x j| * |s j|) <= beta * (∑ j : Fin m, M * |s j|) := by
          exact mul_le_mul_of_nonneg_left hsum_x_le hbeta_nonneg
        _ = (beta * M) * (∑ j : Fin m, |s j|) := by
          rw [← Finset.mul_sum]
          ring
    exact habs_le_basis.trans (hgood'.trans hscale)
  rcases finite_linf_duality_surjective (B := B) (v := v) (C := beta * M)
      (mul_nonneg hbeta_nonneg hM_nonneg) hdual with ⟨y, hy, hybd⟩
  refine ⟨y, hy, ?_⟩
  intro j
  simpa [beta, M] using hybd j

end VendorE4
