import LeanCode.Vocab

























open scoped ENNReal

namespace Assembly.OpConv









theorem isUnit_of_bijective {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : ellp p →L[ℂ] ellp p) (hT : Function.Bijective T) : IsUnit T :=
  (ContinuousLinearMap.isUnit_iff_bijective).mpr hT



theorem matrixInvertibleOn_of_bijective {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (T : ellp p →L[ℂ] ellp p)
    (hAT : IsMatrixOperator p A T) (hT : Function.Bijective T) :
    MatrixInvertibleOn p A :=
  ⟨T, hAT, isUnit_of_bijective T hT⟩











def V (m : ℤ) (c : ℤ → ℂ) : ℤ → ℂ := fun k => c (k - m)




def shiftMat (m : ℤ) : ℤ → ℤ → ℂ := fun i j => if j = i - m then 1 else 0



def projFun (n : ℕ) (c : ℤ → ℂ) : ℤ → ℂ := fun k => if |k| ≤ (n : ℤ) then c k else 0




theorem V_eq_matVec (m : ℤ) (c : ℤ → ℂ) (i : ℤ) :
    ∑' j : ℤ, shiftMat m i j * c j = V m c i := by
  have h : (fun j : ℤ => shiftMat m i j * c j)
      = fun j : ℤ => if j = i - m then c j else 0 := by
    funext j
    unfold shiftMat
    by_cases hj : j = i - m
    · subst hj; simp
    · simp [hj]
  rw [h, tsum_ite_eq (i - m) c]
  rfl


theorem projFun_idem (n : ℕ) (c : ℤ → ℂ) : projFun n (projFun n c) = projFun n c := by
  funext k
  unfold projFun
  by_cases hk : |k| ≤ (n : ℤ) <;> simp [hk]

















theorem shiftConj_entries (A : ℤ → ℤ → ℂ) (c : ℤ → ℂ) (q k : ℤ) :
    (fun i => ∑' j : ℤ, A i j * c (j - q)) (k + q)
      = ∑' j : ℤ, A (k + q) (j + q) * c j := by
  simp only
  rw [← Equiv.tsum_eq (Equiv.addRight q) (fun j => A (k + q) j * c (j - q))]
  simp [Equiv.addRight]



theorem shiftConj_entries_V (A : ℤ → ℤ → ℂ) (c : ℤ → ℂ) (q k : ℤ) :
    V (-q) (fun i => ∑' j : ℤ, A i j * V q c j) k
      = ∑' j : ℤ, A (k + q) (j + q) * c j := by
  simp only [V]
  have hkq : k - -q = k + q := by ring
  rw [hkq]
  exact shiftConj_entries A c q k

end Assembly.OpConv
