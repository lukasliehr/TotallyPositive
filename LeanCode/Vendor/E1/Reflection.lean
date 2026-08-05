import LeanCode.Vendor.E1.Defs

noncomputable section

open MeasureTheory

namespace ExpDecay

theorem reflection_preserves_totalPositive {g : ℝ → ℝ}
    (hg : IsTotallyPositive g) :
    IsTotallyPositive (reflected g) := by
  intro n a b ha hb
  let ar : Fin n → ℝ := fun i => -a (Fin.rev i)
  let br : Fin n → ℝ := fun i => -b (Fin.rev i)
  have har : StrictMono ar := by
    intro i j hij
    dsimp [ar]
    exact neg_lt_neg (ha ((Fin.rev_lt_rev).2 hij))
  have hbr : StrictMono br := by
    intro i j hij
    dsimp [br]
    exact neg_lt_neg (hb ((Fin.rev_lt_rev).2 hij))
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => g (ar i - br j))
  let N : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => reflected g (a i - b j))
  have hdet : 0 ≤ Matrix.det M := hg n ar br har hbr
  have hM_eq : M = N.submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp [M, N, ar, br, reflected, Fin.revPerm_apply, sub_eq_add_neg, add_comm]
  have hN : 0 ≤ Matrix.det N := by
    rw [hM_eq, Matrix.det_submatrix_equiv_self] at hdet
    exact hdet
  simpa [IsTotallyPositive_n, N] using hN

theorem reflection_preserves_integrable {g : ℝ → ℝ}
    (hg : Integrable g) :
    Integrable (reflected g) ∧ totalMass (reflected g) = totalMass g := by
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  constructor
  · change Integrable (fun x : ℝ => g (-x))
    exact hmp.integrable_comp_of_integrable hg
  · dsimp [totalMass, reflected]
    exact hmp.integral_comp (Homeomorph.neg ℝ).measurableEmbedding g

theorem reflection_preserves_totallyPositiveIntegrable {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) :
    IsTotallyPositiveIntegrable (reflected g) := by
  exact ⟨reflection_preserves_totalPositive hg.1,
    (reflection_preserves_integrable hg.2).1⟩

end ExpDecay
