module

public import LeanCode.Conventions
public import LeanCode.Endgame

@[expose] public section

open MeasureTheory

namespace Assembly

theorem frameSetConjecture
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (h1 : α * β < 1)
    (g : ℝ → ℝ)
    (h2 : IsTotallyPositiveIntegrableContinuous g)
    (h3 : g ≠ 0) :
    IsGaborFrame g h2.2.2 (TotallyPositiveHasDecay g h2) α β :=
  Assembly.Endgame.frameSetConjecture_proof hα hβ h1 g h2 h3

theorem frameSetConjecture_summable
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (h1 : α * β < 1)
    (g : ℝ → ℝ)
    (h2 : IsTotallyPositiveIntegrableContinuous g)
    (h3 : g ≠ 0)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Summable (fun p : ℤ × ℤ =>
      ‖inner ℂ f (GaborAtom_L2 g h2.2.2 (TotallyPositiveHasDecay g h2) α β p.1 p.2)‖ ^ 2) :=
  Assembly.Endgame.frameSetConjecture_summable_proof hα hβ h1 g h2 h3 f

end Assembly
