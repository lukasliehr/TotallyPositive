import LeanCode.Conventions
import LeanCode.Endgame











open MeasureTheory

namespace Assembly

theorem frameSetConjecture
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (h1 : α * β < 1)
    (g : ℝ → ℝ)
    (h2 : IsTotallyPositiveIntegrableContinuous g)
    (h3 : g ≠ 0) :
    IsGaborFrame g h2.2.2 (TotallyPositiveHasDecay g h2) α β :=
  Assembly.Endgame.frameSetConjecture_proof hα hβ h1 g h2 h3

end Assembly
