import LeanCode.Base
import LeanCode.Vocab
import LeanCode.ExternalInputs
import LeanCode.Decay



















open Matrix
open MeasureTheory
open scoped ENNReal
open lp

namespace Assembly





theorem TotallyPositiveHasDecay (g : ℝ → ℝ) (h : IsTotallyPositiveIntegrableContinuous g) :
    HasPolynomialDecay g :=
  tpic_hasPolynomialDecay g h

end Assembly
