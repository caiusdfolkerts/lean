module
public import Papers.RationalElimination
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section
noncomputable section

namespace Papers.RationalityTen.Chart563
open MvPolynomial

noncomputable def E0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (some (some (none)))) - (X (some (some (some (none))))) + (1), -(X (some (none)) * X (some (some (none)))) + (X (some (none))) - (1), -(X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (some (some (none))))), -(X (none)) + (1), X (none) * X (some (some (some (some (none))))) - (X (some (none)))]

noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (none)))))]

end Papers.RationalityTen.Chart563
