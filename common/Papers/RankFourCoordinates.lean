module
public import Consolidated.MatrixNormalization

@[expose] public section
noncomputable section

namespace Papers.MatrixGaugeNormalization

abbrev firstFour : Fin 4 → Fin 8 := Fin.castAdd 4
abbrev lastFour : Fin 4 → Fin 8 := Fin.natAdd 4

/-- The nonbasis rows of an eight-vector configuration. -/
def lowerBlock (q : Matrix (Fin 8) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => q (lastFour i) j

/-- Basis normalization followed by the actual real row and column gauges. -/
def normalizedMatrix (p : Matrix (Fin 8) (Fin 4) ℝ) (e : Equiv.Perm (Fin 8))
    (a : Fin 8 → ℝ) (c : Fin 4 → ℝ) : Matrix (Fin 8) (Fin 4) ℝ :=
  scaleRowsColumns (normalizeBasis (p.submatrix e id) firstFour) a c

end Papers.MatrixGaugeNormalization
