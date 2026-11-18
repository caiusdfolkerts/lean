module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Real.Basic
public import Recovery.Unimodular.ProductVectorMatroid

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The standard R₁₀ integral configuration and its real column matroid -/

namespace Unimodular.R10Maximality

def rays : Fin 10 → Fin 5 → ℤ :=
  ![![1,0,0,0,0], ![0,1,0,0,0], ![0,0,1,0,0], ![0,0,0,1,0], ![0,0,0,0,1],
    ![1,1,0,0,1], ![0,1,1,0,1], ![0,0,1,1,1], ![1,0,0,1,1], ![1,1,1,1,1]]


def block : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1,0,0,1,1; 1,1,0,0,1; 0,1,1,0,1; 0,0,1,1,1; 1,1,1,1,1]


def realRays : Fin 10 → Fin 5 → ℝ := fun j i ↦ (rays j i : ℝ)

noncomputable def r10Matroid : Matroid (Fin 10) :=
  VectorMatroid.ofFamily (K := ℝ) realRays

end Unimodular.R10Maximality
