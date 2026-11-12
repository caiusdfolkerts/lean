module

public import ToricPower.FiniteDualHomModel
public import ToricPower.FiniteCochainSourceBounds
public import ToricPower.QuasicoherentBaseLinear
public import ToricPower.FiniteAffineIntersectionSections

/-!
# Scheme-level finite dual Hom comparison

The coefficient-chain comparison is assembled at the level of an
arbitrary scheme and arbitrary whole complexes. Geometric coefficients
are substituted only after the finite support and ordinary Hom interfaces
have been fixed. The target complex remains unrestricted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex HomComplex

namespace ToricPower

variable (k : Type) [Field k] (X : Scheme.{0}) [X.Over (Spec (.of k))]
  [HasFiniteBiproducts (QCoh X)]
  (Φ : QCoh X ⥤ ChainComplex (QCoh X) ℕ) [Φ.Additive]
  (K : CochainComplex (QCoh X) ℕ) (I : CochainComplex (QCoh X) ℤ) (width : ℕ)
  (above : ∀ q : ℕ, width ≤ q → IsZero (K.X q))
  (coefficients : NegativeFunctorTotal.postcompose Φ
      (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤) ≅
    ordinaryCochainCoefficientFunctor k K)

/-- The full signed Hom complex of the original finite source. -/
def quasicoherentFiniteDualHomModelIso :
    ((quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤).mapHomologicalComplex
      (.up ℤ)).obj (NegativeFunctorTotal.total Φ width I) ≅
    linearHomComplex k (K.extend ComplexShape.embeddingUpNat) I :=
  finiteDualHomModelIsoOfNonnegative k Φ
    (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤) K I width
    (finiteCochain_extend_isZero_outside K width above) coefficients

end ToricPower
end
