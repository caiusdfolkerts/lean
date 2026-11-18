module

public import ToricPower.CellularDerivedAdjunction
public import ToricPower.AffineRightDerivedTriangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Exactness of the unbounded cellular derived adjunction

The actual affine right-derived Hom functor is triangulated. Its proved
adjunction therefore gives compatible shifts on derived realization,
with both triangle identities and the unit and counit respecting shifts.
The left adjoint is triangulated by the exact-adjunction theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Functor CochainComplex TopologicalSpace Opposite

namespace ToricPower.Cellular

universe u v

local instance cellularExactAdjunctionDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable (k : Type u) [Field k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] {C : Type u} [Category.{u} C]
  [HasDerivedCategory (C ⥤ ModuleCat.{u} k)]
  (P : Cᵒᵖ ⥤ QCoh X)
  {I : Type v} (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  [∀ i, PreservesFiniteLimits
    (quasicoherentOpenLocalization (V i).ι ⋙ homDiagram k P)]
  [∀ i, PreservesFiniteColimits
    (quasicoherentOpenLocalization (V i).ι ⋙ homDiagram k P)]
  (l : List I) (hl : ∀ i, i ∈ l) (hV : IsOpenCover V)

/-- The actual unbounded right adjoint's canonical shift comparison. -/
def labelRHomAffineCommShift : (labelRHomAffine k P V l).CommShift ℤ :=
  affineRightDerivedCommShift V l hl hV (homDiagram k P)

variable (m : ℕ)
  (hε : ∀ K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ,
    QuasiIso ((finiteConeResolution k m).augmentation.app K))

/-- Shifts on the actual derived realization are determined by its
genuine adjunction with the actual derived Hom diagram. -/
def realizationAffineCommShift :
    (finiteConeRealizationStageDerived k (realization k P) m).CommShift ℤ := by
  letI := labelRHomAffineCommShift k P V l hl hV
  exact (realizationAffineHomAdjunction k P V l hl hV m hε).leftAdjointCommShift ℤ

/-- Both genuine derived comparison maps respect these same shifts. -/
theorem realizationAffineHomAdjunction_commShift :
    letI := labelRHomAffineCommShift k P V l hl hV
    letI := realizationAffineCommShift k P V l hl hV m hε
    (realizationAffineHomAdjunction k P V l hl hV m hε).CommShift ℤ := by
  letI := labelRHomAffineCommShift k P V l hl hV
  exact (realizationAffineHomAdjunction k P V l hl hV m hε).commShift_of_rightAdjoint ℤ

/-- The actual unbounded derived realization is triangulated. -/
theorem realizationAffine_isTriangulated :
    letI := realizationAffineCommShift k P V l hl hV m hε
    (finiteConeRealizationStageDerived k (realization k P) m).IsTriangulated := by
  letI := labelRHomAffineCommShift k P V l hl hV
  letI := realizationAffineCommShift k P V l hl hV m hε
  letI := realizationAffineHomAdjunction_commShift k P V l hl hV m hε
  letI : (labelRHomAffine k P V l).IsTriangulated :=
    affineRightDerived_isTriangulated V l hl hV (homDiagram k P)
  exact (realizationAffineHomAdjunction k P V l hl hV m hε).isTriangulated_leftAdjoint

end ToricPower.Cellular

end
