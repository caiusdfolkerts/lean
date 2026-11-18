module

public import ToricPower.ArrangementRepresentedAugmentation
public import ToricPower.ArrangementCellularAffineNaturality
public import ToricPower.ArrangementCellularExact
public import ToricPower.SingleAugmentationTopEpi

/-!
# The original represented augmentation in actual quasicoherent sheaves

The full inclusion is used before passage to the derived category.
Thus every original cellular map is lifted as an actual complex map;
no fullness of the unbounded derived inclusion is assumed. The
quasi-isomorphism and epimorphism conclusions are explicit transports
of the separate local geometric calculation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "I" => quasicoherentInclusion X
local notation "IC" => Functor.mapHomologicalComplex I (ComplexShape.up ℕ)
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local notation "rep" => Cellular.representableFunctor ℂ (C := Cells)

/-- The genuine diagonal top line, equipped with its proved
quasicoherence as an actual invertible sheaf. -/
def dualDiagonalLineQuasicoherent : QCoh X := by
  letI := dualDiagonalLineSheaf_isInvertible fan nonempty regular basis rays
  exact ⟨J, inferInstance⟩

/-- Original right labels tensored with the genuine top line, in the
actual quasicoherent category. -/
def arrangementRightTopLineDiagram : Cellsᵒᵖ ⥤ QCoh X :=
  arrangementRightQuasicoherentDiagram fan nonempty regular basis rays ⋙
    tensorRight (dualDiagonalLineQuasicoherent fan nonempty regular basis rays)

local notation "P" => arrangementRightTopLineDiagram fan nonempty regular basis rays

/-- The target comparison uses the literal underlying tensor product
and the canonical comparison with a single complex. -/
def arrangementRightTopLineSingleUnderlyingIso :
    (P ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n) ⋙ IC ≅
      arrangementRightCartierDiagram fan nonempty regular basis rays ⋙
        tensorRight J ⋙ HomologicalComplex.single (X).Modules (.up ℕ) n :=
  Functor.associator P (HomologicalComplex.single (QCoh X) (.up ℕ) n) IC ≪≫
    Functor.isoWhiskerLeft P
      (HomologicalComplex.singleMapHomologicalComplex I (.up ℕ) n)

/-- The same represented augmentation, with precisely the canonical
underlying-source and underlying-target comparisons inserted. -/
def arrangementRepresentedQuasicoherentUnderlying :
    (rep ⋙ Φ) ⋙ IC ⟶
      (P ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n) ⋙ IC :=
  (Functor.associator rep Φ IC).hom ≫
    Functor.whiskerLeft rep
      (arrangementCellularUnderlyingFunctorIso fan nonempty regular basis rays).hom ≫
    arrangementRepresentedAugmentation fan nonempty regular basis rays ≫
    (arrangementRightTopLineSingleUnderlyingIso fan nonempty regular basis rays).inv

/-- The original source-natural complex map lifts through the full
ordinary quasicoherent inclusion, degree by degree. -/
def arrangementRepresentedQuasicoherentAugmentation :
    rep ⋙ Φ ⟶ P ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n where
  app c := (IC).preimage
    ((arrangementRepresentedQuasicoherentUnderlying fan nonempty regular basis rays).app c)
  naturality {c d} f := by
    apply (IC).map_injective
    simp only [Functor.map_comp, Functor.map_preimage]
    exact (arrangementRepresentedQuasicoherentUnderlying fan nonempty regular basis rays).naturality f

/-- Forgetting the lift gives its specified original map, not an
independently chosen comparison of isomorphic objects. -/
theorem arrangementRepresentedQuasicoherentAugmentation_underlying (c : Cellsᵒᵖ) :
    (IC).map ((arrangementRepresentedQuasicoherentAugmentation fan nonempty regular basis rays).app c) =
      (arrangementRepresentedQuasicoherentUnderlying fan nonempty regular basis rays).app c :=
  (IC).map_preimage _

/-- Exact conservative inclusion transports the actual geometric
quasi-isomorphism to the actual quasicoherent augmentation. -/
theorem arrangementRepresentedQuasicoherentAugmentation_quasiIso_of_top (c : Cells)
    [QuasiIso (arrangementRepresentedTopAugmentation fan nonempty regular basis rays c)] :
    QuasiIso
      ((arrangementRepresentedQuasicoherentAugmentation fan nonempty regular basis rays).app (op c)) := by
  letI := arrangementRepresentedAugmentation_quasiIso_of_top fan nonempty regular basis rays c
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((arrangementRepresentedQuasicoherentAugmentation fan nonempty regular basis rays).app (op c)) I).mp
  rw [arrangementRepresentedQuasicoherentAugmentation_underlying]
  change QuasiIso (_ ≫ _ ≫ _ ≫ _)
  infer_instance

/-- Once its genuine local quasi-isomorphism is proved, the actual
represented augmentation is epimorphic as a whole complex map. -/
theorem arrangementRepresentedQuasicoherentAugmentation_epi_of_top (c : Cells)
    [QuasiIso (arrangementRepresentedTopAugmentation fan nonempty regular basis rays c)] :
    Epi
      ((arrangementRepresentedQuasicoherentAugmentation fan nonempty regular basis rays).app (op c)) := by
  letI := arrangementRepresentedQuasicoherentAugmentation_quasiIso_of_top
    fan nonempty regular basis rays c
  apply singleAugmentation_epi
  exact arrangementQuasicoherentCellularRealization_outgoing
    fan nonempty regular basis rays (Cellular.representable ℂ c)

end ToricPower

end
