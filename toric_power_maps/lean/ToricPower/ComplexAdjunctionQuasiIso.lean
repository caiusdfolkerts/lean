module

public import ToricPower.ComplexAdjunction
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Actual complex mates under an equivalence preserve quasi-isomorphisms

The proof uses the original unit and the exact right adjoint. No derived
full-faithfulness or derived adjunction is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v' w

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  {F : A ⥤ B} {G : B ⥤ A}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  (adj : F ⊣ G) [F.IsEquivalence] {I : Type w} (shape : ComplexShape I)

/-- The literal termwise unit is an isomorphism of complete complexes. -/
theorem complexAdjunctionUnit_isIso (K : HomologicalComplex A shape) :
    IsIso ((complexAdjunctionUnit adj shape).app K) := by
  haveI (q : I) : IsIso (((complexAdjunctionUnit adj shape).app K).f q) := by
    change IsIso (adj.unit.app (K.X q))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Transposition preserves the original quasi-isomorphism on every
complex, with no boundedness or coefficient-size restriction. -/
theorem complexAdjunction_homEquiv_quasiIso
    (K : HomologicalComplex A shape) (L : HomologicalComplex B shape)
    (f : (F.mapHomologicalComplex shape).obj K ⟶ L) [QuasiIso f] :
    QuasiIso ((complexAdjunction adj shape).homEquiv K L f) := by
  letI : G.IsEquivalence := adj.isEquivalence_right_of_isEquivalence_left
  letI : G.Additive := G.additive_of_preserves_binary_products
  haveI := complexAdjunctionUnit_isIso adj shape K
  change QuasiIso ((complexAdjunctionUnit adj shape).app K ≫
    (G.mapHomologicalComplex shape).map f)
  infer_instance

end ToricPower

end
