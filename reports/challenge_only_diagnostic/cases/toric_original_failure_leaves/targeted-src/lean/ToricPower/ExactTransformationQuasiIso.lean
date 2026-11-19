module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# A natural transformation detected on homology

For exact additive functors, invertibility of the original transformation
on the actual homology objects implies that its termwise transformation
is a quasi-isomorphism. This retains the given comparison map, rather
than replacing it by an unrelated object isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v w z

variable {A : Type u} [Category.{v} A] [Abelian A]
  {D : Type w} [Category.{z} D] [Abelian D]
  {F G : A ⥤ D} [F.Additive] [G.Additive]
  [F.PreservesHomology] [G.PreservesHomology]

/-- The actual termwise comparison is a quasi-isomorphism if its
components on all actual homology objects are isomorphisms. -/
theorem exactTransformation_complex_quasiIso
    (α : F ⟶ G) {ι : Type*} (shape : ComplexShape ι)
    (K : HomologicalComplex A shape)
    (iso : ∀ q : ι, IsIso (α.app (K.homology q))) :
    QuasiIso ((NatTrans.mapHomologicalComplex α shape).app K) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff,ShortComplex.quasiIso_iff]
  change IsIso (ShortComplex.homologyMap ((K.sc q).mapNatTrans α))
  have equality := NatTrans.app_homology α (K.sc q)
  have full : IsIso
      (((K.sc q).mapHomologyIso F).inv ≫
        ShortComplex.homologyMap ((K.sc q).mapNatTrans α) ≫
          ((K.sc q).mapHomologyIso G).hom) := by
    rw [← equality]
    exact iso q
  have tail : IsIso (ShortComplex.homologyMap ((K.sc q).mapNatTrans α) ≫
      ((K.sc q).mapHomologyIso G).hom) :=
    (isIso_comp_left_iff ((K.sc q).mapHomologyIso F).inv _).mp full
  exact (isIso_comp_right_iff _ ((K.sc q).mapHomologyIso G).hom).mp tail

end ToricPower

end
