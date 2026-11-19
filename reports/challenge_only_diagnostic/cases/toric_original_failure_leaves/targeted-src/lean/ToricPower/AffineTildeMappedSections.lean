module

public import ToricPower.AffineTildeBaseSections
public import ToricPower.AffineTildeCochain

/-! # Literal base-field sections of mapped affine complexes -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u
variable (k : Type u) [Field k] (R : CommRingCat.{u}) [Algebra k R]

/-- The comparison is assembled before substituting a geometric ring.
Its degreewise map is the original inverse affine section map. -/
def affineTildeMappedSectionsIso {I : Type*} (shape : ComplexShape I) :
    (tilde.functor R).mapHomologicalComplex shape ⋙
        (FiniteCover.schemeBaseSections k (Spec R) ⊤).mapHomologicalComplex shape ≅
      (ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex shape :=
  Functor.mapHomologicalComplexCompIso
    (F := tilde.functor R) (G := FiniteCover.schemeBaseSections k (Spec R) ⊤)
    (H := ModuleCat.restrictScalars (algebraMap k R))
    (affineTildeBaseSectionsIso k R).symm shape

@[simp]
theorem affineTildeMappedSectionsIso_hom_f {I : Type*} (shape : ComplexShape I)
    (K : HomologicalComplex (ModuleCat.{u} R) shape) (a : I) :
    ((affineTildeMappedSectionsIso k R shape).hom.app K).f a =
      (affineTildeBaseSectionsIso k R).inv.app (K.X a) := rfl

end ToricPower

end
