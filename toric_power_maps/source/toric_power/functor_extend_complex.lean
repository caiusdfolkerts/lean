module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive

/-! # Additive functors commute with extension of complexes by zero -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {A D : Type*} [Category* A] [Category* D]
  [Preadditive A] [Preadditive D] [HasZeroObject A] [HasZeroObject D]
  (F : A ⥤ D) [F.Additive]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex A c)

def mapExtendXIso (i : Option ι) :
    F.obj (HomologicalComplex.extend.X K i) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => IsZero.iso (F.map_isZero (isZero_zero A)) (isZero_zero D)

theorem mapExtendXIso_d (i j : Option ι) :
    F.map (HomologicalComplex.extend.d K i j) ≫ (mapExtendXIso F K j).hom =
      (mapExtendXIso F K i).hom ≫
        HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) i j := by
  cases i <;> cases j <;>
    simp [mapExtendXIso,HomologicalComplex.extend.d]

/-- The actual degreewise comparison, with all differentials retained. -/
def mapExtendIso (e : c.Embedding c') :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => mapExtendXIso F K (e.r i))
    (fun i j _ => (mapExtendXIso_d F K (e.r i) (e.r j)).symm)

theorem mapExtendXIso_hom {i : Option ι} {j : ι} (h : i = some j) :
    (mapExtendXIso F K i).hom =
      F.map (HomologicalComplex.extend.XIso K h).hom ≫
        (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj K) h).inv := by
  subst i
  simp [mapExtendXIso,HomologicalComplex.extend.XIso]
  rfl

theorem mapExtendIso_hom_f (e : c.Embedding c') {i : ι} {i' : ι'}
    (h : e.f i = i') :
    (mapExtendIso F K e).hom.f i' =
      F.map (K.extendXIso e h).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv :=
  mapExtendXIso_hom F K (e.r_eq_some h)

end ToricPower

end
