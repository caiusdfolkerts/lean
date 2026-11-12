module

public import ToricPower.AffineRankOneSections

/-! # Affine unit Hom sections through a specified underlying diagram

The full tensor comparison and the underlying-sheaf comparison are
assembled before a geometric label diagram is substituted. Both maps
remain the original natural maps.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower

universe u

variable (k : Type u) [Field k] {U X : Scheme.{u}}
  [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j] [j.IsOver (Spec (.of k))]
  {C : Type u} [Category.{u} C] (P : C ⥤ QCoh X)
  (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (P.obj c).obj)

/-- Evaluate the tensor-section comparison while the coefficient object
is still a variable. This fixes the ordinary functor presentation
before substituting any actual affine pushforward. -/
def quasicoherentHomTensorSectionsIsoAt
    (F : QCoh X ⥤ C ⥤ ModuleCat.{u} k)
    (e : F ≅ (P ⋙ tensoringLeft (QCoh X)).flip ⋙
      (Functor.whiskeringRight C (QCoh X) (ModuleCat.{u} k)).obj
        (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤))
    (M : QCoh X) :
    F.obj M ≅ P ⋙ tensorRight M ⋙ quasicoherentInclusion X ⋙
      FiniteCover.schemeBaseSections k X ⊤ := e.app M

/-- The evaluated comparison is the original natural-isomorphism component. -/
theorem quasicoherentHomTensorSectionsIsoAt_eq
    (F : QCoh X ⥤ C ⥤ ModuleCat.{u} k)
    (e : F ≅ (P ⋙ tensoringLeft (QCoh X)).flip ⋙
      (Functor.whiskeringRight C (QCoh X) (ModuleCat.{u} k)).obj
        (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤))
    (M : QCoh X) : quasicoherentHomTensorSectionsIsoAt k P F e M = e.app M := rfl

/-- The original Hom--tensor, projection, and underlying-label maps,
composed in a generic context. -/
def quasicoherentHomOpenUnitUnderlyingSectionsIso
    (F : QCoh X ⥤ C ⥤ ModuleCat.{u} k)
    (e : F ≅ (P ⋙ tensoringLeft (QCoh X)).flip ⋙
      (Functor.whiskeringRight C (QCoh X) (ModuleCat.{u} k)).obj
        (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤))
    (T : C ⥤ X.Modules) (underlying : P ⋙ quasicoherentInclusion X ≅ T) :
    F.obj (quasicoherentAffineUnitImage j) ≅
      T ⋙ FiniteCover.schemeBaseSections k X j.opensRange :=
  quasicoherentHomOpenUnitSectionsIso k j P invertible F e ≪≫
    Functor.isoWhiskerRight underlying
      (FiniteCover.schemeBaseSections k X j.opensRange)

end ToricPower

end
