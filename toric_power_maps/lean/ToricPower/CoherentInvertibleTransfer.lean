module

public import ToricPower.CoherentDerivedTransfer
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! ## Source module `ToricPower.CoherentInvertibleTransfer`
Original SHA256: 12167480d628719bb1cc5e60bb1d49ca6a991ba99d289cbee93039c19e6e5687.
Original sources are retained in `third_party/coherent_sources`.
-/
section CoherentSource14

/-!
# Finite pushforward of a generator split into invertible sheaves

The geometric hypothesis is an actual retraction of the structure sheaf
from its ordinary direct image. The projection formula, proved in
`InvertibleProjectionFormula`, transports it to each invertible sheaf.
These retractions are then used in the literal bounded derived category of
coherent sheaves. No derived pullback or split natural transformation is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

namespace ToricPower

universe u

local instance coherentInvertibleStandardDerivedCategory (X : Scheme.{u})
    [IsLocallyNoetherian X] : HasDerivedCategory.{u + 1} (Coh X) :=
  HasDerivedCategory.standard (Coh X)

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Regard an actual invertible module sheaf as an actual coherent sheaf.
The local finite-presentation proof is supplied by the invertibility theory. -/
abbrev coherentInvertible (L : TauCeti.AlgebraicGeometry.InvertibleSheaf Y) : Coh Y :=
  (TauCeti.AlgebraicGeometry.InvertibleSheaf.toFinitelyPresented Y).obj L

/-- The invertible projection-formula retract lives in the full coherent
subcategory: its maps are the same underlying sheaf morphisms. -/
def coherentInvertibleRetractPushforwardPullback (f : X ⟶ Y) [IsFinite f]
    (r : Retract (SheafOfModules.unit Y.ringCatSheaf)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)))
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf Y) :
    Retract (coherentInvertible L)
      ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f).obj
        ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pullback f).obj
          (coherentInvertible L))) := by
  let s := invertibleSheafRetractPushforwardPullback f r L
  exact
    { i := ObjectProperty.homMk s.i
      r := ObjectProperty.homMk s.r
      retract := ObjectProperty.hom_ext _ s.retract }

/-- The same retraction after placing coherent sheaves in degree zero,
with its target identified with the actual finite derived direct image. -/
def coherentInvertibleDerivedRetract (f : X ⟶ Y) [IsFinite f]
    (r : Retract (SheafOfModules.unit Y.ringCatSheaf)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)))
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf Y) :
    Retract (coherentSingle Y (coherentInvertible L))
      ((finiteDerivedPushforward f).obj
        (coherentSingle X
          ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pullback f).obj
            (coherentInvertible L)))) :=
  ((coherentInvertibleRetractPushforwardPullback f r L).map
    (TauCeti.DerivedCategory.Bounded.singleFunctor (Coh Y) 0)).trans
      (Retract.ofIso
        (finiteDerivedPushforwardSingleIso f
          ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pullback f).obj
            (coherentInvertible L))).symm)

/-- A finite invertible decomposition of a target generator, together with
the structure-sheaf retraction, ensures that finite pushforward sends any
source generator to a target generator. -/
theorem coherentPushforward_generates_of_invertibleTargetGenerator
    (f : X ⟶ Y) [IsFinite f]
    (r : Retract (SheafOfModules.unit Y.ringCatSheaf)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)))
    {I : Type*} [Finite I] [Nonempty I]
    (L : I → TauCeti.AlgebraicGeometry.InvertibleSheaf Y)
    (N : Coh Y) (eN : N ≅ ⨁ (fun i => coherentInvertible (L i)))
    (hN : generatesDbCoh (coherentSingle Y N))
    (M : Coh X) (hM : generatesDbCoh (coherentSingle X M)) :
    generatesDbCoh (coherentSingle Y
      ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f).obj M)) := by
  let S := TauCeti.DerivedCategory.Bounded.singleFunctor (Coh Y) 0
  let A : I → Coh Y := fun i => coherentInvertible (L i)
  have hA : (ObjectProperty.ofObj (fun i => S.obj (A i))).IsClassicalTriangulatedGenerator := by
    have h := (classicalGenerator_iff_of_iso (S.mapIso eN ≪≫ S.mapBiproduct A)).mp hN
    change (ObjectProperty.singleton (⨁ (fun i => S.obj (A i)))).triangEnvelope = ⊤ at h
    change (ObjectProperty.ofObj (fun i => S.obj (A i))).triangEnvelope = ⊤
    rwa [biproduct_triangEnvelope_eq] at h
  have hF : generatesDbCoh
      ((finiteDerivedPushforward f).obj (coherentSingle X M)) := by
    apply obj_classicalGenerator_of_generatingRetracts
      (finiteDerivedPushforward f) (coherentSingle X M) hM
      (ObjectProperty.ofObj (fun i => S.obj (A i))) hA
    intro K hK
    obtain ⟨i⟩ := hK
    exact ⟨coherentSingle X
      ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pullback f).obj
        (coherentInvertible (L i))), ⟨coherentInvertibleDerivedRetract f r (L i)⟩⟩
  exact (classicalGenerator_iff_of_iso (finiteDerivedPushforwardSingleIso f M)).mp hF

/-- For a finite endomorphism, one finite invertible decomposition of the
original generator suffices. This is the objectwise form used for toric
power-map generators after the actual line-bundle splitting is constructed. -/
theorem coherentPushforward_generates_of_invertibleSplitting
    (f : X ⟶ X) [IsFinite f]
    (r : Retract (SheafOfModules.unit X.ringCatSheaf)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)))
    {I : Type*} [Finite I] [Nonempty I]
    (L : I → TauCeti.AlgebraicGeometry.InvertibleSheaf X)
    (M : Coh X) (eM : M ≅ ⨁ (fun i => coherentInvertible (L i)))
    (hM : generatesDbCoh (coherentSingle X M)) :
    generatesDbCoh (coherentSingle X
      ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f).obj M)) :=
  coherentPushforward_generates_of_invertibleTargetGenerator f r L M eM hM M hM

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end CoherentSource14
