module

public import ToricPower.FinitePushforward

/-! ## Source module `ToricPower.CoherentDerived`
Original SHA256: 245fb150018157ec380fad4fe2f21f99232e83b2801558864bf4b0e3f5a3a4df.
Original sources are retained in `third_party/coherent_sources`.
-/
section CoherentSource09

/-! # The literal bounded derived category of coherent sheaves

On a locally Noetherian scheme, coherent sheaves are the actual locally
finitely presented module sheaves. `CoherentCategory` proves that their
full subcategory is abelian. Here we use Mathlib's standard localization
of complexes in that abelian category and its genuine bounded subcategory.

Finite pushforward is the exact functor proved in `FinitePushforward`.
Its derived action and its value on a line bundle are therefore ordinary
functor constructions, with no postulated derived equivalence or generator.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u

abbrev Coh (X : Scheme.{u}) := TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf X

local instance coherentStandardDerivedCategory (X : Scheme.{u})
    [IsLocallyNoetherian X] : HasDerivedCategory.{u + 1} (Coh X) :=
  HasDerivedCategory.standard (Coh X)

/-- The bounded derived category of the actual coherent-sheaf category. -/
abbrev DbCoh (X : Scheme.{u}) [IsLocallyNoetherian X] :=
  DerivedCategory.Bounded (Coh X)

/-- A coherent sheaf placed in degree zero. -/
def coherentSingle (X : Scheme.{u}) [IsLocallyNoetherian X] (M : Coh X) : DbCoh X :=
  (TauCeti.DerivedCategory.Bounded.singleFunctor (Coh X) 0).obj M

/-- Classical generation, expressed by the actual thick envelope. -/
def generatesDbCoh {X : Scheme.{u}} [IsLocallyNoetherian X] (K : DbCoh X) : Prop :=
  (ObjectProperty.singleton K).IsClassicalTriangulatedGenerator

/-- An actual coherent sheaf isomorphism gives an isomorphism of the
corresponding degree-zero objects in the literal bounded derived category. -/
def coherentSingleIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : Coh X} (e : M ≅ N) : coherentSingle X M ≅ coherentSingle X N :=
  (TauCeti.DerivedCategory.Bounded.singleFunctor (Coh X) 0).mapIso e

theorem coherentSingle_generates_iff_of_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : Coh X} (e : M ≅ N) :
    generatesDbCoh (coherentSingle X M) ↔ generatesDbCoh (coherentSingle X N) :=
  classicalGenerator_iff_of_iso (coherentSingleIso e)

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsFinite f]

/-- Finite direct image on the bounded coherent derived category. -/
def finiteDerivedPushforward : DbCoh X ⥤ DbCoh Y :=
  (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f).mapBoundedDerivedCategory

instance : (finiteDerivedPushforward f).CommShift ℤ := by
  unfold finiteDerivedPushforward
  infer_instance

instance : (finiteDerivedPushforward f).IsTriangulated := by
  unfold finiteDerivedPushforward
  infer_instance

/-- The derived direct image of a degree-zero coherent sheaf is exactly its
ordinary finite direct image, again in degree zero. -/
def finiteDerivedPushforwardSingleIso (M : Coh X) :
    (finiteDerivedPushforward f).obj (coherentSingle X M) ≅
      coherentSingle Y
        ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f).obj M) :=
  ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f).mapBoundedDerivedCategorySingleFunctor
    0).app M

/-- Forgetting the finite-presentation wrapper recovers the literal
scheme-module direct image, without changing its sections or morphisms. -/
theorem coherentPushforward_obj_underlying (M : Coh X) :
    ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f).obj M).obj =
      (Scheme.Modules.pushforward f).obj M.obj :=
  congrArg (fun F => F.obj M)
    (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward_comp_inclusion f)

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end CoherentSource09
