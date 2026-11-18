module

public import ToricPower.OpenInvertibleDiagramSections
public import ToricPower.QuasicoherentBaseLinear
public import ToricPower.QuasicoherentOpenAdjunction
public import ToricPower.CellularHomAdjunction

/-! # Rank-one affine coefficients and actual invertible diagrams

These generic comparisons separate the underlying quasicoherent tensor
and tilde constructions from their toric specializations. Both maps
are the canonical maps, retaining their scalar action and naturality.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower

universe u

/-- The actual affine direct image of the structure sheaf, with its
object constructor kept separate from the Hom-diagram evaluation. -/
def quasicoherentAffineUnitImage {U X : Scheme.{u}} (j : U ⟶ X) [IsAffineHom j] : QCoh X :=
  (quasicoherentAffinePushforward j).obj (𝟙_ (QCoh U))

/-- The actual affine tilde equivalence takes the rank-one free module
to the unit of the quasicoherent tensor category. -/
def quasicoherentTildeUnitIso (R : CommRingCat.{u}) :
    (tildeEquiv (R := R)).functor.obj (ModuleCat.of R R) ≅ 𝟙_ (QCoh (Spec R)) :=
  ObjectProperty.isoMk _ (tildeSelf (R := R))

variable (k : Type u) [Field k] {U X : Scheme.{u}}
  [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j] [j.IsOver (Spec (.of k))]
  {C : Type u} [Category.{u} C] (P : C ⥤ QCoh X)
  (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (P.obj c).obj)

/-- Full scalar-linear sections of inverse labels tensored with the
actual open direct image of the unit, with every label map retained. -/
def quasicoherentOpenUnitSectionsIso :
    P ⋙ tensorRight (quasicoherentAffineUnitImage j) ⋙
      quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤ ≅
    P ⋙ quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X j.opensRange :=
  openInvertibleDiagramUnitSectionsIso j (P ⋙ quasicoherentInclusion X) invertible k

/-- Apply any already established full Hom--tensor-section comparison
to the actual direct image of the affine unit. -/
def quasicoherentHomOpenUnitSectionsIso
    (F : QCoh X ⥤ C ⥤ ModuleCat.{u} k)
    (e : F ≅ (curriedTensor (QCoh X)).flip ⋙
      (Functor.whiskeringLeft C (QCoh X) (QCoh X)).obj P ⋙
        (Functor.whiskeringRight C (QCoh X) (ModuleCat.{u} k)).obj
          (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤)) :
    F.obj (quasicoherentAffineUnitImage j) ≅
      P ⋙ quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X j.opensRange :=
  e.app _ ≪≫ quasicoherentOpenUnitSectionsIso k j P invertible

/-- The tilde-unit comparison followed by an arbitrary actual
coefficient functor, before specializing its affine ring. -/
def quasicoherentAffineRankOneImageIso (R : CommRingCat.{u})
    {Y : Scheme.{u}} (f : Spec R ⟶ Y) [IsAffineHom f]
    {D : Type*} [Category D] (G : QCoh Y ⥤ D) :
    ((tildeEquiv (R := R)).functor ⋙ quasicoherentAffinePushforward f ⋙ G).obj
      (ModuleCat.of R R) ≅ G.obj (quasicoherentAffineUnitImage f) :=
  G.mapIso ((quasicoherentAffinePushforward f).mapIso (quasicoherentTildeUnitIso R))

/-- The same comparison with the original unbundled ring instance.
The conversion from a bundled commutative ring is checked here before
any geometric ring is substituted. -/
def quasicoherentAffineRankOneImageIsoOfRing (R : Type u) [CommRing R]
    {Y : Scheme.{u}} (f : Spec (CommRingCat.of R) ⟶ Y) [IsAffineHom f]
    {D : Type*} [Category D] (G : QCoh Y ⥤ D) :
    ((tildeEquiv (R := CommRingCat.of R)).functor ⋙ quasicoherentAffinePushforward f ⋙ G).obj
      (ModuleCat.of R R) ≅ G.obj (quasicoherentAffineUnitImage f) :=
  quasicoherentAffineRankOneImageIso (CommRingCat.of R) f G

/-- Assemble the entire coefficient, unit, and section comparison
before substituting a geometric ring or a large label functor. -/
def quasicoherentAffineRankOneComparison (R : Type u) [CommRing R]
    {Y : Scheme.{u}} (f : Spec (CommRingCat.of R) ⟶ Y) [IsAffineHom f]
    {D : Type*} [Category D] (G : QCoh Y ⥤ D) (F : ModuleCat.{u} R ⥤ D)
    (same : F = (tildeEquiv (R := CommRingCat.of R)).functor ⋙
      quasicoherentAffinePushforward f ⋙ G)
    (T : D) (unit : G.obj (quasicoherentAffineUnitImage f) ≅ T) :
    F.obj (ModuleCat.of R R) ≅ T :=
  eqToIso (congrArg (fun H : ModuleCat.{u} R ⥤ D => H.obj (ModuleCat.of R R)) same) ≪≫
    quasicoherentAffineRankOneImageIsoOfRing R f G ≪≫ unit

end ToricPower

end
