module

public import ToricPower.QuasicoherentCartierCechNaturality
public import ToricPower.CartierExtSourceNaturality

/-!
# Naturality of Cartier Ext / Čech comparison in its source

The coefficient-natural comparison also commutes with actual maps of
the source Cartier line. On the Čech side the map is the actual map of
twisted coefficient sheaves supplied by the conjugate tensor adjunction.
The inclusion from quasicoherent sheaves contributes its actual Ext map,
whose contravariant naturality is proved explicitly below.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

private theorem compose_commuting_squares {A : Type*} [Category A]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : A}
    (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂) (b₁ : Y₁ ⟶ Z₁) (b₂ : Y₂ ⟶ Z₂)
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (first : f ≫ a₂ = a₁ ≫ g) (second : g ≫ b₂ = b₁ ≫ h) :
    f ≫ (a₂ ≫ b₂) = (a₁ ≫ b₁) ≫ h := by
  rw [← Category.assoc, first, Category.assoc, second, Category.assoc]

universe u
variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]
  {Index : Type u} [Finite Index]
  (opens : Index → X.Opens) (cover : iSup opens = ⊤)
  (affine : ∀ index, IsAffineOpen (opens index))

local instance quasicoherentSourceCechHasExt : HasExt.{u} (QCoh X) :=
  hasExt_of_enoughInjectives (QCoh X)
local instance ambientSourceCechHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules
local instance underlyingSourceCechHasExt :
    HasExt.{u} (_root_.SheafOfModules X.ringCatSheaf) :=
  hasExt_of_enoughInjectives X.Modules

/-- Source naturality of the comparison beginning with Ext among all
module sheaves and restricted to actual quasicoherent coefficients. -/
@[reassoc]
theorem moduleCartierCechNatIso_source_naturality
    {D E : CartierDivisor X} (f : D.sheaf ⟶ E.sheaf) (M : QCoh X) (n : ℕ) :
    ((extFunctor n).map f.op).app M.obj ≫
        (moduleCartierCechNatIso k X opens cover affine D n).hom.app M =
      (moduleCartierCechNatIso k X opens cover affine E n).hom.app M ≫
        (CechNaturality.cechHomologyFunctor opens n).map
          ((cartierDualTwistMap X f).app M.obj) := by
  let dualMap : (quasicoherentCartierTensorEquivalence (-E)).functor.obj M ⟶
      (quasicoherentCartierTensorEquivalence (-D)).functor.obj M :=
    ObjectProperty.homMk ((cartierDualTwistMap X f).app M.obj)
  change ((extFunctor n).map f.op).app M.obj ≫
      ((cartierExtCohomologyNatIso k X D n).hom.app M.obj ≫
        (CechNaturality.quasicoherentCechIso opens cover affine
          ((quasicoherentCartierTensorEquivalence (-D)).functor.obj M) n).hom) =
    ((cartierExtCohomologyNatIso k X E n).hom.app M.obj ≫
      (CechNaturality.quasicoherentCechIso opens cover affine
        ((quasicoherentCartierTensorEquivalence (-E)).functor.obj M) n).hom) ≫ _
  exact compose_commuting_squares
    ((cartierExtCohomologyNatIso k X E n).hom.app M.obj)
    ((cartierExtCohomologyNatIso k X D n).hom.app M.obj)
    (CechNaturality.quasicoherentCechIso opens cover affine
      ((quasicoherentCartierTensorEquivalence (-E)).functor.obj M) n).hom
    (CechNaturality.quasicoherentCechIso opens cover affine
      ((quasicoherentCartierTensorEquivalence (-D)).functor.obj M) n).hom
    (((extFunctor n).map f.op).app M.obj)
    ((cohomologyFunctor X n).map ((cartierDualTwistMap X f).app M.obj))
    ((CechNaturality.cechHomologyFunctor opens n).map ((cartierDualTwistMap X f).app M.obj))
    (cartierExtCohomologyNatIso_source_naturality k X f M.obj n)
    (CechNaturality.quasicoherentCechIso_naturality opens cover affine n dualMap)

/-- The inclusion-induced Ext comparison commutes with the actual
contravariant map of Cartier sources, in every degree. -/
@[reassoc]
theorem quasicoherentCartierExtComparisonNatIso_source_naturality
    {D E : CartierDivisor X}
    (f : quasicoherentCartierObject X D ⟶ quasicoherentCartierObject X E)
    (M : QCoh X) (n : ℕ) :
    ((extFunctor n).map f.op).app M ≫
        (quasicoherentCartierExtComparisonNatIso k X D n).hom.app M =
      (quasicoherentCartierExtComparisonNatIso k X E n).hom.app M ≫
        ((extFunctor n).map f.hom.op).app M.obj := by
  ext e
  change ((Ext.mk₀ f).comp e (zero_add n)).mapExactFunctor (quasicoherentInclusion X) =
    (Ext.mk₀ f.hom).comp (e.mapExactFunctor (quasicoherentInclusion X)) (zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rfl

/-- The actual quasicoherent Ext / Čech natural isomorphism commutes
with every actual Cartier-source map and every cohomological degree. -/
@[reassoc]
theorem quasicoherentCartierCechNatIso_source_naturality
    {D E : CartierDivisor X}
    (f : quasicoherentCartierObject X D ⟶ quasicoherentCartierObject X E)
    (M : QCoh X) (n : ℕ) :
    ((extFunctor n).map f.op).app M ≫
        (quasicoherentCartierCechNatIso k X opens cover affine D n).hom.app M =
      (quasicoherentCartierCechNatIso k X opens cover affine E n).hom.app M ≫
        (CechNaturality.cechHomologyFunctor opens n).map
          ((cartierDualTwistMap X f.hom).app M.obj) := by
  change ((extFunctor n).map f.op).app M ≫
      ((quasicoherentCartierExtComparisonNatIso k X D n).hom.app M ≫
        (moduleCartierCechNatIso k X opens cover affine D n).hom.app M) =
    ((quasicoherentCartierExtComparisonNatIso k X E n).hom.app M ≫
      (moduleCartierCechNatIso k X opens cover affine E n).hom.app M) ≫ _
  rw [← Category.assoc, quasicoherentCartierExtComparisonNatIso_source_naturality,
    Category.assoc, moduleCartierCechNatIso_source_naturality, Category.assoc]

end ToricPower
