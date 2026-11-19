module

public import ToricPower.QuasicoherentCechComparison
public import ToricPower.QuasicoherentCartierExt

/-!
# Natural Cartier Ext / Čech comparison on actual quasicoherent coefficients

The actual inverse-Cartier tensor functor preserves quasicoherence.
Composing the coefficient-natural Cartier Ext / sheaf-cohomology
comparison with the natural finite-affine Čech comparison therefore gives
an actual natural isomorphism for every degree and every coefficient map.

The source Cartier line is fixed in these statements. Naturality under
variation of that source is a distinct assertion and is not assumed here.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower
universe u
variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]
  {Index : Type u} [Finite Index]
  (opens : Index → X.Opens) (cover : iSup opens = ⊤)
  (affine : ∀ index, IsAffineOpen (opens index))

local instance quasicoherentCechHasExt : HasExt.{u} (QCoh X) :=
  hasExt_of_enoughInjectives (QCoh X)
local instance moduleCechHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- Module-sheaf Ext with a Cartier source is naturally actual Čech
cohomology of the inverse-Cartier twist, on all quasicoherent targets. -/
def moduleCartierCechNatIso (D : CartierDivisor X) (degree : ℕ) :
    quasicoherentInclusion X ⋙ (extFunctor degree).obj (op D.sheaf) ≅
      (quasicoherentCartierTensorEquivalence (-D)).functor ⋙ quasicoherentInclusion X ⋙
        CechNaturality.cechHomologyFunctor opens degree :=
  Functor.isoWhiskerLeft (quasicoherentInclusion X)
      (cartierExtCohomologyNatIso k X D degree) ≪≫
    Functor.isoWhiskerLeft (quasicoherentCartierTensorEquivalence (-D)).functor
      (CechNaturality.quasicoherentCechNatIso opens cover affine degree)

/-- The same actual natural comparison starting with Ext in `QCoh X`.
The first step is the proved inclusion-induced Ext isomorphism. -/
def quasicoherentCartierCechNatIso (D : CartierDivisor X) (degree : ℕ) :
    (extFunctor degree).obj (op (quasicoherentCartierObject X D)) ≅
      (quasicoherentCartierTensorEquivalence (-D)).functor ⋙ quasicoherentInclusion X ⋙
        CechNaturality.cechHomologyFunctor opens degree :=
  quasicoherentCartierExtComparisonNatIso k X D degree ≪≫
    moduleCartierCechNatIso k X opens cover affine D degree

/-- The natural comparison retains the actual action of every
quasicoherent coefficient map. -/
@[reassoc]
theorem quasicoherentCartierCechNatIso_naturality (D : CartierDivisor X) (degree : ℕ)
    {M N : QCoh X} (mapping : M ⟶ N) :
    ((extFunctor degree).obj (op (quasicoherentCartierObject X D))).map mapping ≫
        (quasicoherentCartierCechNatIso k X opens cover affine D degree).hom.app N =
      (quasicoherentCartierCechNatIso k X opens cover affine D degree).hom.app M ≫
        (CechNaturality.cechHomologyFunctor opens degree).map
          ((tensorLeft (-D).sheaf).map mapping.hom) :=
  (quasicoherentCartierCechNatIso k X opens cover affine D degree).hom.naturality mapping

end ToricPower
