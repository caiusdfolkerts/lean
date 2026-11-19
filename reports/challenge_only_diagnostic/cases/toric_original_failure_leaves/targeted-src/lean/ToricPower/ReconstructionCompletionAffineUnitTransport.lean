module

public import ToricPower.AffineRankOneSections

/-! # The original rank-one affine image under tilde

This whole coefficient isomorphism keeps the named affine unit image
as its exact target, before any augmentation is substituted.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ToricPower

/-- The actual tilde equivalence with the original coordinate-module
category fixed before an affine geometric map is substituted. -/
def reconstructionAffineTildeEquivalence (R : Type) [CommRing R] :
    ModuleCat.{0} R ≌ QCoh (Spec (.of R)) :=
  tildeEquiv (R := CommRingCat.of R)

/-- The actual tilde equivalence and direct image send the coordinate
ring to the named rank-one affine coefficient. -/
def reconstructionAffineTildeUnitIso (R : Type) [CommRing R]
    (X : Scheme) (j : Spec (.of R) ⟶ X) [IsAffineHom j] :
    ((reconstructionAffineTildeEquivalence R).functor ⋙
      quasicoherentAffinePushforward j).obj (ModuleCat.of R R) ≅
        quasicoherentAffineUnitImage j :=
  (quasicoherentAffinePushforward j).mapIso
    (quasicoherentTildeUnitIso (CommRingCat.of R))

end ToricPower

end
