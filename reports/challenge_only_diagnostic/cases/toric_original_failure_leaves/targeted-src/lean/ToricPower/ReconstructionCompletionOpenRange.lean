module

public import ToricPower.QuasicoherentPushforwardComposition
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Transporting the affine calculation to its image open

The actual chart isomorphism identifies the direct image from a chart
with the direct image from its image open.  Naturality transports the
original comparison on arbitrary unbounded complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [IsAffineHom j] [IsAffineHom j.opensRange.ι]
  {B : Type*} [Category* B] [Abelian B]
  (F G : CochainComplex (QCoh X) ℤ ⥤ CochainComplex B ℤ)
  (a : F ⟶ G)

/-- The source-chart calculation gives the same natural comparison on
the inclusion of the actual image open. -/
theorem reconstructionOpenRange_quasiIso
    (localQuasiIso : ∀ J : CochainComplex (QCoh U) ℤ,
      QuasiIso (a.app (((quasicoherentAffinePushforward j).mapHomologicalComplex (.up ℤ)).obj J)))
    (K : CochainComplex (QCoh j.opensRange.toScheme) ℤ) :
    QuasiIso (a.app (((quasicoherentAffinePushforward j.opensRange.ι).mapHomologicalComplex (.up ℤ)).obj K)) := by
  let T := quasicoherentAffinePushforward j.isoOpensRange.inv
  let J := (T.mapHomologicalComplex (.up ℤ)).obj K
  let comparison := quasicoherentPushforwardCompIso j.isoOpensRange.inv j ≪≫
    quasicoherentPushforwardCongrIso (Scheme.Hom.isoOpensRange_inv_comp j)
  let e : ((quasicoherentAffinePushforward j).mapHomologicalComplex (.up ℤ)).obj J ≅
      ((quasicoherentAffinePushforward j.opensRange.ι).mapHomologicalComplex (.up ℤ)).obj K :=
    (NatIso.mapHomologicalComplex comparison (.up ℤ)).app K
  haveI := localQuasiIso J
  haveI : QuasiIso (a.app _ ≫ G.map e.inv) := by
    rw [← a.naturality e.inv]
    infer_instance
  exact quasiIso_of_comp_right _ (G.map e.inv)

end ToricPower

end
