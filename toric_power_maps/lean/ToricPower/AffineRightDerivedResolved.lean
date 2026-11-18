module

public import ToricPower.AffineRightDerived
public import ToricPower.HomotopyRightDerived

/-!
# The affine comparison on resolved complexes

On the right orthogonal to locally contractible complexes, the actual
coaugmentation is a homotopy equivalence. Every additive target functor
therefore carries it to a quasi-isomorphism. This proves, without an
acyclicity assumption, that the derived comparison is invertible on all
objects used in the finite affine coresolution.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Functor CochainComplex TopologicalSpace

namespace ToricPower

universe u v w z

local instance affineResolvedDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (l : List I) (hl : ∀ i, i ∈ l)

include hl

/-- Coaugmentation is an actual homotopy equivalence on the right
orthogonal, by its universal mapping property there. -/
theorem affineConeCoaugmentation_homotopy_isIso
    (K : CochainComplex (QCoh X) ℤ)
    (hK : (affineCoverContractible V).rightOrthogonal
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj K)) :
    IsIso ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).map
      ((affineConeCoaugmentation V l).app K)) := by
  let P := affineCoverContractible V
  let Q := HomotopyCategory.quotient (QCoh X) (.up ℤ)
  let f := Q.map ((affineConeCoaugmentation V l).app K)
  have hf : P.trW f := affineConeCoaugmentation_mem_trW V l
    (fun K i => openFiberStage_restrict_homotopy_isZero V l K i (hl i)) K
  have hr := affineConeCoresolution_rightOrthogonal V l K
  apply (ObjectProperty.isLocal_iff_isIso P.rightOrthogonal f hK hr).mp
  intro Z hZ
  rw [← P.isLocal_trW] at hZ
  exact hZ f hf

variable {D : Type w} [Category.{z} D] [Abelian D] [HasDerivedCategory D]
  (H : QCoh X ⥤ D) [H.Additive]
  [∀ i, PreservesFiniteLimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  [∀ i, PreservesFiniteColimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]

/-- The genuine derived comparison is invertible on every resolved
input, for arbitrary additive `H` with the required affine exactness. -/
theorem affineRightDerivedUnit_isIso
    (K : CochainComplex (QCoh X) ℤ)
    (hK : (affineCoverContractible V).rightOrthogonal
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj K)) :
    IsIso ((affineRightDerivedUnit V H l).app K) := by
  have he := (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences
    ((affineConeCoaugmentation V l).app K)).mp
      (affineConeCoaugmentation_homotopy_isIso V l hl K hK)
  have heH := H.homotopyEquivalences_mapHomologicalComplex_map
    ((affineConeCoaugmentation V l).app K) he
  letI : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((affineConeCoaugmentation V l).app K)) :=
    homotopyEquivalences_le_quasiIso D (.up ℤ) _ heH
  unfold affineRightDerivedUnit
  rw [coresolutionDerivedUnit_app]
  dsimp only [Functor.comp_map]
  infer_instance

/-- The same invertibility statement on the actual homotopy category. -/
theorem affineHomotopyRightDerivedComparison_isIso
    (K : HomotopyCategory (QCoh X) (.up ℤ))
    (hK : (affineCoverContractible V).rightOrthogonal K) :
    IsIso ((homotopyRightDerivedComparison H (affineConeDerivedStage V H l)
      (affineRightDerivedUnit V H l)).app K) := by
  letI := affineRightDerivedUnit_isIso V l hl H K.as hK
  exact homotopyRightDerivedComparison_isIso H (affineConeDerivedStage V H l)
    (affineRightDerivedUnit V H l) K

end ToricPower

end
