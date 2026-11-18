module

public import ToricPower.CechIncidenceFaceComparison
public import ToricPower.CechDowkerHomotopy
public import ToricPower.CechOrderIsomorphism
public import ToricPower.CechCanonicalAugmentation

/-!
# Reduced cohomology of the two actual incidence complexes

The comparison is the composite of three genuine chain homotopy
equivalences: chart tuples to their face-order tuples, the common-neighbor
equivalence, and face-order tuples back to negative-ray tuples. Every map
preserves the actual integral augmentation. Scalar duality therefore gives
the comparison in all reduced degrees, including degree minus one.

Neither the existence of a negative ray nor a cohomological nerve theorem
is a hypothesis. Only the relative full-simplex comparison needs an actual
ambient chart, as supplied by a nonempty toric affine cover.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory
open ToricPower.NegativeSupportCech ToricPower.CechIncidenceChains
open ToricPower.CechChainTuples ToricPower.CechIncidenceFace
open ToricPower.CechOrderIsomorphism ToricPower.CechCanonicalAugmentation

namespace ToricPower.CechDowkerReduced

variable {Ray Chart : Type}

/-- A tuple of negative rays is allowed when one actual chart contains
every member. The witness predicate is `True`; negativity is already in
the vertex subtype. -/
def negativeRayIncidence (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    Chart → NegativeRay negative → Prop :=
  fun chart ray => incidence ray.val chart

def rayIncidenceFaceHomotopyEquiv (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) :
    HomotopyEquiv
      (incidenceChains (negativeRayIncidence incidence negative) (fun _ => True))
      (orderTupleChains
        (Dowker.Face (fun chart ray => negativeRayChartRelation incidence negative ray chart))) :=
  (incidenceFaceChainsHomotopyEquiv
    (negativeRayIncidence incidence negative) (fun _ => True)).trans
      (HomotopyEquiv.ofIso (orderTupleChainsIso
        (trueWitnessFaceOrderIso (negativeRayIncidence incidence negative))))

theorem rayIncidenceFaceHomotopyEquiv_hom_augmentation
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    (rayIncidenceFaceHomotopyEquiv incidence negative).hom.f 0 ≫
      orderTupleAugmentation
        (Dowker.Face (fun chart ray => negativeRayChartRelation incidence negative ray chart)) =
      incidenceChainAugmentation (negativeRayIncidence incidence negative) (fun _ => True) := by
  change ((incidenceFaceChainsHomotopyEquiv
      (negativeRayIncidence incidence negative) (fun _ => True)).hom.f 0 ≫
    (orderTupleChainsIso
      (trueWitnessFaceOrderIso (negativeRayIncidence incidence negative))).hom.f 0) ≫ _ = _
  rw [Category.assoc]
  exact (congrArg
    (fun mapping => (incidenceFaceChainsHomotopyEquiv
      (negativeRayIncidence incidence negative) (fun _ => True)).hom.f 0 ≫ mapping)
    (orderTupleChainsIso_hom_augmentation
      (trueWitnessFaceOrderIso (negativeRayIncidence incidence negative)))).trans
    (incidenceFaceChainsHomotopyEquiv_hom_augmentation
      (negativeRayIncidence incidence negative) (fun _ => True))

theorem rayIncidenceFaceHomotopyEquiv_inv_augmentation
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    (rayIncidenceFaceHomotopyEquiv incidence negative).inv.f 0 ≫
      incidenceChainAugmentation (negativeRayIncidence incidence negative) (fun _ => True) =
      orderTupleAugmentation
        (Dowker.Face (fun chart ray => negativeRayChartRelation incidence negative ray chart)) := by
  change ((orderTupleChainsIso
      (trueWitnessFaceOrderIso (negativeRayIncidence incidence negative))).inv.f 0 ≫
    (incidenceFaceChainsHomotopyEquiv
      (negativeRayIncidence incidence negative) (fun _ => True)).inv.f 0) ≫ _ = _
  rw [Category.assoc]
  exact (congrArg
    (fun mapping => (orderTupleChainsIso
      (trueWitnessFaceOrderIso (negativeRayIncidence incidence negative))).inv.f 0 ≫ mapping)
    (incidenceFaceChainsHomotopyEquiv_inv_augmentation
      (negativeRayIncidence incidence negative) (fun _ => True))).trans
    (orderTupleChainsIso_inv_augmentation
      (trueWitnessFaceOrderIso (negativeRayIncidence incidence negative)))

variable [Fintype Ray] [Fintype Chart]

/-- The two original tuple-chain complexes, with both actual homotopies.
Common-neighbor sets are finite; either complex may have no vertices. -/
def negativeIncidenceChainHomotopyEquiv (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) :
    HomotopyEquiv (incidenceChains incidence negative)
      (incidenceChains (negativeRayIncidence incidence negative) (fun _ => True)) := by
  classical
  exact ((incidenceFaceChainsHomotopyEquiv incidence negative).trans
    (Dowker.commonNeighborChainHomotopyEquiv
      (negativeRayChartRelation incidence negative))).trans
        (rayIncidenceFaceHomotopyEquiv incidence negative).symm

theorem negativeIncidenceChainHomotopyEquiv_inv_augmentation
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    (negativeIncidenceChainHomotopyEquiv incidence negative).inv.f 0 ≫
      incidenceChainAugmentation incidence negative =
        incidenceChainAugmentation (negativeRayIncidence incidence negative) (fun _ => True) := by
  classical
  change ((rayIncidenceFaceHomotopyEquiv incidence negative).hom.f 0 ≫
    ((Dowker.commonNeighborChainMap
      (fun chart ray => negativeRayChartRelation incidence negative ray chart)).f 0 ≫
      (incidenceFaceChainsHomotopyEquiv incidence negative).inv.f 0)) ≫ _ = _
  simp only [Category.assoc,
    incidenceFaceChainsHomotopyEquiv_inv_augmentation,
    Dowker.commonNeighborChainMap_augmentation,
    rayIncidenceFaceHomotopyEquiv_hom_augmentation]

theorem negativeIncidenceChainHomotopyEquiv_hom_augmentation
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    (negativeIncidenceChainHomotopyEquiv incidence negative).hom.f 0 ≫
      incidenceChainAugmentation (negativeRayIncidence incidence negative) (fun _ => True) =
        incidenceChainAugmentation incidence negative := by
  classical
  change (((incidenceFaceChainsHomotopyEquiv incidence negative).hom.f 0 ≫
    (Dowker.commonNeighborChainMap
      (negativeRayChartRelation incidence negative)).f 0) ≫
      (rayIncidenceFaceHomotopyEquiv incidence negative).inv.f 0) ≫ _ = _
  simp only [Category.assoc,
    rayIncidenceFaceHomotopyEquiv_inv_augmentation,
    Dowker.commonNeighborChainMap_augmentation,
    incidenceFaceChainsHomotopyEquiv_hom_augmentation]

variable (𝕜 : Type) [Field 𝕜]

/-- Every reduced degree of the negative chart complex agrees with the
corresponding reduced degree of the actual negative-ray complex. -/
def negativeChartRayReducedIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    canonicalNegativeReducedShifted 𝕜 incidence negative degree ≅
      canonicalNegativeReducedShifted 𝕜
        (negativeRayIncidence incidence negative) (fun _ => True) degree :=
  canonicalReducedIsoOfAugmentedChainHomotopyEquiv 𝕜 incidence negative
    (negativeRayIncidence incidence negative) (fun _ => True)
    (negativeIncidenceChainHomotopyEquiv incidence negative)
    (negativeIncidenceChainHomotopyEquiv_inv_augmentation incidence negative) degree

/-- The all-degree relative chart cohomology formula, with the actual
negative-ray reduced complex on its right-hand side. The ambient anchor
is a chart, never a negative ray. -/
def relativeChartRayReducedIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) (degree : ℕ) :
    (relativeComplex 𝕜 incidence negative).homology degree ≅
      canonicalNegativeReducedShifted 𝕜
        (negativeRayIncidence incidence negative) (fun _ => True) degree :=
  relativeHomologyCanonicalReducedIso 𝕜 incidence negative anchor degree ≪≫
    negativeChartRayReducedIso 𝕜 incidence negative degree

end ToricPower.CechDowkerReduced
