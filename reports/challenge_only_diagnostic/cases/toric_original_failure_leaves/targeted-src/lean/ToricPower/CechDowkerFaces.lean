module

public import ToricPower.CechNegativeSupportGeneric
public import ToricPower.DowkerFacePosets

/-!
# Literal face-poset identifications for the negative Čech nerve

The chart complex in `CechNegativeSupportGeneric` uses original ray witnesses
and a negativity predicate.  The generic Dowker relation instead uses the
subtype of negative rays.  The order isomorphisms here prove the equivalence
of these presentations, preserving every nonempty face.

The second complex consists of the negative rays contained in a common chart.
Identifying it with the induced complex of ray sets of cones additionally
requires the smooth-cone face theorem.  No such geometric identification,
subdivision theorem, or cohomology comparison is assumed here.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

open scoped Classical

namespace ToricPower.NegativeSupportCech

variable {Ray : Type*} {Chart : Type}

abbrev NegativeRay (negative : Ray → Prop) := {ray : Ray // negative ray}

def negativeRayChartRelation (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) : NegativeRay negative → Chart → Prop :=
  fun ray chart => incidence ray.val chart

/-- The actual face-poset of the chart complex is the column face-poset of
the incidence relation restricted to negative rays. -/
def negativeChartFaceOrderIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) :
    {face : Finset Chart // face ∈ negativeChartComplex incidence negative} ≃o
      Dowker.Face (negativeRayChartRelation incidence negative) where
  toFun face := ⟨face.val, face.property.1, by
    obtain ⟨ray, negativeRay, contains⟩ := face.property.2
    exact ⟨⟨ray, negativeRay⟩, contains⟩⟩
  invFun face := ⟨face.val, face.property.1, by
    obtain ⟨ray, contains⟩ := face.property.2
    exact ⟨ray.val, ray.property, contains⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The row complex of the same incidence relation.  Its vertices really are
negative rays; a face is a nonempty finite set lying in one actual chart. -/
def negativeRayComplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    PreAbstractSimplicialComplex (NegativeRay negative) where
  faces := {face | face.Nonempty ∧
    ∃ chart, ∀ ray ∈ face, incidence ray.val chart}
  isRelLowerSet_faces := by
    intro face member
    refine ⟨member.1, ?_⟩
    intro smaller subset nonempty
    obtain ⟨chart, contains⟩ := member.2
    exact ⟨nonempty, chart, fun ray present => contains ray (subset present)⟩

def negativeRayFaceOrderIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) :
    {face : Finset (NegativeRay negative) // face ∈ negativeRayComplex incidence negative} ≃o
      Dowker.Face (fun chart ray => negativeRayChartRelation incidence negative ray chart) :=
  OrderIso.refl _

section Finite

variable [Fintype Ray] [Fintype Chart]

/-- The face-poset adjunction uses the actual restricted incidence relation.
Its domain presentations are identified with the two displayed complexes by
the preceding order isomorphisms. -/
def negativeIncidenceAdjunction (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) :=
  Dowker.commonNeighborAdjunction (negativeRayChartRelation incidence negative)

end Finite

end ToricPower.NegativeSupportCech
