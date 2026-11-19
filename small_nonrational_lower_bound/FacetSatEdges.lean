module
prelude
public import FacetSatRaw

@[expose] public section

/-!
# Required-edge clauses

The graph target already requires every graph edge to occur in some selected
facet.  The checked incidence matrix turns that condition into a short
positive clause, without recomputing any cell's edges.
-/

namespace Papers.RationalityTen.FacetSat

open GrowthBitsets GrowthDAG SparseGrowthDAG

variable {n e r v k : Nat}

def EdgeCover (requiredEdges : Nat) (edgeRows : Fin e → Nat)
    (S : List (Fin n)) : Prop :=
  ∀ q, requiredEdges.testBit q.val = true →
    ∃ c, c ∈ S ∧ (edgeRows q).testBit c.val = true

namespace EdgeCover

def ownersCheck (row : Nat) (owners : List (Fin n)) : Bool :=
  decide (Nat.land row (ofList owners) = row)

theorem clause {requiredEdges : Nat} {edgeRows : Fin e → Nat} {S : List (Fin n)}
    (H : EdgeCover requiredEdges edgeRows S) (q : Fin e) (owners : List (Fin n))
    (hrequired : requiredEdges.testBit q.val = true)
    (howners : ownersCheck (edgeRows q) owners = true) :
    (∀ c ∈ owners, c ∈ S → False) → False := by
  intro hn
  obtain ⟨c, hc, hrow⟩ := H q hrequired
  have hbit := congrArg (fun mask : Nat => mask.testBit c.val)
    (of_decide_eq_true howners)
  rw [FiniteMaskSets.testBit_land, hrow, Bool.true_and] at hbit
  have hm : c ∈ owners := (bitAt_ofList owners c).mp
    ((bitAt_eq_testBit _ _).trans hbit)
  exact hn c hm hc

theorem of_target (D : GraphGrowthConstraints.Problem n r e v k)
    (S : List (Fin n)) (H : GraphGrowthConstraints.Target D S) :
    EdgeCover D.requiredEdges D.edgeRows S := by
  intro q hrequired
  have hcover := H.edgeCover q hrequired
  obtain ⟨c, hc, hbit⟩ := (bitAt_unionValues D.edges S q.val).mp
    ((bitAt_eq_testBit _ _).trans hcover)
  refine ⟨c, hc, ?_⟩
  rw [D.edgeRows_exact]
  exact (bitAt_eq_testBit _ _).symm.trans hbit

end EdgeCover

namespace RawProjection

open PackedGraphCertificate

theorem coverage_with_edges (R : RawData)
    (valid : GraphGrowthInputs.Valid R.inputs)
    (checked : MatrixGraphProblem.Checked R.data)
    (vertices kinds : Fields) (hcheck : check R vertices kinds = true)
    {l : Nat} (leaves : Fin l → List (Fin R.n))
    (hunsat : ∀ B, Boundary (data R vertices kinds).toData.kind
      (data R vertices kinds).toData.relation
      (data R vertices kinds).ridges R.data.quota B →
      EdgeCover R.data.requiredEdges R.data.edgeRows B →
      (∀ j, ¬Same (family (leaves j)) (family B)) → False)
    (B : List (Fin R.n))
    (H : GraphGrowthConstraints.Target (R.inputs.problem valid) B) :
    ∃ j, Same (family (leaves j)) (family B) := by
  classical
  apply Classical.byContradiction
  intro hn
  exact hunsat B (boundary_of_target R valid checked vertices kinds hcheck B H)
    (EdgeCover.of_target (R.inputs.problem valid) B H)
    (fun j hj => hn ⟨j, hj⟩)

end RawProjection
end Papers.RationalityTen.FacetSat
