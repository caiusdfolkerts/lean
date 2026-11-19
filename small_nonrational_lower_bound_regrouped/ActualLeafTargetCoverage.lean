module
public import ActualLeafCertificates

@[expose] public section

/-! Full terminal matching, retained for the classification assertion of
Proposition9. This conclusion records the complete actual boundary;
rational realizability is a separate corollary. -/
noncomputable section
namespace Papers.RationalityTen.ActualLeafTargetCoverage
open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open MatroidChecked.FacetBoundaryEncoding
open ActualFacetCatalogueTransport LiteralMaskGeometry
open ChirotopeDensity ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData Nonrational.TerminalVerification
open RawLeafCertificate RawBoundaryMatch ActualLeafCertificates

/-- Both complete facet and polygon families agree with a literal target. -/
def HasTerminal (P : ConvexPolytope 4) : Prop :=
  ∃ j, j < targetCount ∧ ∃ lab : Fin 10 ≃ VertexType P,
    RealizesBoundary P lab (decode (targets j))

theorem rationallyRealizable_of_hasTerminal
    (hvalid : ∀ j, j < targetCount → ValidTarget j)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (h : HasTerminal P) :
    RationallyRealizable P := by
  obtain ⟨j, hj, lab, hB⟩ := h
  exact hvalid j hj P lab hP hB

/-- Every branch of the finite disposition checker has its ordinary
geometric interpretation. No realizability premise is inferred from a
producer label; all negative and positive witnesses are checked. -/
theorem checked_leaf_hasTerminal {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices,
      (Papers.PolytopeVertexCone.actualNeighbors P v.val).card ≠ 4)
    (lab : P.vertices ≃ Fin 10) (cells : Fin n → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (selected : List (Fin n)) (hnodup : selected.Nodup)
    (hfamily : E.family = selected.toFinset)
    (raw : List ConcreteGrowth.Cell) (hraw : selected.map cells = raw)
    (quota : Nat → Nat)
    (hquota : ∀ k, (E.family.filter fun i => (cells i).kind = k).card = quota k)
    (certificate : Certificate) (hcheck : check quota raw certificate = true) :
    HasTerminal P := by
  cases certificate with
  | quota kind =>
    exact (RawClosedLeafObstructions.quota_not_selected_family cells E selected
      hnodup hfamily raw hraw kind (quota kind) (hquota kind) hcheck).elim
  | incidence vertex =>
    obtain ⟨hbound, hbad⟩ := Bool.and_eq_true_iff.mp hcheck
    exact (RawClosedLeafObstructions.incidence_below_five_selected_family
      cells E hP hnonsimple selected hnodup hfamily raw hraw
      ⟨vertex, of_decide_eq_true hbound⟩ hbad).elim
  | euler =>
    exact (RawClosedLeafObstructions.global_euler_not_selected_family
      cells hwell E hP selected hnodup hfamily raw hraw hcheck).elim
  | vertexLink vertex =>
    obtain ⟨hbound, hbad⟩ := Bool.and_eq_true_iff.mp hcheck
    exact (VertexLinkObstruction.checked_not_selected_family
      cells hwell E hP selected hnodup hfamily raw hraw
      ⟨vertex, of_decide_eq_true hbound⟩ hbad).elim
  | matching entry =>
    obtain ⟨hboundary, hentry⟩ := Bool.and_eq_true_iff.mp hcheck
    have hB := realizes_raw_leaf P hP lab cells E selected hfamily raw hraw
    rw [decode_eq_of_boundaryCheck raw entry.boundary hboundary] at hB
    obtain ⟨hbound, permutation, hmatch⟩ :=
      witnessCheck_decode entry.boundary entry.witness hentry
    refine ⟨entry.witness.target, hbound, permutation.symm.trans lab.symm, ?_⟩
    rw [← hmatch]
    exact hB.relabel permutation

#print axioms checked_leaf_hasTerminal

/-- Close an actual rooted case after its exhaustive finite classification.
All geometric hypotheses are retained for the same original polytope. The
word returned by the search changes only its vertex labels. -/
theorem hasTerminal_of_classification {n g k : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices,
      (Papers.PolytopeVertexCone.actualNeighbors P v.val).card ≠ 4)
    (lab : P.vertices ≃ Fin 10) (cells : Fin n → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (frames : Fin g → BoundaryGeneratorFrames.BoundaryFrame cells)
    (leaves : Fin k → List (Fin n)) (rawLeaves : Fin k → List ConcreteGrowth.Cell)
    (hraw : ∀ j, (leaves j).map cells = rawLeaves j)
    (quota : Nat → Nat)
    (hquota : ∀ t, (E.family.filter fun i => (cells i).kind = t).card = quota t)
    (certificates : Fin k → Certificate)
    (hchecked : ∀ j, check quota (rawLeaves j) (certificates j) = true)
    (hcomplete : ∃ j word, (leaves j).Nodup ∧
      GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
        (SparseGrowthDAG.family (OrbitGrowthDAG.applyWord
          (fun f => (frames f).toBoundaryRenaming hwell) word E.family.toList))) :
    HasTerminal P := by
  obtain ⟨j, word, hnodup, heq⟩ := hcomplete
  obtain ⟨newLabel, E', hfamily, hcounts⟩ :=
    ActualGrowthLeafTransport.encoding_of_leaf cells hwell E frames word (leaves j) heq
  exact checked_leaf_hasTerminal P hP hnonsimple newLabel cells hwell E'
    (leaves j) hnodup hfamily (rawLeaves j) (hraw j) quota
    (fun t => (hcounts t).trans (hquota t)) (certificates j) (hchecked j)

#print axioms hasTerminal_of_classification

end Papers.RationalityTen.ActualLeafTargetCoverage
