module

public import RawLeafCertificate
public import ActualGrowthLeafTransport
public import RawClosedLeafObstructions
public import EncodedBoundaryRealization
public import RawBoundaryMatchGeometry
public import TerminalRealization

@[expose] public section

/-!
# Geometric soundness of every terminal disposition

This is the common endpoint for the finite forests. Its input is a complete
encoding of an actual convex four-polytope, together with the exact ordered
leaf, its duplicate-free index list, and its genuine kind counts. A checked
negative certificate contradicts these geometric facts. A checked positive
certificate transports both face families to a verified terminal.
-/

noncomputable section
namespace Papers.RationalityTen.ActualLeafCertificates

open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open MatroidChecked.FacetBoundaryEncoding
open ActualFacetCatalogueTransport LiteralMaskGeometry
open ChirotopeDensity ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData Nonrational.TerminalVerification
open RawLeafCertificate RawBoundaryMatch

/-- The two independently developed mask decoders have identical meaning. -/
theorem decodeMask_eq_maskSet (m : Nat) : decodeMask m = maskSet m := rfl

/-- Extracting a raw list of masks preserves precisely the complete facet
and polygon families of the encoded cells. -/
theorem decode_boundary_map {n : Nat} (cells : Fin n → ConcreteGrowth.Cell)
    (selected : List (Fin n)) :
    decode (boundary (selected.map cells)) =
      encodedBoundary (fun i => decodeCell (cells i)) selected.toFinset := by
  apply Boundary.ext_faces
  · simp only [decode, boundary, List.map_map,
      ActualGrowthLeafTransport.toFinset_map_eq_image,
      Finset.image_image, encodedBoundary, decodeCell, Function.comp_def,
      decodeMask_eq_maskSet]
  · ext S
    simp only [decode, boundary, encodedBoundary, decodeCell,
      Finset.mem_image, List.mem_toFinset, List.mem_flatMap, List.mem_map,
      Finset.mem_biUnion, decodeMask_eq_maskSet]
    aesop

theorem decode_eq_of_boundaryCheck (raw : List ConcreteGrowth.Cell) (B : RawBoundary)
    (h : boundaryCheck raw B = true) : decode (boundary raw) = decode B := by
  obtain ⟨hf, hp⟩ := Bool.and_eq_true_iff.mp h
  have hf' : (boundary raw).facets.toFinset = B.facets.toFinset := by
    ext m
    simpa only [List.mem_toFinset] using sameSetCheck_sound _ _ hf m
  have hp' : (boundary raw).polygons.toFinset = B.polygons.toFinset := by
    ext m
    simpa only [List.mem_toFinset] using sameSetCheck_sound _ _ hp m
  apply Boundary.ext_faces <;> simp only [decode, hf', hp']

theorem realizes_raw_leaf {n : Nat} (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (lab : P.vertices ≃ Fin 10) (cells : Fin n → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (selected : List (Fin n)) (hfamily : E.family = selected.toFinset)
    (raw : List ConcreteGrowth.Cell) (hraw : selected.map cells = raw) :
    RealizesBoundary P lab.symm (decode (boundary raw)) := by
  rw [← hraw, decode_boundary_map]
  exact realizes_literal_boundary_of_family_eq P hP lab
    (fun i => decodeCell (cells i)) E selected.toFinset hfamily

/-- Every branch of the finite disposition checker has its ordinary
geometric interpretation. No realizability premise is inferred from a
producer label; all negative and positive witnesses are checked. -/
theorem checked_leaf_rationallyRealizable {n : Nat}
    (hvalid : ∀ j, j < targetCount → ValidTarget j)
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
    RationallyRealizable P := by
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
    exact rationallyRealizable_of_matching (hvalid entry.witness.target hbound)
      P lab.symm hP (decode entry.boundary) hB permutation hmatch

#print axioms checked_leaf_rationallyRealizable

/-- Close an actual rooted case after its exhaustive finite classification.
All geometric hypotheses are retained for the same original polytope. The
word returned by the search changes only its vertex labels. -/
theorem rationallyRealizable_of_classification {n g k : Nat}
    (hvalid : ∀ j, j < targetCount → ValidTarget j)
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
    RationallyRealizable P := by
  obtain ⟨j, word, hnodup, heq⟩ := hcomplete
  obtain ⟨newLabel, E', hfamily, hcounts⟩ :=
    ActualGrowthLeafTransport.encoding_of_leaf cells hwell E frames word (leaves j) heq
  exact checked_leaf_rationallyRealizable hvalid P hP hnonsimple newLabel cells hwell E'
    (leaves j) hnodup hfamily (rawLeaves j) (hraw j) quota
    (fun t => (hcounts t).trans (hquota t)) (certificates j) (hchecked j)

#print axioms rationallyRealizable_of_classification

end Papers.RationalityTen.ActualLeafCertificates
