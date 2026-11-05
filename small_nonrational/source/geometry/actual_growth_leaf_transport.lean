module

public import BoundaryGeneratorFrames
public import RawClosedLeafObstructions

@[expose] public section

/-!
# From a checked growth leaf to the actual polytope

A search word is interpreted as a composition of vertex permutations, not
merely as a permutation of abstract candidate indices. Consequently a complete
leaf remains an encoding of the original convex polytope with renamed labels.
The exact kind counts are preserved. The ordered leaf itself is retained for
the separately checked quota, incidence, Euler, and terminal-match tests.
-/

noncomputable section
namespace Papers.RationalityTen.ActualGrowthLeafTransport

open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open MatroidChecked.FacetBoundaryEncoding
open LiteralMaskGeometry BoundaryGeneratorFrames
open GrowthDAG SparseGrowthDAG GrowthRenaming

theorem toFinset_map_eq_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (A : List α) : (A.map f).toFinset = A.toFinset.image f := by
  ext b
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

theorem toFinset_eq_of_same {n : Nat} {A B : List (Fin n)}
    (h : Same (family A) (family B)) : A.toFinset = B.toFinset := by
  ext i
  simp only [List.mem_toFinset, ← has_true]
  rw [show has A i = has B i from h i]

/-- The list action used in the finite completeness proof is exactly the
cell action of the corresponding geometric frame. -/
theorem wordFrame_applyWord {n g : Nat} (cells : Fin n → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (frames : Fin g → BoundaryFrame cells) (word : List (Fin g))
    (B : List (Fin n)) :
    OrbitGrowthDAG.applyWord (fun f => (frames f).toBoundaryRenaming hwell) word B =
      B.map (wordFrame cells frames word).cellMap.forward := by
  induction word generalizing B with
  | nil =>
    simp only [OrbitGrowthDAG.applyWord, wordFrame, identityFrame,
      CheckedGraphGrowthFrames.identityBijection, List.map_id_fun, id_eq]
  | cons f rest ih =>
    rw [OrbitGrowthDAG.applyWord, ih, List.map_map]
    rfl

/-- No kind is lost or introduced when the vertex labels are renamed. -/
theorem renameEncoding_kind_card {d n : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {cells : Fin n → ConcreteGrowth.Cell}
    (F : BoundaryFrame cells)
    (E : Encoding P lab (fun i => decodeCell (cells i))) (k : Nat) :
    ((renameEncoding F E).family.filter fun i => (cells i).kind = k).card =
      (E.family.filter fun i => (cells i).kind = k).card := by
  rw [renameEncoding_family, Finset.filter_image]
  simp only [F.kind_preserved]
  exact Finset.card_image_of_injective _ (fun _ _ h => F.cellMap.injective h)

/-- A literal leaf equality supplies a genuine encoding of all actual
facets after the recorded word. It also transports every exact quota. -/
theorem encoding_of_leaf {d n g : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin n → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (frames : Fin g → BoundaryFrame cells) (word : List (Fin g))
    (leaf : List (Fin n))
    (heq : Same (family leaf)
      (family (OrbitGrowthDAG.applyWord
        (fun f => (frames f).toBoundaryRenaming hwell) word E.family.toList))) :
    ∃ newLabel : P.vertices ≃ Fin 10,
      ∃ E' : Encoding P newLabel (fun i => decodeCell (cells i)),
        E'.family = leaf.toFinset ∧
        ∀ k, (E'.family.filter fun i => (cells i).kind = k).card =
          (E.family.filter fun i => (cells i).kind = k).card := by
  let F := wordFrame cells frames word
  refine ⟨lab.trans F.vertices, renameEncoding F E, ?_, ?_⟩
  · have h := toFinset_eq_of_same heq
    rw [wordFrame_applyWord, toFinset_map_eq_image, Finset.toList_toFinset] at h
    exact (renameEncoding_family F E).trans h.symm
  · exact renameEncoding_kind_card F E

/-- The identity-word case is useful for certificate forests whose
candidate universe already fixes every label. -/
theorem encoding_family_of_leaf {d n : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {cells : Fin n → ConcreteGrowth.Cell}
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (leaf : List (Fin n)) (heq : Same (family leaf) (family E.family.toList)) :
    E.family = leaf.toFinset := by
  have h := toFinset_eq_of_same heq
  rw [Finset.toList_toFinset] at h
  exact h.symm

/-- This wrapper keeps the raw leaf in its checked order. A duplicate-free
index list is an explicit finite obligation, not a consequence of equality
of the underlying sets. -/
theorem exists_actual_leaf {d n g k : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin n → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (frames : Fin g → BoundaryFrame cells)
    (leaves : Fin k → List (Fin n)) (rawLeaves : Fin k → List ConcreteGrowth.Cell)
    (hnodup : ∀ j, (leaves j).Nodup)
    (hraw : ∀ j, (leaves j).map cells = rawLeaves j)
    (hcomplete : ∃ j word, Same (family (leaves j))
      (family (OrbitGrowthDAG.applyWord
        (fun f => (frames f).toBoundaryRenaming hwell) word E.family.toList))) :
    ∃ j, ∃ newLabel : P.vertices ≃ Fin 10,
      ∃ E' : Encoding P newLabel (fun i => decodeCell (cells i)),
        E'.family = (leaves j).toFinset ∧ (leaves j).Nodup ∧
        (leaves j).map cells = rawLeaves j ∧
        ∀ k, (E'.family.filter fun i => (cells i).kind = k).card =
          (E.family.filter fun i => (cells i).kind = k).card := by
  obtain ⟨j, word, heq⟩ := hcomplete
  obtain ⟨newLabel, E', hfamily, hcounts⟩ :=
    encoding_of_leaf cells hwell E frames word (leaves j) heq
  exact ⟨j, newLabel, E', hfamily, hnodup j, hraw j, hcounts⟩

#print axioms encoding_of_leaf
#print axioms exists_actual_leaf

end Papers.RationalityTen.ActualGrowthLeafTransport
