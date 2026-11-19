module

public import RootedSmallFacetCoverage

@[expose] public section

/-!
# Complete rooted encodings with the prescribed facet kinds

The finite coverage certificates retain the kind as well as the complete
cell. Consequently the same actual facet assignment supplies both the
candidate indices and their quotas. No inference from coinciding numerical
profiles is used to identify two combinatorial facet types.
-/

noncomputable section
namespace Papers.RationalityTen.RootedKindedActualEncoding

open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open MatroidChecked.FacetBoundaryEncoding
open ActualFacetCatalogueTransport LiteralMaskGeometry

/-- Choose a complete encoding while keeping every supplied actual tag.
The distinguished root is forced to its specified index, even when the
literal candidate table contains redundant records. -/
theorem encoding_with_kinds {d c : Nat} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin 10) (cells : Fin c → ConcreteGrowth.Cell)
    (F : Face P 3) (root : Fin c) (tag : Face P 3 → Nat)
    (hroot : decodeCell (cells root) = actualCell P lab F)
    (hrootKind : (cells root).kind = tag F)
    (hcoverage : ∀ G : Face P 3, ∃ i,
      (cells i).kind = tag G ∧ decodeCell (cells i) = actualCell P lab G) :
    ∃ E : Encoding P lab (fun i => decodeCell (cells i)),
      E.index F = root ∧ ∀ G, (cells (E.index G)).kind = tag G := by
  choose index hindex using hcoverage
  let E : Encoding P lab (fun i => decodeCell (cells i)) :=
    { index := fun G => if G = F then root else index G
      index_spec := by
        intro G
        split_ifs with hGF
        · simpa only [hGF] using hroot
        · exact (hindex G).2 }
  refine ⟨E, ?_, ?_⟩
  · change (if F = F then root else index F) = root
    simp only [ite_true]
  · intro G
    change (cells (if G = F then root else index G)).kind = tag G
    by_cases hGF : G = F
    · subst G
      simpa only [ite_true] using hrootKind
    · simpa only [if_neg hGF] using (hindex G).1

/-- A full local template assignment and complete compatible-placement
certificates give an actual rooted boundary with exactly those type tags.
The eligibility premise is explicit; in concrete rows it follows from the
zero counts of omitted types. -/
theorem normalized_encoding_of_templates {d c : Nat} {T : Type*}
    (size : T → Nat)
    (templates : (t : T) → Finset (PolygonBoundaryCatalogue.Polygon (size t)))
    (tag : T → Nat) (P : ConvexPolytope d) (lab₀ : P.vertices ≃ Fin 10)
    (cells : Fin c → ConcreteGrowth.Cell) (root : Fin c)
    (F : Face P 3) (rootType : T)
    (loc : (facePolytope P F.val.isFace).vertices ≃ Fin (size rootType))
    (hloc : polygonBoundary (facePolytope P F.val.isFace) loc = templates rootType)
    (rootEmbedding : Fin (size rootType) ↪ Fin 10)
    (hrootCell : mapCell rootEmbedding (cellOfBoundary (templates rootType)) =
      decodeCell (cells root))
    (hrootKind : (cells root).kind = 0)
    (assignment : Face P 3 → T)
    (hlocal : ∀ G : Face P 3,
      ∃ localLabel : (facePolytope P G.val.isFace).vertices ≃ Fin (size (assignment G)),
        polygonBoundary (facePolytope P G.val.isFace) localLabel = templates (assignment G))
    (eligible : T → Prop)
    (heligible : ∀ G : Face P 3, G ≠ F → eligible (assignment G))
    (hfinite : ∀ t, eligible t → ∀ f : Fin (size t) ↪ Fin 10,
      (mapCell f (cellOfBoundary (templates t))).Compatible (decodeCell (cells root)) →
        ∃ i, (cells i).kind = tag t ∧
          decodeCell (cells i) = mapCell f (cellOfBoundary (templates t))) :
    ∃ lab : P.vertices ≃ Fin 10,
      ∃ E : Encoding P lab (fun i => decodeCell (cells i)),
        E.index F = root ∧
          ∀ G, (cells (E.index G)).kind = if G = F then 0 else tag (assignment G) := by
  obtain ⟨lab, hlab⟩ := ActualGrowthTarget.normalize_facet_template_to_embedding
    P lab₀ F loc (templates rootType) hloc rootEmbedding
  have hroot : decodeCell (cells root) = actualCell P lab F :=
    hrootCell.symm.trans hlab.symm
  refine ⟨lab, ?_⟩
  apply encoding_with_kinds P lab cells F root
    (fun G => if G = F then 0 else tag (assignment G)) hroot
  · simpa only [ite_true] using hrootKind
  · intro G
    by_cases hGF : G = F
    · subst G
      exact ⟨root, by simpa only [ite_true] using hrootKind, hroot⟩
    obtain ⟨localLabel, hlabel⟩ := hlocal G
    have hcell := actualCell_of_template P lab G localLabel (templates (assignment G)) hlabel
    obtain ⟨i, hk, hi⟩ := hfinite (assignment G) (heligible G hGF)
      (ActualFaceTransport.labelEmbedding P lab G localLabel) (by
        rw [← hcell, hroot]
        exact actualCell_compatible P lab G F hGF)
    exact ⟨i, by simpa only [if_neg hGF] using hk, hi.trans hcell.symm⟩

/-- Exact actual tag counts supply every growth quota, with the actual
ridge pairing and connectedness supplied by the complete encoding. -/
theorem literal_target_of_tag_counts {d c : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (hP : P.dim = 4) (hwell : ∀ i, WellFormed (cells i))
    (tag : Face P 3 → Nat) (htag : ∀ G, (cells (E.index G)).kind = tag G)
    (quota : Nat → Nat)
    (hcounts : ∀ k, (Finset.univ.filter fun G => tag G = k).card = quota k) :
    GrowthRenaming.Target
      (fun a => SparseGrowthDAG.has (ConcreteGrowth.ridgeList cells a))
      (fun a b => ConcreteGrowth.compatible (cells a) (cells b))
      (fun a => (cells a).kind) quota E.family.toList ∧
      ∀ k, (E.family.filter fun a => (cells a).kind = k).card = quota k := by
  have heq (k : Nat) :
      (E.family.filter fun a => (cells a).kind = k).card = quota k := by
    rw [ActualGrowthTarget.encoded_kind_card]
    simp_rw [htag]
    exact hcounts k
  exact ⟨LiteralMaskGeometry.actual_literal_target cells hwell E hP quota
    (fun k => (heq k).le), heq⟩

end Papers.RationalityTen.RootedKindedActualEncoding
