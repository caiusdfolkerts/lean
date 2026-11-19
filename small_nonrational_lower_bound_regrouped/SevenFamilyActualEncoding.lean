module

public import Consolidated.SixActualAssembly

@[expose] public section

/-!
# Exact actual encodings for all three seven-facet families

The numerical partition leaves one distinguished seven-vertex facet.
This file supplies the remaining semantic bridge: complete local templates,
compatible-placement coverage, normalization of that distinguished facet,
and every quota of the rooted search. The six-vertex tag is deliberately
shared by all seven local types in the two-six-facets family; the compatible
placement hypothesis still retains each complete template individually.
-/

noncomputable section
namespace Papers.RationalityTen.SevenFamilyActualEncoding

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeFacetSurplus
open ChirotopeDensity ActualFacetCatalogueTransport ActualFacetTemplateAssignment
open SixFacetProfileRefinement SevenFacetBudgetIdentities
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualResidualPartition

local instance faceFintype {d : Nat} (P : ConvexPolytope d) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _

/-- The positive tags of a rooted seven-facet family. -/
def otherTag : Kind → Nat
  | .tetrahedron => 1
  | .bipyramid => 2
  | .squarePyramid => 3
  | .six _ => 4

private theorem otherTag_pos (a : Kind) : 0 < otherTag a := by
  cases a <;> simp [otherTag]

private theorem otherTag_le (a : Kind) : otherTag a ≤ 4 := by
  cases a <;> simp [otherTag]

/-- The five exact actual quotas, in the finite producer's tag order. -/
def actualQuota {d : Nat} (P : ConvexPolytope d) : Nat → Nat
  | 0 => 1
  | 1 => (tetrahedralFacets P).card
  | 2 => (smallBipyramidFacets P).card
  | 3 => (smallSquareFacets P).card
  | 4 => (sixVertexFacets P).card
  | _ => 0

def size : Option Kind → Nat
  | none => 7
  | some a => a.size

def template (i : Fin 34) : (a : Option Kind) →
    Finset (PolygonBoundaryCatalogue.Polygon (size a))
  | none => FiniteCycleCandidates.N7.templates i
  | some a => a.template

def tag : Option Kind → Nat
  | none => 0
  | some a => otherTag a

/-- A complete template assignment away from the root. The permission
predicate restricts complete six-vertex templates, not merely their profiles. -/
structure Assignment {d : Nat} (P : ConvexPolytope d) (F : Face P 3)
    (allowed : Kind → Prop) where
  kind : {G : Face P 3 // G ≠ F} → Kind
  realizes : ∀ G, RealizesKind P G.val (kind G)
  permitted : ∀ G, allowed (kind G)

def Assignment.total {d : Nat} {P : ConvexPolytope d} {F : Face P 3}
    {allowed : Kind → Prop} (A : Assignment P F allowed) (G : Face P 3) : Option Kind :=
  if h : G = F then none else some (A.kind ⟨G, h⟩)

@[simp] theorem Assignment.total_root {d : Nat} {P : ConvexPolytope d}
    {F : Face P 3} {allowed : Kind → Prop} (A : Assignment P F allowed) :
    A.total F = none := by simp [Assignment.total]

@[simp] theorem Assignment.total_other {d : Nat} {P : ConvexPolytope d}
    {F : Face P 3} {allowed : Kind → Prop} (A : Assignment P F allowed)
    (G : Face P 3) (hG : G ≠ F) :
    A.total G = some (A.kind ⟨G, hG⟩) := by
  simp [Assignment.total, hG]

theorem Assignment.total_realizes {d : Nat} {P : ConvexPolytope d}
    {F : Face P 3} {allowed : Kind → Prop} (A : Assignment P F allowed)
    (i : Fin 34)
    (loc : (facePolytope P F.val.isFace).vertices ≃ Fin 7)
    (hloc : polygonBoundary (facePolytope P F.val.isFace) loc =
      FiniteCycleCandidates.N7.templates i) (G : Face P 3) :
    ∃ localLabel : (facePolytope P G.val.isFace).vertices ≃ Fin (size (A.total G)),
      polygonBoundary (facePolytope P G.val.isFace) localLabel = template i (A.total G) := by
  by_cases hG : G = F
  · subst G
    rw [A.total_root]
    exact ⟨loc, hloc⟩
  · rw [A.total_other G hG]
    exact A.realizes ⟨G, hG⟩

/-- Every tag has the exact actual facet count. This is proved before
choosing a finite candidate index or invoking any growth classification. -/
theorem Assignment.tag_counts {d n : Nat} {P : ConvexPolytope d}
    {F : Face P 3} {allowed : Kind → Prop} (A : Assignment P F allowed)
    (lab : P.vertices ≃ Fin n) (hF : facetVertexCount P F = 7) (k : Nat) :
    (Finset.univ.filter fun G : Face P 3 =>
      (if G = F then 0 else tag (A.total G)) = k).card = actualQuota P k := by
  let actualTag (G : Face P 3) := if G = F then 0 else tag (A.total G)
  have hroot : actualTag F = 0 := by simp only [actualTag, ite_true]
  have hother (G : Face P 3) (hG : G ≠ F) :
      actualTag G = otherTag (A.kind ⟨G, hG⟩) := by
    simp only [actualTag, if_neg hG, A.total_other G hG, tag]
  have hm (G : Face P 3) (hG : G ≠ F) :
      Matches P G (A.kind ⟨G, hG⟩) := by
    obtain ⟨localLabel, hlocal⟩ := A.realizes ⟨G, hG⟩
    exact matches_of_template P lab G (A.kind ⟨G, hG⟩) localLabel hlocal
  have hzero (G : Face P 3) : actualTag G = 0 ↔ G = F := by
    by_cases hG : G = F
    · subst G; simp only [hroot, true_iff]
    · rw [hother G hG]
      exact iff_of_false (Nat.ne_of_gt (otherTag_pos _)) hG
  have hone (G : Face P 3) : actualTag G = 1 ↔ facetVertexCount P G = 4 := by
    by_cases hG : G = F
    · subst G; simp only [hroot, hF]; omega
    · have h := (hm G hG).1
      rw [hother G hG, h]
      cases A.kind ⟨G, hG⟩ <;> simp [otherTag, Kind.size]
  have htwo (G : Face P 3) : actualTag G = 2 ↔
      facetVertexCount P G = 5 ∧ facetPolygonExcess P G = 0 := by
    by_cases hG : G = F
    · subst G; simp only [hroot, hF]; omega
    · have h := hm G hG
      rw [hother G hG, h.1, h.2.2.2]
      cases A.kind ⟨G, hG⟩ <;> simp [otherTag, Kind.size, Kind.quadrilaterals, Kind.pentagons]
  have hthree (G : Face P 3) : actualTag G = 3 ↔
      facetVertexCount P G = 5 ∧ facetPolygonExcess P G = 1 := by
    by_cases hG : G = F
    · subst G; simp only [hroot, hF]; omega
    · have h := hm G hG
      rw [hother G hG, h.1, h.2.2.2]
      cases A.kind ⟨G, hG⟩ <;> simp [otherTag, Kind.size, Kind.quadrilaterals, Kind.pentagons]
  have hfour (G : Face P 3) : actualTag G = 4 ↔ facetVertexCount P G = 6 := by
    by_cases hG : G = F
    · subst G; simp only [hroot, hF]; omega
    · have h := (hm G hG).1
      rw [hother G hG, h]
      cases A.kind ⟨G, hG⟩ <;> simp [otherTag, Kind.size]
  change (Finset.univ.filter fun G => actualTag G = k).card = actualQuota P k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ 5 ≤ k := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | hk
  · simp only [hzero, Finset.filter_eq', Finset.mem_univ, if_true, Finset.card_singleton,
      actualQuota]
  · simp only [hone, actualQuota, tetrahedralFacets]
  · simp only [htwo, actualQuota, smallBipyramidFacets]
  · simp only [hthree, actualQuota, smallSquareFacets]
  · simp only [hfour, actualQuota, sixVertexFacets]
  · have hz : actualQuota P k = 0 := by
      match k, hk with
      | 0, h | 1, h | 2, h | 3, h | 4, h => omega
      | _ + 5, _ => rfl
    rw [hz]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro G _ heq
    by_cases hG : G = F
    · subst G; rw [hroot] at heq; omega
    · rw [hother G hG] at heq
      have := otherTag_le (A.kind ⟨G, hG⟩)
      omega

/-- A kind that actually occurs away from the root has positive quota. -/
theorem Assignment.quota_pos {d n : Nat} {P : ConvexPolytope d}
    {F : Face P 3} {allowed : Kind → Prop} (A : Assignment P F allowed)
    (lab : P.vertices ≃ Fin n) (hF : facetVertexCount P F = 7)
    (G : {G : Face P 3 // G ≠ F}) : 0 < actualQuota P (otherTag (A.kind G)) := by
  rw [← A.tag_counts lab hF]
  apply Finset.card_pos.mpr
  refine ⟨G.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simp only [if_neg G.property, A.total_other G.val G.property, tag]

/-- The complete compatible-placement premise for an actual seven case.
Zero-quota kinds can be omitted from the finite universe. -/
structure Coverage {n : Nat} (cells : Fin n → ConcreteGrowth.Cell) (root : Fin n)
    (i : Fin 34) (allowed : Kind → Prop) (quota : Nat → Nat) where
  rootEmbedding : Fin 7 ↪ Fin 10
  rootCell : mapCell rootEmbedding (cellOfBoundary (FiniteCycleCandidates.N7.templates i)) =
    decodeCell (cells root)
  rootKind : (cells root).kind = 0
  complete : ∀ a : Kind, allowed a → 0 < quota (otherTag a) →
    ∀ f : Fin a.size ↪ Fin 10,
      (mapCell f (cellOfBoundary a.template)).Compatible (decodeCell (cells root)) →
        ∃ j, (cells j).kind = otherTag a ∧
          decodeCell (cells j) = mapCell f (cellOfBoundary a.template)

/-- Exact actual coverage and a finite classification yield a classified
encoding of the original polytope, including all five quotas. -/
theorem classified_encoding {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (hn : P.vertices.card = 10)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (i : Fin 34) (loc : (facePolytope P F.val.isFace).vertices ≃ Fin 7)
    (hloc : polygonBoundary (facePolytope P F.val.isFace) loc =
      FiniteCycleCandidates.N7.templates i)
    (allowed : Kind → Prop) (A : Assignment P F allowed)
    (cells : Fin n → ConcreteGrowth.Cell) (quota : Nat → Nat) (root : Fin n)
    (classification : RootedFamilyClosure.FiniteClassification cells quota root)
    (coverage : Coverage cells root i allowed quota)
    (hquota : quota = actualQuota P) : HasClassifiedEncoding P := by
  let lab₀ : P.vertices ≃ Fin 10 :=
    (Fintype.equivFin P.vertices).trans (finCongr (by simpa only [Fintype.card_coe] using hn))
  obtain ⟨lab, E, hroot, htag⟩ := RootedKindedActualEncoding.normalized_encoding_of_templates
    size (template i) tag P lab₀ cells root F none loc hloc
    coverage.rootEmbedding coverage.rootCell coverage.rootKind A.total
    (A.total_realizes i loc hloc)
    (fun a => ∃ b, a = some b ∧ allowed b ∧ 0 < quota (otherTag b))
    (by
      intro G hG
      refine ⟨A.kind ⟨G, hG⟩, A.total_other G hG, A.permitted ⟨G, hG⟩, ?_⟩
      rw [hquota]
      exact A.quota_pos lab₀ hF ⟨G, hG⟩)
    (by
      intro a ha f hf
      obtain ⟨b, rfl, hb, hpos⟩ := ha
      exact coverage.complete b hb hpos f hf)
  obtain ⟨_, hcounts⟩ := RootedKindedActualEncoding.literal_target_of_tag_counts
    cells E hP classification.wellFormed
    (fun G => if G = F then 0 else tag (A.total G)) htag quota (by
      intro k
      rw [hquota]
      exact A.tag_counts lab₀ hF k)
  exact ⟨n, cells, quota, root, classification, lab, E,
    (E.mem_family root).mpr ⟨F, hroot⟩, hcounts⟩

/-- Choice only packages already classified complete local templates. -/
theorem assignment_of_realizers {d : Nat} (P : ConvexPolytope d)
    (F : Face P 3) (allowed : Kind → Prop)
    (h : ∀ G : Face P 3, G ≠ F → ∃ a, RealizesKind P G a ∧ allowed a) :
    Nonempty (Assignment P F allowed) := by
  choose kind hk using fun G : {G : Face P 3 // G ≠ F} => h G.val G.property
  exact ⟨⟨kind, fun G => (hk G).1, fun G => (hk G).2⟩⟩

theorem pure_assignment {d n : Nat} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3)
    (hother : ∀ G : Face P 3, G ≠ F → facetVertexCount P G ≤ 5) :
    Nonempty (Assignment P F (fun a => a.size ≤ 5)) := by
  apply assignment_of_realizers
  intro G hG
  obtain ⟨a, localLabel, hlocal⟩ := realizes_kind P G ((hother G hG).trans (by decide))
  have hm := matches_of_template P lab G a localLabel hlocal
  exact ⟨a, ⟨localLabel, hlocal⟩, hm.1 ▸ hother G hG⟩

theorem mixed_assignment {d n : Nat} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F G : Face P 3)
    (j : Fin 7) (loc : (facePolytope P G.val.isFace).vertices ≃ Fin 6)
    (hloc : polygonBoundary (facePolytope P G.val.isFace) loc =
      FiniteCycleCandidates.N6.templates j)
    (hother : ∀ H : Face P 3, H ≠ F → H ≠ G → facetVertexCount P H ≤ 5) :
    Nonempty (Assignment P F (fun a => a.size ≤ 5 ∨ a = .six j)) := by
  apply assignment_of_realizers
  intro H hH
  by_cases hG : H = G
  · subst H
    exact ⟨.six j, ⟨loc, hloc⟩, Or.inr rfl⟩
  · obtain ⟨a, localLabel, hlocal⟩ :=
      realizes_kind P H ((hother H hH hG).trans (by decide))
    have hm := matches_of_template P lab H a localLabel hlocal
    exact ⟨a, ⟨localLabel, hlocal⟩, Or.inl (hm.1 ▸ hother H hH hG)⟩

theorem two_six_assignment {d : Nat} (P : ConvexPolytope d) (F : Face P 3)
    (hother : ∀ G : Face P 3, G ≠ F → facetVertexCount P G ≤ 6) :
    Nonempty (Assignment P F (fun _ => True)) := by
  apply assignment_of_realizers
  intro G hG
  obtain ⟨a, ha⟩ := realizes_kind P G (hother G hG)
  exact ⟨a, ha, trivial⟩

/-- Exactly the five producer quota slots; tags above four have zero quota. -/
def rowQuota (T BP SP L : Nat) : Nat → Nat
  | 0 => 1
  | 1 => T
  | 2 => BP
  | 3 => SP
  | 4 => L
  | _ => 0

theorem quota_eq_actual {d : Nat} (P : ConvexPolytope d) (T BP SP L : Nat)
    (hT : T = (tetrahedralFacets P).card)
    (hBP : BP = (smallBipyramidFacets P).card)
    (hSP : SP = (smallSquareFacets P).card)
    (hL : L = (sixVertexFacets P).card) : rowQuota T BP SP L = actualQuota P := by
  subst T; subst BP; subst SP; subst L
  rfl

private def tenLabels (P : ConvexPolytope 4) (h : P.vertices.card = 10) :
    P.vertices ≃ Fin 10 :=
  (Fintype.equivFin P.vertices).trans (finCongr (by simpa only [Fintype.card_coe] using h))

/-- The pure-seven case now asks only for its finite family classification
and complete compatible-template placement certificates. -/
theorem pure_case {n : Nat} (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SevenPureCase P) (cells : Fin n → ConcreteGrowth.Cell) (root : Fin n)
    (classification : RootedFamilyClosure.FiniteClassification cells
      (rowQuota C.row.T C.row.BP C.row.SP 0) root)
    (coverage : Coverage cells root C.template (fun a => a.size ≤ 5)
      (rowQuota C.row.T C.row.BP C.row.SP 0)) : HasClassifiedEncoding P := by
  obtain ⟨A⟩ := pure_assignment P (tenLabels P C.vertices) C.facet C.otherSmall
  apply classified_encoding P hP C.vertices C.facet C.seven C.template C.labels
    C.boundary _ A cells _ root classification coverage
  apply quota_eq_actual P _ _ _ _ C.counts.tetrahedra C.counts.bipyramids C.counts.squarePyramids
  symm
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro G hG
  have hsize : facetVertexCount P G = 6 := (Finset.mem_filter.mp hG).2
  by_cases hGF : G = C.facet
  · subst G; have := C.seven; omega
  · have := C.otherSmall G hGF; omega

/-- The unique six-vertex facet is forced to its supplied complete local
six-template. This avoids an unjustified inference from numerical profiles. -/
theorem mixed_case {n : Nat} (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SevenMixedCase P) (cells : Fin n → ConcreteGrowth.Cell) (root : Fin n)
    (classification : RootedFamilyClosure.FiniteClassification cells
      (rowQuota C.row.T C.row.BP C.row.SP 1) root)
    (coverage : Coverage cells root C.template
      (fun a => a.size ≤ 5 ∨ a = .six C.sixTemplate)
      (rowQuota C.row.T C.row.BP C.row.SP 1)) : HasClassifiedEncoding P := by
  obtain ⟨A⟩ := mixed_assignment P (tenLabels P C.vertices) C.facet C.sixFacet
    C.sixTemplate C.sixLabels C.sixBoundary C.otherSmall
  apply classified_encoding P hP C.vertices C.facet C.seven C.template C.labels
    C.boundary _ A cells _ root classification coverage
  exact quota_eq_actual P _ _ _ _ C.counts.tetrahedra C.counts.bipyramids C.counts.squarePyramids C.six_count.symm

/-- All seven six-vertex types remain admissible in the two-six branch;
there is no lost local type or restricted parameter range. -/
theorem two_six_case {n : Nat} (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SevenTwoSixCase P) (cells : Fin n → ConcreteGrowth.Cell) (root : Fin n)
    (classification : RootedFamilyClosure.FiniteClassification cells
      (rowQuota 0 (7 - C.squarePyramids.val) C.squarePyramids.val 2) root)
    (coverage : Coverage cells root C.template (fun _ => True)
      (rowQuota 0 (7 - C.squarePyramids.val) C.squarePyramids.val 2)) :
    HasClassifiedEncoding P := by
  obtain ⟨A⟩ := two_six_assignment P C.facet C.otherSmall
  apply classified_encoding P hP C.vertices C.facet C.seven C.template C.labels
    C.boundary _ A cells _ root classification coverage
  exact quota_eq_actual P _ _ _ _ C.tetrahedron_count.symm C.bipyramid_count.symm
    C.square_count.symm C.six_count.symm

end Papers.RationalityTen.SevenFamilyActualEncoding
