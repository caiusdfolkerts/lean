module

public import Papers.GraphicalZonotopes.ThreeTreeDeletion
public import Papers.GraphicalZonotopes.ThreeTreeIncidenceTree
public import Papers.GraphicalZonotopes.ThreeTreeSharedEdges

/-! # The boundary-face dictionary for stacked triangulations

The face set is part of the construction. Starting with the four faces of a
tetrahedron, a stacking step removes one available face and inserts its three
cones over the face's edges. The dictionary identifies those actual boundary
faces with triangles contained in exactly one construction tetrahedron.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def boundaryTriangles (G : SimpleGraph V) : Finset (Finset V) :=
  (triangles G).filter (fun T => triangleMultiplicity G T = 1)

@[simp] theorem mem_boundaryTriangles {G : SimpleGraph V} {T : Finset V} :
    T ∈ boundaryTriangles G ↔ T.card = 3 ∧ G.IsClique T ∧ triangleMultiplicity G T = 1 := by
  simp only [boundaryTriangles,mem_filter,mem_triangles,and_assoc]

theorem triangleMultiplicity_cliqueGraph_of_subset {C T : Finset V}
    (hC : C.card = 4) (hTC : T ⊆ C) : triangleMultiplicity (cliqueGraph C) T = 1 := by
  rw [triangleMultiplicity,tetrahedra_cliqueGraph hC,filter_singleton,if_pos hTC,card_singleton]

theorem boundaryTriangles_cliqueGraph {C : Finset V} (hC : C.card = 4) :
    boundaryTriangles (cliqueGraph C) = C.powersetCard 3 := by
  ext T
  rw [boundaryTriangles,mem_filter,triangles_cliqueGraph hC]
  exact ⟨fun h => h.1,fun h => ⟨h,
    triangleMultiplicity_cliqueGraph_of_subset hC (mem_powersetCard.mp h).1⟩⟩

private theorem old_triangle_subset_attach_iff {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u ∉ S) {A T : Finset V}
    (hA : A.card = 3) (hT : T.card = 3) (hcT : G.IsClique T) :
    T ⊆ insert u A ↔ T = A := by
  constructor
  · intro hsub
    have huT : u ∉ T := fun hm => hu (h.clique_subset_active (by omega) hcT hm)
    apply eq_of_subset_of_card_le
    · intro t ht
      exact (mem_insert.mp (hsub ht)).resolve_left (fun he => huT (he ▸ ht))
    · omega
  · rintro rfl
    exact subset_insert _ _

/-- The boundary update is exactly the usual one-to-three subdivision of a
triangular face. It is proved from actual clique incidences. -/
theorem boundaryTriangles_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u ∉ S) {A : Finset V}
    (hA : A.card = 3) (hAS : A ⊆ S) (hcA : G.IsClique A)
    (hbA : triangleMultiplicity G A = 1) :
    boundaryTriangles (G ⊔ attachmentStar u A) =
      (boundaryTriangles G).erase A ∪ (A.powersetCard 2).image (insert u) := by
  ext T
  constructor
  · intro hT
    obtain ⟨hTc,hTcl,hTm⟩ := mem_boundaryTriangles.mp hT
    by_cases huT : u ∈ T
    · apply mem_union_right
      have ht : T ∈ triangles (G ⊔ attachmentStar u A) := mem_triangles.mpr ⟨hTc,hTcl⟩
      rw [triangles_after_attachment h hu hA hAS hcA] at ht
      refine (mem_union.mp ht).resolve_left ?_
      intro htold
      exact hu (h.clique_subset_active (by omega) (mem_triangles.mp htold).2 huT)
    · have hcOld : G.IsClique T := clique_before_attachment huT hTcl
      have hTA : T ≠ A := by
        rintro rfl
        rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,
          hbA,if_pos (subset_insert _ _)] at hTm
        omega
      have hnot : ¬ T ⊆ insert u A := fun hh => hTA
        ((old_triangle_subset_attach_iff h hu hA hTc hcOld).mp hh)
      rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,if_neg hnot,Nat.add_zero] at hTm
      exact mem_union_left _ (mem_erase.mpr ⟨hTA,mem_boundaryTriangles.mpr ⟨hTc,hcOld,hTm⟩⟩)
  · intro hT
    rcases mem_union.mp hT with hT | hT
    · obtain ⟨hTA,hT⟩ := mem_erase.mp hT
      obtain ⟨hTc,hTcl,hTm⟩ := mem_boundaryTriangles.mp hT
      have hnot : ¬ T ⊆ insert u A := fun hh => hTA
        ((old_triangle_subset_attach_iff h hu hA hTc hTcl).mp hh)
      apply mem_boundaryTriangles.mpr
      refine ⟨hTc,fun a ha b hb hab => Or.inl (hTcl ha hb hab),?_⟩
      rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,if_neg hnot,Nat.add_zero,hTm]
    · obtain ⟨E,hE,rfl⟩ := mem_image.mp hT
      obtain ⟨hEA,hEc⟩ := mem_powersetCard.mp hE
      have huE : u ∉ E := fun hh => hu (hAS (hEA hh))
      have htri : insert u E ∈ triangles (G ⊔ attachmentStar u A) := by
        rw [triangles_after_attachment h hu hA hAS hcA]
        exact mem_union_right _ (mem_image.mpr ⟨E,mem_powersetCard.mpr ⟨hEA,hEc⟩,rfl⟩)
      apply mem_boundaryTriangles.mpr
      refine ⟨(mem_triangles.mp htri).1,(mem_triangles.mp htri).2,?_⟩
      rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,
        h.triangleMultiplicity_eq_zero_of_outside hu (mem_insert_self _ _),
        if_pos (insert_subset_insert u hEA)]

private theorem thin_after_boundary_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u ∉ S) {A : Finset V}
    (hA : A.card = 3) (hAS : A ⊆ S) (hcA : G.IsClique A)
    (hbA : triangleMultiplicity G A = 1)
    (hthin : ∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) :
    ∀ T : Finset V,T.card = 3 → (G ⊔ attachmentStar u A).IsClique T →
      triangleMultiplicity (G ⊔ attachmentStar u A) T ≤ 2 := by
  intro T hT hcT
  rw [triangleMultiplicity_after_attachment h hu hA hAS hcA]
  by_cases huT : u ∈ T
  · rw [h.triangleMultiplicity_eq_zero_of_outside hu huT]
    split_ifs <;> omega
  · have hcOld : G.IsClique T := clique_before_attachment huT hcT
    by_cases hTA : T = A
    · subst T
      rw [hbA]
      split_ifs <;> omega
    · have hnot : ¬ T ⊆ insert u A := fun hh => hTA
        ((old_triangle_subset_attach_iff h hu hA hT hcOld).mp hh)
      rw [if_neg hnot,Nat.add_zero]
      exact hthin T hT hcOld

/-- The ordinary combinatorial definition of a stacked boundary
triangulation, including its explicit evolving triangular face set. -/
inductive StackedTriangulationOn : Finset V → SimpleGraph V → Finset (Finset V) → Prop
  | tetrahedron (C : Finset V) (hC : C.card = 4) :
      StackedTriangulationOn C (cliqueGraph C) (C.powersetCard 3)
  | stack {S : Finset V} {G : SimpleGraph V} {F : Finset (Finset V)}
      (h : StackedTriangulationOn S G F) (u : V) (hu : u ∉ S)
      (T : Finset V) (hT : T.card = 3) (hTS : T ⊆ S) (hcT : G.IsClique T)
      (hface : T ∈ F) :
      StackedTriangulationOn (insert u S) (G ⊔ attachmentStar u T)
        (F.erase T ∪ (T.powersetCard 2).image (insert u))

theorem StackedTriangulationOn.properties {S : Finset V} {G : SimpleGraph V}
    {F : Finset (Finset V)} (h : StackedTriangulationOn S G F) :
    ThreeTreeOn S G ∧
      (∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) ∧
      F = boundaryTriangles G := by
  induction h with
  | tetrahedron C hC =>
    refine ⟨ThreeTreeOn.tetrahedron C hC,?_,(boundaryTriangles_cliqueGraph hC).symm⟩
    intro T hT hcT
    rw [triangleMultiplicity_cliqueGraph_of_subset hC
      ((ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT)]
    omega
  | @stack S G F h u hu T hT hTS hcT hface ih =>
    obtain ⟨ht,hthin,hF⟩ := ih
    have hb : triangleMultiplicity G T = 1 :=
      (mem_boundaryTriangles.mp (hF ▸ hface)).2.2
    refine ⟨ThreeTreeOn.attach ht u hu T hT hTS hcT,
      thin_after_boundary_attachment ht hu hT hTS hcT hb hthin,?_⟩
    rw [hF,boundaryTriangles_after_attachment ht hu hT hTS hcT hb]

theorem ThreeTreeOn.stacked {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G) :
    (∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) →
      StackedTriangulationOn S G (boundaryTriangles G) := by
  induction h with
  | tetrahedron C hC =>
    intro _
    rw [boundaryTriangles_cliqueGraph hC]
    exact StackedTriangulationOn.tetrahedron C hC
  | @attach S G h u hu T hT hTS hcT ih =>
    intro hthin
    have hOld : ∀ A : Finset V,A.card = 3 → G.IsClique A → triangleMultiplicity G A ≤ 2 := by
      intro A hA hcA
      exact (triangleMultiplicity_mono (show G ≤ G ⊔ attachmentStar u T from le_sup_left) A).trans
        (hthin A hA (fun a ha b hb hab => Or.inl (hcA ha hb hab)))
    have hb : triangleMultiplicity G T = 1 := by
      obtain ⟨C,hC,hTC⟩ := h.triangle_extends hT hcT
      have hpos : 0 < triangleMultiplicity G T :=
        card_pos.mpr ⟨C,mem_filter.mpr ⟨hC,hTC⟩⟩
      have hnew := hthin T hT (fun a ha b hb hab => Or.inl (hcT ha hb hab))
      rw [triangleMultiplicity_after_attachment h hu hT hTS hcT,
        if_pos (subset_insert _ _)] at hnew
      omega
    rw [boundaryTriangles_after_attachment h hu hT hTS hcT hb]
    exact StackedTriangulationOn.stack (ih hOld) u hu T hT hTS hcT
      (mem_boundaryTriangles.mpr ⟨hT,hcT,hb⟩)

def IsStackedTriangulation (G : SimpleGraph V) : Prop :=
  ∃ F : Finset (Finset V),StackedTriangulationOn univ G F

/-- Equivalence with the usual three-tree formulation, with the exact
boundary face set recovered as a theorem. -/
theorem isStackedTriangulation_iff {G : SimpleGraph V} :
    IsStackedTriangulation G ↔ IsThreeTree G ∧
      (∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) := by
  constructor
  · rintro ⟨F,hF⟩
    exact ⟨hF.properties.1,hF.properties.2.1⟩
  · rintro ⟨ht,hthin⟩
    exact ⟨boundaryTriangles G,ht.stacked hthin⟩

end GraphicalZonotopes
