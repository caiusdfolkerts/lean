module

public import consolidated_dev.conditional_complete_integration
public import supplementary.two_homotheties

@[expose] public section

/-!
# The given-facet and boundary-cover statements of the paper

The first interface states Lemma 3 for the specified facet. The remaining
interfaces state both cases of Lemma 13 from the actual original graph
configuration, derive its vertex budget, and compose the previously proved
geometric alternatives. These Lemma 3 and 13 proofs do not invoke the main
sharp-bound theorem. The final corollary applies the established lower bound
after deriving its dimension premise from actual decomposability.
-/

noncomputable section

namespace Papers.PaperInterfaces

open Set Finset
open Papers.Polytopes Papers.ActualFaceOrder
open Papers.PolytopeFourRegularTail
open Papers.Polytopes.HomothetyParameters Papers.ProperImagePersistence
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {d : ℕ}

/-- Lemma 3: the original facet itself has unique exterior neighbors.
Rigidity is intrinsic to the induced graph on its complementary vertices. -/
theorem shephard_property_of_given_rigid_complement
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (hdecomp : MinkowskiDecomposable P)
    (F : Set (E d)) (hF : IsFacet P F)
    (hrigid : ParallelRigid P ((P.vertices : Set (E d)) \ F)) :
    ∀ x ∈ P.vertices, x ∈ F →
      ∃! y : E d, GeneralVertexStep P x y ∧ y ∉ F := by
  obtain ⟨f, hf, hnon⟩ := (minkowski_decomposable_iff_parallel_map P).mp hdecomp
  apply facet_shephard_of_parallel_complement P hP f hf hnon hF
  exact hrigid f (fun x hx y hy hxy => hf x hx.1 y hy.1 hxy)

/-- The paper's seven-vertex configuration: two actual triangles meeting
at one vertex, and an actual edge disjoint from both triangles. Extra
edges between these vertices are allowed, as in the paper. -/
structure SigmaConfiguration (P : ConvexPolytope d) where
  center : E d
  left : Finset (E d)
  right : Finset (E d)
  edge : Finset (E d)
  within : left ∪ right ∪ edge ⊆ P.vertices
  left_triangle : (ambientActualGraph P).IsNClique 3 left
  right_triangle : (ambientActualGraph P).IsNClique 3 right
  edge_pair : (ambientActualGraph P).IsNClique 2 edge
  intersection : left ∩ right = {center}
  disjoint : Disjoint (left ∪ right) edge

namespace SigmaConfiguration

variable {P : ConvexPolytope d}

def vertices (S : SigmaConfiguration P) : Finset (E d) :=
  S.left ∪ S.right ∪ S.edge

theorem vertices_card (S : SigmaConfiguration P) : S.vertices.card = 7 := by
  have hcount := Finset.card_union_add_card_inter S.left S.right
  rw [S.intersection, Finset.card_singleton,
    S.left_triangle.card_eq, S.right_triangle.card_eq] at hcount
  have hunion : (S.left ∪ S.right).card = 5 := by omega
  rw [vertices, Finset.card_union_of_disjoint S.disjoint,
    hunion, S.edge_pair.card_eq]

/-- The actual triangle and edge incidences supply the rigidity fields
of the boundary configuration used by the geometric proof. -/
def toTail (S : SigmaConfiguration P) : SigmaTail P S.vertices := by
  have hleft : S.left ⊆ S.vertices := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hx)))
  have hright : S.right ⊆ S.vertices := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hx)))
  have hedge : S.edge ⊆ S.vertices := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inr hx)
  have triangle (A : Finset (E d)) (hA : A ⊆ S.vertices)
      (hclique : (ambientActualGraph P).IsNClique 3 A) :
      RigidInTail P S.vertices A := by
    obtain ⟨a, b, c, hab, hac, hbc, heq⟩ := SimpleGraph.is3Clique_iff.mp hclique
    have ha : a ∈ S.vertices := hA (by rw [heq]; simp)
    have hb : b ∈ S.vertices := hA (by rw [heq]; simp)
    have hc : c ∈ S.vertices := hA (by rw [heq]; simp)
    rw [heq]
    exact rigid_triangle S.within ha hb hc hab.2 hac.2 hbc.2
  have edgeRigid : RigidInTail P S.vertices S.edge := by
    obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp S.edge_pair.card_eq
    have hstep : (ambientActualGraph P).Adj a b := by
      have hclique := S.edge_pair.isClique
      rw [heq] at hclique
      exact SimpleGraph.isClique_pair.mp
        (by simpa only [Finset.coe_insert, Finset.coe_singleton] using hclique) hab
    have ha : a ∈ S.vertices := hedge (by rw [heq]; simp)
    have hb : b ∈ S.vertices := hedge (by rw [heq]; simp)
    rw [heq]
    exact rigid_pair ha hb hstep.2
  exact {
    center := S.center
    left := S.left
    right := S.right
    edge := S.edge
    left_subset := hleft
    right_subset := hright
    edge_subset := hedge
    left_card := S.left_triangle.card_eq
    right_card := S.right_triangle.card_eq
    edge_card := S.edge_pair.card_eq
    intersection := S.intersection
    disjoint := S.disjoint
    union := rfl
    left_rigid := triangle S.left hleft S.left_triangle
    right_rigid := triangle S.right hright S.right_triangle
    edge_rigid := edgeRigid }

end SigmaConfiguration

/-- The boundary route is composed with all three already proved
persistence branches, without appealing to the main theorem. -/
theorem boundary_pieces_persist
    {I : Type*} [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f)
    (hnon : ¬ IsHomothetyOnVertices P f)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (c e j : I) (z : E d) (R : GlobalRigidBoundaryPieces P I c e j z)
    (hcolors : Fintype.card I = d) (hdlo : 4 ≤ d) (hdhi : d ≤ 5)
    (Q : ConvexPolytope d) (φ : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hQ : Q.IsFullDim := (Papers.ActualFaceOrder.dim_eq φ).trans hP
  rcases global_boundary_cover_routes P hP f hf hnon hN c e j z R
      hcolors hdlo hdhi with hsmall | hS | himage
  · exact decomposable_after_iso_of_small_essential_cover
      P hP (by omega) f hf hsmall hN Q hQ φ
  · exact decomposable_after_iso_of_shephard_property
      P hP f hf hnon hS Q hQ φ
  · obtain ⟨P', hP', ⟨ρ⟩, hcard, g, hg, hgnon, hrank⟩ := himage
    exact proper_image_persists P' hP' (by omega) g hg hgnon (Or.inl hrank)
      (by rw [hcard]; exact hN) Q hQ (ρ.symm.trans φ)

/-- Lemma 13 in dimension four, from the original rigid four-set and
actual seven-vertex configuration. The eleven-vertex bound is derived. -/
theorem decomposable_after_iso_of_boundary_cover_four
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (f : E 4 → E 4) (hf : IsParallelMap P f)
    (hnon : ¬ IsHomothetyOnVertices P f)
    (A : Finset (E 4)) (hAV : A ⊆ P.vertices) (hAc : A.card = 4)
    (hArigid : ParallelRigid P (A : Set (E 4)))
    (S : SigmaConfiguration P) (hcover : A ∪ S.vertices = P.vertices)
    (Q : ConvexPolytope 4) (hPQ : CombinatoriallyEquivalent P Q) :
    MinkowskiDecomposable Q := by
  have hN : P.vertices.card ≤ 4 * 4 - 5 := by
    have hcount := Finset.card_union_le A S.vertices
    rw [hcover, hAc, S.vertices_card] at hcount
    omega
  let pieces : Fin 1 → Finset (E 4) := fun _ => A
  obtain ⟨R⟩ := S.toTail.to_global_boundary S.within 1 pieces
    (fun _ => hAV) (fun _ => hAc.le)
    (fun _ => rigid_of_parallelRigid hAV hArigid) (by
      intro x hx
      have hxcover : x ∈ A ∪ S.vertices := by rw [hcover]; exact hx
      rcases Finset.mem_union.mp hxcover with hxA | hxS
      · exact Or.inl ⟨0, hxA⟩
      · exact Or.inr hxS)
  obtain ⟨φ⟩ := hPQ
  exact boundary_pieces_persist P hP f hf hnon hN
    (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) S.center R
    (by simp) (by omega) (by omega) Q φ

/-- Lemma 13 in dimension five, from the original disjoint rigid
four-sets and actual seven-vertex configuration. The fifteen-vertex
bound is derived from that cover, not assumed. -/
theorem decomposable_after_iso_of_boundary_cover_five
    (P : ConvexPolytope 5) (hP : P.IsFullDim)
    (f : E 5 → E 5) (hf : IsParallelMap P f)
    (hnon : ¬ IsHomothetyOnVertices P f)
    (A B : Finset (E 5)) (hAV : A ⊆ P.vertices) (hBV : B ⊆ P.vertices)
    (hAc : A.card = 4) (hBc : B.card = 4) (hAB : Disjoint A B)
    (hArigid : ParallelRigid P (A : Set (E 5)))
    (hBrigid : ParallelRigid P (B : Set (E 5)))
    (S : SigmaConfiguration P) (hcover : (A ∪ B) ∪ S.vertices = P.vertices)
    (Q : ConvexPolytope 5) (hPQ : CombinatoriallyEquivalent P Q) :
    MinkowskiDecomposable Q := by
  have hABcard : (A ∪ B).card = 8 := by
    rw [Finset.card_union_of_disjoint hAB, hAc, hBc]
  have hN : P.vertices.card ≤ 4 * 5 - 5 := by
    have hcount := Finset.card_union_le (A ∪ B) S.vertices
    rw [hcover, hABcard, S.vertices_card] at hcount
    omega
  let pieces : Fin 2 → Finset (E 5) := ![A, B]
  have hwithin (i : Fin 2) : pieces i ⊆ P.vertices := by
    fin_cases i
    · exact hAV
    · exact hBV
  have hcard (i : Fin 2) : (pieces i).card ≤ 4 := by
    fin_cases i
    · exact hAc.le
    · exact hBc.le
  have hrigid (i : Fin 2) : RigidInTail P P.vertices (pieces i) := by
    fin_cases i
    · exact rigid_of_parallelRigid hAV hArigid
    · exact rigid_of_parallelRigid hBV hBrigid
  obtain ⟨R⟩ := S.toTail.to_global_boundary S.within 2 pieces hwithin hcard hrigid (by
    intro x hx
    have hxcover : x ∈ (A ∪ B) ∪ S.vertices := by rw [hcover]; exact hx
    rcases Finset.mem_union.mp hxcover with hxAB | hxS
    · rcases Finset.mem_union.mp hxAB with hxA | hxB
      · exact Or.inl ⟨0, hxA⟩
      · exact Or.inl ⟨1, hxB⟩
    · exact Or.inr hxS)
  obtain ⟨φ⟩ := hPQ
  exact boundary_pieces_persist P hP f hf hnon hN
    (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) S.center R
    (by simp) (by omega) (by omega) Q φ

/-- The assertion following Theorem 1, with no separate dimension premise.
Actual decomposability and the vertex budget exclude dimensions below three;
the established below-threshold theorem then applies. Unlike the preceding
Lemma 3 and 13 interfaces, this corollary uses the main lower-bound result. -/
theorem decomposability_determined_by_face_lattice_below_threshold_all_dimensions
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (hN : P.vertices.card ≤ 4 * d - 5) (hdecomp : MinkowskiDecomposable P)
    (Q : ConvexPolytope d) (hPQ : CombinatoriallyEquivalent P Q) :
    MinkowskiDecomposable Q := by
  obtain ⟨f, hf, hnon⟩ := (minkowski_decomposable_iff_parallel_map P).mp hdecomp
  have hd := three_le_dimension_of_small_nonhomothetic_parallel_map
    P hP f hf hnon hN
  exact decomposability_determined_by_face_lattice_below_threshold
    P hP hd hN hdecomp Q hPQ

end Papers.PaperInterfaces

end
