import bier.corner_base
import bier.stellar_combinatorics

/-! Translating the exact stellar face formula into actual corner facets. -/
noncomputable section
namespace Bier
open Classical Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

namespace PolytopeRealization
variable {L : Complex V} (r : PolytopeRealization L n)

def label : VertexType r.polytope ↪ V :=
  r.vertexEquiv.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem label_vertexEquiv (v : L.vertices) : r.label (r.vertexEquiv v) = v.val := by
  simp [label]

theorem label_mem (w : VertexType r.polytope) : r.label w ∈ L.vertices :=
  (r.vertexEquiv.symm w).property

def labelledVertices (F : Finset V) : Finset (VertexType r.polytope) :=
  Finset.univ.filter (fun w => r.label w ∈ F)

@[simp] theorem mem_labelledVertices (F : Finset V) (w : VertexType r.polytope) :
    w ∈ r.labelledVertices F ↔ r.label w ∈ F := by simp [labelledVertices]

theorem labelledVertices_image (F : Finset V) (hF : F ⊆ L.vertices) :
    (r.labelledVertices F).image r.label = F := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (r.mem_labelledVertices F w).mp hw
  · intro hv
    exact Finset.mem_image.mpr ⟨r.vertexEquiv ⟨v, hF hv⟩,
      (r.mem_labelledVertices F _).mpr (by simpa), by simp⟩

theorem face_labels_iff (s : Finset (VertexType r.polytope)) :
    L.face (s.image r.label) ↔ s = ∅ ∨ ProperVertexFace r.polytope s := by
  let a := s.map r.vertexEquiv.symm.toEmbedding
  have himage : a.image Subtype.val = s.image r.label := by
    simp only [a, Finset.map_eq_image, Finset.image_image]
    rfl
  have hmap : a.map r.vertexEquiv.toEmbedding = s := by ext v; simp [a]
  rw [← himage, r.faces, hmap]
  have hzero : a = ∅ ↔ s = ∅ := by simp [a]
  rw [hzero]
  constructor
  · rintro (hz | ⟨t, ht, hst⟩)
    · exact Or.inl hz
    · by_cases hz : s = ∅
      · exact Or.inl hz
      right
      have hs := Finset.nonempty_iff_ne_empty.mpr hz
      refine ⟨boundary_subsimplex_isFace r.polytope r.simplicial ht hst hs, ?_⟩
      intro heq
      have hd := boundary_subsimplex_dimension r.polytope r.simplicial ht hst hs
      rw [heq] at hd
      have hc := (Finset.card_le_card hst).trans_eq
        (boundaryFacets_pure r.polytope r.simplicial t ht)
      change r.polytope.dim + 1 = s.card at hd
      omega
  · rintro (hz | hface)
    · exact Or.inl hz
    · exact Or.inr (properVertexFace_boundary r.polytope hface)

end PolytopeRealization

namespace StellarFacetData
variable {K L : Complex V} {F : Finset V} {v : V}
    (h : StellarFacetData K L F v) (r : PolytopeRealization L n)

include h

def apex : VertexType r.polytope := r.vertexEquiv ⟨v, h.new_vertex_mem⟩
def neighbors (_h : StellarFacetData K L F v) (r : PolytopeRealization L n) :
    Finset (VertexType r.polytope) := r.labelledVertices F

@[simp] theorem label_apex : r.label (h.apex r) = v := by simp [apex]

theorem facet_vertices : F ⊆ L.vertices := by
  intro w hw
  apply h.old_vertex_mem
  rw [Complex.mem_vertices]
  exact K.downward (Finset.singleton_subset_iff.mpr hw) h.oldFace

@[simp] theorem neighbors_image : (h.neighbors r).image r.label = F :=
  r.labelledVertices_image F h.facet_vertices

theorem neighbors_card : (h.neighbors r).card = F.card := by
  simpa only [Finset.card_image_of_injective _ r.label.injective] using
    congrArg Finset.card (h.neighbors_image r)

theorem apex_not_mem : h.apex r ∉ h.neighbors r := by
  change h.apex r ∉ r.labelledVertices F
  rw [r.mem_labelledVertices, h.label_apex]
  exact h.not_mem_facet

theorem corner_labels (i : VertexType r.polytope) :
    (insert (h.apex r) ((h.neighbors r).erase i)).image r.label =
      insert v (F.erase (r.label i)) := by
  rw [Finset.image_insert, Finset.image_erase r.label.injective, h.neighbors_image, h.label_apex]

theorem corner_proper (i : VertexType r.polytope) (hi : i ∈ h.neighbors r) :
    ProperVertexFace r.polytope (insert (h.apex r) ((h.neighbors r).erase i)) := by
  have hh := h.corner_face ((r.mem_labelledVertices F i).mp hi)
  rw [← h.corner_labels r i, r.face_labels_iff] at hh
  exact hh.resolve_left (Finset.insert_ne_empty _ _)

theorem polytope_dimension : r.polytope.dim = (h.neighbors r).card := by
  have hne : (h.neighbors r).Nonempty := by
    apply Finset.card_pos.mp
    rw [h.neighbors_card]
    exact lt_of_lt_of_le (by decide : 0 < 2) h.card_two
  obtain ⟨i, hi⟩ := hne
  have hcp := h.corner_proper r i hi
  have hcard : (insert (h.apex r) ((h.neighbors r).erase i)).card = (h.neighbors r).card := by
    rw [Finset.card_insert_of_notMem (fun hh => h.apex_not_mem r (Finset.mem_of_mem_erase hh)),
      Finset.card_erase_of_mem hi]
    have hh := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hlo := properVertexFace_card_le r.polytope r.simplicial hcp
  rw [hcard] at hlo
  have hup : r.polytope.dim ≤ F.card := by
    obtain ⟨t, ht, _⟩ := properVertexFace_boundary r.polytope hcp
    have htf : L.face (t.image r.label) := (r.face_labels_iff t).mpr
      (Or.inr (by
        have htne : t.Nonempty := by
          have hc := boundaryFacets_pure r.polytope r.simplicial t ht
          change t.card = r.polytope.dim at hc
          rw [← hc] at hlo
          exact Finset.card_pos.mp (lt_of_lt_of_le (Finset.card_pos.mpr ⟨i, hi⟩) hlo)
        refine ⟨boundary_subsimplex_isFace r.polytope r.simplicial ht (Finset.Subset.refl _) htne, ?_⟩
        obtain ⟨G, rfl⟩ := (mem_boundaryFacets r.polytope t).mp ht
        rw [vertexHull_faceVertices r.polytope G.val.property]
        exact (facet_proper r.polytope G).ne))
    have hh := h.face_card_le htf
    rw [Finset.card_image_of_injective _ r.label.injective] at hh
    have hc := boundaryFacets_pure r.polytope r.simplicial t ht
    change t.card = r.polytope.dim at hc
    exact hc ▸ hh
  rw [← h.neighbors_card r] at hup
  exact le_antisymm hup hlo

def cornerSystem : CornerSystem r.polytope (h.apex r) (h.neighbors r) :=
  Classical.choice (exists_cornerSystem r.polytope (h.apex r) (h.neighbors r)
    (h.apex_not_mem r) (h.polytope_dimension r) (fun i hi => (h.corner_proper r i hi).1))

theorem containing_apex (a : Finset (VertexType r.polytope))
    (ha : ProperVertexFace r.polytope a) (hp : h.apex r ∈ a) :
    a ⊆ insert (h.apex r) (h.neighbors r) := by
  have hLa := (r.face_labels_iff a).mpr (Or.inr ha)
  have hv : v ∈ a.image r.label := by
    rw [← h.label_apex r]
    exact Finset.mem_image_of_mem _ hp
  have hc := ((h.faces _).mp hLa).2.resolve_left (fun hk => h.not_mem_old_face hk hv)
  intro w hw
  have hl := hc (Finset.mem_image_of_mem r.label hw)
  rcases Finset.mem_insert.mp hl with he | ht
  · exact Finset.mem_insert.mpr (Or.inl (r.label.injective (he.trans (h.label_apex r).symm)))
  · exact Finset.mem_insert_of_mem ((r.mem_labelledVertices F w).mpr ht)

end StellarFacetData
end Bier
