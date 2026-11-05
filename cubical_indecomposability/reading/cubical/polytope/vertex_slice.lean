import cubical.polytope.generic_height
import cubical.polytope.figura_al_vertice

/-!
# Concrete vertex figures and descending links

The geometric vertex figure is a separating hyperplane slice of the
polytope. Its vertices correspond to the actual neighbors of the cut-off
vertex. Their coordinates lie on the corresponding edges with positive
interpolation parameter, so the sign of every other linear height is
preserved relative to the cut-off vertex.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n}

/-- Neighbors of one actual polytope vertex. -/
abbrev NeighborOf (v : VertexType P) :=
  {w : VertexType P // (polytopeGraph P).Adj v w}

/-- Adjacency in a descending vertex link, expressed by geometric two-faces. -/
def LowerTwoFaceRelation (v : VertexType P) (l : E n →L[ℝ] ℝ)
    (a b : NeighborOf v) : Prop :=
  l a.val.val < l v.val ∧ l b.val.val < l v.val ∧ a ≠ b ∧
    ∃ F : Set (E n), P.IsFace F ∧ faceDim F = 2 ∧
      v.val ∈ F ∧ a.val.val ∈ F ∧ b.val.val ∈ F

namespace DatiFetta

variable {v : E n} (D : DatiFetta P v)

theorem attra_mem_face {F : Set (E n)} (hF : P.IsFace F) (hvF : v ∈ F)
    {w : E n} (hw : w ∈ P.vertices) (hwF : w ∈ F) (hwv : w ≠ v) :
    D.attra w ∈ F :=
  (hF.1.convex (convex_convexHull ℝ _)).segment_subset hvF hwF
    (D.attra_mem_segment (D.hsep w hw hwv))

theorem edge_slice_data {F : Set (E n)} (hF : P.IsFace F) (hdF : faceDim F = 1)
    (hvF : v ∈ F) {w : E n} (hw : w ∈ P.vertices) (hwF : w ∈ F) (hwv : w ≠ v) :
    F ∩ {x | D.l x = D.c} = {D.attra w} ∧
      D.attra w ∈ D.politopo.vertices := by
  have hslice := D.faccia_fetta hF hvF (by omega)
  have hdim : faceDim (F ∩ {x | D.l x = D.c}) = 0 := by
    have hh := D.fetta_faceDim hF hvF (by omega)
    omega
  obtain ⟨q, hqset, hqvert⟩ := punto_di_faccia0_e_vertice D.politopo hslice hdim
  have hmem : D.attra w ∈ F ∩ {x | D.l x = D.c} :=
    ⟨D.attra_mem_face hF hvF hw hwF hwv, D.attra_level (D.hsep w hw hwv)⟩
  rw [hqset] at hmem
  have heq : D.attra w = q := Set.mem_singleton_iff.mp hmem
  exact ⟨hqset.trans (congrArg (fun z => ({z} : Set (E n))) heq.symm), heq.symm ▸ hqvert⟩

theorem attra_height_sub (l : E n →L[ℝ] ℝ) (w : E n) :
    l (D.attra w) - l v =
      ((D.l v - D.c) / (D.l v - D.l w)) * (l w - l v) := by
  rw [← map_sub, D.attra_sub, map_smul, map_sub]
  rfl

theorem attra_lt_base_iff (l : E n →L[ℝ] ℝ)
    {w : E n} (hw : w ∈ P.vertices) (hwv : w ≠ v) :
    l (D.attra w) < l v ↔ l w < l v := by
  have ht := D.tau_pos (D.hsep w hw hwv)
  have heq := D.attra_height_sub l w
  constructor <;> intro h <;> nlinarith

end DatiFetta

namespace DatiFetta

variable {v : VertexType P} (D : DatiFetta P v.val)

theorem neighbor_ne_base (a : NeighborOf v) : a.val.val ≠ v.val := by
  intro h
  exact a.property.1 (Subtype.ext h.symm)

noncomputable def neighborToFigureVertex (a : NeighborOf v) : VertexType D.politopo := by
  refine ⟨D.attra a.val.val, ?_⟩
  obtain ⟨F, hF, hdF, hvF, haF⟩ := a.property.2
  exact (D.edge_slice_data hF hdF hvF a.val.property haF (neighbor_ne_base a)).2

@[simp] theorem neighborToFigureVertex_val (a : NeighborOf v) :
    (D.neighborToFigureVertex a).val = D.attra a.val.val := rfl

theorem neighborToFigureVertex_injective : Function.Injective D.neighborToFigureVertex := by
  intro a b hab
  have hab' : D.attra a.val.val = D.attra b.val.val := congrArg Subtype.val hab
  obtain ⟨F, hF, hdF, hvF, haF⟩ := a.property.2
  obtain ⟨G, hG, hdG, hvG, hbG⟩ := b.property.2
  have hFs := (D.edge_slice_data hF hdF hvF a.val.property haF (neighbor_ne_base a)).1
  have hGs := (D.edge_slice_data hG hdG hvG b.val.property hbG (neighbor_ne_base b)).1
  have hGF : G ⊆ F := D.fetta_mono hG hvG hF hvF (by rw [hGs, hFs, hab'])
  have hseg := edge_eq_segment P hF hdF v.property a.val.property hvF haF
    (neighbor_ne_base a).symm
  have hbend := vertice_in_segmento_estremo_generico P hF hseg b.val.property (hGF hbG)
  apply Subtype.ext
  apply Subtype.ext
  rcases hbend with hb | hb
  · exact (neighbor_ne_base b hb).elim
  · exact hb.symm

theorem neighborToFigureVertex_surjective : Function.Surjective D.neighborToFigureVertex := by
  intro q
  have hqF := vertex_isFace D.politopo q.property
  obtain ⟨F, hF, hvF, hdpos, hslice⟩ := D.faccia_dalla_fetta hqF
  have hdF : faceDim F = 1 := by
    have hh := D.fetta_faceDim hF hvF hdpos
    rw [hslice, faceDim_singleton] at hh
    omega
  obtain ⟨w, hw, hwF, hwv, _hseg⟩ := spigolo_segmento P hF hdF v.property hvF
  let a : NeighborOf v := ⟨⟨w, hw⟩, ⟨by
    intro h
    exact hwv (congrArg Subtype.val h).symm,
    F, hF, hdF, hvF, hwF⟩⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  have hh := (D.edge_slice_data hF hdF hvF hw hwF hwv).1
  rw [hslice] at hh
  exact (Set.singleton_injective hh).symm

/-- Actual neighbors correspond bijectively to the extreme points of the slice. -/
noncomputable def neighborEquiv : NeighborOf v ≃ VertexType D.politopo :=
  Equiv.ofBijective D.neighborToFigureVertex
    ⟨D.neighborToFigureVertex_injective, D.neighborToFigureVertex_surjective⟩

@[simp] theorem neighborEquiv_val (a : NeighborOf v) :
    (D.neighborEquiv a).val = D.attra a.val.val := rfl

theorem neighborEquiv_lt_base_iff (l : E n →L[ℝ] ℝ) (a : NeighborOf v) :
    l (D.neighborEquiv a).val < l v.val ↔ l a.val.val < l v.val :=
  D.attra_lt_base_iff l a.val.property (neighbor_ne_base a)

/-- An edge in the vertex figure is exactly a two-face through the base vertex. -/
theorem neighborEquiv_adj_iff (a b : NeighborOf v) :
    (polytopeGraph D.politopo).Adj (D.neighborEquiv a) (D.neighborEquiv b) ↔
      a ≠ b ∧ ∃ F : Set (E n), P.IsFace F ∧ faceDim F = 2 ∧
        v.val ∈ F ∧ a.val.val ∈ F ∧ b.val.val ∈ F := by
  constructor
  · rintro ⟨hne, G, hG, hdG, haG, hbG⟩
    have hab : a ≠ b := fun h => hne (congrArg D.neighborEquiv h)
    obtain ⟨F, hF, hvF, hdpos, hslice⟩ := D.faccia_dalla_fetta hG
    have hdF : faceDim F = 2 := by
      have hh := D.fetta_faceDim hF hvF hdpos
      rw [hslice, hdG] at hh
      omega
    have neighbor_mem : ∀ c : NeighborOf v,
        (D.neighborEquiv c).val ∈ G → c.val.val ∈ F := by
      intro c hcG
      obtain ⟨e, he, hde, hve, hce⟩ := c.property.2
      have hes := (D.edge_slice_data he hde hve c.val.property hce (neighbor_ne_base c)).1
      have heF : e ⊆ F := D.fetta_mono he hve hF hvF (by
        rw [hes, hslice]
        exact Set.singleton_subset_iff.mpr hcG)
      exact heF hce
    exact ⟨hab, F, hF, hdF, hvF, neighbor_mem a haG, neighbor_mem b hbG⟩
  · rintro ⟨hne, F, hF, hdF, hvF, haF, hbF⟩
    have hslice := D.faccia_fetta hF hvF (by omega)
    have hdim : faceDim (F ∩ {x | D.l x = D.c}) = 1 := by
      have hh := D.fetta_faceDim hF hvF (by omega)
      omega
    refine ⟨fun h => hne (D.neighborEquiv.injective h), _, hslice, hdim, ?_, ?_⟩
    · exact ⟨D.attra_mem_face hF hvF a.val.property haF (neighbor_ne_base a),
        D.attra_level (D.hsep _ a.val.property (neighbor_ne_base a))⟩
    · exact ⟨D.attra_mem_face hF hvF b.val.property hbF (neighbor_ne_base b),
        D.attra_level (D.hsep _ b.val.property (neighbor_ne_base b))⟩

/-- The descending link of a geometric polytope vertex is connected. -/
theorem lowerNeighbors_connected (l : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn l (D.politopo.vertices : Set (E n)))
    (a b : NeighborOf v) (ha : l a.val.val < l v.val) (hb : l b.val.val < l v.val) :
    Relation.ReflTransGen (LowerTwoFaceRelation v l) a b := by
  classical
  let f (q : E n) : NeighborOf v :=
    if hq : q ∈ D.politopo.vertices then D.neighborEquiv.symm ⟨q, hq⟩ else a
  have f_on (q : E n) (hq : q ∈ D.politopo.vertices) :
      D.neighborEquiv (f q) = ⟨q, hq⟩ := by
    simp only [f, dite_eq_left hq, Equiv.apply_symm_apply]
  have f_apply (a' : NeighborOf v) : f (D.neighborEquiv a').val = a' := by
    apply D.neighborEquiv.injective
    exact f_on _ (D.neighborEquiv a').property
  have hpath := sublevel_connected D.politopo l (l v.val) hinj
    (D.neighborEquiv a).property (D.neighborEquiv b).property
    ((D.neighborEquiv_lt_base_iff l a).mpr ha)
    ((D.neighborEquiv_lt_base_iff l b).mpr hb)
  have hmap : ∀ p q, SublevelStep D.politopo l (l v.val) p q →
      LowerTwoFaceRelation v l (f p) (f q) := by
    rintro p q ⟨hp, ⟨hq, hpq, G, hG, hdG, hpG, hqG⟩, hlp, hlq⟩
    have hAdj : (polytopeGraph D.politopo).Adj
        (D.neighborEquiv (f p)) (D.neighborEquiv (f q)) := by
      rw [f_on p hp, f_on q hq]
      exact ⟨fun h => hpq (congrArg Subtype.val h), G, hG, hdG, hpG, hqG⟩
    have hpl : l (f p).val.val < l v.val :=
      (D.neighborEquiv_lt_base_iff l (f p)).mp (by rw [f_on p hp]; exact hlp)
    have hql : l (f q).val.val < l v.val :=
      (D.neighborEquiv_lt_base_iff l (f q)).mp (by rw [f_on q hq]; exact hlq)
    exact ⟨hpl, hql, (D.neighborEquiv_adj_iff (f p) (f q)).mp hAdj⟩
  have hlift := Relation.ReflTransGen.lift f hmap _ _ hpath
  change Relation.ReflTransGen (LowerTwoFaceRelation v l)
    (f (D.neighborEquiv a).val) (f (D.neighborEquiv b).val) at hlift
  simpa only [f_apply] using hlift

end DatiFetta

end LeanEval.Geometry.PlatonicClassification
