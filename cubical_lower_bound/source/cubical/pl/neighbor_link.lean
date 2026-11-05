import cubical.pl.vertex_link
import cubical.pl_relabel

/-!
# Original simplicial vertex links of cubical PL spheres

At a cubical vertex the incident edge labels form a simplicial complex:
the neighbors in each incident cube span one simplex.  Its face poset
is the strict upper interval of the vertex cell.  The proof below
identifies its barycentric realization with the vertex link in the
canonical cubical realization by genuine piecewise affine maps.
-/

noncomputable section

open Classical

namespace Cubical.PL.CubeComplex

open Set Geometry
open DifferentialGeometry.Topology.Engulfing
open DifferentialGeometry.Topology.PiecewiseLinear

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

abbrev Neighbor (v : V) := {w : V // K.graph.Adj v w}

def neighborSimplex (F : K.Cell) (v : V) : Finset (K.Neighbor v) :=
  Finset.univ.filter (fun w => w.val ∈ F.val)

@[simp] theorem mem_neighborSimplex (F : K.Cell) (v : V) (w : K.Neighbor v) :
    w ∈ K.neighborSimplex F v ↔ w.val ∈ F.val := by
  simp [neighborSimplex]

@[simp] theorem image_neighborSimplex (F : K.Cell) (v : V) :
    (K.neighborSimplex F v).image Subtype.val = K.neighborFace F.val v := by
  ext w
  simp only [Finset.mem_image, mem_neighborSimplex, mem_neighborFace]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hu, u.property⟩
  · rintro ⟨hw, h⟩
    exact ⟨⟨w, h⟩, hw, rfl⟩

theorem neighborSimplex_mono {F G : K.Cell} (hFG : F ≤ G) (v : V) :
    K.neighborSimplex F v ⊆ K.neighborSimplex G v := by
  intro w hw
  exact (K.mem_neighborSimplex G v w).mpr (hFG ((K.mem_neighborSimplex F v w).mp hw))

theorem neighborSimplex_subset_iff (F G : K.Cell) (v : V) (hvF : v ∈ F.val)
    (hvG : v ∈ G.val) :
    K.neighborSimplex F v ⊆ K.neighborSimplex G v ↔ F ≤ G := by
  refine ⟨?_, fun h => K.neighborSimplex_mono h v⟩
  intro h
  apply (K.neighborFace_subset_iff F G v hvF hvG).mp
  simpa only [K.image_neighborSimplex] using
    (Finset.image_subset_image (f := (Subtype.val : K.Neighbor v → V)) h)

theorem neighborSimplex_eq_iff (F G : K.Cell) (v : V) (hvF : v ∈ F.val)
    (hvG : v ∈ G.val) :
    K.neighborSimplex F v = K.neighborSimplex G v ↔ F = G := by
  constructor
  · intro h
    exact le_antisymm ((K.neighborSimplex_subset_iff F G v hvF hvG).mp h.subset)
      ((K.neighborSimplex_subset_iff G F v hvG hvF).mp h.symm.subset)
  · rintro rfl
    rfl

theorem neighborSimplex_card (F : K.Cell) (v : V) (hvF : v ∈ F.val) :
    (K.neighborSimplex F v).card = K.dimension F.val := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective, K.image_neighborSimplex,
    K.neighborFace_card F v hvF]

def vertexCell (v : V) : K.Cell := ⟨{v}, K.singleton_mem v⟩

@[simp] theorem mem_vertexCell (v w : V) : w ∈ (K.vertexCell v).val ↔ w = v := by
  simp [vertexCell]

theorem vertexCell_le_iff (v : V) (F : K.Cell) : K.vertexCell v ≤ F ↔ v ∈ F.val :=
  Finset.singleton_subset_iff

theorem le_vertexCell_iff (F : K.Cell) (v : V) : F ≤ K.vertexCell v ↔ F = K.vertexCell v := by
  refine ⟨?_, fun h => h.le⟩
  intro h
  apply le_antisymm h
  apply (K.vertexCell_le_iff v F).mpr
  obtain ⟨w, hw⟩ := K.nonempty F.val F.property
  have hwv : w = v := (K.mem_vertexCell v w).mp (h hw)
  exact hwv ▸ hw

@[simp] theorem neighborSimplex_vertexCell (v : V) :
    K.neighborSimplex (K.vertexCell v) v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hwv : w.val = v := (K.mem_vertexCell v w.val).mp
    ((K.mem_neighborSimplex _ _ _).mp hw)
  exact w.property.ne hwv.symm

theorem neighborSimplex_nonempty_iff (F : K.Cell) (v : V) (hvF : v ∈ F.val) :
    (K.neighborSimplex F v).Nonempty ↔ F ≠ K.vertexCell v := by
  constructor
  · intro h heq
    simpa [heq] using h
  · intro h
    apply Finset.nonempty_iff_ne_empty.mpr
    intro heq
    apply h
    apply (K.neighborSimplex_eq_iff F (K.vertexCell v) v hvF (by simp)).mp
    simpa using heq

def neighborComplex (v : V) : PreAbstractSimplicialComplex (K.Neighbor v) where
  faces := {s | s.Nonempty ∧ ∃ F : K.Cell, v ∈ F.val ∧ K.neighborSimplex F v = s}
  isRelLowerSet_faces := by
    rintro s ⟨hs, F, hvF, hFs⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    have hsub : t.image Subtype.val ⊆ K.neighborFace F.val v := by
      rw [← K.image_neighborSimplex F v]
      exact Finset.image_subset_image (hFs ▸ hts)
    obtain ⟨G, hGF, hvG, hG⟩ := K.neighborFace_subface F v hvF _ hsub
    refine ⟨ht, G, hvG, ?_⟩
    apply Finset.image_injective Subtype.val_injective
    rw [K.image_neighborSimplex, hG]

theorem singleton_mem_neighborComplex (v : V) (w : K.Neighbor v) :
    {w} ∈ (K.neighborComplex v).faces := by
  let F : K.Cell := ⟨{v, w.val}, w.property.2.1⟩
  refine ⟨Finset.singleton_nonempty _, F, by simp [F], ?_⟩
  ext u
  simp only [mem_neighborSimplex, F, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact (u.property.ne h.symm).elim
    · exact Subtype.ext h
  · rintro rfl
    exact Or.inr rfl

def neighborGraph (v : V) : SimpleGraph (K.Neighbor v) := abstractEdgeGraph (K.neighborComplex v)

def orderVertexLink (v : V) : PreAbstractSimplicialComplex K.Cell :=
  DifferentialGeometry.Topology.SimplicialComplex.link K.orderComplex {K.vertexCell v}

theorem mem_orderVertexLink (v : V) (C : Finset K.Cell) :
    C ∈ (K.orderVertexLink v).faces ↔
      C.Nonempty ∧ (∀ F ∈ C, v ∈ F.val ∧ F ≠ K.vertexCell v) ∧
        ∀ F ∈ C, ∀ G ∈ C, F ≤ G ∨ G ≤ F := by
  constructor
  · rintro ⟨hne, hdisj, hchain⟩
    have hnot : K.vertexCell v ∉ C := Finset.disjoint_singleton_left.mp hdisj
    refine ⟨hne, ?_, ?_⟩
    · intro F hF
      have hneF : F ≠ K.vertexCell v := fun h => hnot (h ▸ hF)
      refine ⟨?_, hneF⟩
      have hcomp := hchain.2 F (Finset.mem_union_right _ hF) (K.vertexCell v)
        (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      rcases hcomp with hle | hle
      · exact (hneF ((K.le_vertexCell_iff F v).mp hle)).elim
      · exact (K.vertexCell_le_iff v F).mp hle
    · intro F hF G hG
      exact hchain.2 F (Finset.mem_union_right _ hF) G (Finset.mem_union_right _ hG)
  · rintro ⟨hne, hvertices, hchain⟩
    refine ⟨hne, Finset.disjoint_singleton_left.mpr ?_, ?_⟩
    · intro h
      exact (hvertices _ h).2 rfl
    · refine ⟨⟨K.vertexCell v, by simp⟩, ?_⟩
      intro F hF G hG
      simp only [Finset.mem_union, Finset.mem_singleton] at hF hG
      rcases hF with rfl | hF <;> rcases hG with rfl | hG
      · exact Or.inl le_rfl
      · exact Or.inl ((K.vertexCell_le_iff v G).mpr (hvertices G hG).1)
      · exact Or.inr ((K.vertexCell_le_iff v F).mpr (hvertices F hF).1)
      · exact hchain F hF G hG

def simplexCell (v : V) (s : Finset (K.Neighbor v)) : K.Cell :=
  if h : ∃ F : K.Cell, v ∈ F.val ∧ K.neighborSimplex F v = s then h.choose
  else K.vertexCell v

theorem simplexCell_neighborSimplex (F : K.Cell) (v : V) (hvF : v ∈ F.val) :
    K.simplexCell v (K.neighborSimplex F v) = F := by
  unfold simplexCell
  rw [dite_eq_left ⟨F, hvF, rfl⟩]
  have hh := Exists.choose_spec (⟨F, hvF, rfl⟩ :
    ∃ G : K.Cell, v ∈ G.val ∧ K.neighborSimplex G v = K.neighborSimplex F v)
  exact (K.neighborSimplex_eq_iff _ F v hh.1 hvF).mp hh.2

theorem simplexCell_spec (v : V) {s : Finset (K.Neighbor v)}
    (hs : s ∈ (K.neighborComplex v).faces) :
    v ∈ (K.simplexCell v s).val ∧ K.neighborSimplex (K.simplexCell v s) v = s ∧
      K.simplexCell v s ≠ K.vertexCell v := by
  obtain ⟨hne, F, hvF, rfl⟩ := hs
  rw [K.simplexCell_neighborSimplex F v hvF]
  exact ⟨hvF, rfl, (K.neighborSimplex_nonempty_iff F v hvF).mp hne⟩

theorem neighborSimplex_image_orderVertexLink (v : V) (C : Finset K.Cell)
    (hC : C ∈ (K.orderVertexLink v).faces) :
    C.image (fun F => K.neighborSimplex F v) ∈
      (abstractBarycentric (K.neighborComplex v)).faces := by
  have h := (K.mem_orderVertexLink v C).mp hC
  have hface (F : K.Cell) (hF : F ∈ C) :
      K.neighborSimplex F v ∈ (K.neighborComplex v).faces :=
    ⟨(K.neighborSimplex_nonempty_iff F v (h.2.1 F hF).1).mpr (h.2.1 F hF).2,
      F, (h.2.1 F hF).1, rfl⟩
  refine ⟨Finset.image_nonempty.mpr h.1, ⟨?_, ?_⟩, ?_⟩
  · rintro s hs
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hs
    exact (hface F hF).1
  · rintro s hs t ht
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp ht
    exact (h.2.2 F hF G hG).imp (fun hh => K.neighborSimplex_mono hh v)
      (fun hh => K.neighborSimplex_mono hh v)
  · rintro s hs
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hs
    exact hface F hF

theorem simplexCell_image_barycentric (v : V) (D : Finset (Finset (K.Neighbor v)))
    (hD : D ∈ (abstractBarycentric (K.neighborComplex v)).faces) :
    D.image (K.simplexCell v) ∈ (K.orderVertexLink v).faces := by
  apply (K.mem_orderVertexLink v _).mpr
  refine ⟨Finset.image_nonempty.mpr hD.1, ?_, ?_⟩
  · intro F hF
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hF
    have hh := K.simplexCell_spec v (hD.2.2 s hs)
    exact ⟨hh.1, hh.2.2⟩
  · intro F hF G hG
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hG
    have hs' := K.simplexCell_spec v (hD.2.2 s hs)
    have ht' := K.simplexCell_spec v (hD.2.2 t ht)
    rcases hD.2.1.2 s hs t ht with hst | hts
    · left
      apply (K.neighborSimplex_subset_iff _ _ v hs'.1 ht'.1).mp
      simpa only [hs'.2.1, ht'.2.1] using hst
    · right
      apply (K.neighborSimplex_subset_iff _ _ v ht'.1 hs'.1).mp
      simpa only [hs'.2.1, ht'.2.1] using hts

theorem isPLSphere_orderVertexLink_iff_barycentric (v : V) (n : ℕ) :
    IsPLSphere n (standardRealization (K.orderVertexLink v)).space ↔
      IsPLSphere n (standardRealization (abstractBarycentric (K.neighborComplex v))).space := by
  apply isPLSphere_iff_of_vertexIso (K.orderVertexLink v)
    (abstractBarycentric (K.neighborComplex v))
    (fun F => K.neighborSimplex F v) (K.simplexCell v)
  · exact K.neighborSimplex_image_orderVertexLink v
  · exact K.simplexCell_image_barycentric v
  · intro F hF
    have hvF := ((K.mem_orderVertexLink v {F}).mp hF).2.1 F (by simp)
    exact K.simplexCell_neighborSimplex F v hvF.1
  · intro s hs
    exact (K.simplexCell_spec v (hs.2.2 s (by simp))).2.1

/-- The original neighbor complex is a genuine PL sphere.  Its topology
is obtained from the geometric vertex link and the proved PL equivalence
of barycentric subdivision, with no rigidity hypotheses. -/
theorem isPLSphere_neighborComplex (v : V) {n : ℕ}
    (hK : IsPLSphere (n + 1) (standardRealization K.orderComplex).space) :
    IsPLSphere n (standardRealization (K.neighborComplex v)).space := by
  have hlink : IsPLSphere n (standardRealization (K.orderVertexLink v)).space :=
    isPLSphere_abstract_vertex_link K.orderComplex hK (K.singleton_mem_orderComplex _)
  exact (isPLSphere_barycentric_iff (K.neighborComplex v) n).mp
    ((K.isPLSphere_orderVertexLink_iff_barycentric v n).mp hlink)

/-- Generic rigidity of the original neighbor graph of every vertex of
a cubical PL sphere of dimension at least three. -/
theorem neighborGraph_genericallyRigid (v : V) {n : ℕ} (hn : 1 ≤ n)
    (hK : IsPLSphere (n + 2) (standardRealization K.orderComplex).space) :
    Cubical.Rigidity.GenericallyRigid (K.neighborGraph v)
      (EuclideanSpace ℝ (Fin (n + 2))) := by
  apply abstractEdgeGraph_genericallyRigid (K.neighborComplex v)
    (K.singleton_mem_neighborComplex v) hn
  exact K.isPLSphere_neighborComplex v hK

theorem neighborGraph_genericallyRigid_dim (v : V) {m : ℕ} (hm : 3 ≤ m)
    (hK : IsPLSphere m (standardRealization K.orderComplex).space) :
    Cubical.Rigidity.GenericallyRigid (K.neighborGraph v)
      (EuclideanSpace ℝ (Fin m)) := by
  cases m with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m =>
        exact K.neighborGraph_genericallyRigid v (n := m + 1) (by omega) hK

theorem neighborGraph_adj_iff (v : V) (a b : K.Neighbor v) :
    (K.neighborGraph v).Adj a b ↔
      a ≠ b ∧ ∃ F : K.Cell, v ∈ F.val ∧ K.dimension F.val = 2 ∧
        K.neighborSimplex F v = {a, b} := by
  constructor
  · rintro ⟨hne, hface⟩
    obtain ⟨_, F, hvF, hF⟩ := hface
    refine ⟨hne, F, hvF, ?_, hF⟩
    rw [← K.neighborSimplex_card F v hvF, hF, Finset.card_pair hne]
  · rintro ⟨hne, F, hvF, _, hF⟩
    exact ⟨hne, by simp, F, hvF, hF⟩

end Cubical.PL.CubeComplex
