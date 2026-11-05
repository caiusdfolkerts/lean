import bier.complex

/-! Actual abstract links and relabelings, retaining the empty face and ghosts. -/

noncomputable section

namespace Bier.Complex

open DifferentialGeometry.Topology.PiecewiseLinear

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

@[ext] theorem ext {K L : Bier.Complex V} (h : K.face = L.face) : K = L := by
  cases K
  cases L
  cases h
  rfl

def link (K : Bier.Complex V) (v : V) (hv : K.face {v}) : Bier.Complex V where
  face s := v ∉ s ∧ K.face (insert v s)
  empty := by simpa using hv
  downward hst ht := ⟨fun hv => ht.1 (hst hv), K.downward (Finset.insert_subset_insert v hst) ht.2⟩

@[simp] theorem link_face (K : Bier.Complex V) (v : V) (hv : K.face {v}) (s : Finset V) :
    (K.link v hv).face s ↔ v ∉ s ∧ K.face (insert v s) := Iff.rfl

@[simp] theorem link_vertex (K : Bier.Complex V) (v : V) (hv : K.face {v}) (w : V) :
    w ∈ (K.link v hv).vertices ↔ w ≠ v ∧ K.face {v, w} := by
  simp [link, eq_comm]

theorem link_vertex_is_vertex (K : Bier.Complex V) (v : V) (hv : K.face {v})
    {w : V} (hw : w ∈ (K.link v hv).vertices) : w ∈ K.vertices := by
  exact (mem_vertices K w).mpr (K.downward (by simp) ((link_vertex K v hv w).mp hw).2)

def map (K : Bier.Complex V) (f : V → W) : Bier.Complex W where
  face s := ∃ t, K.face t ∧ t.image f = s
  empty := ⟨∅, K.empty, by simp⟩
  downward := by
    classical
    intro s t hst ht
    obtain ⟨u, hu, rfl⟩ := ht
    refine ⟨u.filter (fun v => f v ∈ s), K.downward (Finset.filter_subset _ _) hu, ?_⟩
    exact image_filter_mem_eq hst

@[simp] theorem map_face (K : Bier.Complex V) (f : V → W) (s : Finset W) :
    (K.map f).face s ↔ ∃ t, K.face t ∧ t.image f = s := Iff.rfl

theorem map_image_face_iff (K : Bier.Complex V) (f : V → W) (hf : Function.Injective f)
    (s : Finset V) : (K.map f).face (s.image f) ↔ K.face s := by
  constructor
  · rintro ⟨t, ht, heq⟩
    exact Finset.image_injective hf heq ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩

theorem map_vertex_iff (K : Bier.Complex V) (f : V → W) (w : W) :
    w ∈ (K.map f).vertices ↔ ∃ v ∈ K.vertices, f v = w := by
  classical
  rw [mem_vertices, map_face]
  constructor
  · rintro ⟨t, ht, heq⟩
    have hw : w ∈ t.image f := heq.symm ▸ Finset.mem_singleton_self w
    obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hw
    exact ⟨v, (mem_vertices K v).mpr (K.downward (Finset.singleton_subset_iff.mpr hv) ht), hfv⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨{v}, (mem_vertices K v).mp hv, by simp⟩

def mapVertexEquiv (K : Bier.Complex V) (f : V → W) (hf : Function.Injective f) :
    ↥K.vertices ≃ ↥(K.map f).vertices := by
  classical
  apply Equiv.ofBijective (fun v => ⟨f v, (map_vertex_iff K f _).mpr ⟨v, v.property, rfl⟩⟩)
  constructor
  · intro v w heq
    exact Subtype.ext (hf (congrArg Subtype.val heq))
  · intro w
    obtain ⟨v, hv, heq⟩ := (map_vertex_iff K f w).mp w.property
    exact ⟨⟨v, hv⟩, Subtype.ext heq⟩

@[simp] theorem mapVertexEquiv_apply (K : Bier.Complex V) (f : V → W)
    (hf : Function.Injective f) (v : ↥K.vertices) :
    (mapVertexEquiv K f hf v).val = f v := rfl

end Bier.Complex
