import cubical.pl.cell_parity

/-! The simplicial neighbor link of a vertex in an abstract cubical complex. -/

noncomputable section

open Classical

namespace Cubical.PL.CubeComplex

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

def neighborFace (F : Finset V) (v : V) : Finset V :=
  F.filter (K.graph.Adj v)

@[simp] theorem mem_neighborFace (F : Finset V) (v w : V) :
    w ∈ K.neighborFace F v ↔ w ∈ F ∧ K.graph.Adj v w := by
  simp [neighborFace]

def cellNeighbor (F : K.Cell) (v : F.val) (i : Fin (K.dimension F.val)) : V :=
  (K.cellVertex F (Cube.flip ((K.cellVertex F).symm v) i)).val

theorem cellNeighbor_mem (F : K.Cell) (v : F.val) (i : Fin (K.dimension F.val)) :
    K.cellNeighbor F v i ∈ K.neighborFace F.val v.val := by
  apply (K.mem_neighborFace _ _ _).mpr
  refine ⟨(K.cellVertex F _).property, ?_⟩
  have h := (K.chart_adj_iff F ((K.cellVertex F).symm v)
    (Cube.flip ((K.cellVertex F).symm v) i)).mpr ⟨i, rfl⟩
  simpa only [Equiv.apply_symm_apply, cellNeighbor] using h

theorem cellNeighbor_injective (F : K.Cell) (v : F.val) :
    Function.Injective (K.cellNeighbor F v) := by
  intro i j h
  exact Cube.flip_index_injective ((K.cellVertex F).symm v)
    ((K.cellVertex F).injective (Subtype.ext h))

def cellNeighborsEquiv (F : K.Cell) (v : F.val) :
    Fin (K.dimension F.val) ≃ K.neighborFace F.val v.val :=
  Equiv.ofBijective (fun i => ⟨K.cellNeighbor F v i, K.cellNeighbor_mem F v i⟩)
    ⟨by
      intro i j h
      have hv : K.cellNeighbor F v i = K.cellNeighbor F v j :=
        congrArg (fun z : K.neighborFace F.val v.val => z.val) h
      exact K.cellNeighbor_injective F v hv, by
      rintro ⟨w, hw⟩
      have hw' := (K.mem_neighborFace F.val v.val w).mp hw
      let z : F.val := ⟨w, hw'.1⟩
      have h : (Cube.graph (K.dimension F.val)).Adj
          ((K.cellVertex F).symm v) ((K.cellVertex F).symm z) := by
        apply (K.chart_adj_iff F _ _).mp
        simpa only [Equiv.apply_symm_apply] using hw'.2
      obtain ⟨i, hi⟩ := h
      refine ⟨i, Subtype.ext ?_⟩
      change (K.cellVertex F (Cube.flip ((K.cellVertex F).symm v) i)).val = w
      rw [← hi, Equiv.apply_symm_apply]
      ⟩

theorem neighborFace_card (F : K.Cell) (v : V) (hv : v ∈ F.val) :
    (K.neighborFace F.val v).card = K.dimension F.val := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (K.cellNeighborsEquiv F ⟨v, hv⟩)]
  exact Fintype.card_fin _

theorem neighborFace_mono {F G : Finset V} (hFG : F ⊆ G) (v : V) :
    K.neighborFace F v ⊆ K.neighborFace G v := by
  intro w hw
  exact (K.mem_neighborFace G v w).mpr
    ⟨hFG ((K.mem_neighborFace F v w).mp hw).1, ((K.mem_neighborFace F v w).mp hw).2⟩

@[simp] theorem neighborFace_inter (F G : Finset V) (v : V) :
    K.neighborFace (F ∩ G) v = K.neighborFace F v ∩ K.neighborFace G v := by
  ext w
  simp only [mem_neighborFace, Finset.mem_inter]
  tauto

theorem neighborFace_subset_iff (F G : K.Cell) (v : V) (hvF : v ∈ F.val)
    (hvG : v ∈ G.val) :
    K.neighborFace F.val v ⊆ K.neighborFace G.val v ↔ F ≤ G := by
  refine ⟨?_, fun h => K.neighborFace_mono h v⟩
  intro h
  let H : K.Cell := ⟨F.val ∩ G.val, K.inter_mem F.val F.property G.val G.property
    ⟨v, Finset.mem_inter.mpr ⟨hvF, hvG⟩⟩⟩
  have hvH : v ∈ H.val := Finset.mem_inter.mpr ⟨hvF, hvG⟩
  have hHF : H ≤ F := Finset.inter_subset_left
  have hn : K.neighborFace H.val v = K.neighborFace F.val v := by
    change K.neighborFace (F.val ∩ G.val) v = _
    rw [K.neighborFace_inter, Finset.inter_eq_left.mpr h]
  have hdim : K.dimension H.val = K.dimension F.val := by
    rw [← K.neighborFace_card H v hvH, ← K.neighborFace_card F v hvF, hn]
  have heq := (K.dimension_eq_iff_eq H F hHF).mp hdim
  have hHG : H ≤ G := Finset.inter_subset_right
  exact heq ▸ hHG

theorem neighborFace_injective_at (v : V) :
    Function.Injective (fun F : {F : K.Cell // v ∈ F.val} => K.neighborFace F.val.val v) := by
  intro F G h
  apply Subtype.ext
  apply le_antisymm
  · exact (K.neighborFace_subset_iff F.val G.val v F.property G.property).mp h.subset
  · exact (K.neighborFace_subset_iff G.val F.val v G.property F.property).mp h.symm.subset

theorem neighborFace_coordinate (F : K.Cell) (v : F.val)
    (A : Finset (Fin (K.dimension F.val))) :
    K.neighborFace (chartFace (K.cellVertex F) ((K.cellVertex F).symm v) A) v.val =
      A.image (K.cellNeighbor F v) := by
  ext w
  constructor
  · intro hw
    have hw' := (K.mem_neighborFace _ _ _).mp hw
    have hwF := chartFace_subset (K.cellVertex F) ((K.cellVertex F).symm v) A hw'.1
    let z : K.neighborFace F.val v.val := ⟨w, (K.mem_neighborFace _ _ _).mpr ⟨hwF, hw'.2⟩⟩
    obtain ⟨i, hi⟩ := (K.cellNeighborsEquiv F v).surjective z
    have hiw : K.cellNeighbor F v i = w := congrArg Subtype.val hi
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hiw⟩
    have hmem : K.cellNeighbor F v i ∈
        chartFace (K.cellVertex F) ((K.cellVertex F).symm v) A := hiw ▸ hw'.1
    change (K.cellVertex F (Cube.flip ((K.cellVertex F).symm v) i)).val ∈ _ at hmem
    rw [mem_chartFace, Equiv.symm_apply_apply, mem_coordinateFace] at hmem
    exact (Cube.flip_mem_faceAt_iff _ A i).mp hmem
  · intro hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    apply (K.mem_neighborFace _ _ _).mpr
    refine ⟨?_, ((K.mem_neighborFace _ _ _).mp (K.cellNeighbor_mem F v i)).2⟩
    change (K.cellVertex F (Cube.flip ((K.cellVertex F).symm v) i)).val ∈ _
    rw [mem_chartFace, Equiv.symm_apply_apply, mem_coordinateFace]
    exact (Cube.flip_mem_faceAt_iff _ A i).mpr hi

theorem neighborFace_subface (F : K.Cell) (v : V) (hvF : v ∈ F.val)
    (a : Finset V) (ha : a ⊆ K.neighborFace F.val v) :
    ∃ G : K.Cell, G ≤ F ∧ v ∈ G.val ∧ K.neighborFace G.val v = a := by
  let x : F.val := ⟨v, hvF⟩
  let A : Finset (Fin (K.dimension F.val)) :=
    Finset.univ.filter (fun i => K.cellNeighbor F x i ∈ a)
  let G : K.Cell := ⟨chartFace (K.cellVertex F) ((K.cellVertex F).symm x) A,
    K.chart_face_mem F _ A⟩
  refine ⟨G, chartFace_subset _ _ _, ?_, ?_⟩
  · have hh : (K.cellVertex F ((K.cellVertex F).symm x)).val ∈ G.val := by
      apply Finset.mem_image.mpr
      exact ⟨_, self_mem_coordinateFace _ A, rfl⟩
    simpa only [Equiv.apply_symm_apply] using hh
  · change K.neighborFace (chartFace (K.cellVertex F) ((K.cellVertex F).symm x) A) v = a
    rw [K.neighborFace_coordinate F x A]
    ext w
    constructor
    · rintro hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hi).2
    · intro hw
      obtain ⟨i, hi⟩ := (K.cellNeighborsEquiv F x).surjective ⟨w, ha hw⟩
      have hiw : K.cellNeighbor F x i = w := congrArg Subtype.val hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiw ▸ hw⟩, hiw⟩

end Cubical.PL.CubeComplex
