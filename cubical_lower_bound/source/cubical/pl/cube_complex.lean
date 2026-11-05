import cubical.cube
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Finite abstract cubical complexes

A cell is recorded by its actual vertex set.  Its chart is a bijection with a
bit-vector cube, and the chart identifies precisely all coordinate subfaces.
Thus this definition includes abstract cubical complexes with no assumed
convex realization.  Intersections are required to be common faces whenever
nonempty, as in the hypothesis of the paper's PL-sphere extension.
-/

noncomputable section

open Classical

namespace Cubical.PL

def coordinateFace {n : ℕ} (s : Cube.Vertex n) (A : Finset (Fin n)) :
    Finset (Cube.Vertex n) :=
  Finset.univ.filter (fun t => t ∈ Cube.FaceAt s A)

@[simp] theorem mem_coordinateFace {n : ℕ} (s t : Cube.Vertex n)
    (A : Finset (Fin n)) : t ∈ coordinateFace s A ↔ t ∈ Cube.FaceAt s A := by
  simp [coordinateFace]

theorem self_mem_coordinateFace {n : ℕ} (s : Cube.Vertex n) (A : Finset (Fin n)) :
    s ∈ coordinateFace s A := by
  simp only [mem_coordinateFace]
  intro i hi
  rfl

@[simp] theorem coordinateFace_empty {n : ℕ} (s : Cube.Vertex n) :
    coordinateFace s ∅ = {s} := by
  ext t
  simp only [mem_coordinateFace, Finset.mem_singleton, Cube.FaceAt, Set.mem_setOf_eq]
  constructor
  · intro h
    funext i
    exact h i (by simp)
  · rintro rfl i hi
    rfl

@[simp] theorem coordinateFace_univ {n : ℕ} (s : Cube.Vertex n) :
    coordinateFace s Finset.univ = Finset.univ := by
  ext t
  simp [coordinateFace, Cube.FaceAt]

theorem coordinateFace_singleton {n : ℕ} (s : Cube.Vertex n) (i : Fin n) :
    coordinateFace s {i} = {s, Cube.flip s i} := by
  ext t
  simp only [mem_coordinateFace, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ht
    by_cases hti : t i = s i
    · left
      funext j
      by_cases hji : j = i
      · simpa [hji] using hti
      · exact ht j (by simpa using hji)
    · right
      funext j
      by_cases hji : j = i
      · subst j
        rw [Cube.flip_same]
        cases hs : s i <;> cases ht' : t i <;> simp_all
      · rw [Cube.flip_other s i j hji]
        exact ht j (by simpa using hji)
  · rintro (rfl | rfl)
    · intro j hj
      rfl
    · intro j hj
      exact Cube.flip_other s i j (by simpa using hj)

def chartFace {V : Type*} [DecidableEq V] {F : Finset V} {n : ℕ}
    (φ : Cube.Vertex n ≃ F) (s : Cube.Vertex n) (A : Finset (Fin n)) : Finset V :=
  (coordinateFace s A).image (fun t => (φ t).val)

@[simp] theorem mem_chartFace {V : Type*} [DecidableEq V] {F : Finset V} {n : ℕ}
    (φ : Cube.Vertex n ≃ F) (s : Cube.Vertex n) (A : Finset (Fin n)) (v : F) :
    v.val ∈ chartFace φ s A ↔ φ.symm v ∈ coordinateFace s A := by
  simp only [chartFace, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, heq⟩
    have : φ t = v := Subtype.ext heq
    simpa only [← this, φ.symm_apply_apply] using ht
  · intro h
    exact ⟨φ.symm v, h, congrArg Subtype.val (φ.apply_symm_apply v)⟩

theorem chartFace_subset {V : Type*} [DecidableEq V] {F : Finset V} {n : ℕ}
    (φ : Cube.Vertex n ≃ F) (s : Cube.Vertex n) (A : Finset (Fin n)) :
    chartFace φ s A ⊆ F := by
  intro v hv
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
  exact (φ t).property

@[simp] theorem chartFace_univ {V : Type*} [DecidableEq V] {F : Finset V} {n : ℕ}
    (φ : Cube.Vertex n ≃ F) (s : Cube.Vertex n) :
    chartFace φ s Finset.univ = F := by
  apply Finset.Subset.antisymm (chartFace_subset φ s _)
  intro v hv
  apply Finset.mem_image.mpr
  exact ⟨φ.symm ⟨v, hv⟩, by simp, congrArg Subtype.val (φ.apply_symm_apply _)⟩

structure CubeComplex (V : Type*) [Fintype V] [DecidableEq V] where
  faces : Finset (Finset V)
  nonempty : ∀ F ∈ faces, F.Nonempty
  singleton_mem : ∀ v, {v} ∈ faces
  inter_mem : ∀ F ∈ faces, ∀ G ∈ faces, (F ∩ G).Nonempty → F ∩ G ∈ faces
  dimension : Finset V → ℕ
  chart : ∀ F ∈ faces, Cube.Vertex (dimension F) ≃ F
  chart_faces : ∀ F (hF : F ∈ faces) s A,
    chartFace (chart F hF) s A ∈ faces ∧
      dimension (chartFace (chart F hF) s A) = A.card
  subfaces : ∀ F (hF : F ∈ faces) G, G ∈ faces → G ⊆ F →
    ∃ s A, G = chartFace (chart F hF) s A

namespace CubeComplex

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

abbrev Cell := {F : Finset V // F ∈ K.faces}

instance : Fintype K.Cell := inferInstance

def cellVertex (F : K.Cell) : Cube.Vertex (K.dimension F.val) ≃ F.val :=
  K.chart F.val F.property

theorem cell_vertex_card (F : K.Cell) : F.val.card = 2 ^ K.dimension F.val := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (K.cellVertex F)]
  exact Cube.card_vertex _

theorem singleton_dimension (v : V) : K.dimension {v} = 0 := by
  have h := K.cell_vertex_card ⟨{v}, K.singleton_mem v⟩
  simp only [Finset.card_singleton] at h
  have : 2 ^ K.dimension {v} = 2 ^ 0 := by simpa using h.symm
  exact Nat.pow_right_injective (by decide : 1 < 2) this

def graph : SimpleGraph V where
  Adj v w := v ≠ w ∧ {v, w} ∈ K.faces ∧ K.dimension {v, w} = 1
  symm := by
    constructor
    intro v w h
    simpa only [Finset.pair_comm] using And.intro h.1.symm h.2
  loopless := by
    constructor
    intro v h
    exact h.1 rfl

theorem chart_face_mem (F : K.Cell) (s : Cube.Vertex (K.dimension F.val))
    (A : Finset (Fin (K.dimension F.val))) :
    chartFace (K.cellVertex F) s A ∈ K.faces :=
  (K.chart_faces F.val F.property s A).1

theorem chart_face_dimension (F : K.Cell) (s : Cube.Vertex (K.dimension F.val))
    (A : Finset (Fin (K.dimension F.val))) :
    K.dimension (chartFace (K.cellVertex F) s A) = A.card :=
  (K.chart_faces F.val F.property s A).2

theorem dimension_mono (F G : K.Cell) (hFG : F.val ⊆ G.val) :
    K.dimension F.val ≤ K.dimension G.val := by
  obtain ⟨s, A, hA⟩ := K.subfaces G.val G.property F.val F.property hFG
  rw [hA, (K.chart_faces G.val G.property s A).2]
  exact (Finset.card_le_card (Finset.subset_univ A)).trans_eq (Fintype.card_fin _)

theorem dimension_eq_iff_eq (F G : K.Cell) (hFG : F.val ⊆ G.val) :
    K.dimension F.val = K.dimension G.val ↔ F = G := by
  constructor
  · intro h
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le hFG
    rw [K.cell_vertex_card F, K.cell_vertex_card G, h]
  · rintro rfl
    rfl

theorem dimension_lt_of_lt (F G : K.Cell) (hFG : F < G) :
    K.dimension F.val < K.dimension G.val := by
  exact lt_of_le_of_ne (K.dimension_mono F G hFG.le)
    (fun h => hFG.ne ((K.dimension_eq_iff_eq F G hFG.le).mp h))

theorem chart_adj_iff (F : K.Cell) (s t : Cube.Vertex (K.dimension F.val)) :
    K.graph.Adj (K.cellVertex F s).val (K.cellVertex F t).val ↔
      (Cube.graph (K.dimension F.val)).Adj s t := by
  constructor
  · rintro ⟨hne, hpair, hdim⟩
    have hsub : {(K.cellVertex F s).val, (K.cellVertex F t).val} ⊆ F.val := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨(K.cellVertex F s).property, (K.cellVertex F t).property⟩
    obtain ⟨a, A, hA⟩ := K.subfaces F.val F.property _ hpair hsub
    change _ = chartFace (K.cellVertex F) a A at hA
    have hcard : A.card = 1 := by
      rw [hA, K.chart_face_dimension F] at hdim
      exact hdim
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    have hs : s ∈ coordinateFace a {i} := by
      have hh : (K.cellVertex F s).val ∈ chartFace (K.cellVertex F) a {i} := by
        rw [← hA]
        simp
      simpa using (mem_chartFace (K.cellVertex F) a {i} (K.cellVertex F s)).mp hh
    have ht : t ∈ coordinateFace a {i} := by
      have hh : (K.cellVertex F t).val ∈ chartFace (K.cellVertex F) a {i} := by
        rw [← hA]
        simp
      simpa using (mem_chartFace (K.cellVertex F) a {i} (K.cellVertex F t)).mp hh
    have hst : s ≠ t := fun h => hne (congrArg (fun x => (K.cellVertex F x).val) h)
    rw [coordinateFace_singleton] at hs ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact (hst (hs.trans ht.symm)).elim
    · exact ⟨i, by rw [hs, ht]⟩
    · exact ⟨i, by rw [hs, ht, Cube.flip_flip]⟩
    · exact (hst (hs.trans ht.symm)).elim
  · rintro ⟨i, rfl⟩
    have hface : chartFace (K.cellVertex F) s {i} =
        {(K.cellVertex F s).val, (K.cellVertex F (Cube.flip s i)).val} := by
      simp [chartFace, coordinateFace_singleton]
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      exact Cube.flip_ne_self s i
        ((K.cellVertex F).injective (Subtype.ext heq)).symm
    · rw [← hface]
      exact K.chart_face_mem F s {i}
    · rw [← hface, K.chart_face_dimension]
      simp

def cellGraphIso (F : K.Cell) :
    Cube.graph (K.dimension F.val) ≃g K.graph.induce (F.val : Set V) where
  __ := K.cellVertex F
  map_rel_iff' := by intro s t; exact K.chart_adj_iff F s t

def orderComplex : PreAbstractSimplicialComplex K.Cell where
  faces := {C | C.Nonempty ∧ ∀ F ∈ C, ∀ G ∈ C, F ≤ G ∨ G ≤ F}
  isRelLowerSet_faces := by
    rintro C ⟨hne, hchain⟩
    refine ⟨hne, ?_⟩
    intro D hDC hD
    exact ⟨hD, fun F hF G hG => hchain F (hDC hF) G (hDC hG)⟩

@[simp] theorem singleton_mem_orderComplex (F : K.Cell) :
    {F} ∈ K.orderComplex.faces := by
  refine ⟨Finset.singleton_nonempty _, ?_⟩
  intro G hG H hH
  simp only [Finset.mem_singleton] at hG hH
  subst G H
  exact Or.inl le_rfl

theorem pair_mem_orderComplex_iff (F G : K.Cell) :
    {F, G} ∈ K.orderComplex.faces ↔ F ≤ G ∨ G ≤ F := by
  constructor
  · intro h
    exact h.2 F (by simp) G (by simp)
  · intro h
    refine ⟨by simp, ?_⟩
    intro A hA B hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact Or.inl le_rfl
    · exact h
    · exact h.symm
    · exact Or.inl le_rfl

end CubeComplex

end Cubical.PL
