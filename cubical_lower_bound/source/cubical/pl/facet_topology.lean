import cubical.pl.cube_complex
import cubical.pl_abstract
import Mathlib.Data.Fintype.Fin

/-! # Purity and facet connectivity of genuine cubical PL spheres

The topology is the ordinary PL topology of the canonical face-chain
realization. Cell dimensions and facet incidences are derived from that
topology and the coordinate cube charts.
-/

noncomputable section

namespace Cubical.PL.CubeComplex

open Set Classical
open DifferentialGeometry.Topology.Engulfing
open DifferentialGeometry.Topology.PiecewiseLinear

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

def realization := standardRealization K.orderComplex

instance realization_faces_finite : Finite K.realization.faces :=
  (standardRealization_finite_faces K.orderComplex).to_subtype

/-- A genuine PL sphere, using an actual piecewise affine homeomorphism
with piecewise affine inverse from the standard simplex boundary. -/
def IsSphere (m : ℕ) : Prop := IsPLSphere m K.realization.space

theorem chartFace_mono (F : K.Cell) (s : Cube.Vertex (K.dimension F.val))
    {A B : Finset (Fin (K.dimension F.val))} (hAB : A ⊆ B) :
    chartFace (K.cellVertex F) s A ⊆ chartFace (K.cellVertex F) s B := by
  apply Finset.image_subset_image
  intro t ht
  rw [mem_coordinateFace] at ht ⊢
  intro i hi
  exact ht i (fun h => hi (hAB h))

def initialCoords (n : ℕ) (j : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < j.val)

theorem initialCoords_card (n : ℕ) (j : Fin (n + 1)) :
    (initialCoords n j).card = j.val := by
  rw [initialCoords, Fin.card_filter_val_lt, Nat.min_eq_right (by omega)]

theorem initialCoords_mono (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    initialCoords n i ⊆ initialCoords n j := by
  intro a ha
  simp only [initialCoords, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact lt_of_lt_of_le ha hij

theorem initialCoords_last (n : ℕ) : initialCoords n (Fin.last n) = Finset.univ := by
  ext i
  simp [initialCoords, i.isLt]

def flagCell (F : K.Cell) (j : Fin (K.dimension F.val + 1)) : K.Cell :=
  ⟨chartFace (K.cellVertex F) (fun _ => false) (initialCoords _ j),
    K.chart_face_mem F _ _⟩

@[simp] theorem flagCell_dimension (F : K.Cell) (j : Fin (K.dimension F.val + 1)) :
    K.dimension (K.flagCell F j).val = j.val := by
  change K.dimension (chartFace (K.cellVertex F) _ _) = _
  rw [K.chart_face_dimension, initialCoords_card]

theorem flagCell_mono (F : K.Cell) : Monotone (K.flagCell F) := by
  intro i j hij
  exact K.chartFace_mono F _ (initialCoords_mono _ hij)

theorem flagCell_injective (F : K.Cell) : Function.Injective (K.flagCell F) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg (fun G : K.Cell => K.dimension G.val) h
  simpa only [K.flagCell_dimension] using hh

@[simp] theorem flagCell_last (F : K.Cell) :
    K.flagCell F (Fin.last (K.dimension F.val)) = F := by
  apply Subtype.ext
  change chartFace (K.cellVertex F) _ _ = F.val
  rw [initialCoords_last, chartFace_univ]

def completeFlag (F : K.Cell) : Finset K.Cell := Finset.univ.image (K.flagCell F)

theorem completeFlag_mem (F : K.Cell) : K.completeFlag F ∈ K.orderComplex.faces := by
  refine ⟨⟨F, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨Fin.last _, Finset.mem_univ _, K.flagCell_last F⟩
  · intro A hA B hB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact (le_total i j).imp (fun h => K.flagCell_mono F h) (fun h => K.flagCell_mono F h)

@[simp] theorem completeFlag_card (F : K.Cell) :
    (K.completeFlag F).card = K.dimension F.val + 1 := by
  rw [completeFlag, Finset.card_image_of_injective _ (K.flagCell_injective F)]
  simp

theorem self_mem_completeFlag (F : K.Cell) : F ∈ K.completeFlag F :=
  Finset.mem_image.mpr ⟨Fin.last _, Finset.mem_univ _, K.flagCell_last F⟩

theorem chain_dimension_injective {C : Finset K.Cell} (hC : C ∈ K.orderComplex.faces) :
    Set.InjOn (fun F : K.Cell => K.dimension F.val) C := by
  intro F hF G hG heq
  rcases hC.2 F hF G hG with h | h
  · exact (K.dimension_eq_iff_eq F G h).mp heq
  · exact ((K.dimension_eq_iff_eq G F h).mp heq.symm).symm

theorem chain_card_le {m : ℕ} (hK : K.IsSphere m)
    {C : Finset K.Cell} (hC : C ∈ K.orderComplex.faces) : C.card ≤ m + 1 := by
  have h := card_le_of_isPLSphere K.realization hK
    ((image_mem_standardRealization_iff K.orderComplex C).mpr hC)
  rwa [Finset.card_image_of_injective _ standardVertex_injective] at h

theorem cell_dimension_le {m : ℕ} (hK : K.IsSphere m) (F : K.Cell) :
    K.dimension F.val ≤ m := by
  have h := K.chain_card_le hK (K.completeFlag_mem F)
  rw [K.completeFlag_card] at h
  omega

theorem exists_top_chain_superset {m : ℕ} (hK : K.IsSphere m)
    {C : Finset K.Cell} (hC : C ∈ K.orderComplex.faces) :
    ∃ D ∈ K.orderComplex.faces, C ⊆ D ∧ D.card = m + 1 := by
  obtain ⟨t, ht, hsub, hcard⟩ := exists_face_superset_card_eq_of_isPLSphere
    K.realization hK ((image_mem_standardRealization_iff K.orderComplex C).mpr hC)
  obtain ⟨D, hD, rfl⟩ := ht
  refine ⟨D, hD, ?_, ?_⟩
  · exact (Finset.image_subset_image_iff standardVertex_injective).mp hsub
  · change (D.image standardVertex).card = m + 1 at hcard
    rwa [Finset.card_image_of_injective _ standardVertex_injective] at hcard

theorem top_chain_dimensions {m : ℕ} (hK : K.IsSphere m)
    {C : Finset K.Cell} (hC : C ∈ K.orderComplex.faces) (hc : C.card = m + 1) :
    C.image (fun F => K.dimension F.val) = Finset.range (m + 1) := by
  have hsub : C.image (fun F => K.dimension F.val) ⊆ Finset.range (m + 1) := by
    intro j hj
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (by have := K.cell_dimension_le hK F; omega)
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_iff.mpr (K.chain_dimension_injective hC), Finset.card_range, hc]

theorem top_chain_has_dimension {m : ℕ} (hK : K.IsSphere m)
    {C : Finset K.Cell} (hC : C ∈ K.orderComplex.faces) (hc : C.card = m + 1)
    (j : ℕ) (hj : j ≤ m) : ∃ F ∈ C, K.dimension F.val = j := by
  have hm : j ∈ C.image (fun F => K.dimension F.val) := by
    rw [K.top_chain_dimensions hK hC hc]
    exact Finset.mem_range.mpr (by omega)
  exact Finset.mem_image.mp hm

theorem top_cell_ge_chain {m : ℕ} (hK : K.IsSphere m)
    {C : Finset K.Cell} (hC : C ∈ K.orderComplex.faces)
    {F : K.Cell} (hF : F ∈ C) (hdF : K.dimension F.val = m) :
    ∀ G ∈ C, G ≤ F := by
  intro G hG
  rcases hC.2 G hG F hF with h | h
  · exact h
  · have hdG : K.dimension G.val = K.dimension F.val := by
      have hle := K.dimension_mono F G h
      have hbound := K.cell_dimension_le hK G
      omega
    exact le_of_eq ((K.dimension_eq_iff_eq F G h).mp hdG.symm).symm

abbrev Facet (m : ℕ) := {F : K.Cell // K.dimension F.val = m}

theorem cell_in_facet {m : ℕ} (hK : K.IsSphere m) (F : K.Cell) :
    ∃ G : K.Facet m, F ≤ G.val := by
  obtain ⟨C, hC, hFC, hc⟩ := K.exists_top_chain_superset hK (K.singleton_mem_orderComplex F)
  obtain ⟨G, hG, hdG⟩ := K.top_chain_has_dimension hK hC hc m le_rfl
  exact ⟨⟨G, hdG⟩, K.top_cell_ge_chain hK hC hG hdG F (hFC (Finset.mem_singleton_self F))⟩

end Cubical.PL.CubeComplex
