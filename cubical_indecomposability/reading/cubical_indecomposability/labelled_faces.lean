import papers.finite_hull_certificates
import cubical.polytope.graph
import cubical.polytope.dim_stretta
import Mathlib.Tactic.FinCases

/-!
# Exposed faces from finite support certificates

All sets in this file are ordinary exposed subsets of a real convex hull.
Finite vertex masks are only names for those subsets.  The correspondence
between inclusion of masks and inclusion of geometric faces is proved here.
-/

noncomputable section

namespace CubicalIndecomposability

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

variable {n : ℕ} {V I : Type*} [Fintype V] [DecidableEq V]

/-- Supporting equalities can be combined by addition: nonnegative slacks
cannot cancel. -/
theorem sum_support_eq_iff (P : ConvexPolytope n)
    (l : I → E n →L[ℝ] ℝ) (c : I → ℝ) (rows : Finset I)
    (hbound : ∀ i, ∀ x ∈ P.vertices, c i ≤ l i x)
    (x : E n) (hx : x ∈ P.vertices) :
    (∑ i ∈ rows, l i x) = (∑ i ∈ rows, c i) ↔
      ∀ i ∈ rows, l i x = c i := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _hi => sub_nonneg.mpr (hbound i x hx))]
  simp only [sub_eq_zero]

/-- The face cut out by a finite collection of supporting equalities. -/
def supportIntersection (P : ConvexPolytope n)
    (l : I → E n →L[ℝ] ℝ) (c : I → ℝ) (rows : Finset I) : Set (E n) :=
  minimumFace P (∑ i ∈ rows, l i) (∑ i ∈ rows, c i)

theorem supportIntersection_isFace (P : ConvexPolytope n)
    (l : I → E n →L[ℝ] ℝ) (c : I → ℝ) (rows : Finset I)
    (hbound : ∀ i, ∀ x ∈ P.vertices, c i ≤ l i x)
    (hattained : ∃ x ∈ P.vertices, ∀ i ∈ rows, l i x = c i) :
    P.IsFace (supportIntersection P l c rows) := by
  apply minimumFace_isFace
  · intro x hx
    simp only [ContinuousLinearMap.sum_apply]
    exact Finset.sum_le_sum fun i hi => hbound i x hx
  · obtain ⟨x, hx, h⟩ := hattained
    refine ⟨x, hx, ?_⟩
    simp only [ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl h

theorem vertex_mem_supportIntersection (P : ConvexPolytope n)
    (l : I → E n →L[ℝ] ℝ) (c : I → ℝ) (rows : Finset I)
    (hbound : ∀ i, ∀ x ∈ P.vertices, c i ≤ l i x)
    (x : E n) (hx : x ∈ P.vertices) :
    x ∈ supportIntersection P l c rows ↔ ∀ i ∈ rows, l i x = c i := by
  change (x ∈ P.toSet ∧ _) ↔ _
  have hxbody : x ∈ P.toSet := subset_convexHull ℝ _ hx
  rw [and_iff_right hxbody]
  simp only [ContinuousLinearMap.sum_apply]
  exact sum_support_eq_iff P l c rows hbound x hx

/-- A labelled face is exactly the hull of its labelled vertices. -/
theorem face_eq_label_hull (P : ConvexPolytope n) (p : V → E n)
    (hp : P.vertices = Finset.univ.image p)
    {F : Set (E n)} (hF : P.IsFace F) (s : Finset V)
    (hs : ∀ v, p v ∈ F ↔ v ∈ s) :
    F = convexHull ℝ (p '' (s : Set V)) := by
  classical
  rw [face_eq_hull_vertices P hF]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter, hp,
    Finset.mem_image, Finset.mem_univ, true_and, Set.mem_image]
  constructor
  · rintro ⟨⟨v, rfl⟩, hv⟩
    exact ⟨v, (hs v).mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, (hs v).mpr hv⟩

/-- Exact vertex labels reflect geometric face inclusion. -/
theorem face_subset_iff_labels (P : ConvexPolytope n) (p : V → E n)
    (hp : P.vertices = Finset.univ.image p)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (s t : Finset V) (hs : ∀ v, p v ∈ F ↔ v ∈ s)
    (ht : ∀ v, p v ∈ G ↔ v ∈ t) :
    F ⊆ G ↔ s ⊆ t := by
  constructor
  · intro h v hv
    exact (ht v).mp (h ((hs v).mpr hv))
  · intro h
    rw [face_eq_label_hull P p hp hF s hs,
      face_eq_label_hull P p hp hG t ht]
    exact convexHull_mono (Set.image_mono h)

theorem face_eq_iff_labels (P : ConvexPolytope n) (p : V → E n)
    (hp : P.vertices = Finset.univ.image p)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (s t : Finset V) (hs : ∀ v, p v ∈ F ↔ v ∈ s)
    (ht : ∀ v, p v ∈ G ↔ v ∈ t) :
    F = G ↔ s = t := by
  constructor
  · intro h
    apply Finset.Subset.antisymm
    · exact (face_subset_iff_labels P p hp hF hG s t hs ht).mp h.le
    · exact (face_subset_iff_labels P p hp hG hF t s ht hs).mp h.ge
  · intro h
    apply Set.Subset.antisymm
    · exact (face_subset_iff_labels P p hp hF hG s t hs ht).mpr h.le
    · exact (face_subset_iff_labels P p hp hG hF t s ht hs).mpr h.ge

theorem face_ssubset_iff_labels (P : ConvexPolytope n) (p : V → E n)
    (hp : P.vertices = Finset.univ.image p)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (s t : Finset V) (hs : ∀ v, p v ∈ F ↔ v ∈ s)
    (ht : ∀ v, p v ∈ G ↔ v ∈ t) :
    F ⊂ G ↔ s ⊂ t := by
  rw [ssubset_iff_subset_ne, Finset.ssubset_iff_subset_ne]
  exact and_congr (face_subset_iff_labels P p hp hF hG s t hs ht)
    (not_congr (face_eq_iff_labels P p hp hF hG s t hs ht))

/-- Five strictly nested nonempty faces in four-space must have dimensions
zero, one, two, three and four.  Thus incidence flags suffice to certify
dimensions without introducing a numerical rank assertion. -/
theorem dimension_of_five_face_flag (P : ConvexPolytope 4)
    (F : Fin 5 → Set (E 4)) (hF : ∀ i, P.IsFace (F i))
    (h01 : F 0 ⊂ F 1) (h12 : F 1 ⊂ F 2)
    (h23 : F 2 ⊂ F 3) (h34 : F 3 ⊂ F 4) :
    ∀ i : Fin 5, faceDim (F i) = (i : ℕ) := by
  have hd01 := faceDim_lt_of_ssubset P (hF 0) (hF 1) h01
  have hd12 := faceDim_lt_of_ssubset P (hF 1) (hF 2) h12
  have hd23 := faceDim_lt_of_ssubset P (hF 2) (hF 3) h23
  have hd34 := faceDim_lt_of_ssubset P (hF 3) (hF 4) h34
  have htop : faceDim (F 4) ≤ 4 := by
    change Module.finrank ℝ (vectorSpan ℝ (F 4)) ≤ 4
    have h := Submodule.finrank_le (vectorSpan ℝ (F 4))
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using h
  intro i
  fin_cases i
  · change faceDim (F 0) = 0
    omega
  · change faceDim (F 1) = 1
    omega
  · change faceDim (F 2) = 2
    omega
  · change faceDim (F 3) = 3
    omega
  · change faceDim (F 4) = 4
    omega

end CubicalIndecomposability
