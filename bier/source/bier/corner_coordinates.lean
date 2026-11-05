import bier.delete_vertex

/-! Supporting corner facets give honest affine coordinates on the whole polytope. -/

noncomputable section

namespace Bier

open Classical Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {n : ℕ}

structure CornerSystem (P : ConvexPolytope n) (p : VertexType P)
    (T : Finset (VertexType P)) where
  functional : T → E n →L[ℝ] ℝ
  nonneg : ∀ i (w : VertexType P), 0 ≤ functional i (w.val - p.val)
  dual : ∀ i j : T, functional i (j.val.val - p.val) = if i = j then 1 else 0
  reconstruction : ∀ x ∈ P.toSet,
    x - p.val = ∑ i : T, functional i (x - p.val) • (i.val.val - p.val)

theorem exists_cornerSystem (P : ConvexPolytope n) (p : VertexType P)
    (T : Finset (VertexType P)) (hp : p ∉ T) (hdim : P.dim = T.card)
    (hcorner : ∀ i ∈ T, P.IsFace (vertexHull P (insert p (T.erase i)))) :
    Nonempty (CornerSystem P p T) := by
  have hex : ∀ i : T, ∃ q : E n →L[ℝ] ℝ,
      (∀ w : VertexType P, 0 ≤ q (w.val - p.val)) ∧
      ∀ j : T, q (j.val.val - p.val) = if i = j then 1 else 0 := by
    intro i
    obtain ⟨l, c, hle, heq⟩ := face_vertex_exposer P (hcorner i i.property)
    have hmem : ∀ w : VertexType P,
        w.val ∈ vertexHull P (insert p (T.erase i.val)) ↔ w ∈ insert p (T.erase i.val) := by
      intro w
      rw [← mem_faceVertices, faceVertices_vertexHull]
    have hlp : l p.val = c := (heq p).mpr ((hmem p).mpr (Finset.mem_insert_self _ _))
    have hli : l i.val.val < c := lt_of_le_of_ne (hle i.val) (by
      intro h
      have hh := (hmem i.val).mp ((heq i.val).mp h)
      have hip : i.val ≠ p := fun h => hp (h ▸ i.property)
      simpa [hip] using hh)
    let d := c - l i.val.val
    have hd : 0 < d := sub_pos.mpr hli
    let q : E n →L[ℝ] ℝ := (-d⁻¹) • l
    refine ⟨q, ?_, ?_⟩
    · intro w
      change 0 ≤ -d⁻¹ * l (w.val - p.val)
      rw [map_sub, hlp]
      have he : -d⁻¹ * (l w.val - c) = d⁻¹ * (c - l w.val) := by ring
      rw [he]
      exact mul_nonneg (inv_nonneg.mpr hd.le) (sub_nonneg.mpr (hle w))
    · intro j
      by_cases hij : i = j
      · subst j
        rw [if_pos rfl]
        change -d⁻¹ * l (i.val.val - p.val) = 1
        rw [map_sub, hlp]
        have he : l i.val.val - c = -d := by dsimp [d]; ring
        rw [he, neg_mul_neg, inv_mul_cancel₀ hd.ne']
      · rw [if_neg hij]
        have hji : j.val ≠ i.val := fun h => hij (Subtype.ext h.symm)
        have hjmem : j.val ∈ insert p (T.erase i.val) :=
          Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hji, j.property⟩)
        have hlj : l j.val.val = c := (heq j.val).mpr ((hmem j.val).mpr hjmem)
        change -d⁻¹ * l (j.val.val - p.val) = 0
        rw [map_sub, hlj, hlp, sub_self, mul_zero]
  choose q hnonneg hdual using hex
  let b : T → E n := fun i => i.val.val - p.val
  have hLI : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hh := congrArg (q i) ha
    simp only [map_sum, map_smul, map_zero, b, hdual, smul_eq_mul] at hh
    simpa using hh
  have hsub : Submodule.span ℝ (Set.range b) ≤ vectorSpan ℝ P.toSet := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact vsub_mem_vectorSpan ℝ (subset_convexHull ℝ _ i.val.property)
      (subset_convexHull ℝ _ p.property)
  have hspan : Submodule.span ℝ (Set.range b) = vectorSpan ℝ P.toSet := by
    apply Submodule.eq_of_le_of_finrank_le hsub
    rw [finrank_span_eq_card hLI, Fintype.card_coe]
    exact hdim.le
  refine ⟨⟨q, hnonneg, hdual, ?_⟩⟩
  intro x hx
  have hxspan : x - p.val ∈ Submodule.span ℝ (Set.range b) := by
    rw [hspan]
    exact vsub_mem_vectorSpan ℝ hx (subset_convexHull ℝ _ p.property)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hxspan
  have hcoeff : ∀ i, q i (x - p.val) = a i := by
    intro i
    have hh := congrArg (q i) ha
    simp only [map_sum, map_smul, b, hdual, smul_eq_mul] at hh
    simpa using hh.symm
  simp_rw [hcoeff]
  exact ha.symm

namespace CornerSystem

variable {P : ConvexPolytope n} {p : VertexType P} {T : Finset (VertexType P)}
  (C : CornerSystem P p T)

def height : E n →L[ℝ] ℝ := ∑ i : T, C.functional i

@[simp] theorem height_apply (x : E n) : C.height x = ∑ i : T, C.functional i x := by
  simp [height]

@[simp] theorem height_neighbor (i : T) : C.height (i.val.val - p.val) = 1 := by
  simp [height, C.dual]

theorem mem_corner_of_height_le (w : VertexType P) (hw : C.height (w.val - p.val) ≤ 1) :
    w ∈ insert p T := by
  let f : Option T → E n := fun a => a.elim p.val (fun i => i.val.val)
  let μ : Option T → ℝ := fun a => a.elim (1 - C.height (w.val - p.val))
    (fun i => C.functional i (w.val - p.val))
  have hμ : ∀ a : Option T, 0 ≤ μ a := by
    intro a
    cases a with
    | none => exact sub_nonneg.mpr hw
    | some i => exact C.nonneg i w
  have hsum : ∑ a : Option T, μ a = 1 := by
    simp [μ, Fintype.sum_option, height]
  have hvec : ∑ a : Option T, μ a • f a = w.val := by
    simp only [Fintype.sum_option, μ, f, Option.elim_none, Option.elim_some]
    have hrecon := C.reconstruction w.val (subset_convexHull ℝ _ w.property)
    simp_rw [smul_sub] at hrecon
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul] at hrecon
    rw [← C.height_apply] at hrecon
    rw [sub_smul, one_smul]
    calc
      _ = (∑ i : T, C.functional i (w.val - p.val) • i.val.val -
          C.height (w.val - p.val) • p.val) + p.val := by abel
      _ = (w.val - p.val) + p.val := by rw [← hrecon]
      _ = w.val := sub_add_cancel _ _
  have hmem : w.val ∈ vertexHull P (insert p T) := by
    rw [← hvec]
    apply (convex_convexHull ℝ _).sum_mem (fun a _ => hμ a) hsum
    intro a _
    apply subset_convexHull ℝ _
    cases a with
    | none => exact Finset.mem_image.mpr ⟨p, Finset.mem_insert_self _ _, rfl⟩
    | some i => exact Finset.mem_image.mpr ⟨i.val, Finset.mem_insert_of_mem i.property, rfl⟩
  have hm := (mem_faceVertices P (vertexHull P (insert p T)) w).mpr hmem
  rwa [faceVertices_vertexHull] at hm

theorem height_gt_one_of_outside (w : VertexType P) (hw : w ∉ insert p T) :
    1 < C.height (w.val - p.val) := lt_of_not_ge (fun h => hw (C.mem_corner_of_height_le w h))

end CornerSystem
end Bier
