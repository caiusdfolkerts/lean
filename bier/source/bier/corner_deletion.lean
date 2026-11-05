import bier.corner_coordinates

/-! Actual faces after deleting a vertex with a simplicial corner. -/

noncomputable section
namespace Bier
open Classical Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {n : ℕ}

def ProperVertexFace (P : ConvexPolytope n) (s : Finset (VertexType P)) : Prop :=
  P.IsFace (vertexHull P s) ∧ vertexHull P s ≠ P.toSet

theorem vertexHull_subset (P : ConvexPolytope n) (s : Finset (VertexType P)) :
    vertexHull P s ⊆ P.toSet := convexHull_mono (by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  exact v.property)

theorem vertexHull_eq_top_iff (P : ConvexPolytope n) (s : Finset (VertexType P)) :
    vertexHull P s = P.toSet ↔ s = Finset.univ := by
  constructor
  · intro h
    apply Finset.eq_univ_of_forall
    intro v
    rw [← faceVertices_vertexHull P s, mem_faceVertices, h]
    exact subset_convexHull ℝ _ v.property
  · rintro rfl
    unfold vertexHull ConvexPolytope.toSet
    congr 1
    ext x
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨v, hv⟩ => hv ▸ v.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

theorem properVertexFace_boundary (P : ConvexPolytope n) {s : Finset (VertexType P)}
    (h : ProperVertexFace P s) : ∃ t ∈ boundaryFacets P, s ⊆ t := by
  have hlt : faceDim (vertexHull P s) < P.dim := faceDim_lt_of_ssubset P h.1
    (toSet_isFace P) ((vertexHull_subset P s).ssubset_of_ne h.2)
  obtain ⟨F, hF, hdF, hsF⟩ := face_contained_in_facet P h.1 hlt
  refine ⟨faceVertices P F, (mem_boundaryFacets P _).mpr ⟨⟨⟨F, hF⟩, hdF⟩, rfl⟩, ?_⟩
  intro v hv
  rw [mem_faceVertices]
  apply hsF
  rw [← mem_faceVertices, faceVertices_vertexHull]
  exact hv

theorem properVertexFace_card_le (P : ConvexPolytope n) (hs : IsSimplicial P)
    {s : Finset (VertexType P)} (h : ProperVertexFace P s) : s.card ≤ P.dim := by
  obtain ⟨t, ht, hst⟩ := properVertexFace_boundary P h
  exact (Finset.card_le_card hst).trans_eq (boundaryFacets_pure P hs t ht)

theorem properVertexFace_affineIndependent (P : ConvexPolytope n) (hs : IsSimplicial P)
    {s : Finset (VertexType P)} (h : ProperVertexFace P s) :
    AffineIndependent ℝ (fun v : s => v.val.val) := by
  obtain ⟨t, ht, hst⟩ := properVertexFace_boundary P h
  obtain ⟨F, rfl⟩ := (mem_boundaryFacets P t).mp ht
  let f : s ↪ VertexType (facePolytope P F.val.property) :=
    ⟨fun v => ⟨v.val.val, Finset.mem_filter.mpr ⟨v.val.property,
      (mem_faceVertices P F.val.val v.val).mp (hst v.property)⟩⟩,
      fun v w h => Subtype.ext (Subtype.ext (congrArg (fun x => x.val) h))⟩
  exact (hs _ F.val.property F.property).comp_embedding f

namespace CornerSystem
variable {P : ConvexPolytope n} {p : VertexType P} {T : Finset (VertexType P)}
    (C : CornerSystem P p T)

include C

theorem affineIndependent : AffineIndependent ℝ (fun i : T => i.val.val) := by
  have hli : LinearIndependent ℝ (fun i : T => i.val.val - p.val) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have hh := congrArg (C.functional i) ha
    simp only [map_sum, map_smul, map_zero, C.dual, smul_eq_mul] at hh
    simpa using hh
  have h := (affineIndependent_vadd ℝ (p := fun i : T => i.val.val - p.val)
    (v := p.val)).mpr hli.affineIndependent
  convert h using 1
  funext i
  change i.val.val = p.val + (i.val.val - p.val)
  abel

abbrev deleted (_C : CornerSystem P p T) (hne : (P.vertices.erase p.val).Nonempty) :=
  deleteVertex P p hne
abbrev inclusion (C : CornerSystem P p T) (hne : (P.vertices.erase p.val).Nonempty) :
    VertexType (C.deleted hne) ↪ VertexType P := deleteVertexEmbedding P p hne

variable (hne : (P.vertices.erase p.val).Nonempty)

def oldVertex (w : VertexType P) (hw : w ≠ p) : VertexType (C.deleted hne) :=
  ⟨w.val, Finset.mem_erase.mpr ⟨fun h => hw (Subtype.ext h), w.property⟩⟩

@[simp] theorem inclusion_oldVertex (w : VertexType P) (hw : w ≠ p) :
    C.inclusion hne (C.oldVertex hne w hw) = w := rfl

theorem inclusion_ne (w : VertexType (C.deleted hne)) : C.inclusion hne w ≠ p := by
  intro h
  exact (Finset.mem_erase.mp w.property).1 (congrArg Subtype.val h)

theorem hull_map (s : Finset (VertexType (C.deleted hne))) :
    vertexHull P (s.map (C.inclusion hne)) = vertexHull (C.deleted hne) s := by
  unfold vertexHull
  have he : (s.map (C.inclusion hne)).image (fun v => v.val) = s.image (fun v => v.val) := by
    rw [Finset.map_eq_image, Finset.image_image]
    rfl
  rw [he]

/-- Every old supporting face remains exposed after deleting the corner vertex. -/
theorem face_of_old {s : Finset (VertexType (C.deleted hne))} (hs : s.Nonempty)
    (h : P.IsFace (vertexHull P (s.map (C.inclusion hne)))) :
    (C.deleted hne).IsFace (vertexHull (C.deleted hne) s) := by
  obtain ⟨l, c, hle, heq⟩ := face_vertex_exposer P h
  apply vertexHull_exposed (C.deleted hne) s hs l c
  · intro w
    exact hle (C.inclusion hne w)
  · intro w
    rw [← deleteVertexEmbedding_val P p hne w, heq, ← mem_faceVertices,
      faceVertices_vertexHull]
    simp

/-- A supporting face on the far side of the deleted vertex lies in the new base. -/
theorem face_below_base {s : Finset (VertexType (C.deleted hne))}
    (l : E n →L[ℝ] ℝ) (c : ℝ) (hp : c < l p.val)
    (hle : ∀ w : VertexType (C.deleted hne), l w.val ≤ c)
    (heq : ∀ w : VertexType (C.deleted hne), l w.val = c ↔ w ∈ s)
    (hTp : p ∉ T) : s.map (C.inclusion hne) ⊆ T := by
  intro w hw
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
  by_contra hqT
  have hout : C.inclusion hne q ∉ insert p T := by
    simpa only [Finset.mem_insert, not_or] using ⟨C.inclusion_ne hne q, hqT⟩
  have hheight := C.height_gt_one_of_outside _ hout
  have hcoeff : ∀ i : T, l (i.val.val - p.val) ≤ c - l p.val := by
    intro i
    have hip : i.val ≠ p := fun h => hTp (h ▸ i.property)
    rw [map_sub]
    exact sub_le_sub_right (hle (C.oldVertex hne i.val hip)) (l p.val)
  have hsum := Finset.sum_le_sum (fun (i : T) (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hcoeff i) (C.nonneg i (C.inclusion hne q)))
  have hrecon := congrArg l (C.reconstruction q.val (subset_convexHull ℝ _
    (C.inclusion hne q).property))
  simp only [map_sum, map_smul, smul_eq_mul] at hrecon
  change (∑ i : T, C.functional i (q.val - p.val) * l (i.val.val - p.val)) ≤
    ∑ i : T, C.functional i (q.val - p.val) * (c - l p.val) at hsum
  rw [← Finset.sum_mul, ← C.height_apply, ← hrecon, map_sub] at hsum
  have hval := (heq q).mpr hq
  change 1 < C.height (q.val - p.val) at hheight
  nlinarith

/-- Exact alternatives for a proper exposed face of the deleted hull. -/
theorem proper_face_alternatives
    (hTp : p ∉ T)
    (hcontaining : ∀ a, ProperVertexFace P a → p ∈ a → a ⊆ insert p T)
    {s : Finset (VertexType (C.deleted hne))} (hs : s.Nonempty)
    (hface : ProperVertexFace (C.deleted hne) s) :
    ProperVertexFace P (s.map (C.inclusion hne)) ∨ s.map (C.inclusion hne) ⊆ T := by
  obtain ⟨l, c, hle, heq0⟩ := face_vertex_exposer (C.deleted hne) hface.1
  have heq : ∀ w : VertexType (C.deleted hne), l w.val = c ↔ w ∈ s := by
    intro w
    rw [heq0, ← mem_faceVertices, faceVertices_vertexHull]
  by_cases hp : l p.val ≤ c
  · let a := Finset.univ.filter (fun w : VertexType P => l w.val = c)
    have hPa : P.IsFace (vertexHull P a) := by
      apply vertexHull_exposed P a ?_ l c ?_ ?_
      · obtain ⟨w, hw⟩ := hs
        exact ⟨C.inclusion hne w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (heq w).mpr hw⟩⟩
      · intro w
        by_cases hwp : w = p
        · simpa only [hwp] using hp
        · exact hle (C.oldVertex hne w hwp)
      · intro w
        simp [a]
    have hproper : ProperVertexFace P a := by
      refine ⟨hPa, ?_⟩
      intro htop
      have ha := (vertexHull_eq_top_iff P a).mp htop
      apply hface.2
      rw [vertexHull_eq_top_iff]
      apply Finset.eq_univ_of_forall
      intro w
      apply (heq w).mp
      have hw : C.inclusion hne w ∈ a := ha ▸ Finset.mem_univ _
      exact (Finset.mem_filter.mp hw).2
    by_cases he : l p.val = c
    · right
      have hpa : p ∈ a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
      intro w hw
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
      have hqa : C.inclusion hne q ∈ a := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (heq q).mpr hq⟩
      exact (Finset.mem_insert.mp (hcontaining a hproper hpa hqa)).resolve_left
        (C.inclusion_ne hne q)
    · left
      have ha : a = s.map (C.inclusion hne) := by
        ext w
        constructor
        · intro hw
          have hwc := (Finset.mem_filter.mp hw).2
          have hwp : w ≠ p := fun h => he (h ▸ hwc)
          exact Finset.mem_map.mpr ⟨C.oldVertex hne w hwp, (heq _).mp hwc, rfl⟩
        · intro hw
          obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (heq q).mpr hq⟩
      rwa [ha] at hproper
  · right
    exact C.face_below_base hne l c (lt_of_not_ge hp) hle heq hTp

end CornerSystem
end Bier
