import bier.corner_deletion

/-! The new exposed simplex and complete proper-face correspondence after deletion. -/
noncomputable section
namespace Bier
open Classical Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {n : ℕ}
namespace CornerSystem
variable {P : ConvexPolytope n} {p : VertexType P} {T : Finset (VertexType P)}
    (C : CornerSystem P p T) (hne : (P.vertices.erase p.val).Nonempty)

def base : Finset (VertexType (C.deleted hne)) :=
  Finset.univ.filter (fun w => C.inclusion hne w ∈ T)

@[simp] theorem mem_base (w : VertexType (C.deleted hne)) :
    w ∈ C.base hne ↔ C.inclusion hne w ∈ T := by simp [base]

theorem base_map (hp : p ∉ T) : (C.base hne).map (C.inclusion hne) = T := by
  ext w
  constructor
  · intro hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
    exact (C.mem_base hne q).mp hq
  · intro hw
    have hwp : w ≠ p := fun he => hp (he ▸ hw)
    exact Finset.mem_map.mpr ⟨C.oldVertex hne w hwp, (C.mem_base hne _).mpr hw, rfl⟩

theorem base_nonempty (hp : p ∉ T) (hT : T.Nonempty) : (C.base hne).Nonempty := by
  rw [← C.base_map hne hp] at hT
  exact Finset.map_nonempty.mp hT

theorem height_ge_one (w : VertexType (C.deleted hne)) :
    1 ≤ C.height (w.val - p.val) := by
  by_cases hw : C.inclusion hne w ∈ T
  · have hh := C.height_neighbor ⟨C.inclusion hne w, hw⟩
    exact hh.ge
  · have hout : C.inclusion hne w ∉ insert p T := by
      simpa only [Finset.mem_insert, not_or] using ⟨C.inclusion_ne hne w, hw⟩
    exact (C.height_gt_one_of_outside _ hout).le

theorem height_eq_one_iff (w : VertexType (C.deleted hne)) :
    C.height (w.val - p.val) = 1 ↔ w ∈ C.base hne := by
  rw [C.mem_base]
  constructor
  · intro hh
    have hm := C.mem_corner_of_height_le (C.inclusion hne w) hh.le
    exact (Finset.mem_insert.mp hm).resolve_left (C.inclusion_ne hne w)
  · intro hw
    exact C.height_neighbor ⟨C.inclusion hne w, hw⟩

theorem base_face (hp : p ∉ T) (hT : T.Nonempty) :
    (C.deleted hne).IsFace (vertexHull (C.deleted hne) (C.base hne)) := by
  apply vertexHull_exposed (C.deleted hne) (C.base hne) (C.base_nonempty hne hp hT)
    (-C.height) (-1 - C.height p.val)
  · intro w
    have hh := C.height_ge_one hne w
    rw [map_sub] at hh
    change -C.height w.val ≤ -1 - C.height p.val
    linarith
  · intro w
    change -C.height w.val = -1 - C.height p.val ↔ w ∈ C.base hne
    rw [← C.height_eq_one_iff hne w, map_sub]
    constructor <;> intro h <;> linarith

theorem base_affineIndependent (hp : p ∉ T) (hT : T.Nonempty) :
    AffineIndependent ℝ (fun w : VertexType
      (facePolytope (C.deleted hne) (C.base_face hne hp hT)) => w.val) := by
  let f : VertexType (facePolytope (C.deleted hne) (C.base_face hne hp hT)) ↪ T :=
    { toFun := fun w => by
        let q : VertexType (C.deleted hne) := ⟨w.val, (Finset.mem_filter.mp w.property).1⟩
        have hq : q ∈ C.base hne := by
          rw [← faceVertices_vertexHull (C.deleted hne) (C.base hne), mem_faceVertices]
          exact (Finset.mem_filter.mp w.property).2
        exact ⟨C.inclusion hne q, (C.mem_base hne q).mp hq⟩
      inj' := by
        intro w z hz
        exact Subtype.ext (congrArg (fun q : T => q.val.val) hz) }
  exact C.affineIndependent.comp_embedding f

theorem base_proper (hp : p ∉ T) (hT : T.Nonempty)
    (hout : ∃ w : VertexType P, w ∉ insert p T) :
    ProperVertexFace (C.deleted hne) (C.base hne) := by
  refine ⟨C.base_face hne hp hT, ?_⟩
  obtain ⟨w, hw⟩ := hout
  have hwp : w ≠ p := fun he => hw (he ▸ Finset.mem_insert_self _ _)
  intro he
  have hall := (vertexHull_eq_top_iff (C.deleted hne) (C.base hne)).mp he
  have hm : C.oldVertex hne w hwp ∈ C.base hne := hall ▸ Finset.mem_univ _
  exact hw (Finset.mem_insert_of_mem ((C.mem_base hne _).mp hm))

theorem subset_base_proper (hp : p ∉ T) (hT : T.Nonempty)
    (hout : ∃ w : VertexType P, w ∉ insert p T)
    {s : Finset (VertexType (C.deleted hne))} (hs : s.Nonempty)
    (hst : s.map (C.inclusion hne) ⊆ T) : ProperVertexFace (C.deleted hne) s := by
  have hsb : s ⊆ C.base hne := by
    intro w hw
    exact (C.mem_base hne _).mpr (hst (Finset.mem_map.mpr ⟨w, hw, rfl⟩))
  have hb := C.base_proper hne hp hT hout
  refine ⟨face_subset_simplex_isFace (C.deleted hne) hb.1
    (C.base_affineIndependent hne hp hT) s ?_ hs, ?_⟩
  · rwa [faceVertices_vertexHull]
  · intro htop
    apply hb.2
    apply Set.Subset.antisymm (vertexHull_subset _ _)
    rw [← htop]
    exact vertexHull_mono _ hsb

theorem proper_of_old (hPs : IsSimplicial P) (hdim : P.dim = T.card)
    (hp : p ∉ T) (hT : T.Nonempty) (hout : ∃ w : VertexType P, w ∉ insert p T)
    {s : Finset (VertexType (C.deleted hne))} (hs : s.Nonempty)
    (h : ProperVertexFace P (s.map (C.inclusion hne))) :
    ProperVertexFace (C.deleted hne) s := by
  refine ⟨C.face_of_old hne hs h.1, ?_⟩
  have hcard := properVertexFace_card_le P hPs h
  rw [Finset.card_map, hdim] at hcard
  have hbase : C.base hne ≠ Finset.univ := by
    intro he
    exact (C.base_proper hne hp hT hout).2
      ((vertexHull_eq_top_iff (C.deleted hne) (C.base hne)).mpr he)
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ (C.base hne), hbase⟩)
  have he : (C.base hne).card = T.card := by
    simpa only [Finset.card_map] using congrArg Finset.card (C.base_map hne hp)
  rw [he] at hlt
  intro htop
  have hsall := (vertexHull_eq_top_iff (C.deleted hne) s).mp htop
  rw [hsall] at hcard
  omega

theorem proper_face_iff (hPs : IsSimplicial P) (hdim : P.dim = T.card)
    (hp : p ∉ T) (hT : T.Nonempty) (hout : ∃ w : VertexType P, w ∉ insert p T)
    (hcontaining : ∀ a, ProperVertexFace P a → p ∈ a → a ⊆ insert p T)
    {s : Finset (VertexType (C.deleted hne))} (hs : s.Nonempty) :
    ProperVertexFace (C.deleted hne) s ↔
      ProperVertexFace P (s.map (C.inclusion hne)) ∨ s.map (C.inclusion hne) ⊆ T := by
  constructor
  · exact C.proper_face_alternatives hne hp hcontaining hs
  · rintro (ho | ht)
    · exact C.proper_of_old hne hPs hdim hp hT hout hs ho
    · exact C.subset_base_proper hne hp hT hout hs ht

theorem proper_affineIndependent (hPs : IsSimplicial P)
    (hp : p ∉ T)
    (hcontaining : ∀ a, ProperVertexFace P a → p ∈ a → a ⊆ insert p T)
    {s : Finset (VertexType (C.deleted hne))} (hs : s.Nonempty)
    (h : ProperVertexFace (C.deleted hne) s) :
    AffineIndependent ℝ (fun v : s => v.val.val) := by
  rcases C.proper_face_alternatives hne hp hcontaining hs h with ho | ht
  · let f : s ↪ (s.map (C.inclusion hne)) :=
      ⟨fun v => ⟨C.inclusion hne v.val, Finset.mem_map.mpr ⟨v.val, v.property, rfl⟩⟩,
        fun v w h => Subtype.ext ((C.inclusion hne).injective (congrArg Subtype.val h))⟩
    exact (properVertexFace_affineIndependent P hPs ho).comp_embedding f
  · let f : s ↪ T :=
      ⟨fun v => ⟨C.inclusion hne v.val, ht (Finset.mem_map.mpr ⟨v.val, v.property, rfl⟩)⟩,
        fun v w h => Subtype.ext ((C.inclusion hne).injective (congrArg Subtype.val h))⟩
    exact C.affineIndependent.comp_embedding f

end CornerSystem
end Bier
