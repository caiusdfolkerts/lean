module

public import triangulation
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Between

/-! Exact geometric intersections of all subfaces of the stored triangles. -/

@[expose] public section

namespace NormalProjective.Planar

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

theorem image_face_independent {s : Finset V} (hs : s ∈ T.faces) :
    AffineIndependent ℝ ((↑) : (s.image T.point) → ℂ) := by
  classical
  have h := (T.face_independent s hs).range
  have heq : Set.range (fun v : s => T.point v) = (s.image T.point : Set ℂ) := by
    ext z
    simp
  change AffineIndependent ℝ (fun x : ↥(s.image T.point : Set ℂ) => (x : ℂ))
  rw [← heq]
  exact h

theorem same_face_subface_intersection {s a b : Finset V} (hs : s ∈ T.faces)
    (ha : a ⊆ s) (hb : b ⊆ s) :
    simplex T.point a ∩ simplex T.point b = simplex T.point (a ∩ b) := by
  classical
  have h := (T.image_face_independent hs).convexHull_inter
    (Finset.image_subset_image ha) (Finset.image_subset_image hb)
  rw [← Finset.coe_inter,← Finset.image_inter _ _ T.point_injective] at h
  simpa only [simplex,Finset.coe_image] using h.symm

/-- Pairwise gluing for triangles implies pairwise gluing for every pair of
their subfaces. Both applications of affine independence are explicit. -/
theorem subface_intersection {s t a b : Finset V}
    (hs : s ∈ T.faces) (ht : t ∈ T.faces) (ha : a ⊆ s) (hb : b ⊆ t) :
    simplex T.point a ∩ simplex T.point b = simplex T.point (a ∩ b) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hsx : x ∈ simplex T.point s := convexHull_mono (image_mono ha) hx.1
    have htx : x ∈ simplex T.point t := convexHull_mono (image_mono hb) hx.2
    have hist : x ∈ simplex T.point (s ∩ t) :=
      T.intersection s hs t ht ▸ And.intro hsx htx
    have haint : x ∈ simplex T.point (a ∩ (s ∩ t)) :=
      T.same_face_subface_intersection hs ha Finset.inter_subset_left ▸ And.intro hx.1 hist
    have haint' : x ∈ simplex T.point (a ∩ t) := by
      have heq : a ∩ (s ∩ t) = a ∩ t := by
        ext v
        simp only [Finset.mem_inter]
        exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,ha h.1,h.2⟩⟩
      rwa [heq] at haint
    have hlast : x ∈ simplex T.point ((a ∩ t) ∩ b) :=
      T.same_face_subface_intersection ht Finset.inter_subset_right hb ▸ And.intro haint' hx.2
    have heq : (a ∩ t) ∩ b = a ∩ b := by
      ext v
      simp only [Finset.mem_inter]
      exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hb h.2⟩,h.2⟩⟩
    rwa [heq] at hlast
  · exact fun x hx => ⟨convexHull_mono (image_mono Finset.inter_subset_left) hx,
      convexHull_mono (image_mono Finset.inter_subset_right) hx⟩

theorem simplex_pair (a b : V) :
    simplex T.point {a,b} = segment ℝ (T.point a) (T.point b) := by
  simp [simplex,Set.image_pair,convexHull_pair]

theorem edge_intersection {a b c d : V}
    (hab : T.graph.Adj a b) (hcd : T.graph.Adj c d) :
    segment ℝ (T.point a) (T.point b) ∩ segment ℝ (T.point c) (T.point d) =
      simplex T.point ({a,b} ∩ {c,d}) := by
  obtain ⟨_,s,hs,ha,hb⟩ := hab
  obtain ⟨_,t,ht,hc,hd⟩ := hcd
  rw [← T.simplex_pair,← T.simplex_pair]
  exact T.subface_intersection (a := {a,b}) (b := {c,d}) hs ht
    (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro ha hb)
    (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hc hd)

theorem point_mem_simplex_iff {s a : Finset V} (hs : s ∈ T.faces)
    (ha : a ⊆ s) (v : V) : T.point v ∈ simplex T.point a ↔ v ∈ a := by
  constructor
  · intro hv
    obtain ⟨t,ht,hvt⟩ := T.vertex_covered v
    have hx : T.point v ∈ simplex T.point ({v} ∩ a) := by
      rw [← T.subface_intersection ht hs (by simpa using hvt) ha]
      exact ⟨by simp [simplex],hv⟩
    by_contra hva
    have hempty : ({v} : Finset V) ∩ a = ∅ := by simp [hva]
    simpa [hempty,simplex] using hx
  · exact point_mem_simplex T.point a

theorem point_mem_edge_iff {a b : V} (hab : T.graph.Adj a b) (v : V) :
    T.point v ∈ segment ℝ (T.point a) (T.point b) ↔ v = a ∨ v = b := by
  obtain ⟨_,s,hs,ha,hb⟩ := hab
  rw [← T.simplex_pair,T.point_mem_simplex_iff (a := {a,b}) hs
    (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro ha hb)]
  simp

end Triangulation

end NormalProjective.Planar
