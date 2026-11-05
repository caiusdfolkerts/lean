module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# A crossing center inside a polytope

This file uses the ordinary exposed-segment and extreme-point properties of
actual polytope edges and vertices.  It proves the geometric classification
before any counting or graph connectivity is invoked.
-/

namespace Papers.Polytopes.ExposedEdgeCenters

variable {V I : Type*} [AddCommGroup V] [Module ℝ V]

def point (x : V) : V × ℝ := (x, 1)

def edgeLine (x y : V) : Submodule ℝ (V × ℝ) :=
  Submodule.span ℝ ({point x, point y} : Set (V × ℝ))

theorem convex_point_image (C : Set V) (hC : Convex ℝ C) :
    Convex ℝ (point '' C) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hC hx hy ha hb hab, ?_⟩
  apply Prod.ext
  · rfl
  · change 1 = a * 1 + b * 1
    simpa using hab.symm

/-- Homogeneous linear extension of an ordinary affine form. -/
def affineForm (g : V →ᵃ[ℝ] ℝ) : (V × ℝ) →ₗ[ℝ] ℝ where
  toFun p := g.linear p.1 + p.2 * g 0
  map_add' p q := by
    change g.linear (p.1 + q.1) + (p.2 + q.2) * g 0 =
      (g.linear p.1 + p.2 * g 0) + (g.linear q.1 + q.2 * g 0)
    rw [map_add]
    ring
  map_smul' c p := by
    change g.linear (c • p.1) + (c * p.2) * g 0 =
      c * (g.linear p.1 + p.2 * g 0)
    rw [map_smul]
    change c * g.linear p.1 + (c * p.2) * g 0 =
      c * (g.linear p.1 + p.2 * g 0)
    ring

@[simp]
theorem affineForm_point (g : V →ᵃ[ℝ] ℝ) (x : V) :
    affineForm g (point x) = g x := by
  change g.linear x + 1 * g 0 = g x
  rw [one_mul]
  simpa only [vadd_eq_add, add_zero] using (g.map_vadd (0 : V) x).symm


theorem point_weighted_sum (x y : V) (a b : ℝ) (hab : a + b = 1) :
    point (a • x + b • y) = a • point x + b • point y := by
  apply Prod.ext
  · rfl
  · change 1 = a * 1 + b * 1
    simpa using hab.symm

theorem affine_apply_weighted_sum
    (g : V →ᵃ[ℝ] ℝ) (x y : V) (a b : ℝ) (hab : a + b = 1) :
    g (a • x + b • y) = a * g x + b * g y := by
  rw [← affineForm_point, point_weighted_sum x y a b hab, map_add,
    map_smul, map_smul, affineForm_point, affineForm_point]
  rfl

/-- An actual nonnegative affine support exposing a segment makes that
segment an extreme subset of the convex body. -/
theorem isExtreme_segment_of_affine_support
    (C : Set V) (hC : Convex ℝ C) (g : V →ᵃ[ℝ] ℝ)
    {x y : V} (hx : x ∈ C) (hy : y ∈ C)
    (hnonneg : ∀ z ∈ C, 0 ≤ g z)
    (hzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ x y) :
    IsExtreme ℝ C (segment ℝ x y) := by
  have hsub : segment ℝ x y ⊆ C := by
    rintro z ⟨a,b,ha,hb,hab,rfl⟩
    exact hC hx hy ha hb hab
  refine ⟨hsub, ?_⟩
  intro u hu v hv z hz hzopen
  obtain ⟨a,b,ha,hb,hab,habz⟩ := hzopen
  have hgz : g z = 0 := (hzero z (hsub hz)).mpr hz
  have hsum : a * g u + b * g v = 0 := by
    rw [← affine_apply_weighted_sum g u v a b hab, habz]
    exact hgz
  have hgu : g u = 0 := by
    by_contra hne
    have hpositive : 0 < a * g u :=
      mul_pos ha (lt_of_le_of_ne (hnonneg u hu) (by intro h; exact hne h.symm))
    have hsecond : 0 ≤ b * g v := mul_nonneg hb.le (hnonneg v hv)
    linarith
  exact (hzero u hu).mp hgu

theorem point_ne_zero (x : V) : point x ≠ 0 := by
  intro h
  have := congrArg Prod.snd h
  norm_num [point] at this

theorem edgeLine_le_ker_affineForm
    (g : V →ᵃ[ℝ] ℝ) {x y : V} (hx : g x = 0) (hy : g y = 0) :
    edgeLine x y ≤ (affineForm g).ker := by
  refine Submodule.span_le.mpr ?_
  intro w hw
  rcases Set.mem_insert_iff.mp hw with rfl | hw
  · change affineForm g (point x) = 0
    simpa using hx
  · have hw' : w = point y := Set.mem_singleton_iff.mp hw
    subst w
    change affineForm g (point y) = 0
    simpa using hy

theorem edgeLine_comm (x y : V) : edgeLine x y = edgeLine y x := by
  simp only [edgeLine, Set.pair_comm]

theorem affine_eq_zero_on_edgeLine
    (g : V →ᵃ[ℝ] ℝ) {x y z : V}
    (hx : g x = 0) (hy : g y = 0)
    (hz : point z ∈ edgeLine x y) :
    g z = 0 := by
  have hle : edgeLine x y ≤ (affineForm g).ker := by
    refine Submodule.span_le.mpr ?_
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · change affineForm g (point x) = 0
      simpa using hx
    · have hw' : w = point y := Set.mem_singleton_iff.mp hw
      subst w
      change affineForm g (point y) = 0
      simpa using hy
  simpa using hle hz

/-- The center point belongs to the actual exposed edge, because its supporting
form vanishes on the whole homogeneous edge line. -/
theorem mem_segment_of_center_in_body
    (C : Set V) (g : V →ᵃ[ℝ] ℝ) {x y z : V}
    (hx : g x = 0) (hy : g y = 0)
    (hzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ x y)
    (hzC : z ∈ C) (hzline : point z ∈ edgeLine x y) :
    z ∈ segment ℝ x y :=
  (hzero z hzC).mp (affine_eq_zero_on_edgeLine g hx hy hzline)

theorem extreme_point_on_segment
    (C : Set V) {x y z : V}
    (hz : z ∈ C.extremePoints ℝ) (hx : x ∈ C) (hy : y ∈ C)
    (hsegment : z ∈ segment ℝ x y) :
    z = x ∨ z = y := by
  rcases (mem_extremePoints_iff_forall_segment.mp hz).2 x hx y hy hsegment with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem support_zero_iff_endpoint
    (C : Set V) (g : V →ᵃ[ℝ] ℝ) {x y : V}
    (hx : x ∈ C) (hy : y ∈ C)
    (hgx : g x = 0) (hgy : g y = 0)
    (hzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ x y)
    {z : V} (hz : z ∈ C.extremePoints ℝ) :
    g z = 0 ↔ z = x ∨ z = y := by
  constructor
  · intro hg
    exact extreme_point_on_segment C hz hx hy ((hzero z hz.1).mp hg)
  · rintro (rfl | rfl) <;> assumption


theorem endpoint_of_vertex_center
    (C : Set V) (g : V →ᵃ[ℝ] ℝ) {x y v : V}
    (hx : x ∈ C) (hy : y ∈ C) (hv : v ∈ C.extremePoints ℝ)
    (hgx : g x = 0) (hgy : g y = 0)
    (hzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ x y)
    (J : Submodule ℝ (V × ℝ))
    (hJline : J ≤ edgeLine x y) (hvJ : point v ∈ J) :
    v = x ∨ v = y := by
  exact (support_zero_iff_endpoint C g hx hy hgx hgy hzero hv).mp
    (affine_eq_zero_on_edgeLine g hgx hgy (hJline hvJ))

theorem endpoints_eq_of_shared_nonvertex
    (C : Set V) {x y u v z : V}
    (hx : x ∈ C.extremePoints ℝ) (hy : y ∈ C.extremePoints ℝ)
    (hu : u ∈ C.extremePoints ℝ) (hv : v ∈ C.extremePoints ℝ)
    (hxy : x ≠ y)
    (huv : IsExtreme ℝ C (segment ℝ u v))
    (hzxy : z ∈ segment ℝ x y) (hzuv : z ∈ segment ℝ u v)
    (hz : z ∉ C.extremePoints ℝ) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have hxz : x ≠ z := by
    intro h
    apply hz
    simpa [← h] using hx
  have hyz : y ≠ z := by
    intro h
    apply hz
    simpa [← h] using hy
  have hzopen : z ∈ openSegment ℝ x y :=
    mem_openSegment_of_ne_left_right hxz hyz hzxy
  have hxuv : x ∈ segment ℝ u v :=
    huv.left_mem_of_mem_openSegment hx.1 hy.1 hzuv hzopen
  have hyuv : y ∈ segment ℝ u v :=
    huv.right_mem_of_mem_openSegment hx.1 hy.1 hzuv hzopen
  have hxend := extreme_point_on_segment C hx hu.1 hv.1 hxuv
  have hyend := extreme_point_on_segment C hy hu.1 hv.1 hyuv
  rcases hxend with hxu | hxv <;> rcases hyend with hyu | hyv
  · exact (hxy (hxu.trans hyu.symm)).elim
  · exact Or.inl ⟨hxu, hyv⟩
  · exact Or.inr ⟨hxv, hyu⟩
  · exact (hxy (hxv.trans hyv.symm)).elim

/-- A family of actual edges containing one point is either a star at an
extreme point or consists of one unordered edge. -/
theorem star_or_single_edge_of_common_point
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (hextreme : ∀ i, IsExtreme ℝ C (segment ℝ (left i) (right i)))
    (z : V) (hz : ∀ i, z ∈ segment ℝ (left i) (right i)) :
    (z ∈ C.extremePoints ℝ ∧ ∀ i, z = left i ∨ z = right i) ∨
      (∀ i j, (left i = left j ∧ right i = right j) ∨
        (left i = right j ∧ right i = left j)) := by
  by_cases hzext : z ∈ C.extremePoints ℝ
  · exact Or.inl ⟨hzext, fun i =>
      extreme_point_on_segment C hzext (hl i).1 (hr i).1 (hz i)⟩
  · exact Or.inr (fun i j =>
      endpoints_eq_of_shared_nonvertex C (hl i) (hr i) (hl j) (hr j)
        (hne i) (hextreme j) (hz i) (hz j) hzext)

def CenterMeets (C : Set V) (J : Submodule ℝ (V × ℝ)) : Prop :=
  ∃ z ∈ C, point z ∈ J

/-- The inside-center classification for exposed edge lines. -/
theorem star_or_single_edge_of_center_meets
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (hextreme : ∀ i, IsExtreme ℝ C (segment ℝ (left i) (right i)))
    (support : I → V →ᵃ[ℝ] ℝ)
    (hsleft : ∀ i, support i (left i) = 0)
    (hsright : ∀ i, support i (right i) = 0)
    (hszero : ∀ i z, z ∈ C →
      (support i z = 0 ↔ z ∈ segment ℝ (left i) (right i)))
    (J : Submodule ℝ (V × ℝ))
    (hline : ∀ i, J ≤ edgeLine (left i) (right i))
    (hmeet : CenterMeets C J) :
    (∃ z ∈ C.extremePoints ℝ, point z ∈ J ∧
      ∀ i, z = left i ∨ z = right i) ∨
      (∀ i j, (left i = left j ∧ right i = right j) ∨
        (left i = right j ∧ right i = left j)) := by
  obtain ⟨z, hzC, hzJ⟩ := hmeet
  have hz (i : I) : z ∈ segment ℝ (left i) (right i) :=
    mem_segment_of_center_in_body C (support i) (hsleft i) (hsright i)
      (hszero i) hzC (hline i hzJ)
  rcases star_or_single_edge_of_common_point C left right hl hr hne hextreme z hz with
    ⟨hzext, hstar⟩ | hsingle
  · exact Or.inl ⟨z, hzext, hzJ, hstar⟩
  · exact Or.inr hsingle

/-- A projective center common to two disjoint actual edges is exterior.
This property survives every combinatorial realization of the matching. -/
theorem center_exterior_of_disjoint_edges
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (hextreme : ∀ i, IsExtreme ℝ C (segment ℝ (left i) (right i)))
    (support : I → V →ᵃ[ℝ] ℝ)
    (hsleft : ∀ i, support i (left i) = 0)
    (hsright : ∀ i, support i (right i) = 0)
    (hszero : ∀ i z, z ∈ C →
      (support i z = 0 ↔ z ∈ segment ℝ (left i) (right i)))
    (J : Submodule ℝ (V × ℝ))
    (hline : ∀ i, J ≤ edgeLine (left i) (right i))
    (i j : I)
    (hdisjoint : Disjoint ({left i, right i} : Set V) {left j, right j}) :
    ¬ CenterMeets C J := by
  intro hmeet
  rcases star_or_single_edge_of_center_meets C left right hl hr hne hextreme
    support hsleft hsright hszero J hline hmeet with hstar | hsingle
  · obtain ⟨z, -, -, hz⟩ := hstar
    have hzi : z ∈ ({left i, right i} : Set V) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz i
    have hzj : z ∈ ({left j, right j} : Set V) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz j
    exact Set.disjoint_left.mp hdisjoint hzi hzj
  · have hi : left i ∈ ({left i, right i} : Set V) := by simp
    have hj : left i ∈ ({left j, right j} : Set V) := by
      rcases hsingle i j with h | h <;> simp [h.1]
    exact Set.disjoint_left.mp hdisjoint hi hj


/-- Distinct actual edges can share a projective point in the body only at
an actual vertex. The statement also covers edges with a common endpoint. -/
theorem exterior_center_of_distinct_exposed_edges
    (C : Set V) (hC : Convex ℝ C) {x y u v : V}
    (hx : x ∈ C.extremePoints ℝ) (hy : y ∈ C.extremePoints ℝ)
    (hu : u ∈ C.extremePoints ℝ) (hv : v ∈ C.extremePoints ℝ)
    (hxy : x ≠ y)
    (g h : V →ᵃ[ℝ] ℝ)
    (hgx : g x = 0) (hgy : g y = 0)
    (hhu : h u = 0) (hhv : h v = 0)
    (hgn : ∀ z ∈ C, 0 ≤ h z)
    (hgzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ x y)
    (hhzero : ∀ z ∈ C, h z = 0 ↔ z ∈ segment ℝ u v)
    (hdistinct : ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)))
    (J : Submodule ℝ (V × ℝ))
    (hJxy : J ≤ edgeLine x y) (hJuv : J ≤ edgeLine u v)
    (hnotvertex : ∀ z ∈ C.extremePoints ℝ, point z ∉ J) :
    ¬ CenterMeets C J := by
  rintro ⟨z,hzC,hzJ⟩
  have hzxy : z ∈ segment ℝ x y :=
    mem_segment_of_center_in_body C g hgx hgy hgzero hzC (hJxy hzJ)
  have hzuv : z ∈ segment ℝ u v :=
    mem_segment_of_center_in_body C h hhu hhv hhzero hzC (hJuv hzJ)
  have hznot : z ∉ C.extremePoints ℝ := fun hz => hnotvertex z hz hzJ
  have hex := isExtreme_segment_of_affine_support C hC h hu.1 hv.1 hgn hhzero
  exact hdistinct
    (endpoints_eq_of_shared_nonvertex C hx hy hu hv hxy hex hzxy hzuv hznot)

theorem center_eq_vertex_line (J : Submodule ℝ (V × ℝ))
    (hJ : Module.finrank ℝ J = 1) {z : V} (hz : point z ∈ J) :
    J = Submodule.span ℝ ({point z} : Set (V × ℝ)) :=
  eq_span_singleton_of_mem_of_finrank_eq_one hJ hz (point_ne_zero z)

/-- For canonically oriented crossing edges, the nonvertex alternative really
contains at most one edge index. Opposite endpoints have different colors,
which supplies hcross. -/
theorem crossing_family_subsingleton_of_inside_nonvertex_center
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (hextreme : ∀ i, IsExtreme ℝ C (segment ℝ (left i) (right i)))
    (support : I → V →ᵃ[ℝ] ℝ)
    (hsleft : ∀ i, support i (left i) = 0)
    (hsright : ∀ i, support i (right i) = 0)
    (hszero : ∀ i z, z ∈ C →
      (support i z = 0 ↔ z ∈ segment ℝ (left i) (right i)))
    (J : Submodule ℝ (V × ℝ))
    (hline : ∀ i, J ≤ edgeLine (left i) (right i))
    (hnotvertex : ∀ z ∈ C.extremePoints ℝ, point z ∉ J)
    (hmeet : CenterMeets C J)
    (hcross : ∀ i j, left i ≠ right j)
    (hinj : Function.Injective fun i => (left i, right i)) :
    Subsingleton I := by
  rcases star_or_single_edge_of_center_meets C left right hl hr hne hextreme
    support hsleft hsright hszero J hline hmeet with hstar | hsingle
  · obtain ⟨z, hz, hzJ, -⟩ := hstar
    exact (hnotvertex z hz hzJ).elim
  · refine ⟨fun i j => ?_⟩
    rcases hsingle i j with h | h
    · exact hinj (Prod.ext h.1 h.2)
    · exact (hcross i j h.1).elim

end Papers.Polytopes.ExposedEdgeCenters

