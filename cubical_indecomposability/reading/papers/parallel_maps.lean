module
public import papers.polytope_targets
public import papers.finite_hull_certificates
public import cubical.polytope.balinski_generale

@[expose] public section

/-!
# Parallel maps on actual polytope edges

The edge relation is the geometric one: two distinct extreme vertices on an
exposed one-dimensional face. The local maximum principle is derived from
the finite face pivot, and all statements below concern this actual graph.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Pointwise RealInnerProductSpace
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def IsParallelMap (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∀ x ∈ P.vertices, ∀ y ∈ P.vertices, GeneralVertexStep P x y →
    ∃ c : ℝ, f y - f x = c • (y - x)

def IsPositiveParallelMap (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∀ x ∈ P.vertices, ∀ y ∈ P.vertices, GeneralVertexStep P x y →
    ∃ c : ℝ, 0 < c ∧ f y - f x = c • (y - x)

theorem IsPositiveParallelMap.parallel {P : ConvexPolytope d} {f : E d → E d}
    (h : IsPositiveParallelMap P f) : IsParallelMap P f := by
  intro x hx y hy hxy
  obtain ⟨c, _, hc⟩ := h x hx y hy hxy
  exact ⟨c, hc⟩

def IsHomothetyOnVertices (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∃ a : ℝ, ∃ b : E d, ∀ v ∈ P.vertices, f v = a • v + b

/-- Failure of a global linear maximum gives an actual increasing edge. -/
theorem exists_increasing_edge (P : ConvexPolytope d) (l : E d →L[ℝ] ℝ)
    {x z : E d} (hx : x ∈ P.vertices) (hz : z ∈ P.vertices) (hlt : l x < l z) :
    ∃ y : E d, GeneralVertexStep P x y ∧ l x < l y := by
  have hxFace : P.IsFace ({x} : Set (E d)) := vertex_isFace P hx
  obtain ⟨g, hg⟩ := hxFace.1 hxFace.2
  let w : E d := (InnerProductSpace.toDual ℝ (E d)).symm l
  have hw (y : E d) : inner ℝ w y = l y := InnerProductSpace.toDual_symm_apply
  have hconst : ∀ y ∈ ({x} : Set (E d)), inner ℝ w y = inner ℝ w x := by
    rintro y rfl
    rfl
  obtain ⟨F, hF, hproper, himprove⟩ := perno_parametrico_crescente_monotono
    P hxFace g hg x (Set.mem_singleton x) w hconst ⟨z, hz, by simpa only [hw] using hlt⟩
  have hdim : 1 ≤ faceDim F := by
    have h := faceDim_lt_of_ssubset P hxFace hF hproper
    rw [faceDim_singleton] at h
    omega
  obtain ⟨e, he, hde, hxe, heF⟩ := edge_inside_face_at_vertex P hF hx
    (hproper.1 (Set.mem_singleton x)) hdim
  obtain ⟨y, hy, hye, hyx, _⟩ := spigolo_segmento P he hde hx hxe
  refine ⟨y, ⟨hy, hyx.symm, e, he, hde, hxe, hye⟩, ?_⟩
  have hyout : y ∉ ({x} : Set (E d)) := by simpa only [Set.mem_singleton_iff] using hyx
  simpa only [hw] using himprove y (heF hye) hyout

theorem positive_parallel_max_reflect {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsPositiveParallelMap P f) (l : E d →L[ℝ] ℝ)
    {x : E d} (hx : x ∈ P.vertices)
    (hmax : ∀ y ∈ P.vertices, l (f y) ≤ l (f x)) :
    ∀ y ∈ P.vertices, l y ≤ l x := by
  intro z hz
  by_contra hnot
  obtain ⟨y, hxy, hlt⟩ := exists_increasing_edge P l hx hz (lt_of_not_ge hnot)
  obtain ⟨c, hc, heq⟩ := hf x hx y hxy.1 hxy
  have h := congrArg l heq
  simp only [map_sub, map_smul, smul_eq_mul] at h
  have hle := hmax y hxy.1
  nlinarith

/-- A parallel map remains constant under a supporting functional along
each face on which that functional is constant. -/
theorem parallel_constant_on_face {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsParallelMap P f) {F : Set (E d)} (hF : P.IsFace F)
    (l : E d →L[ℝ] ℝ) (hconst : ∀ x ∈ F, ∀ y ∈ F, l x = l y)
    {x y : E d} (hx : x ∈ P.vertices) (hy : y ∈ P.vertices)
    (hxF : x ∈ F) (hyF : y ∈ F) : l (f x) = l (f y) := by
  classical
  let Q := facePolytope P hF
  have hxQ : x ∈ Q.vertices := Finset.mem_filter.mpr ⟨hx, hxF⟩
  have hyQ : y ∈ Q.vertices := Finset.mem_filter.mpr ⟨hy, hyF⟩
  have hw := balinski_light_general Q hxQ hyQ
  have hwalk : ∀ z, Relation.ReflTransGen (GeneralVertexStep Q) x z →
      z ∈ Q.vertices ∧ l (f z) = l (f x) := by
    intro z hpath
    induction hpath with
    | refl => exact ⟨hxQ, rfl⟩
    | @tail u v hpath huv ih =>
      have hu := Finset.mem_filter.mp ih.1
      have hv := Finset.mem_filter.mp huv.1
      obtain ⟨_, hne, e, he, hde, hue, hve⟩ := huv
      have hstep : GeneralVertexStep P u v :=
        ⟨hv.1, hne, e, isFace_of_facePolytope P hF he, hde, hue, hve⟩
      obtain ⟨c, hc⟩ := hf u hu.1 v hv.1 hstep
      have h := congrArg l hc
      simp only [map_sub, map_smul, smul_eq_mul, hconst v hv.2 u hu.2,
        sub_self, mul_zero, sub_eq_zero] at h
      exact ⟨Finset.mem_filter.mpr hv, h.trans ih.2⟩
  exact (hwalk y hw).2.symm

theorem positive_parallel_max_preserve {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsPositiveParallelMap P f) (l : E d →L[ℝ] ℝ)
    {x : E d} (hx : x ∈ P.vertices)
    (hmax : ∀ y ∈ P.vertices, l y ≤ l x) :
    ∀ y ∈ P.vertices, l (f y) ≤ l (f x) := by
  classical
  obtain ⟨w, hw, hwm⟩ := P.vertices.exists_max_image (fun y => l (f y)) P.vertices_nonempty
  have hwmax := positive_parallel_max_reflect hf l hw hwm
  let F : Set (E d) := {z ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l z}
  have hxF : x ∈ F := ⟨subset_convexHull ℝ _ hx, le_su_toSet P l hmax⟩
  have hwF : w ∈ F := ⟨subset_convexHull ℝ _ hw, le_su_toSet P l hwmax⟩
  have hF : P.IsFace F := ⟨by intro _; exact ⟨l, rfl⟩, ⟨x, hxF⟩⟩
  have hconst : ∀ a ∈ F, ∀ b ∈ F, l a = l b := by
    intro a ha b hb
    exact le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)
  have heq := parallel_constant_on_face hf.parallel hF l hconst hx hw hxF hwF
  intro y hy
  exact (hwm y hy).trans_eq heq.symm

theorem positive_parallel_strict_max_preserve {P : ConvexPolytope d} {f : E d → E d}
    (hf : IsPositiveParallelMap P f) (l : E d →L[ℝ] ℝ)
    {x : E d} (hx : x ∈ P.vertices)
    (hstrict : ∀ y ∈ P.vertices, y ≠ x → l y < l x) :
    ∀ y ∈ P.vertices, y ≠ x → l (f y) < l (f x) := by
  have hmax : ∀ y ∈ P.vertices, l y ≤ l x := by
    intro y hy
    by_cases h : y = x
    · simp [h]
    · exact (hstrict y hy h).le
  have hfm := positive_parallel_max_preserve hf l hx hmax
  intro y hy hyx
  refine lt_of_le_of_ne (hfm y hy) ?_
  intro heq
  have hym : ∀ z ∈ P.vertices, l (f z) ≤ l (f y) := by
    intro z hz
    exact (hfm z hz).trans_eq heq.symm
  have h := positive_parallel_max_reflect hf l hy hym x hx
  exact (not_le_of_gt (hstrict y hy hyx)) h

theorem exists_vertex_exposer (P : ConvexPolytope d) {x : E d} (hx : x ∈ P.vertices) :
    ∃ l : E d →L[ℝ] ℝ, ∀ y ∈ P.vertices, y ≠ x → l y < l x := by
  obtain ⟨l, hl⟩ := (vertex_isFace P hx).1 (Set.singleton_nonempty x)
  have hm : x ∈ {z ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l z} := by
    rw [← hl]
    exact Set.mem_singleton x
  refine ⟨l, ?_⟩
  intro y hy hyx
  have hybody : y ∈ P.toSet := subset_convexHull ℝ _ hy
  refine lt_of_le_of_ne (hm.2 y hybody) ?_
  intro heq
  apply hyx
  have hyface : y ∈ ({x} : Set (E d)) := by
    rw [hl]
    exact ⟨hybody, fun z hz => (hm.2 z hz).trans_eq heq.symm⟩
  exact hyface

def positiveMapPolytope (P : ConvexPolytope d) (f : E d → E d)
    (hf : IsPositiveParallelMap P f) : ConvexPolytope d := by
  classical
  apply polytopeOfStrictMinima (P.vertices.image f) (P.vertices_nonempty.image f)
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨l, hl⟩ := exists_vertex_exposer P hv
  refine ⟨-l, ?_⟩
  intro y hy hyne
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  have hwv : w ≠ v := by intro h; exact hyne (congrArg f h)
  simpa only [ContinuousLinearMap.neg_apply, neg_lt_neg_iff] using
    positive_parallel_strict_max_preserve hf l hv hl w hw hwv

@[simp] theorem positiveMapPolytope_vertices (P : ConvexPolytope d) (f : E d → E d)
    (hf : IsPositiveParallelMap P f) :
    (positiveMapPolytope P f hf).vertices = P.vertices.image f := rfl

end Papers.Polytopes
