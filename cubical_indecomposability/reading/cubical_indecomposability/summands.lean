import papers.parallel_minkowski

set_option autoImplicit false

/-!
# Arbitrary convex Minkowski summands

The redrawing criterion applies to ordinary convex sets, without presupposing
that a summand has finitely many vertices.  Vertexwise components generate
the entire summands; supporting functionals prove this directly.  Thus the
conclusion below covers all convex bodies as well as polytopal summands.
-/

noncomputable section

namespace CubicalIndecomposability

open Set
open scoped Classical
open scoped Pointwise
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

variable {d : ℕ}

/-- Every convex summand is the finite hull of its components at the vertices
of the sum.  No finiteness or compactness of the summand is assumed. -/
theorem convex_summand_component_hull (P : ConvexPolytope d) (A B : Set (E d))
    (hA : Convex ℝ A) (hP : P.toSet = A + B) (f g : E d → E d)
    (hf : ∀ v ∈ P.vertices, f v ∈ A)
    (hg : ∀ v ∈ P.vertices, g v ∈ B)
    (hsum : ∀ v ∈ P.vertices, f v + g v = v) :
    A = convexHull ℝ (f '' (P.vertices : Set (E d))) := by
  apply Set.Subset.antisymm
  · intro a ha
    by_contra hout
    have hfinite : (f '' (P.vertices : Set (E d))).Finite :=
      P.vertices.finite_toSet.image f
    obtain ⟨l, c, hbound, hc⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) (hfinite.isClosed_convexHull ℝ) hout
    obtain ⟨v, hv, hvm⟩ := P.vertices.exists_max_image l P.vertices_nonempty
    have habody : a + g v ∈ P.toSet := by
      rw [hP]
      exact Set.mem_add.mpr ⟨a, ha, g v, hg v hv, rfl⟩
    have hle := le_su_toSet P l hvm (a + g v) habody
    have hlt := hbound (f v) (subset_convexHull ℝ _ (Set.mem_image_of_mem f hv))
    have hvalue := congrArg l (hsum v hv)
    simp only [map_add] at hle hvalue
    linarith
  · apply convexHull_min _ hA
    rintro _ ⟨v, hv, rfl⟩
    exact hf v hv

/-- Components of vertices in an arbitrary set decomposition form a parallel
redrawing on every actual edge of the convex polytope. -/
theorem convex_summand_component_parallel (P : ConvexPolytope d) (A B : Set (E d))
    (hP : P.toSet = A + B) (f g : E d → E d)
    (hf : ∀ v ∈ P.vertices, f v ∈ A)
    (hg : ∀ v ∈ P.vertices, g v ∈ B)
    (hsum : ∀ v ∈ P.vertices, f v + g v = v) :
    IsParallelMap P f := by
  intro x hx y hy hxy
  obtain ⟨_, hne, F, hF, hdF, hxF, hyF⟩ := hxy
  obtain ⟨l, hl⟩ := hF.1 hF.2
  have hxmax := hxF
  have hymax := hyF
  rw [hl] at hxmax hymax
  have hswap₁ : f x + g y ∈ P.toSet := by
    rw [hP]
    exact Set.mem_add.mpr ⟨f x, hf x hx, g y, hg y hy, rfl⟩
  have hswap₂ : f y + g x ∈ P.toSet := by
    rw [hP]
    exact Set.mem_add.mpr ⟨f y, hf y hy, g x, hg x hx, rfl⟩
  have hle₁ := hxmax.2 (f x + g y) hswap₁
  have hle₂ := hymax.2 (f y + g x) hswap₂
  have hvalx : l (f x) + l (g x) = l x := by rw [← map_add, hsum x hx]
  have hvaly : l (f y) + l (g y) = l y := by rw [← map_add, hsum y hy]
  have hxyval : l x = l y := le_antisymm (hymax.2 x hxmax.1) (hxmax.2 y hymax.1)
  have hswapval : l (f x + g y) = l x := by
    simp only [map_add] at hle₁ hle₂ ⊢
    linarith
  have hswapF : f x + g y ∈ F := by
    rw [hl]
    exact ⟨hswap₁, fun z hz => (hxmax.2 z hz).trans_eq hswapval.symm⟩
  rw [edge_eq_segment P hF hdF hx hy hxF hyF hne] at hswapF
  obtain ⟨a, b, _, _, hab, hpoint⟩ := hswapF
  refine ⟨a, ?_⟩
  calc
    f y - f x = (f y + g y) - (f x + g y) := by abel
    _ = y - (f x + g y) := by rw [hsum y hy]
    _ = y - (a • x + b • y) := by rw [hpoint]
    _ = a • (y - x) := by
      have hb : b = 1 - a := by linarith
      rw [hb]
      module

/-- For a non-point polytope, a homothetic summand has scale in `[0,1]`.
The proof uses two swapped component sums and a strictly exposing functional. -/
theorem homothetic_component_scale_bounds (P : ConvexPolytope d) (A B : Set (E d))
    (hP : P.toSet = A + B) (f g : E d → E d)
    (hf : ∀ v ∈ P.vertices, f v ∈ A)
    (hg : ∀ v ∈ P.vertices, g v ∈ B)
    (hsum : ∀ v ∈ P.vertices, f v + g v = v)
    (r : ℝ) (b : E d) (hhom : ∀ v ∈ P.vertices, f v = r • v + b)
    (x y : E d) (hx : x ∈ P.vertices) (hy : y ∈ P.vertices) (hxy : x ≠ y) :
    0 ≤ r ∧ r ≤ 1 := by
  obtain ⟨l, hmax, hunique⟩ := exists_vertex_exposer_body P hy
  have hxbody : x ∈ P.toSet := subset_convexHull ℝ _ hx
  have hlt : l x < l y := by
    refine lt_of_le_of_ne (hmax x hxbody) ?_
    intro heq
    exact hxy (hunique x hxbody heq)
  have hswap₁ : f x + g y ∈ P.toSet := by
    rw [hP]
    exact Set.mem_add.mpr ⟨f x, hf x hx, g y, hg y hy, rfl⟩
  have hswap₂ : f y + g x ∈ P.toSet := by
    rw [hP]
    exact Set.mem_add.mpr ⟨f y, hf y hy, g x, hg x hx, rfl⟩
  have hle₁ := hmax (f x + g y) hswap₁
  have hle₂ := hmax (f y + g x) hswap₂
  have hsumx := congrArg l (hsum x hx)
  have hsumy := congrArg l (hsum y hy)
  have hfx := congrArg l (hhom x hx)
  have hfy := congrArg l (hhom y hy)
  simp only [map_add, map_smul, smul_eq_mul] at hle₁ hle₂ hsumx hsumy hfx hfy
  constructor
  · by_contra hneg
    have hr : r < 0 := lt_of_not_ge hneg
    have hprod := mul_pos_of_neg_of_neg hr (sub_neg.mpr hlt)
    nlinarith
  · by_contra hlarge
    have hr : 1 - r < 0 := by linarith
    have hprod := mul_pos_of_neg_of_neg hr (sub_neg.mpr hlt)
    nlinarith

/-- Parallel rigidity implies full Minkowski indecomposability for arbitrary
convex summands.  Both summands, including point summands at the endpoints,
are explicitly identified as homothetic copies of the original body. -/
theorem convex_summands_homothetic_of_parallel_rigid (P : ConvexPolytope d)
    (hrigid : ∀ f : E d → E d, IsParallelMap P f → IsHomothetyOnVertices P f)
    (hnonpoint : ∃ x ∈ P.vertices, ∃ y ∈ P.vertices, x ≠ y)
    (A B : Set (E d)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hP : P.toSet = A + B) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ ∃ b : E d,
      A = (fun x : E d => r • x + b) '' P.toSet ∧
      B = (fun x : E d => (1 - r) • x - b) '' P.toSet := by
  have hex : ∀ v : E d, ∃ a b : E d, v ∈ P.vertices →
      a ∈ A ∧ b ∈ B ∧ a + b = v := by
    intro v
    by_cases hv : v ∈ P.vertices
    · have hmem : v ∈ A + B := by
        rw [← hP]
        exact subset_convexHull ℝ _ hv
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hmem
      exact ⟨a, b, fun _ => ⟨ha, hb, hab⟩⟩
    · exact ⟨0, 0, fun h => (hv h).elim⟩
  choose f g hfg using hex
  have hf := fun v hv => (hfg v hv).1
  have hg := fun v hv => (hfg v hv).2.1
  have hid := fun v hv => (hfg v hv).2.2
  have hparallel := convex_summand_component_parallel P A B hP f g hf hg hid
  obtain ⟨r, b, hhom⟩ := hrigid f hparallel
  obtain ⟨x, hx, y, hy, hxy⟩ := hnonpoint
  obtain ⟨hr0, hr1⟩ := homothetic_component_scale_bounds P A B hP f g
    hf hg hid r b hhom x y hx hy hxy
  refine ⟨r, hr0, hr1, b, ?_, ?_⟩
  · rw [convex_summand_component_hull P A B hA hP f g hf hg hid,
      hull_homothety_on_vertices P f r b hhom]
  · have hswap : P.toSet = B + A := hP.trans (add_comm _ _)
    have hid' : ∀ v ∈ P.vertices, g v + f v = v := by
      intro v hv
      rw [add_comm, hid v hv]
    have hgformula : ∀ v ∈ P.vertices, g v = (1 - r) • v + -b := by
      intro v hv
      have h := hid v hv
      rw [hhom v hv] at h
      calc
        g v = v - (r • v + b) := by
          apply eq_sub_iff_add_eq.mpr
          simpa only [add_comm] using h
        _ = (1 - r) • v + -b := by module
    rw [convex_summand_component_hull P B A hB hswap g f hg hf hid']
    simpa only [sub_eq_add_neg] using
      hull_homothety_on_vertices P g (1 - r) (-b) hgformula

/-- The redrawing criterion without a dimension or non-point hypothesis.
The one-point case follows directly from the equality of Minkowski sums. -/
theorem convex_summands_homothetic (P : ConvexPolytope d)
    (hrigid : ∀ f : E d → E d, IsParallelMap P f → IsHomothetyOnVertices P f)
    (A B : Set (E d)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hP : P.toSet = A + B) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ ∃ b : E d,
      A = (fun x : E d => r • x + b) '' P.toSet ∧
      B = (fun x : E d => (1 - r) • x - b) '' P.toSet := by
  by_cases hnonpoint : ∃ x ∈ P.vertices, ∃ y ∈ P.vertices, x ≠ y
  · exact convex_summands_homothetic_of_parallel_rigid P hrigid hnonpoint A B hA hB hP
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  have hsing : ∀ w ∈ P.vertices, w = v := by
    intro w hw
    by_contra hne
    exact hnonpoint ⟨w, hw, v, hv, hne⟩
  have hsingle : P.toSet = {v} := by
    apply Set.Subset.antisymm
    · exact convexHull_min hsing (convex_singleton v)
    · exact Set.singleton_subset_iff.mpr (subset_convexHull ℝ _ hv)
  have hvsum : v ∈ A + B := by
    rw [← hP]
    exact subset_convexHull ℝ _ hv
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hvsum
  have hAsingle : A = {a} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxsum : x + b ∈ P.toSet := by
        rw [hP]
        exact Set.mem_add.mpr ⟨x, hx, b, hb, rfl⟩
      rw [hsingle] at hxsum
      exact add_right_cancel ((Set.mem_singleton_iff.mp hxsum).trans hab.symm)
    · exact Set.singleton_subset_iff.mpr ha
  have hBsingle : B = {b} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hysum : a + y ∈ P.toSet := by
        rw [hP]
        exact Set.mem_add.mpr ⟨a, ha, y, hy, rfl⟩
      rw [hsingle] at hysum
      exact add_left_cancel ((Set.mem_singleton_iff.mp hysum).trans hab.symm)
    · exact Set.singleton_subset_iff.mpr hb
  refine ⟨0, le_rfl, zero_le_one, a, ?_, ?_⟩
  · simpa only [zero_smul, zero_add, hsingle, Set.image_singleton] using hAsingle
  · simp only [sub_zero, one_smul, hsingle, Set.image_singleton]
    rw [hBsingle]
    congr 1
    rw [← hab]
    abel

end CubicalIndecomposability
