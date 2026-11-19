module
public import papers.parallel_maps
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-!
# The convex-geometric bridge for parallel maps

Supporting functionals connect the edge equations to actual Minkowski sums.
The hull equalities here are equalities of sets in Euclidean space, not
formal sums or relations added to the definition of a parallel map.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Pointwise Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem exists_vertex_exposer_body (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) :
    ∃ l : E d →L[ℝ] ℝ,
      (∀ x ∈ P.toSet, l x ≤ l v) ∧
      (∀ x ∈ P.toSet, l x = l v → x = v) := by
  obtain ⟨l, hl⟩ := (vertex_isFace P hv).1 (Set.singleton_nonempty v)
  have hvmax : v ∈ {x ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l x} := by
    rw [← hl]
    exact Set.mem_singleton v
  refine ⟨l, hvmax.2, ?_⟩
  intro x hx heq
  have hxf : x ∈ ({v} : Set (E d)) := by
    rw [hl]
    exact ⟨hx, fun y hy => (hvmax.2 y hy).trans_eq heq.symm⟩
  exact hxf

/-- Two positive parallel maps summing to each original vertex produce
an equality of the corresponding convex bodies. -/
theorem positive_parallel_sum_eq (P : ConvexPolytope d) (f g : E d → E d)
    (hf : IsPositiveParallelMap P f) (hg : IsPositiveParallelMap P g)
    (hsum : ∀ v ∈ P.vertices, f v + g v = v) :
    P.toSet = (positiveMapPolytope P f hf).toSet +
      (positiveMapPolytope P g hg).toSet := by
  let A := positiveMapPolytope P f hf
  let B := positiveMapPolytope P g hg
  apply Set.Subset.antisymm
  · apply convexHull_min _ ((convex_convexHull ℝ _).add (convex_convexHull ℝ _))
    intro v hv
    exact Set.mem_add.mpr ⟨f v, subset_convexHull ℝ _ (Finset.mem_image_of_mem f hv),
      g v, subset_convexHull ℝ _ (Finset.mem_image_of_mem g hv), hsum v hv⟩
  · rintro z ⟨a, ha, b, hb, rfl⟩
    by_contra hout
    obtain ⟨l, c, hbound, hc⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (P.vertices : Set (E d)))
      (P.vertices.finite_toSet.isClosed_convexHull ℝ) hout
    obtain ⟨v, hv, hvm⟩ := P.vertices.exists_max_image l P.vertices_nonempty
    have hfa : ∀ q ∈ A.vertices, l q ≤ l (f v) := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
      exact positive_parallel_max_preserve hf l hv hvm w hw
    have hgb : ∀ q ∈ B.vertices, l q ≤ l (g v) := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
      exact positive_parallel_max_preserve hg l hv hvm w hw
    have hla := le_su_toSet A l hfa a ha
    have hlb := le_su_toSet B l hgb b hb
    have hvlt := hbound v (subset_convexHull ℝ _ hv)
    have hlv : l (f v) + l (g v) = l v := by rw [← map_add, hsum v hv]
    rw [map_add] at hc
    linarith

theorem positiveMap_homothetic_on_vertices (P : ConvexPolytope d) (f : E d → E d)
    (hf : IsPositiveParallelMap P f)
    (hcopy : IsHomotheticCopy P (positiveMapPolytope P f hf)) :
    IsHomothetyOnVertices P f := by
  obtain ⟨r, hr, b, hcopy⟩ := hcopy
  refine ⟨r, b, ?_⟩
  intro v hv
  obtain ⟨l, hmax, hunique⟩ := exists_vertex_exposer_body P hv
  have hvmax : ∀ w ∈ P.vertices, l w ≤ l v :=
    fun w hw => hmax w (subset_convexHull ℝ _ hw)
  have hfmax := positive_parallel_max_preserve hf l hv hvmax
  have hfv : f v ∈ (positiveMapPolytope P f hf).toSet :=
    subset_convexHull ℝ _ (Finset.mem_image_of_mem f hv)
  rw [hcopy] at hfv
  obtain ⟨u, hu, heq⟩ := hfv
  have hrv : r • v + b ∈ (positiveMapPolytope P f hf).toSet := by
    rw [hcopy]
    exact Set.mem_image_of_mem _ (subset_convexHull ℝ _ hv)
  have hrvle : l (r • v + b) ≤ l (f v) := by
    apply le_su_toSet (positiveMapPolytope P f hf) l _ _ hrv
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    exact hfmax w hw
  have hlu : l u = l v := by
    rw [← heq] at hrvle
    simp only [map_add, map_smul, smul_eq_mul] at hrvle
    have := hmax u hu
    nlinarith
  have huv := hunique u hu hlu
  simpa only [huv] using heq.symm

/-- For any vertexwise choices in a Minkowski decomposition, their first
coordinates generate the entire first summand. -/
theorem minkowski_component_hull (P A B : ConvexPolytope d)
    (hP : P.toSet = A.toSet + B.toSet) (f g : E d → E d)
    (hf : ∀ v ∈ P.vertices, f v ∈ A.toSet)
    (hg : ∀ v ∈ P.vertices, g v ∈ B.toSet)
    (hsum : ∀ v ∈ P.vertices, f v + g v = v) :
    A.toSet = convexHull ℝ (f '' (P.vertices : Set (E d))) := by
  apply Set.Subset.antisymm
  · intro a ha
    by_contra hout
    have hfinite : (f '' (P.vertices : Set (E d))).Finite := P.vertices.finite_toSet.image f
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
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨v, hv, rfl⟩
    exact hf v hv

/-- The choice of the component at a vertex induces a parallel map on
every actual edge of the sum. -/
theorem minkowski_component_parallel (P A B : ConvexPolytope d)
    (hP : P.toSet = A.toSet + B.toSet) (f g : E d → E d)
    (hf : ∀ v ∈ P.vertices, f v ∈ A.toSet)
    (hg : ∀ v ∈ P.vertices, g v ∈ B.toSet)
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
  have hyid := hsum y hy
  calc
    f y - f x = (f y+g y) - (f x + g y) := by abel
    _ = y - (f x + g y) := by rw [hyid]
    _ = y - (a • x + b • y) := by rw [hpoint]
    _ = a • (y - x) := by
      have hb : b = 1 - a := by linarith
      rw [hb]
      module

def homothetyAffineMap (r : ℝ) (b : E d) : E d →ᵃ[ℝ] E d where
  toFun x := r • x + b
  linear := r • LinearMap.id
  map_vadd' p v := by
    simp only [vadd_eq_add, smul_add, LinearMap.smul_apply, LinearMap.id_apply]
    abel

theorem hull_homothety_on_vertices (P : ConvexPolytope d) (f : E d → E d)
    (r : ℝ) (b : E d) (h : ∀ v ∈ P.vertices, f v = r • v + b) :
    convexHull ℝ (f '' (P.vertices : Set (E d))) =
      (fun x => r • x + b) '' P.toSet := by
  have himage : f '' (P.vertices : Set (E d)) =
      homothetyAffineMap r b '' (P.vertices : Set (E d)) := by
    apply Set.image_congr
    exact h
  rw [himage, ← (homothetyAffineMap r b).image_convexHull]
  rfl

/-- A genuine nontrivial Minkowski decomposition yields a nonhomothetic
parallel map. No summand-reconstruction theorem is assumed here. -/
theorem parallel_map_of_minkowski_decomposable (P : ConvexPolytope d)
    (hP : MinkowskiDecomposable P) :
    ∃ f : E d → E d, IsParallelMap P f ∧ ¬IsHomothetyOnVertices P f := by
  obtain ⟨A, B, hsum, hA, hB⟩ := hP
  have hex : ∀ v : E d, ∃ a b : E d, v ∈ P.vertices →
      a ∈ A.toSet ∧ b ∈ B.toSet ∧ a + b = v := by
    intro v
    by_cases hv : v ∈ P.vertices
    · have hmem : v ∈ A.toSet + B.toSet := by
        rw [← hsum]
        exact subset_convexHull ℝ _ hv
      obtain ⟨a, ha, b, hb, hab⟩ := hmem
      exact ⟨a, b, fun _ => ⟨ha, hb, hab⟩⟩
    · exact ⟨0, 0, fun h => (hv h).elim⟩
  choose f g hfg using hex
  have hf := fun v hv => (hfg v hv).1
  have hg := fun v hv => (hfg v hv).2.1
  have hid := fun v hv => (hfg v hv).2.2
  refine ⟨f, minkowski_component_parallel P A B hsum f g hf hg hid, ?_⟩
  rintro ⟨r, b, hrb⟩
  have hAhull := minkowski_component_hull P A B hsum f g hf hg hid
  by_cases hr : 0 < r
  · apply hA
    refine ⟨r, hr, b, ?_⟩
    rw [hAhull, hull_homothety_on_vertices P f r b hrb]
  · have hBsum : P.toSet = B.toSet + A.toSet := hsum.trans (add_comm _ _)
    have hBident : ∀ v ∈ P.vertices, g v + f v = v := by
      intro v hv
      rw [add_comm, hid v hv]
    have hBhull := minkowski_component_hull P B A hBsum g f hg hf hBident
    have hgformula : ∀ v ∈ P.vertices, g v = (1 - r) • v + -b := by
      intro v hv
      have h := hid v hv
      rw [hrb v hv] at h
      calc
        g v = v - (r • v + b) := by
          apply eq_sub_iff_add_eq.mpr
          simpa only [add_comm] using h
        _ = (1 - r) • v + -b := by module
    apply hB
    refine ⟨1 - r, by linarith, -b, ?_⟩
    rw [hBhull, hull_homothety_on_vertices P g (1 - r) (-b) hgformula]

end Papers.Polytopes
