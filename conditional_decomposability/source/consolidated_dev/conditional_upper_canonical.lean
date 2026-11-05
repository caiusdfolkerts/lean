module
public import consolidated_dev.minkowski_map_core
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module

set_option Elab.async false

section BundlePart0
/- Source: Papers/ParallelSkewConnection.lean -/



@[expose] public section

/-!
# Joining rigid pieces by skew edges

Four affinely independent endpoints express the ordinary skewness of two
lines. The two internal sides of the four-cycle need not be actual graph
edges: homothety on each rigid piece already supplies their parallel-map
equations. This is the geometric joining criterion used in the cited
conditionally decomposable constructions.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem HomotheticOn.union_of_affine_cross_cycle
    {f : E d → E d} {S T : Set (E d)}
    (hS : HomotheticOn f S) (hT : HomotheticOn f T)
    (p : Fin 4 → E d) (hp : AffineIndependent ℝ p)
    (h0 : p 0 ∈ S) (h3 : p 3 ∈ S) (h1 : p 1 ∈ T) (h2 : p 2 ∈ T)
    (h01 : ∃ a : ℝ, f (p 1) - f (p 0) = a • (p 1 - p 0))
    (h23 : ∃ a : ℝ, f (p 3) - f (p 2) = a • (p 3 - p 2)) :
    HomotheticOn f (S ∪ T) := by
  obtain ⟨a, b, hab⟩ := hS
  obtain ⟨c, e, hce⟩ := hT
  have h12 : ∃ r : ℝ, f (p 2) - f (p 1) = r • (p 2 - p 1) := by
    refine ⟨c, ?_⟩
    rw [hce _ h2, hce _ h1]
    module
  have h30 : ∃ r : ℝ, f (p 0) - f (p 3) = r • (p 0 - p 3) := by
    refine ⟨a, ?_⟩
    rw [hab _ h0, hab _ h3]
    module
  obtain ⟨r, t, hrt⟩ := homothetic_of_affine_cycle4 p hp f h01 h12 h23 h30
  have hA := homothety_parameters_unique
    (hp.injective.ne (by decide : (0 : Fin 4) ≠ 3))
    ((hab _ h0).symm.trans (hrt _ (Set.mem_range_self 0)))
    ((hab _ h3).symm.trans (hrt _ (Set.mem_range_self 3)))
  have hB := homothety_parameters_unique
    (hp.injective.ne (by decide : (1 : Fin 4) ≠ 2))
    ((hce _ h1).symm.trans (hrt _ (Set.mem_range_self 1)))
    ((hce _ h2).symm.trans (hrt _ (Set.mem_range_self 2)))
  refine ⟨r, t, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · rw [hab _ hx, hA.1, hA.2]
  · rw [hce _ hx, hB.1, hB.2]

/-- Two locally rigid pieces joined by two actual edges with affinely
independent endpoints form a locally rigid union. -/
theorem ParallelRigid.union_of_skew_connections
    {P : ConvexPolytope d} {S T : Set (E d)}
    (hS : ParallelRigid P S) (hT : ParallelRigid P T)
    (p : Fin 4 → E d) (hp : AffineIndependent ℝ p)
    (h0 : p 0 ∈ S) (h3 : p 3 ∈ S) (h1 : p 1 ∈ T) (h2 : p 2 ∈ T)
    (h01 : GeneralVertexStep P (p 0) (p 1))
    (h23 : GeneralVertexStep P (p 2) (p 3)) : ParallelRigid P (S ∪ T) := by
  intro f hf
  apply (hS f (hf.mono Set.subset_union_left)).union_of_affine_cross_cycle
    (hT f (hf.mono Set.subset_union_right)) p hp h0 h3 h1 h2
  · exact hf _ (Or.inl h0) _ (Or.inr h1) h01
  · exact hf _ (Or.inr h2) _ (Or.inl h3) h23

end Papers.Polytopes

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/ConditionalEightData.lean -/





@[expose] public section

/-! Exact data for two geometric realizations of the eight-vertex base.
The data themselves assert no face completeness or decomposition result. -/

noncomputable section
namespace Papers.Polytopes.ConditionalEight

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def vertexRows : Fin 2 → Fin 8 → Fin 3 → ℤ :=
  ![![![0, 0, 0], ![10, 0, 10], ![10, 10, 0], ![0, 10, 10], ![0, 0, 20], ![10, 0, 30], ![10, 10, 20], ![0, 10, 30]], ![![0, 0, 0], ![10, 0, 10], ![10, 10, 0], ![0, 11, 10], ![0, 0, 20], ![10, 0, 30], ![10, 12, 20], ![0, 13, 30]]]

def supportRows : Fin 2 → Fin 8 → Fin 4 → ℤ :=
  ![![![-1, 1, 1, 0], ![1, -1, 1, 0], ![1, 1, -1, 20], ![-1, -1, -1, 40], ![0, 1, 0, 0], ![-1, 0, 0, 10], ![0, -1, 0, 10], ![1, 0, 0, 0]], ![![-1, 1, 1, 0], ![10, -10, 11, 0], ![13, 10, -13, 260], ![-13, -10, -12, 490], ![0, 1, 0, 0], ![-1, 0, 0, 10], ![0, -10, 1, 100], ![1, 0, 0, 0]]]

def axisCoefficients : Fin 2 → Fin 3 → Fin 3 → ℝ :=
  ![![![1/20, 1/20, -1/20], ![-1/20, 1/20, 1/20], ![1/20, -1/20, 1/20]], ![![1/21, 11/210, -1/21], ![-1/21, 1/21, 1/21], ![11/210, -11/210, 1/21]]]

def members : Fin 8 → Finset (Fin 8) :=
  ![{0, 1, 2}, {0, 2, 3}, {4, 5, 7}, {5, 6, 7}, {0, 1, 4, 5}, {1, 2, 5, 6}, {2, 3, 6, 7}, {0, 3, 4, 7}]

def facetTriple : Fin 8 → Fin 3 → Fin 8 :=
  ![![0, 1, 2], ![0, 2, 3], ![4, 5, 7], ![5, 6, 7], ![0, 1, 4], ![1, 2, 5], ![2, 3, 6], ![0, 3, 4]]

end Papers.Polytopes.ConditionalEight

end
end
end BundlePart1

section BundlePart2
/- Source: Cubical/Polytope/TwoFaces.lean -/




@[expose] public section

/-! # Uniqueness of a two-face through two nonadjacent vertices -/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem face_eq_of_subset_of_dimension_eq (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hFG : F ⊆ G) (hdim : faceDim F = faceDim G) : F = G := by
  by_contra hne
  have hlt := faceDim_lt_of_ssubset P hF hG (hFG.ssubset_of_ne hne)
  omega

/-- Two different two-faces cannot share two nonadjacent vertices. This is
the geometric fact ensuring that different link edges have distinct opposite
white vertices in Lemma 2. -/
theorem two_faces_eq_of_nonadjacent_vertices (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hdF : faceDim F = 2) (hdG : faceDim G = 2)
    (u v : VertexType P) (huF : u.val ∈ F) (hvF : v.val ∈ F)
    (huG : u.val ∈ G) (hvG : v.val ∈ G)
    (hne : u ≠ v) (hnadj : ¬(polytopeGraph P).Adj u v) : F = G := by
  have hI : P.IsFace (F ∩ G) := isFace_inter P hF hG ⟨u.val, huF, huG⟩
  have hdim0 : faceDim (F ∩ G) ≠ 0 := by
    intro hdim
    obtain ⟨x, hx, _⟩ := punto_di_faccia0_e_vertice P hI hdim
    have hu : u.val = x := by simpa [hx] using (show u.val ∈ F ∩ G from ⟨huF, huG⟩)
    have hv : v.val = x := by simpa [hx] using (show v.val ∈ F ∩ G from ⟨hvF, hvG⟩)
    exact hne (Subtype.ext (hu.trans hv.symm))
  have hdim1 : faceDim (F ∩ G) ≠ 1 := by
    intro hdim
    exact hnadj ⟨hne, F ∩ G, hI, hdim, ⟨huF, huG⟩, ⟨hvF, hvG⟩⟩
  have hle : faceDim (F ∩ G) ≤ faceDim F :=
    Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
  have hdI : faceDim (F ∩ G) = 2 := by omega
  have hIF := face_eq_of_subset_of_dimension_eq P hI hF Set.inter_subset_left
    (hdI.trans hdF.symm)
  have hIG := face_eq_of_subset_of_dimension_eq P hI hG Set.inter_subset_right
    (hdI.trans hdG.symm)
  exact hIF.symm.trans hIG

end LeanEval.Geometry.PlatonicClassification

end
end BundlePart2

section BundlePart3
/- Source: Papers/ConditionalEightGeometry.lean -/




@[expose] public section

/-!
# Exact convex geometry of the eight-vertex base

Every listed point is exposed by the displayed integer supporting forms.
The coordinate-span certificate proves full dimension. The eight displayed
faces are actual facets; their completeness is established separately.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

theorem faceDim_ge_two_of_three_vertices {d : ℕ}
    (P : ConvexPolytope d) (F : Set (E d))
    {u v w : E d} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices) (hw : w ∈ P.vertices)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (huF : u ∈ F) (hvF : v ∈ F) (hwF : w ∈ F) : 2 ≤ faceDim F := by
  by_contra hdim
  have hle : faceDim F ≤ 1 := by omega
  have hcol : Collinear ℝ F := collinear_iff_finrank_le_one.mpr hle
  apply vertices_not_collinear P hu hv hw huv huw hvw
  apply Collinear.subset (s₂ := F) ?_ hcol
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem two_faces_eq_of_three_common_vertices {d : ℕ}
    (P : ConvexPolytope d) {F G : Set (E d)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hdF : faceDim F = 2) (hdG : faceDim G = 2)
    {u v w : E d} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices) (hw : w ∈ P.vertices)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (huF : u ∈ F) (hvF : v ∈ F) (hwF : w ∈ F)
    (huG : u ∈ G) (hvG : v ∈ G) (hwG : w ∈ G) : F = G := by
  have hI : P.IsFace (F ∩ G) := isFace_inter P hF hG ⟨u, huF, huG⟩
  have hlo := faceDim_ge_two_of_three_vertices P (F ∩ G) hu hv hw huv huw hvw
    ⟨huF, huG⟩ ⟨hvF, hvG⟩ ⟨hwF, hwG⟩
  have hhi : faceDim (F ∩ G) ≤ faceDim F :=
    Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
  have hdim : faceDim (F ∩ G) = 2 := by omega
  have hIF := face_eq_of_subset_of_dimension_eq P hI hF Set.inter_subset_left (hdim.trans hdF.symm)
  have hIG := face_eq_of_subset_of_dimension_eq P hI hG Set.inter_subset_right (hdim.trans hdG.symm)
  exact hIF.symm.trans hIG

theorem face_has_three_vertices {d : ℕ} (P : ConvexPolytope d)
    {F : Set (E d)} (hF : P.IsFace F) (hdF : 2 ≤ faceDim F) :
    ∃ u ∈ P.vertices, ∃ v ∈ P.vertices, ∃ w ∈ P.vertices,
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ u ∈ F ∧ v ∈ F ∧ w ∈ F := by
  let Q := facePolytope P hF
  obtain ⟨v₀, hv₀⟩ := Q.vertices_nonempty
  letI : Nonempty (VertexType Q) := ⟨⟨v₀, hv₀⟩⟩
  have hrange : Set.range (fun v : VertexType Q => v.val) = (Q.vertices : Set (E d)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact v.property
    · exact fun hx => ⟨⟨x, hx⟩, rfl⟩
  have hspan : vectorSpan ℝ (Set.range (fun v : VertexType Q => v.val)) = vectorSpan ℝ F := by
    rw [hrange]
    have hc := congrArg AffineSubspace.direction
      (affineSpan_convexHull (𝕜 := ℝ) (Q.vertices : Set (E d)))
    simp only [direction_affineSpan] at hc
    change vectorSpan ℝ Q.toSet = vectorSpan ℝ (Q.vertices : Set (E d)) at hc
    rw [← hc]
    exact congrArg (vectorSpan ℝ) (facePolytope_toSet P hF)
  have hcard := finrank_vectorSpan_range_add_one_le ℝ (fun v : VertexType Q => v.val)
  rw [hspan] at hcard
  change faceDim F + 1 ≤ Fintype.card (VertexType Q) at hcard
  have hthree : 2 < Fintype.card (VertexType Q) := by omega
  obtain ⟨u, v, w, huv, huw, hvw⟩ := Fintype.two_lt_card_iff.mp hthree
  obtain ⟨huP, huF⟩ := Finset.mem_filter.mp u.property
  obtain ⟨hvP, hvF⟩ := Finset.mem_filter.mp v.property
  obtain ⟨hwP, hwF⟩ := Finset.mem_filter.mp w.property
  exact ⟨u.val, huP, v.val, hvP, w.val, hwP,
    fun h => huv (Subtype.ext h), fun h => huw (Subtype.ext h),
    fun h => hvw (Subtype.ext h), huF, hvF, hwF⟩

namespace ConditionalEight

def point (k : Fin 2) (v : Fin 8) : E 3 :=
  WithLp.toLp 2 (fun i => (vertexRows k v i : ℝ))

def coordinate (i : Fin 3) : E 3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => x i
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def support (k : Fin 2) (f : Fin 8) : E 3 →L[ℝ] ℝ :=
  ∑ i : Fin 3, (supportRows k f i.castSucc : ℝ) • coordinate i

def offset (k : Fin 2) (f : Fin 8) : ℝ := -(supportRows k f 3 : ℝ)

theorem support_apply (k : Fin 2) (f : Fin 8) (x : E 3) :
    support k f x = (supportRows k f 0 : ℝ) * x 0 +
      (supportRows k f 1 : ℝ) * x 1 + (supportRows k f 2 : ℝ) * x 2 := by
  simp [support, coordinate, Fin.sum_univ_succ, add_assoc]

theorem support_bound (k : Fin 2) (f v : Fin 8) : offset k f ≤ support k f (point k v) := by
  fin_cases k <;> fin_cases f <;> fin_cases v <;>
    norm_num [support_apply, offset, point, supportRows, vertexRows]

theorem support_incidence (k : Fin 2) (f v : Fin 8) :
    support k f (point k v) = offset k f ↔ v ∈ members f := by
  fin_cases k <;> fin_cases f <;> fin_cases v <;>
    norm_num [support_apply, offset, point, supportRows, vertexRows, members]

theorem incidence_separates : ∀ v w : Fin 8, v ≠ w →
    ∃ f : Fin 8, v ∈ members f ∧ w ∉ members f := by decide

theorem support_separation (k : Fin 2) (v w : Fin 8) (hvw : v ≠ w) :
    ∃ f, support k f (point k v) = offset k f ∧ offset k f < support k f (point k w) := by
  obtain ⟨f, hv, hw⟩ := incidence_separates v w hvw
  refine ⟨f, (support_incidence k f v).mpr hv, ?_⟩
  apply lt_of_le_of_ne (support_bound k f w)
  intro h
  exact hw ((support_incidence k f w).mp h.symm)

def polytope (k : Fin 2) : ConvexPolytope 3 :=
  polytopeOfSeparatingSupports (point k) (by decide) (support k) (offset k)
    (support_bound k) (support_separation k)

@[simp] theorem polytope_vertices (k : Fin 2) : (polytope k).vertices = Finset.univ.image (point k) := rfl

theorem polytope_card (k : Fin 2) : (polytope k).vertices.card = 8 :=
  polytopeOfSeparatingSupports_card (point k) (by decide) (support k) (offset k)
    (support_bound k) (support_separation k)

theorem point_injective (k : Fin 2) : Function.Injective (point k) :=
  separatingSupports_injective (point k) (support k) (offset k) (support_separation k)

theorem point_vertex (k : Fin 2) (v : Fin 8) : point k v ∈ (polytope k).vertices :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem point_zero (k : Fin 2) : point k 0 = 0 := by
  ext i
  fin_cases k <;> fin_cases i <;> norm_num [point, vertexRows]

def axis (i : Fin 3) : E 3 := WithLp.toLp 2 (fun j => if j = i then 1 else 0)

def basisVertex (i : Fin 3) : Fin 8 := ⟨i.val + 1, by omega⟩

theorem coordinate_expansion (x : E 3) : x = ∑ i : Fin 3, x i • axis i := by
  ext j
  fin_cases j <;> simp [axis, Fin.sum_univ_succ]

theorem axis_combination (k : Fin 2) (i : Fin 3) :
    axis i = ∑ j : Fin 3, axisCoefficients k i j • point k (basisVertex j) := by
  ext q
  fin_cases k <;> fin_cases i <;> fin_cases q <;>
    norm_num [axis, axisCoefficients, basisVertex, point, vertexRows, Fin.sum_univ_succ]

theorem polytope_fullDim (k : Fin 2) : (polytope k).IsFullDim := by
  let U := vectorSpan ℝ (polytope k).toSet
  have hp (v : Fin 8) : point k v ∈ U := by
    change point k v ∈ vectorSpan ℝ (polytope k).toSet
    have h := vsub_mem_vectorSpan ℝ
      (subset_convexHull ℝ _ (point_vertex k v)) (subset_convexHull ℝ _ (point_vertex k 0))
    simpa only [ConvexPolytope.toSet, point_zero, vsub_eq_sub, sub_zero] using h
  have ha (i : Fin 3) : axis i ∈ U := by
    rw [axis_combination k i]
    exact U.sum_mem (fun j _ => U.smul_mem _ (hp _))
  have htop : U = ⊤ := by
    apply top_unique
    intro x _
    rw [coordinate_expansion x]
    exact U.sum_mem (fun i _ => U.smul_mem _ (ha i))
  change finrank ℝ U = 3
  rw [htop, finrank_top, finrank_euclideanSpace_fin]

def face (k : Fin 2) (f : Fin 8) : Set (E 3) :=
  minimumFace (polytope k) (support k f) (offset k f)

theorem point_mem_face_iff (k : Fin 2) (f v : Fin 8) :
    point k v ∈ face k f ↔ v ∈ members f := by
  change (point k v ∈ (polytope k).toSet ∧ support k f (point k v) = offset k f) ↔ _
  rw [support_incidence]
  exact and_iff_right (show point k v ∈ (polytope k).toSet from
    subset_convexHull ℝ _ (point_vertex k v))

theorem facetTriple_mem (f : Fin 8) (i : Fin 3) : facetTriple f i ∈ members f := by
  fin_cases f <;> fin_cases i <;> decide

theorem facetTriple_injective (f : Fin 8) : Function.Injective (facetTriple f) := by
  fin_cases f <;> decide

theorem face_isFace (k : Fin 2) (f : Fin 8) : (polytope k).IsFace (face k f) := by
  apply minimumFace_isFace
  · intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact support_bound k f v
  · exact ⟨point k (facetTriple f 0), point_vertex k _,
      (support_incidence k f _).mpr (facetTriple_mem f 0)⟩

theorem face_proper (k : Fin 2) (f : Fin 8) : face k f ≠ (polytope k).toSet := by
  have hout : ∀ f : Fin 8, ∃ v : Fin 8, v ∉ members f := by decide
  obtain ⟨v, hv⟩ := hout f
  intro heq
  exact hv ((point_mem_face_iff k f v).mp (heq.symm ▸ subset_convexHull ℝ _ (point_vertex k v)))

theorem face_dimension (k : Fin 2) (f : Fin 8) : faceDim (face k f) = 2 := by
  let p := fun i : Fin 3 => point k (facetTriple f i)
  have hinj : Function.Injective p := (point_injective k).comp (facetTriple_injective f)
  have hlo := faceDim_ge_two_of_three_vertices (polytope k) (face k f)
    (point_vertex k (facetTriple f 0)) (point_vertex k (facetTriple f 1)) (point_vertex k (facetTriple f 2))
    (hinj.ne (by decide : (0 : Fin 3) ≠ 1)) (hinj.ne (by decide : (0 : Fin 3) ≠ 2))
    (hinj.ne (by decide : (1 : Fin 3) ≠ 2))
    ((point_mem_face_iff k f _).mpr (facetTriple_mem f 0))
    ((point_mem_face_iff k f _).mpr (facetTriple_mem f 1))
    ((point_mem_face_iff k f _).mpr (facetTriple_mem f 2))
  have hhi := faceDim_lt_of_ssubset (polytope k) (face_isFace k f) (toSet_isFace (polytope k))
    ((Set.ssubset_iff_subset_ne).mpr ⟨face_subset_toSet _ (face_isFace k f), face_proper k f⟩)
  change faceDim (face k f) < (polytope k).dim at hhi
  have hd := polytope_fullDim k
  change (polytope k).dim = 3 at hd
  omega

theorem face_isFacet (k : Fin 2) (f : Fin 8) : IsFacet (polytope k) (face k f) := by
  refine ⟨face_isFace k f, ?_⟩
  rw [face_dimension, show (polytope k).dim = 3 from polytope_fullDim k]

end ConditionalEight
end Papers.Polytopes

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/ConditionalEightFaces.lean -/



@[expose] public section

/-!
# Complete facet certificates for the two eight-vertex realizations

For each triple of distinct labels, the exact certificate says either that
the triple belongs to a displayed facet, or that a nonnegative affine form
vanishing there must vanish identically. Every geometric facet contains
three distinct vertices. This proves completeness and hence the ordinary
face-order equivalence of the two convex hulls.
-/

noncomputable section
namespace Papers.Polytopes.ConditionalEight

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def affineEvaluate (a : Fin 4 → ℝ) (x : E 3) : ℝ :=
  a 0 * x 0 + a 1 * x 1 + a 2 * x 2 + a 3

def affineCoefficients (f : E 3 →ᵃ[ℝ] ℝ) : Fin 4 → ℝ :=
  ![f.linear (axis 0), f.linear (axis 1), f.linear (axis 2), f 0]

theorem affine_evaluate_coefficients (f : E 3 →ᵃ[ℝ] ℝ) (x : E 3) :
    affineEvaluate (affineCoefficients f) x = f x := by
  have h := congrArg f.linear (coordinate_expansion x)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  rw [affine_form_apply f x]
  simpa [affineEvaluate, affineCoefficients, Fin.sum_univ_succ, mul_comm, add_assoc] using
    congrArg (fun y : ℝ => y + f 0) h.symm

theorem affineCoefficients_ne_zero {f : E 3 →ᵃ[ℝ] ℝ} (hf : f ≠ 0) :
    affineCoefficients f ≠ 0 := by
  intro hz
  apply hf
  ext x
  rw [← affine_evaluate_coefficients, hz]
  simp [affineEvaluate]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sorted_triple_certificate
    (k : Fin 2) (a : Fin 4 → ℝ) (hnon : ∀ v : Fin 8, 0 ≤ affineEvaluate a (point k v))
    (i j l : Fin 8) (hij : i < j) (hjl : j < l)
    (hi : affineEvaluate a (point k i) = 0)
    (hj : affineEvaluate a (point k j) = 0)
    (hl : affineEvaluate a (point k l) = 0) :
    a = 0 ∨ ∃ f : Fin 8, i ∈ members f ∧ j ∈ members f ∧ l ∈ members f := by
  have h0 := hnon 0
  have h1 := hnon 1
  have h2 := hnon 2
  have h3 := hnon 3
  have h4 := hnon 4
  have h5 := hnon 5
  have h6 := hnon 6
  have h7 := hnon 7
  fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals norm_num at hij
  all_goals norm_num at hjl
  all_goals first | exact Or.inr (by decide) | skip
  all_goals
    norm_num [affineEvaluate, point, vertexRows] at h0 h1 h2 h3 h4 h5 h6 h7 hi hj hl
    left
    have ha0 : a 0=0 := by linarith
    have ha1 : a 1=0 := by linarith
    have ha2 : a 2=0 := by linarith
    have ha3 : a 3=0 := by linarith
    funext q
    fin_cases q <;> simpa only [Pi.zero_apply] using (by assumption : a _=0)

theorem three_zero_in_common_facet
    (k : Fin 2) (a : Fin 4 → ℝ) (ha : a ≠ 0)
    (hnon : ∀ v : Fin 8, 0 ≤ affineEvaluate a (point k v))
    (i j l : Fin 8) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi : affineEvaluate a (point k i) = 0)
    (hj : affineEvaluate a (point k j) = 0)
    (hl : affineEvaluate a (point k l) = 0) :
    ∃ f : Fin 8, i ∈ members f ∧ j ∈ members f ∧ l ∈ members f := by
  have sorted (x y z : Fin 8) (hxy : x < y) (hyz : y < z)
      (hx : affineEvaluate a (point k x) = 0)
      (hy : affineEvaluate a (point k y) = 0)
      (hz : affineEvaluate a (point k z) = 0) :
      ∃ f : Fin 8, x ∈ members f ∧ y ∈ members f ∧ z ∈ members f :=
    (sorted_triple_certificate k a hnon x y z hxy hyz hx hy hz).resolve_left ha
  rcases lt_or_gt_of_ne hij with hij | hji
  · rcases lt_or_gt_of_ne hjl with hjl | hlj
    · exact sorted i j l hij hjl hi hj hl
    · rcases lt_or_gt_of_ne hil with hil | hli
      · obtain ⟨f, hfi, hfl, hfj⟩ := sorted i l j hil hlj hi hl hj
        exact ⟨f, hfi, hfj, hfl⟩
      · obtain ⟨f, hfl, hfi, hfj⟩ := sorted l i j hli hij hl hi hj
        exact ⟨f, hfi, hfj, hfl⟩
  · rcases lt_or_gt_of_ne hil with hil | hli
    · obtain ⟨f, hfj, hfi, hfl⟩ := sorted j i l hji hil hj hi hl
      exact ⟨f, hfi, hfj, hfl⟩
    · rcases lt_or_gt_of_ne hjl with hjl | hlj
      · obtain ⟨f, hfj, hfl, hfi⟩ := sorted j l i hjl hli hj hl hi
        exact ⟨f, hfi, hfj, hfl⟩
      · obtain ⟨f, hfl, hfj, hfi⟩ := sorted l j i hlj hji hl hj hi
        exact ⟨f, hfi, hfj, hfl⟩

theorem facets_complete (k : Fin 2) (F : Set (E 3)) (hF : IsFacet (polytope k) F) :
    ∃ f : Fin 8, F = face k f := by
  have hdF : faceDim F = 2 := by
    have h := hF.2
    have hd := polytope_fullDim k
    change (polytope k).dim = 3 at hd
    omega
  obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw, huF, hvF, hwF⟩ :=
    face_has_three_vertices (polytope k) hF.1 (by omega)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨g, hg⟩ := exists_supportsFace (polytope k) hF.1
  have hcoeff := affineCoefficients_ne_zero (hF.support_ne_zero hg)
  have hnon (v : Fin 8) : 0 ≤ affineEvaluate (affineCoefficients g) (point k v) := by
    rw [affine_evaluate_coefficients]
    exact hg.1 _ (subset_convexHull ℝ _ (point_vertex k v))
  have hi : affineEvaluate (affineCoefficients g) (point k i) = 0 := by
    rw [affine_evaluate_coefficients]
    exact hg.eq_zero huF
  have hj : affineEvaluate (affineCoefficients g) (point k j) = 0 := by
    rw [affine_evaluate_coefficients]
    exact hg.eq_zero hvF
  have hl : affineEvaluate (affineCoefficients g) (point k l) = 0 := by
    rw [affine_evaluate_coefficients]
    exact hg.eq_zero hwF
  obtain ⟨f, hif, hjf, hlf⟩ := three_zero_in_common_facet k (affineCoefficients g) hcoeff hnon
    i j l (fun h => huv (congrArg (point k) h)) (fun h => huw (congrArg (point k) h))
    (fun h => hvw (congrArg (point k) h)) hi hj hl
  refine ⟨f, ?_⟩
  exact two_faces_eq_of_three_common_vertices (polytope k) hF.1 (face_isFace k f)
    hdF (face_dimension k f) (point_vertex k i) (point_vertex k j) (point_vertex k l)
    huv huw hvw huF hvF hwF
    ((point_mem_face_iff k f i).mpr hif) ((point_mem_face_iff k f j).mpr hjf)
    ((point_mem_face_iff k f l).mpr hlf)

def vertexLabels (k : Fin 2) : Fin 8 ≃ VertexType (polytope k) :=
  Equiv.ofBijective (fun i => ⟨point k i, point_vertex k i⟩) (by
    constructor
    · intro i j h
      exact point_injective k (congrArg Subtype.val h)
    · intro v
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp v.property
      exact ⟨i, Subtype.ext hi⟩)

@[simp] theorem vertexLabels_val (k : Fin 2) (i : Fin 8) : (vertexLabels k i).val = point k i := rfl

def faceOrderIso : FaceType (polytope 0) ≃o FaceType (polytope 1) := by
  let b := (vertexLabels 0).symm.trans (vertexLabels 1)
  have hb (i : Fin 8) : b (vertexLabels 0 i) = vertexLabels 1 i := by
    dsimp only [b, Equiv.trans_apply]
    rw [Equiv.symm_apply_apply]
  apply faceOrderIsoOfFacetIncidence (polytope 0) (polytope_fullDim 0)
    (polytope 1) (polytope_fullDim 1) b
  · intro F hF
    obtain ⟨f, hFf⟩ := facets_complete 0 F.val hF
    refine ⟨⟨face 1 f, face_isFace 1 f⟩, face_isFacet 1 f, ?_⟩
    intro v
    obtain ⟨i, rfl⟩ := (vertexLabels 0).surjective v
    rw [hb, vertexLabels_val, vertexLabels_val, hFf]
    exact (point_mem_face_iff 1 f i).trans (point_mem_face_iff 0 f i).symm
  · intro F hF
    obtain ⟨f, hFf⟩ := facets_complete 1 F.val hF
    refine ⟨⟨face 0 f, face_isFace 0 f⟩, face_isFacet 0 f, ?_⟩
    intro v
    obtain ⟨i, rfl⟩ := (vertexLabels 0).surjective v
    rw [hb, vertexLabels_val, vertexLabels_val, hFf]
    exact (point_mem_face_iff 1 f i).trans (point_mem_face_iff 0 f i).symm

end Papers.Polytopes.ConditionalEight

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/ConditionalEightEdges.lean -/



@[expose] public section

/-! The exact ordinary edge graph of both base realizations. -/

noncomputable section
namespace Papers.Polytopes.ConditionalEight

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def neighbors : Fin 8 → Finset (Fin 8) :=
  ![{1, 2, 3, 4}, {0, 2, 5}, {0, 1, 3, 6}, {0, 2, 7},
    {0, 5, 7}, {1, 4, 6, 7}, {2, 5, 7}, {3, 4, 5, 6}]

def IsEdge (i j : Fin 8) : Prop := j ∈ neighbors i

instance decidableIsEdge (i j : Fin 8) : Decidable (IsEdge i j) :=
  inferInstanceAs (Decidable (j ∈ neighbors i))

theorem edge_facets_certificate : ∀ i j : Fin 8, IsEdge i j → i ≠ j ∧
    ∃ f g : Fin 8, members f ∩ members g = {i, j} := by decide

theorem nonedge_closure_certificate : ∀ i j : Fin 8, i ≠ j → ¬IsEdge i j →
    ∃ l : Fin 8, l ≠ i ∧ l ≠ j ∧
      ∀ f : Fin 8, i ∈ members f → j ∈ members f → l ∈ members f := by decide

theorem face_inter_vertex_filter (k : Fin 2) (f g : Fin 8) :
    (polytope k).vertices.filter (fun x => x ∈ face k f ∩ face k g) =
      (members f ∩ members g).image (point k) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxV, hxf, hxg⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxV
    exact Finset.mem_image.mpr ⟨i, Finset.mem_inter.mpr
      ⟨(point_mem_face_iff k f i).mp hxf, (point_mem_face_iff k g i).mp hxg⟩, rfl⟩
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hif, hig⟩ := Finset.mem_inter.mp hi
    exact Finset.mem_filter.mpr ⟨point_vertex k i,
      (point_mem_face_iff k f i).mpr hif, (point_mem_face_iff k g i).mpr hig⟩

theorem step_of_edge (k : Fin 2) (i j : Fin 8) (h : IsEdge i j) :
    GeneralVertexStep (polytope k) (point k i) (point k j) := by
  obtain ⟨hij, f, g, hfg⟩ := edge_facets_certificate i j h
  letI : DecidablePred (fun x : E 3 => x∈face k f∩face k g) :=
    fun _ => Classical.propDecidable _
  have hi : i ∈ members f ∩ members g := by rw [hfg]; simp
  have hj : j ∈ members f ∩ members g := by rw [hfg]; simp
  have hip : point k i ∈ face k f ∩ face k g :=
    ⟨(point_mem_face_iff k f i).mpr (Finset.mem_inter.mp hi).1,
      (point_mem_face_iff k g i).mpr (Finset.mem_inter.mp hi).2⟩
  have hjp : point k j ∈ face k f ∩ face k g :=
    ⟨(point_mem_face_iff k f j).mpr (Finset.mem_inter.mp hj).1,
      (point_mem_face_iff k g j).mpr (Finset.mem_inter.mp hj).2⟩
  have hface := isFace_inter (polytope k) (face_isFace k f) (face_isFace k g) ⟨point k i, hip⟩
  have hseg : face k f ∩ face k g = segment ℝ (point k i) (point k j) := by
    have hh := face_eq_hull_vertices (polytope k) hface
    rw [hh,← convexHull_pair]
    apply congrArg (convexHull ℝ)
    ext x
    constructor
    · intro hx
      obtain ⟨hxV,hxf,hxg⟩ := Finset.mem_filter.mp hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hxV
      have hqfg : q∈members f∩members g := Finset.mem_inter.mpr
        ⟨(point_mem_face_iff k f q).mp hxf,
          (point_mem_face_iff k g q).mp hxg⟩
      rw [hfg] at hqfg
      have hqij : q=i ∨ q=j := by
        simpa only [Finset.mem_insert,Finset.mem_singleton] using hqfg
      rcases hqij with rfl | rfl <;> simp
    · intro hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · rw [hx]
        exact Finset.mem_filter.mpr ⟨point_vertex k i,hip⟩
      · have hxj := Set.mem_singleton_iff.mp hx
        rw [hxj]
        exact Finset.mem_filter.mpr ⟨point_vertex k j,hjp⟩
  refine ⟨point_vertex k j, (point_injective k).ne hij, face k f ∩ face k g,
    hface, ?_, hip, hjp⟩
  unfold faceDim
  rw [hseg, vectorSpan_segment]
  exact finrank_span_singleton (by
    change point k j - point k i ≠ 0
    exact sub_ne_zero.mpr ((point_injective k).ne hij.symm))

theorem edge_of_step (k : Fin 2) (i j : Fin 8)
    (h : GeneralVertexStep (polytope k) (point k i) (point k j)) : IsEdge i j := by
  obtain ⟨_, hne, F, hF, hdF, hiF, hjF⟩ := h
  have hij : i ≠ j := fun h => hne (congrArg (point k) h)
  by_contra hnot
  obtain ⟨l, hli, hlj, hclosure⟩ := nonedge_closure_certificate i j hij hnot
  have hlF : point k l ∈ F := by
    rw [face_eq_inter_facets (polytope k) (polytope_fullDim k) F hF]
    refine ⟨subset_convexHull ℝ _ (point_vertex k l), ?_⟩
    intro G hG hFG
    obtain ⟨f, rfl⟩ := facets_complete k G hG
    exact (point_mem_face_iff k f l).mpr
      (hclosure f ((point_mem_face_iff k f i).mp (hFG hiF))
        ((point_mem_face_iff k f j).mp (hFG hjF)))
  have hseg := edge_eq_segment (polytope k) hF hdF (point_vertex k i) (point_vertex k j) hiF hjF hne
  have hend := (vertex_mem_segment_iff (polytope k) (point_vertex k i)
    (point_vertex k j) (point_vertex k l)).mp (hseg ▸ hlF)
  rcases hend with h | h
  · exact hli ((point_injective k) h)
  · exact hlj ((point_injective k) h)

theorem edge_iff_step (k : Fin 2) (i j : Fin 8) :
    IsEdge i j ↔ GeneralVertexStep (polytope k) (point k i) (point k j) :=
  ⟨step_of_edge k i j, edge_of_step k i j⟩

end Papers.Polytopes.ConditionalEight

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/ConditionalEightDecomposition.lean -/




@[expose] public section

/-! The first base realization has a genuine nontrivial Minkowski decomposition. -/

noncomputable section
namespace Papers.Polytopes.ConditionalEight

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def splitLabel (i : Fin 8) : E 3 := if i.val < 4 then 0 else axis 2

def splitMap : E 3 → E 3 := Function.extend (point 0) splitLabel (fun _ => 0)

theorem splitMap_point (i : Fin 8) : splitMap (point 0 i) = splitLabel i :=
  (point_injective 0).extend_apply splitLabel (fun _ => 0) i

theorem splitLabel_parallel (i j : Fin 8) (h : IsEdge i j) :
    ∃ c : ℝ, splitLabel j - splitLabel i = c • (point 0 j - point 0 i) := by
  refine ⟨if (i.val < 4 ↔ j.val < 4) then 0 else (1 / 20 : ℝ), ?_⟩
  fin_cases i <;> fin_cases j <;> norm_num [IsEdge, neighbors] at h
  all_goals
    ext q
    fin_cases q <;> norm_num [splitLabel, axis, point, vertexRows]

theorem splitMap_parallel : IsParallelMap (polytope 0) splitMap := by
  intro x hx y hy hxy
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨c, hc⟩ := splitLabel_parallel i j (edge_of_step 0 i j hxy)
  exact ⟨c, by simpa only [splitMap_point] using hc⟩

theorem splitMap_not_homothety : ¬IsHomothetyOnVertices (polytope 0) splitMap := by
  rintro ⟨a, b, hab⟩
  have h0 := hab (point 0 0) (point_vertex 0 0)
  have h1 := hab (point 0 1) (point_vertex 0 1)
  have h4 := hab (point 0 4) (point_vertex 0 4)
  rw [splitMap_point] at h0 h1 h4
  have h00 := congrArg (fun x : E 3 => x 0) h0
  have h02 := congrArg (fun x : E 3 => x 2) h0
  have h10 := congrArg (fun x : E 3 => x 0) h1
  have h42 := congrArg (fun x : E 3 => x 2) h4
  norm_num [splitLabel, point, vertexRows, axis] at h00 h02 h10 h42
  linarith

theorem decomposable : MinkowskiDecomposable (polytope 0) :=
  (minkowski_decomposable_iff_parallel_map (polytope 0)).mpr
    ⟨splitMap, splitMap_parallel, splitMap_not_homothety⟩

end Papers.Polytopes.ConditionalEight

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/ConditionalEightIndecomposable.lean -/



@[expose] public section

/-!
# The second base realization is indecomposable

Its lower and upper four-vertex pieces are unions of two actual triangles.
Two actual crossing edges have affinely independent endpoints and join the
two rigid pieces. The proof concerns every parallel map of the entire
geometric edge graph, hence ordinary Minkowski indecomposability.
-/

noncomputable section
namespace Papers.Polytopes.ConditionalEight

open Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def lowerPiece : Set (E 3) :=
  ({point 1 0, point 1 1, point 1 2} : Set (E 3)) ∪ {point 1 0, point 1 2, point 1 3}

def upperPiece : Set (E 3) :=
  ({point 1 4, point 1 5, point 1 7} : Set (E 3)) ∪ {point 1 5, point 1 6, point 1 7}

theorem lowerPiece_rigid : ParallelRigid (polytope 1) lowerPiece := by
  have h₁ := parallelRigid_triangle (polytope 1) (point_vertex 1 0) (point_vertex 1 1)
    (point_vertex 1 2) (step_of_edge 1 0 1 (by decide))
    (step_of_edge 1 0 2 (by decide)) (step_of_edge 1 1 2 (by decide))
  have h₂ := parallelRigid_triangle (polytope 1) (point_vertex 1 0) (point_vertex 1 2)
    (point_vertex 1 3) (step_of_edge 1 0 2 (by decide))
    (step_of_edge 1 0 3 (by decide)) (step_of_edge 1 2 3 (by decide))
  exact h₁.union_of_two_common h₂ (u := point 1 0) (v := point 1 2)
    (by simp) (by simp) (by simp) (by simp)
    ((point_injective 1).ne (by decide : (0 : Fin 8) ≠ 2))

theorem upperPiece_rigid : ParallelRigid (polytope 1) upperPiece := by
  have h₁ := parallelRigid_triangle (polytope 1) (point_vertex 1 4) (point_vertex 1 5)
    (point_vertex 1 7) (step_of_edge 1 4 5 (by decide))
    (step_of_edge 1 4 7 (by decide)) (step_of_edge 1 5 7 (by decide))
  have h₂ := parallelRigid_triangle (polytope 1) (point_vertex 1 5) (point_vertex 1 6)
    (point_vertex 1 7) (step_of_edge 1 5 6 (by decide))
    (step_of_edge 1 5 7 (by decide)) (step_of_edge 1 6 7 (by decide))
  exact h₁.union_of_two_common h₂ (u := point 1 5) (v := point 1 7)
    (by simp) (by simp) (by simp) (by simp)
    ((point_injective 1).ne (by decide : (5 : Fin 8) ≠ 7))

def crossCycle : Fin 4 → E 3 := ![point 1 0, point 1 4, point 1 6, point 1 2]

theorem crossCycle_independent : AffineIndependent ℝ crossCycle := by
  apply (affineIndependent_iff_of_fintype ℝ crossCycle).mpr
  intro w hsum hlin i
  rw [Finset.weightedVSub_eq_linear_combination _ hsum] at hlin
  have h0 := congrArg (fun x : E 3 => x 0) hlin
  have h1 := congrArg (fun x : E 3 => x 1) hlin
  have h2 := congrArg (fun x : E 3 => x 2) hlin
  norm_num [crossCycle, point, vertexRows, Fin.sum_univ_succ] at h0 h1 h2 hsum
  have hw0 : w 0=0 := by linarith
  have hw1 : w 1=0 := by linarith
  have hw2 : w 2=0 := by linarith
  have hw3 : w 3=0 := by linarith
  fin_cases i <;> assumption

theorem pieces_cover : lowerPiece ∪ upperPiece = ((polytope 1).vertices : Set (E 3)) := by
  ext x
  constructor
  · intro hx
    simp only [lowerPiece, upperPiece, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    all_goals rcases hx with hx | hx
    all_goals rcases hx with rfl | rfl | rfl
    all_goals exact point_vertex 1 _
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    fin_cases i <;> simp [lowerPiece, upperPiece]

theorem vertices_rigid : ParallelRigid (polytope 1) ((polytope 1).vertices : Set (E 3)) := by
  rw [← pieces_cover]
  apply lowerPiece_rigid.union_of_skew_connections upperPiece_rigid crossCycle crossCycle_independent
  · simp [crossCycle, lowerPiece]
  · simp [crossCycle, lowerPiece]
  · simp [crossCycle, upperPiece]
  · simp [crossCycle, upperPiece]
  · exact step_of_edge 1 0 4 (by decide)
  · exact step_of_edge 1 6 2 (by decide)

theorem indecomposable : ¬MinkowskiDecomposable (polytope 1) := by
  intro h
  obtain ⟨g, hg, hnon⟩ := (minkowski_decomposable_iff_parallel_map (polytope 1)).mp h
  exact hnon (vertices_rigid g hg)

theorem conditionallyDecomposable : ConditionallyDecomposable (polytope 0) :=
  ⟨⟨polytope 0, CombinatoriallyEquivalent.refl _, decomposable⟩,
    ⟨polytope 1, ⟨faceOrderIso⟩, indecomposable⟩⟩

theorem face_vertex_filter (k : Fin 2) (f : Fin 8) :
    (polytope k).vertices.filter (fun x => x ∈ face k f) = (members f).image (point k) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxV, hxF⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxV
    exact Finset.mem_image.mpr ⟨i, (point_mem_face_iff k f i).mp hxF, rfl⟩
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨point_vertex k i, (point_mem_face_iff k f i).mpr hi⟩

theorem four_vertices_outside_facet :
    (polytope 0).vertices.card =
      ((polytope 0).vertices.filter (fun x => x ∈ face 0 4)).card + 4 := by
  rw [polytope_card, face_vertex_filter, Finset.card_image_of_injective _ (point_injective 0)]
  norm_num [members]

end Papers.Polytopes.ConditionalEight

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/WedgeGeometry.lean -/









@[expose] public section

set_option autoImplicit false

/-!
# The ordinary wedge and Minkowski addition

The set is the literal interval bundle 0 ≤ t ≤ f(x). The Minkowski identity
allows a summand on which f vanishes identically, so the degenerate faces
arising from arbitrary-dimensional Minkowski summands require no exception.
-/

noncomputable section
namespace Papers.Wedges
open Set
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def wedge (P : Set V) (f : V →ₗ[ℝ] ℝ) : Set (V × ℝ) :=
  {z | z.1 ∈ P ∧ 0 ≤ z.2 ∧ z.2 ≤ f z.1}

def bottom : V →ₗ[ℝ] V × ℝ := (LinearMap.id : V →ₗ[ℝ] V).prod 0

def top (f : V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] V × ℝ := (LinearMap.id : V →ₗ[ℝ] V).prod f

@[simp] theorem bottom_apply (x : V) : bottom x = (x, 0) := rfl
@[simp] theorem top_apply (f : V →ₗ[ℝ] ℝ) (x : V) : top f x = (x, f x) := rfl

theorem convex_wedge {P : Set V} (hP : Convex ℝ P) (f : V →ₗ[ℝ] ℝ) :
    Convex ℝ (wedge P f) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hP hx.1 hy.1 ha hb hab, ?_, ?_⟩
  · change 0 ≤ a * x.2 + b * y.2
    exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
  · change a * x.2 + b * y.2 ≤ f (a • x.1 + b • y.1)
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hx.2.2 ha)
      (mul_le_mul_of_nonneg_left hy.2.2 hb)

theorem fst_image_wedge (P : Set V) (f : V →ₗ[ℝ] ℝ)
    (hP : ∀ x ∈ P, 0 ≤ f x) : Prod.fst '' wedge P f = P := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    exact hz.1
  · intro x hx
    exact ⟨(x, 0), ⟨hx, le_rfl, hP x hx⟩, rfl⟩

/-- The complete set identity, with nonnegative heights and no proper-face
or full-dimensionality assumptions on either summand. -/
theorem wedge_add (A B : Set V) (f : V →ₗ[ℝ] ℝ)
    (hA : ∀ x ∈ A, 0 ≤ f x) (hB : ∀ x ∈ B, 0 ≤ f x) :
    wedge (A + B) f = wedge A f + wedge B f := by
  apply Set.Subset.antisymm
  · rintro ⟨x, t⟩ ⟨hx, ht0, ht⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
    have hsum : t ≤ f a + f b := by simpa only [map_add] using ht
    by_cases hta : t ≤ f a
    · apply Set.mem_add.mpr
      exact ⟨(a, t), ⟨ha, ht0, hta⟩, (b, 0), ⟨hb, le_rfl, hB b hb⟩,
        by ext <;> simp⟩
    · have hat : f a < t := lt_of_not_ge hta
      apply Set.mem_add.mpr
      refine ⟨(a, f a), ⟨ha, hA a ha, le_rfl⟩,
        (b, t - f a), ⟨hb, sub_nonneg.mpr hat.le, by linarith⟩, ?_⟩
      ext <;> simp
  · intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
    refine ⟨Set.mem_add.mpr ⟨a.1, ha.1, b.1, hb.1, rfl⟩,
      add_nonneg ha.2.1 hb.2.1, ?_⟩
    change a.2 + b.2 ≤ f (a.1 + b.1)
    rw [map_add]
    exact add_le_add ha.2.2 hb.2.2

/-- A finite convex hull wedges to the convex hull of its two lifted vertex
sets. The equality also covers points at height zero, which occur only once
in the union. -/
theorem wedge_convexHull (S : Set V) (f : V →ₗ[ℝ] ℝ)
    (hS : ∀ x ∈ S, 0 ≤ f x) :
    wedge (convexHull ℝ S) f = convexHull ℝ (bottom '' S ∪ top f '' S) := by
  have hnon : ∀ x ∈ convexHull ℝ S, 0 ≤ f x :=
    convexHull_min hS (convex_halfSpace_ge f.isLinear 0)
  apply Set.Subset.antisymm
  · rintro ⟨x, t⟩ ⟨hx, ht0, ht⟩
    have hb : bottom x ∈ convexHull ℝ (bottom '' S ∪ top f '' S) := by
      apply convexHull_mono Set.subset_union_left
      rw [← bottom.image_convexHull]
      exact Set.mem_image_of_mem bottom hx
    have hu : top f x ∈ convexHull ℝ (bottom '' S ∪ top f '' S) := by
      apply convexHull_mono Set.subset_union_right
      rw [← (top f).image_convexHull]
      exact Set.mem_image_of_mem (top f) hx
    by_cases hzero : f x = 0
    · have htzero : t = 0 := by rw [hzero] at ht; linarith
      simpa only [bottom_apply, htzero] using hb
    · have hpos : 0 < f x := lt_of_le_of_ne (hnon x hx) (Ne.symm hzero)
      have hβ : 0 ≤ t / f x := div_nonneg ht0 hpos.le
      have hα : 0 ≤ 1 - t / f x := sub_nonneg.mpr ((div_le_one hpos).mpr ht)
      have hmem := (convex_convexHull ℝ (bottom '' S ∪ top f '' S)) hb hu
        hα hβ (by ring : 1 - t / f x + t / f x = 1)
      have heq : (1 - t / f x) • bottom x + (t / f x) • top f x = (x, t) := by
        apply Prod.ext
        · change (1 - t / f x) • x + (t / f x) • x = x
          module
        · change (1 - t / f x) * 0 + (t / f x) * f x = t
          field_simp [hzero] <;> ring
      exact heq ▸ hmem
  · apply convexHull_min
    · intro z hz
      rcases hz with hz | hz
      · obtain ⟨x, hx, rfl⟩ := hz
        exact ⟨subset_convexHull ℝ _ hx, le_rfl, hS x hx⟩
      · obtain ⟨x, hx, rfl⟩ := hz
        exact ⟨subset_convexHull ℝ _ hx, hS x hx, le_rfl⟩
    · exact convex_wedge (convex_convexHull ℝ S) f

end Papers.Wedges

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/WedgeAffineGeometry.lean -/



@[expose] public section

/-!
# Wedges with an affine height

The height is an actual affine functional, so no translation of the base
polytope is implicit. The wedge is the interval bundle over the original
set. Its finite generating set consists of its two endpoint lifts. The
Minkowski identity permits different affine constants on the two summands.
-/

noncomputable section
namespace Papers.Wedges

open Set
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def affineWedge (P : Set V) (f : V →ᵃ[ℝ] ℝ) : Set (V × ℝ) :=
  {z | z.1 ∈ P ∧ 0 ≤ z.2 ∧ z.2 ≤ f z.1}

def bottomAffine : V →ᵃ[ℝ] V × ℝ :=
  (AffineMap.id ℝ V).prod (AffineMap.const ℝ V 0)

def topAffine (f : V →ᵃ[ℝ] ℝ) : V →ᵃ[ℝ] V × ℝ :=
  (AffineMap.id ℝ V).prod f

@[simp] theorem bottomAffine_apply (x : V) : bottomAffine x = (x, 0) := rfl

@[simp] theorem topAffine_apply (f : V →ᵃ[ℝ] ℝ) (x : V) :
    topAffine f x = (x, f x) := rfl

theorem convex_affineWedge {P : Set V} (hP : Convex ℝ P) (f : V →ᵃ[ℝ] ℝ) :
    Convex ℝ (affineWedge P f) := by
  have h₁ : Convex ℝ ((AffineMap.fst : V × ℝ →ᵃ[ℝ] V) ⁻¹' P) :=
    Convex.affine_preimage _ hP
  have h₂ : Convex ℝ ((AffineMap.snd : V × ℝ →ᵃ[ℝ] ℝ) ⁻¹' Ici 0) :=
    Convex.affine_preimage _ (convex_Ici 0)
  have h₃ := Convex.affine_preimage
      (f.comp (AffineMap.fst : V × ℝ →ᵃ[ℝ] V) - AffineMap.snd)
      (convex_Ici (0 : ℝ))
  convert h₁.inter (h₂.inter h₃) using 1
  ext z
  change (z.1 ∈ P ∧ 0 ≤ z.2 ∧ z.2 ≤ f z.1) ↔
    z.1 ∈ P ∧ 0 ≤ z.2 ∧ 0 ≤ f z.1 - z.2
  rw [sub_nonneg]

theorem affine_nonneg_on_convexHull (S : Set V) (f : V →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) : ∀ x ∈ convexHull ℝ S, 0 ≤ f x :=
  convexHull_min hf (Convex.affine_preimage f (convex_Ici 0))

theorem affineWedge_convexHull (S : Set V) (f : V →ᵃ[ℝ] ℝ)
    (hS : ∀ x ∈ S, 0 ≤ f x) :
    affineWedge (convexHull ℝ S) f =
      convexHull ℝ (bottomAffine '' S ∪ topAffine f '' S) := by
  have hnon := affine_nonneg_on_convexHull S f hS
  apply Set.Subset.antisymm
  · rintro ⟨x, t⟩ ⟨hx, ht0, ht⟩
    have hb : bottomAffine x ∈ convexHull ℝ (bottomAffine '' S ∪ topAffine f '' S) := by
      apply convexHull_mono Set.subset_union_left
      rw [← bottomAffine.image_convexHull]
      exact Set.mem_image_of_mem bottomAffine hx
    have hu : topAffine f x ∈ convexHull ℝ (bottomAffine '' S ∪ topAffine f '' S) := by
      apply convexHull_mono Set.subset_union_right
      rw [← (topAffine f).image_convexHull]
      exact Set.mem_image_of_mem (topAffine f) hx
    by_cases hzero : f x = 0
    · have htzero : t = 0 := by rw [hzero] at ht; linarith
      simpa only [bottomAffine_apply, htzero] using hb
    · have hpos : 0 < f x := lt_of_le_of_ne (hnon x hx) (Ne.symm hzero)
      have hβ : 0 ≤ t / f x := div_nonneg ht0 hpos.le
      have hα : 0 ≤ 1 - t / f x := sub_nonneg.mpr ((div_le_one hpos).mpr ht)
      have hmem := (convex_convexHull ℝ (bottomAffine '' S ∪ topAffine f '' S))
        hb hu hα hβ (by ring : 1 - t / f x + t / f x = 1)
      have heq : (1 - t / f x) • bottomAffine x + (t / f x) • topAffine f x = (x, t) := by
        apply Prod.ext
        · change (1 - t / f x) • x + (t / f x) • x = x
          module
        · change (1 - t / f x) * 0 + (t / f x) * f x = t
          field_simp [hzero] <;> ring
      exact heq ▸ hmem
  · apply convexHull_min
    · intro z hz
      rcases hz with hz | hz
      · obtain ⟨x, hx, rfl⟩ := hz
        exact ⟨subset_convexHull ℝ _ hx, le_rfl, hS x hx⟩
      · obtain ⟨x, hx, rfl⟩ := hz
        exact ⟨subset_convexHull ℝ _ hx, hS x hx, le_rfl⟩
    · exact convex_affineWedge (convex_convexHull ℝ S) f

/-- The complete interval-splitting identity. Compatibility of the three
affine heights is an explicit equality on the actual summands. -/
theorem affineWedge_add (A B : Set V) (f fA fB : V →ᵃ[ℝ] ℝ)
    (hA : ∀ a ∈ A, 0 ≤ fA a) (hB : ∀ b ∈ B, 0 ≤ fB b)
    (hadd : ∀ a ∈ A, ∀ b ∈ B, f (a + b) = fA a + fB b) :
    affineWedge (A + B) f = affineWedge A fA + affineWedge B fB := by
  apply Set.Subset.antisymm
  · rintro ⟨x, t⟩ ⟨hx, ht0, ht⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
    have hsum : t ≤ fA a + fB b := by rwa [hadd a ha b hb] at ht
    by_cases hta : t ≤ fA a
    · apply Set.mem_add.mpr
      exact ⟨(a, t), ⟨ha, ht0, hta⟩, (b, 0), ⟨hb, le_rfl, hB b hb⟩,
        by ext <;> simp⟩
    · have hat : fA a < t := lt_of_not_ge hta
      apply Set.mem_add.mpr
      refine ⟨(a, fA a), ⟨ha, hA a ha, le_rfl⟩,
        (b, t - fA a), ⟨hb, sub_nonneg.mpr hat.le, by linarith⟩, ?_⟩
      ext <;> simp
  · intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
    refine ⟨Set.mem_add.mpr ⟨a.1, ha.1, b.1, hb.1, rfl⟩,
      add_nonneg ha.2.1 hb.2.1, ?_⟩
    change a.2 + b.2 ≤ f (a.1 + b.1)
    rw [hadd a.1 ha.1 b.1 hb.1]
    exact add_le_add ha.2.2 hb.2.2

end Papers.Wedges

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/WedgeVertices.lean -/




@[expose] public section

/-!
# The actual extreme vertices of an affine wedge

The interval-bundle construction is placed in ordinary Euclidean space of
one higher dimension. Every listed endpoint is proved extreme by a strict
supporting affine form. The two lifts coincide exactly on the zero-height
face, giving the unrestricted vertex count 2N − |F|.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.Wedges
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def wedgeCoordinates : (E d × ℝ) ≃ₗ[ℝ] E (d + 1) where
  toFun z := WithLp.toLp 2 (Fin.cons z.2 (fun i => z.1 i))
  invFun z := (WithLp.toLp 2 (fun i => z i.succ), z 0)
  map_add' z w := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  map_smul' c z := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  left_inv z := by
    apply Prod.ext
    · ext i
      rfl
    · rfl
  right_inv z := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i

def wedgeProjection : E (d + 1) →ₗ[ℝ] E d :=
  (LinearMap.fst ℝ (E d) ℝ).comp wedgeCoordinates.symm.toLinearMap

def wedgeHeight : E (d + 1) →ₗ[ℝ] ℝ :=
  (LinearMap.snd ℝ (E d) ℝ).comp wedgeCoordinates.symm.toLinearMap

def wedgeLower : E d →ₗ[ℝ] E (d + 1) :=
  wedgeCoordinates.toLinearMap.comp (LinearMap.inl ℝ (E d) ℝ)

def wedgeUpper (f : E d →ᵃ[ℝ] ℝ) : E d →ᵃ[ℝ] E (d + 1) :=
  wedgeCoordinates.toLinearMap.toAffineMap.comp (topAffine f)

@[simp] theorem wedgeProjection_coordinates (z : E d × ℝ) :
    wedgeProjection (wedgeCoordinates z) = z.1 := by
  change (wedgeCoordinates.symm (wedgeCoordinates z)).1 = z.1
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem wedgeHeight_coordinates (z : E d × ℝ) :
    wedgeHeight (wedgeCoordinates z) = z.2 := by
  change (wedgeCoordinates.symm (wedgeCoordinates z)).2 = z.2
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem wedgeLower_apply (x : E d) :
    wedgeLower x = wedgeCoordinates (x, (0 : ℝ)) := rfl

@[simp] theorem wedgeUpper_apply (f : E d →ᵃ[ℝ] ℝ) (x : E d) :
    wedgeUpper f x = wedgeCoordinates (x, f x) := rfl

@[simp] theorem wedgeProjection_lower (x : E d) : wedgeProjection (wedgeLower x) = x := by
  rw [wedgeLower_apply, wedgeProjection_coordinates]

@[simp] theorem wedgeProjection_upper (f : E d →ᵃ[ℝ] ℝ) (x : E d) :
    wedgeProjection (wedgeUpper f x) = x := by
  rw [wedgeUpper_apply, wedgeProjection_coordinates]

@[simp] theorem wedgeHeight_lower (x : E d) : wedgeHeight (wedgeLower x) = 0 := by
  rw [wedgeLower_apply, wedgeHeight_coordinates]

@[simp] theorem wedgeHeight_upper (f : E d →ᵃ[ℝ] ℝ) (x : E d) :
    wedgeHeight (wedgeUpper f x) = f x := by
  rw [wedgeUpper_apply, wedgeHeight_coordinates]

theorem wedgeLower_injective : Function.Injective (wedgeLower (d := d)) := by
  intro x y h
  simpa only [wedgeProjection_lower] using congrArg wedgeProjection h

theorem wedgeUpper_injective (f : E d →ᵃ[ℝ] ℝ) : Function.Injective (wedgeUpper f) := by
  intro x y h
  simpa only [wedgeProjection_upper] using congrArg wedgeProjection h

theorem wedgeLower_eq_upper_iff (f : E d →ᵃ[ℝ] ℝ) (x y : E d) :
    wedgeLower x = wedgeUpper f y ↔ x = y ∧ f y = 0 := by
  constructor
  · intro h
    have hxy : x = y := by
      simpa only [wedgeProjection_lower, wedgeProjection_upper] using congrArg wedgeProjection h
    have hf : 0 = f y := by
      simpa only [wedgeHeight_lower, wedgeHeight_upper] using congrArg wedgeHeight h
    exact ⟨hxy, hf.symm⟩
  · rintro ⟨rfl, hy⟩
    rw [wedgeLower_apply, wedgeUpper_apply, hy]

def wedgeVertexSet (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) : Finset (E (d + 1)) :=
  P.vertices.image wedgeLower ∪ P.vertices.image (wedgeUpper f)

theorem wedgeVertexSet_nonempty (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) :
    (wedgeVertexSet P f).Nonempty := by
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  exact ⟨wedgeLower v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)⟩

def polytopeOfStrictAffineMinima (S : Finset (E d)) (hne : S.Nonempty)
    (hmin : ∀ v ∈ S, ∃ f : E d →ᵃ[ℝ] ℝ, ∀ w ∈ S, w ≠ v → f v < f w) :
    ConvexPolytope d :=
  polytopeOfStrictMinima S hne (by
    intro v hv
    obtain ⟨f, hf⟩ := hmin v hv
    refine ⟨f.linear.toContinuousLinearMap, ?_⟩
    intro w hw hwv
    have h := hf w hw hwv
    rw [affine_form_apply f v, affine_form_apply f w] at h
    exact (add_lt_add_iff_right (f 0)).mp h)

theorem vertex_support_strict
    (P : ConvexPolytope d) (v : E d) (hv : v ∈ P.vertices) :
    ∃ g : E d →ᵃ[ℝ] ℝ, g v = 0 ∧
      (∀ w ∈ P.vertices, 0 ≤ g w) ∧
      ∀ w ∈ P.vertices, w ≠ v → 0 < g w := by
  obtain ⟨g, hg⟩ := exists_supportsFace P (vertex_isFace P hv)
  refine ⟨g, hg.eq_zero (Set.mem_singleton _),
    fun w hw => hg.1 w (subset_convexHull ℝ _ hw), ?_⟩
  intro w hw hwv
  apply lt_of_le_of_ne (hg.1 w (subset_convexHull ℝ _ hw))
  intro hz
  exact hwv ((hg.mem_iff w).mpr ⟨subset_convexHull ℝ _ hw, hz.symm⟩)

def wedgeLowerExposer (g : E d →ᵃ[ℝ] ℝ) : E (d + 1) →ᵃ[ℝ] ℝ :=
  g.comp wedgeProjection.toAffineMap + wedgeHeight.toAffineMap

def wedgeUpperExposer (f g : E d →ᵃ[ℝ] ℝ) : E (d + 1) →ᵃ[ℝ] ℝ :=
  g.comp wedgeProjection.toAffineMap + f.comp wedgeProjection.toAffineMap - wedgeHeight.toAffineMap

@[simp] theorem wedgeLowerExposer_lower (g : E d →ᵃ[ℝ] ℝ) (x : E d) :
    wedgeLowerExposer g (wedgeLower x) = g x := by
  change g (wedgeProjection (wedgeLower x)) + wedgeHeight (wedgeLower x) = g x
  rw [wedgeProjection_lower, wedgeHeight_lower, add_zero]

@[simp] theorem wedgeLowerExposer_upper (f g : E d →ᵃ[ℝ] ℝ) (x : E d) :
    wedgeLowerExposer g (wedgeUpper f x) = g x + f x := by
  change g (wedgeProjection (wedgeUpper f x)) + wedgeHeight (wedgeUpper f x) = _
  rw [wedgeProjection_upper, wedgeHeight_upper]

@[simp] theorem wedgeUpperExposer_lower (f g : E d →ᵃ[ℝ] ℝ) (x : E d) :
    wedgeUpperExposer f g (wedgeLower x) = g x + f x := by
  change g (wedgeProjection (wedgeLower x)) + f (wedgeProjection (wedgeLower x)) -
    wedgeHeight (wedgeLower x) = _
  rw [wedgeProjection_lower, wedgeHeight_lower, sub_zero]

@[simp] theorem wedgeUpperExposer_upper (f g : E d →ᵃ[ℝ] ℝ) (x : E d) :
    wedgeUpperExposer f g (wedgeUpper f x) = g x := by
  change g (wedgeProjection (wedgeUpper f x)) + f (wedgeProjection (wedgeUpper f x)) -
    wedgeHeight (wedgeUpper f x) = _
  rw [wedgeProjection_upper, wedgeHeight_upper, add_sub_cancel_right]

theorem wedgeVertexSet_strict_minima
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    ∀ v ∈ wedgeVertexSet P f, ∃ g : E (d + 1) →ᵃ[ℝ] ℝ,
      ∀ w ∈ wedgeVertexSet P f, w ≠ v → g v < g w := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨v, hvP, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨g, hgv, hg, hstrict⟩ := vertex_support_strict P v hvP
    refine ⟨wedgeLowerExposer g, ?_⟩
    intro w hw hwv
    rw [wedgeLowerExposer_lower, hgv]
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨w, hwP, rfl⟩ := Finset.mem_image.mp hw
      rw [wedgeLowerExposer_lower]
      exact hstrict w hwP (fun h => hwv (congrArg wedgeLower h))
    · obtain ⟨w, hwP, rfl⟩ := Finset.mem_image.mp hw
      rw [wedgeLowerExposer_upper]
      by_cases hwv' : w = v
      · subst w
        rw [hgv, zero_add]
        apply lt_of_le_of_ne (hf v hvP)
        intro hzero
        exact hwv ((wedgeLower_eq_upper_iff f v v).mpr ⟨rfl, hzero.symm⟩).symm
      · exact add_pos_of_pos_of_nonneg (hstrict w hwP hwv') (hf w hwP)
  · obtain ⟨v, hvP, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨g, hgv, hg, hstrict⟩ := vertex_support_strict P v hvP
    refine ⟨wedgeUpperExposer f g, ?_⟩
    intro w hw hwv
    rw [wedgeUpperExposer_upper, hgv]
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨w, hwP, rfl⟩ := Finset.mem_image.mp hw
      rw [wedgeUpperExposer_lower]
      by_cases hwv' : w = v
      · subst w
        rw [hgv, zero_add]
        apply lt_of_le_of_ne (hf v hvP)
        intro hzero
        exact hwv ((wedgeLower_eq_upper_iff f v v).mpr ⟨rfl, hzero.symm⟩)
      · exact add_pos_of_pos_of_nonneg (hstrict w hwP hwv') (hf w hwP)
    · obtain ⟨w, hwP, rfl⟩ := Finset.mem_image.mp hw
      rw [wedgeUpperExposer_upper]
      exact hstrict w hwP (fun h => hwv (congrArg (wedgeUpper f) h))

def wedgePolytope (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) : ConvexPolytope (d + 1) :=
  polytopeOfStrictAffineMinima (wedgeVertexSet P f) (wedgeVertexSet_nonempty P f)
    (wedgeVertexSet_strict_minima P f hf)

@[simp] theorem wedgePolytope_vertices
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    (wedgePolytope P f hf).vertices = wedgeVertexSet P f := rfl

theorem wedgeVertexSet_intersection (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) :
    P.vertices.image wedgeLower ∩ P.vertices.image (wedgeUpper f) =
      (P.vertices.filter (fun v => f v = 0)).image wedgeLower := by
  ext z
  constructor
  · intro hz
    obtain ⟨hLower, hUpper⟩ := Finset.mem_inter.mp hz
    obtain ⟨x, hxP, rfl⟩ := Finset.mem_image.mp hLower
    obtain ⟨y, hyP, hxy⟩ := Finset.mem_image.mp hUpper
    obtain ⟨rfl, hf⟩ := (wedgeLower_eq_upper_iff f x y).mp hxy.symm
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hxP, hf⟩)
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx, hf⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ hx, ?_⟩
    exact Finset.mem_image.mpr
      ⟨x, hx, ((wedgeLower_eq_upper_iff f x x).mpr ⟨rfl, hf⟩).symm⟩

theorem wedgePolytope_card
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    (wedgePolytope P f hf).vertices.card =
      2 * P.vertices.card - (P.vertices.filter (fun v => f v = 0)).card := by
  rw [wedgePolytope_vertices, wedgeVertexSet, Finset.card_union, wedgeVertexSet_intersection,
    Finset.card_image_of_injective _ wedgeLower_injective,
    Finset.card_image_of_injective _ (wedgeUpper_injective f),
    Finset.card_image_of_injective _ wedgeLower_injective]
  omega

theorem wedgePolytope_body
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    (wedgePolytope P f hf).toSet = wedgeCoordinates '' affineWedge P.toSet f := by
  change convexHull ℝ ((wedgePolytope P f hf).vertices : Set (E (d + 1))) =
    wedgeCoordinates '' affineWedge (convexHull ℝ (P.vertices : Set (E d))) f
  rw [affineWedge_convexHull (P.vertices : Set (E d)) f hf]
  change convexHull ℝ ((wedgePolytope P f hf).vertices : Set (E (d + 1))) =
    wedgeCoordinates.toLinearMap '' convexHull ℝ
      (bottomAffine '' (P.vertices : Set (E d)) ∪ topAffine f '' (P.vertices : Set (E d)))
  rw [wedgeCoordinates.toLinearMap.image_convexHull]
  apply congrArg (convexHull ℝ)
  ext z
  simp only [wedgePolytope_vertices, wedgeVertexSet, Finset.coe_union, Finset.coe_image,
    Set.mem_union, Set.mem_image, Set.image_union]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨bottomAffine x, ⟨x, hx, rfl⟩, rfl⟩
    · exact Or.inr ⟨topAffine f x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro (⟨y, ⟨x, hx, rfl⟩, rfl⟩ | ⟨y, ⟨x, hx, rfl⟩, rfl⟩)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩

end Papers.Polytopes

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/WedgeFacets.lean -/



@[expose] public section

/-!
# Dimension and the two distinguished facets of a wedge

The new coordinate is an actual extra Euclidean coordinate. The lower and
upper copies of the original polytope are exposed faces. A positive-height
vertex supplies the missing vertical direction, so the construction raises
dimension by exactly one.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical
open Papers.Wedges
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def wedgeVertical : E (d + 1) := wedgeCoordinates ((0 : E d), (1 : ℝ))

theorem wedgeCoordinates_projection_height (z : E (d + 1)) :
    wedgeCoordinates (wedgeProjection z, wedgeHeight z) = z := by
  change wedgeCoordinates (wedgeCoordinates.symm z) = z
  exact wedgeCoordinates.apply_symm_apply z

theorem wedge_coordinates_split (x : E d) (t : ℝ) :
    wedgeLower x + t • wedgeVertical = wedgeCoordinates (x, t) := by
  rw [wedgeLower_apply]
  change wedgeCoordinates (x, 0) + t • wedgeCoordinates (0, 1) = _
  rw [← map_smul, ← map_add]
  congr 1
  ext <;> simp

theorem wedge_split (z : E (d + 1)) :
    wedgeLower (wedgeProjection z) + wedgeHeight z • wedgeVertical = z := by
  rw [wedge_coordinates_split, wedgeCoordinates_projection_height]

theorem wedge_upper_split (f : E d →ᵃ[ℝ] ℝ) (x : E d) :
    wedgeUpper f x = wedgeLower x + f x • wedgeVertical := by
  rw [wedge_coordinates_split, wedgeUpper_apply]

theorem mem_wedgePolytope_iff
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (z : E (d + 1)) :
    z ∈ (wedgePolytope P f hf).toSet ↔
      wedgeProjection z ∈ P.toSet ∧ 0 ≤ wedgeHeight z ∧
        wedgeHeight z ≤ f (wedgeProjection z) := by
  rw [wedgePolytope_body]
  constructor
  · rintro ⟨⟨x, t⟩, hz, rfl⟩
    change x ∈ P.toSet ∧ 0 ≤ t ∧ t ≤ f x at hz
    simpa only [wedgeProjection_coordinates, wedgeHeight_coordinates] using hz
  · intro hz
    exact ⟨(wedgeProjection z, wedgeHeight z), hz, wedgeCoordinates_projection_height z⟩

theorem wedge_lower_mem
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    {x : E d} (hx : x ∈ P.toSet) : wedgeLower x ∈ (wedgePolytope P f hf).toSet := by
  apply (mem_wedgePolytope_iff P f hf _).mpr
  rw [wedgeProjection_lower, wedgeHeight_lower]
  exact ⟨hx, le_rfl, affine_nonneg_on_hull P.vertices f hf x hx⟩

theorem wedge_upper_mem
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    {x : E d} (hx : x ∈ P.toSet) : wedgeUpper f x ∈ (wedgePolytope P f hf).toSet := by
  apply (mem_wedgePolytope_iff P f hf _).mpr
  rw [wedgeProjection_upper, wedgeHeight_upper]
  exact ⟨hx, affine_nonneg_on_hull P.vertices f hf x hx, le_rfl⟩

theorem wedgePolytope_fullDim
    (P : ConvexPolytope d) (hP : P.IsFullDim) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (hpos : ∃ v ∈ P.vertices, 0 < f v) : (wedgePolytope P f hf).IsFullDim := by
  let U := vectorSpan ℝ (wedgePolytope P f hf).toSet
  have hspan : vectorSpan ℝ P.toSet = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change finrank ℝ (vectorSpan ℝ P.toSet) = d at hP
    simpa only [finrank_euclideanSpace_fin] using hP
  have hmap : (vectorSpan ℝ P.toSet).map wedgeLower ≤ U := by
    change (vectorSpan ℝ P.toSet).map wedgeLower.toAffineMap.linear ≤ U
    rw [AffineMap.map_vectorSpan]
    apply vectorSpan_mono ℝ
    rintro _ ⟨x, hx, rfl⟩
    exact wedge_lower_mem P f hf hx
  have hlower (x : E d) : wedgeLower x ∈ U := by
    apply hmap
    exact ⟨x, by rw [hspan]; trivial, rfl⟩
  obtain ⟨v, hv, hvpos⟩ := hpos
  have hvbody : v ∈ P.toSet := subset_convexHull ℝ _ hv
  have hdir : f v • wedgeVertical ∈ U := by
    have h := vsub_mem_vectorSpan ℝ (wedge_upper_mem P f hf hvbody)
      (wedge_lower_mem P f hf hvbody)
    rw [wedge_upper_split] at h
    simpa only [vsub_eq_sub, add_sub_cancel_left] using h
  have hvertical : wedgeVertical (d := d) ∈ U := by
    have h := U.smul_mem (f v)⁻¹ hdir
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hvpos), one_smul] using h
  have htop : U = ⊤ := by
    apply top_unique
    intro z _
    rw [← wedge_split z]
    exact U.add_mem (hlower _) (U.smul_mem _ hvertical)
  change finrank ℝ U = d + 1
  rw [htop, finrank_top, finrank_euclideanSpace_fin]

theorem positive_vertex_of_nonzero_support
    (P : ConvexPolytope d) (hP : P.IsFullDim) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) (hne : f ≠ 0) :
    ∃ v ∈ P.vertices, 0 < f v := by
  by_contra h
  push_neg at h
  apply hne
  apply affine_eq_zero_of_vertices P hP f
  intro v hv
  exact le_antisymm (h v hv) (hf v hv)

theorem faceDim_image_affine_injective {e : ℕ}
    (a : E d →ᵃ[ℝ] E e) (ha : Function.Injective a) (S : Set (E d)) :
    faceDim (a '' S) = faceDim S := by
  unfold faceDim
  rw [← a.map_vectorSpan]
  exact (Submodule.equivMapOfInjective a.linear
    (a.linear_injective_iff.mpr ha) (vectorSpan ℝ S)).finrank_eq.symm

theorem wedge_lower_support
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    SupportsFace (wedgePolytope P f hf) (wedgeLower '' P.toSet) wedgeHeight.toAffineMap := by
  constructor
  · intro z hz
    exact ((mem_wedgePolytope_iff P f hf z).mp hz).2.1
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨wedge_lower_mem P f hf hx, wedgeHeight_lower x⟩
    · rintro ⟨hz, hh⟩
      refine ⟨wedgeProjection z, ((mem_wedgePolytope_iff P f hf z).mp hz).1, ?_⟩
      have h := wedge_split z
      change wedgeHeight z = 0 at hh
      simpa only [hh, zero_smul, add_zero] using h

def wedgeUpperSupport (f : E d →ᵃ[ℝ] ℝ) : E (d + 1) →ᵃ[ℝ] ℝ :=
  f.comp wedgeProjection.toAffineMap - wedgeHeight.toAffineMap

theorem wedge_upper_support
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    SupportsFace (wedgePolytope P f hf) (wedgeUpper f '' P.toSet) (wedgeUpperSupport f) := by
  constructor
  · intro z hz
    change 0 ≤ f (wedgeProjection z) - wedgeHeight z
    exact sub_nonneg.mpr ((mem_wedgePolytope_iff P f hf z).mp hz).2.2
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨wedge_upper_mem P f hf hx, ?_⟩
      change f (wedgeProjection (wedgeUpper f x)) - wedgeHeight (wedgeUpper f x) = 0
      rw [wedgeProjection_upper, wedgeHeight_upper, sub_self]
    · rintro ⟨hz, hh⟩
      refine ⟨wedgeProjection z, ((mem_wedgePolytope_iff P f hf z).mp hz).1, ?_⟩
      change f (wedgeProjection z) - wedgeHeight z = 0 at hh
      rw [wedgeUpper_apply, sub_eq_zero.mp hh, wedgeCoordinates_projection_height]

theorem wedge_lower_isFace
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    (wedgePolytope P f hf).IsFace (wedgeLower '' P.toSet) := by
  have hs := wedge_lower_support P f hf
  rw [hs.2]
  apply affineZeroFace_isFace _ _ hs.1
  change ({x | x ∈ (wedgePolytope P f hf).toSet ∧ wedgeHeight.toAffineMap x = 0}).Nonempty
  rw [← hs.2]
  exact (toSet_isFace P).2.image wedgeLower

theorem wedge_upper_isFace
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    (wedgePolytope P f hf).IsFace (wedgeUpper f '' P.toSet) := by
  have hs := wedge_upper_support P f hf
  rw [hs.2]
  apply affineZeroFace_isFace _ _ hs.1
  change ({x | x ∈ (wedgePolytope P f hf).toSet ∧ wedgeUpperSupport f x = 0}).Nonempty
  rw [← hs.2]
  exact (toSet_isFace P).2.image (wedgeUpper f)

theorem wedge_lower_isFacet
    (P : ConvexPolytope d) (hP : P.IsFullDim) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) (hne : f ≠ 0) :
    IsFacet (wedgePolytope P f hf) (wedgeLower '' P.toSet) := by
  refine ⟨wedge_lower_isFace P f hf, ?_⟩
  have hW := wedgePolytope_fullDim P hP f hf
    (positive_vertex_of_nonzero_support P hP f hf hne)
  rw [show (wedgePolytope P f hf).dim = d + 1 from hW]
  change faceDim (wedgeLower.toAffineMap '' P.toSet) + 1 = d + 1
  rw [faceDim_image_affine_injective _ wedgeLower_injective]
  exact congrArg (fun n => n + 1) hP

theorem wedge_upper_isFacet
    (P : ConvexPolytope d) (hP : P.IsFullDim) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) (hne : f ≠ 0) :
    IsFacet (wedgePolytope P f hf) (wedgeUpper f '' P.toSet) := by
  refine ⟨wedge_upper_isFace P f hf, ?_⟩
  have hW := wedgePolytope_fullDim P hP f hf
    (positive_vertex_of_nonzero_support P hP f hf hne)
  rw [show (wedgePolytope P f hf).dim = d + 1 from hW,
    faceDim_image_affine_injective _ (wedgeUpper_injective f)]
  exact congrArg (fun n => n + 1) hP

end Papers.Polytopes

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/WedgeFaces.lean -/




@[expose] public section

/-!
# The full face dictionary of a wedge

Every exposed face is a lower lift, an upper lift, or the whole interval
bundle over a face of the base. The sign of the vertical coefficient of an
arbitrary exposing affine form proves completeness of this dictionary.
No assumption about a preassigned list of facets is used.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical
open Papers.Wedges
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

inductive WedgeFaceKind
  | lower
  | upper
  | vertical
  deriving DecidableEq

def wedgeFaceLift (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) (kind : WedgeFaceKind) (F : Set (E d)) :
    Set (E (d + 1)) :=
  match kind with
  | .lower => wedgeLower '' F
  | .upper => wedgeUpper f '' F
  | .vertical => {z ∈ (wedgePolytope P f hf).toSet | wedgeProjection z ∈ F}

theorem wedge_affine_vertical (g : E (d + 1) →ᵃ[ℝ] ℝ) (z : E (d + 1)) :
    g z = g (wedgeLower (wedgeProjection z)) + wedgeHeight z * g.linear wedgeVertical := by
  calc
    g z = g.linear z + g 0 := affine_form_apply g z
    _ = g.linear (wedgeLower (wedgeProjection z) + wedgeHeight z • wedgeVertical) + g 0 := by
      rw [wedge_split]
    _ = g (wedgeLower (wedgeProjection z)) + wedgeHeight z * g.linear wedgeVertical := by
      rw [map_add, map_smul, affine_form_apply g (wedgeLower (wedgeProjection z))]
      change g.linear (wedgeLower (wedgeProjection z)) +
        wedgeHeight z * g.linear wedgeVertical + g 0 = _
      ring

theorem wedge_affine_upper_vertical (g : E (d + 1) →ᵃ[ℝ] ℝ)
    (f : E d →ᵃ[ℝ] ℝ) (z : E (d + 1)) :
    g z = g (wedgeUpper f (wedgeProjection z)) +
      (wedgeHeight z - f (wedgeProjection z)) * g.linear wedgeVertical := by
  have h := wedge_affine_vertical g z
  have hu := wedge_affine_vertical g (wedgeUpper f (wedgeProjection z))
  rw [wedgeProjection_upper, wedgeHeight_upper] at hu
  linear_combination h - hu

theorem wedgeFaceLift_isFace
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (kind : WedgeFaceKind) {F : Set (E d)} (hF : P.IsFace F) :
    (wedgePolytope P f hf).IsFace (wedgeFaceLift P f hf kind F) := by
  obtain ⟨g, hg⟩ := exists_supportsFace P hF
  obtain ⟨x, hx⟩ := hF.2
  have hxP : x ∈ P.toSet := face_subset_toSet P hF hx
  have hzero : g x = 0 := hg.eq_zero hx
  cases kind with
  | lower =>
    let h : E (d + 1) →ᵃ[ℝ] ℝ := g.comp wedgeProjection.toAffineMap + wedgeHeight.toAffineMap
    have hnon : ∀ z ∈ (wedgePolytope P f hf).toSet, 0 ≤ h z := by
      intro z hz
      obtain ⟨hp, ht, _⟩ := (mem_wedgePolytope_iff P f hf z).mp hz
      exact add_nonneg (hg.1 _ hp) ht
    have heq : wedgeFaceLift P f hf .lower F = affineZeroFace (wedgePolytope P f hf) h := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨wedge_lower_mem P f hf (face_subset_toSet P hF hy), ?_⟩
        change g (wedgeProjection (wedgeLower y)) + wedgeHeight (wedgeLower y) = 0
        rw [wedgeProjection_lower, wedgeHeight_lower, hg.eq_zero hy, add_zero]
      · rintro ⟨hz, hh⟩
        obtain ⟨hp, ht, _⟩ := (mem_wedgePolytope_iff P f hf z).mp hz
        change g (wedgeProjection z) + wedgeHeight z = 0 at hh
        have hg0 := hg.1 _ hp
        have ht0 : wedgeHeight z = 0 := by linarith
        refine ⟨wedgeProjection z, (hg.mem_iff _).mpr ⟨hp, by linarith⟩, ?_⟩
        simpa only [ht0, zero_smul, add_zero] using wedge_split z
    rw [heq]
    apply affineZeroFace_isFace _ _ hnon
    rw [← heq]
    exact ⟨wedgeLower x, x, hx, rfl⟩
  | upper =>
    let h : E (d + 1) →ᵃ[ℝ] ℝ :=
      g.comp wedgeProjection.toAffineMap + wedgeUpperSupport f
    have hnon : ∀ z ∈ (wedgePolytope P f hf).toSet, 0 ≤ h z := by
      intro z hz
      obtain ⟨hp, _, ht⟩ := (mem_wedgePolytope_iff P f hf z).mp hz
      exact add_nonneg (hg.1 _ hp) (sub_nonneg.mpr ht)
    have heq : wedgeFaceLift P f hf .upper F = affineZeroFace (wedgePolytope P f hf) h := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨wedge_upper_mem P f hf (face_subset_toSet P hF hy), ?_⟩
        change g (wedgeProjection (wedgeUpper f y)) +
          (f (wedgeProjection (wedgeUpper f y)) - wedgeHeight (wedgeUpper f y)) = 0
        rw [wedgeProjection_upper, wedgeHeight_upper, hg.eq_zero hy, sub_self, add_zero]
      · rintro ⟨hz, hh⟩
        obtain ⟨hp, _, ht⟩ := (mem_wedgePolytope_iff P f hf z).mp hz
        change g (wedgeProjection z) + (f (wedgeProjection z) - wedgeHeight z) = 0 at hh
        have hg0 := hg.1 _ hp
        have ht0 : f (wedgeProjection z) = wedgeHeight z := by linarith
        refine ⟨wedgeProjection z, (hg.mem_iff _).mpr ⟨hp, by linarith⟩, ?_⟩
        rw [wedgeUpper_apply, ht0, wedgeCoordinates_projection_height]
    rw [heq]
    apply affineZeroFace_isFace _ _ hnon
    rw [← heq]
    exact ⟨wedgeUpper f x, x, hx, rfl⟩
  | vertical =>
    let h : E (d + 1) →ᵃ[ℝ] ℝ := g.comp wedgeProjection.toAffineMap
    have hnon : ∀ z ∈ (wedgePolytope P f hf).toSet, 0 ≤ h z := by
      intro z hz
      exact hg.1 _ ((mem_wedgePolytope_iff P f hf z).mp hz).1
    have heq : wedgeFaceLift P f hf .vertical F = affineZeroFace (wedgePolytope P f hf) h := by
      ext z
      constructor
      · rintro ⟨hz, hp⟩
        exact ⟨hz, hg.eq_zero hp⟩
      · rintro ⟨hz, hh⟩
        exact ⟨hz, (hg.mem_iff _).mpr
          ⟨((mem_wedgePolytope_iff P f hf z).mp hz).1, hh⟩⟩
    rw [heq]
    apply affineZeroFace_isFace _ _ hnon
    rw [← heq]
    exact ⟨wedgeLower x, wedge_lower_mem P f hf hxP, by simpa using hx⟩

/-- All nonempty geometric faces, including the whole wedge, occur in
the dictionary. The three cases are allowed to coincide on the collapsed
zero-height face; no uniqueness assertion is needed or assumed. -/
theorem wedgeFaceLift_complete
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    {G : Set (E (d + 1))} (hG : (wedgePolytope P f hf).IsFace G) :
    ∃ kind : WedgeFaceKind, ∃ F : Set (E d), P.IsFace F ∧ G = wedgeFaceLift P f hf kind F := by
  obtain ⟨g, hg⟩ := exists_supportsFace (wedgePolytope P f hf) hG
  obtain ⟨z₀, hz₀⟩ := hG.2
  have hz₀W := face_subset_toSet _ hG hz₀
  have hz₀g := hg.eq_zero hz₀
  obtain ⟨hp₀, ht₀, hu₀⟩ := (mem_wedgePolytope_iff P f hf z₀).mp hz₀W
  let a := g.linear wedgeVertical
  rcases lt_trichotomy a 0 with ha | ha | ha
  · let h : E d →ᵃ[ℝ] ℝ := g.comp (wedgeUpper f)
    have hnon : ∀ x ∈ P.toSet, 0 ≤ h x :=
      fun x hx => hg.1 _ (wedge_upper_mem P f hf hx)
    have hz₀h : h (wedgeProjection z₀) = 0 := by
      have hv := wedge_affine_upper_vertical g f z₀
      have hn := hnon _ hp₀
      change g.linear wedgeVertical < 0 at ha
      change 0 ≤ g (wedgeUpper f (wedgeProjection z₀)) at hn
      change g (wedgeUpper f (wedgeProjection z₀)) = 0
      have ht := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hu₀) ha.le
      linarith
    let F := affineZeroFace P h
    have hF : P.IsFace F := affineZeroFace_isFace P h hnon
      ⟨wedgeProjection z₀, hp₀, hz₀h⟩
    refine ⟨.upper, F, hF, ?_⟩
    ext z
    constructor
    · intro hz
      obtain ⟨hzW, hzg⟩ := (hg.mem_iff z).mp hz
      obtain ⟨hp, _, hu⟩ := (mem_wedgePolytope_iff P f hf z).mp hzW
      have hv := wedge_affine_upper_vertical g f z
      have hn := hnon _ hp
      change g.linear wedgeVertical < 0 at ha
      change 0 ≤ g (wedgeUpper f (wedgeProjection z)) at hn
      have ht := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hu) ha.le
      have hzero : g (wedgeUpper f (wedgeProjection z)) = 0 := by linarith
      have hproduct : (wedgeHeight z - f (wedgeProjection z)) * g.linear wedgeVertical = 0 := by
        linarith
      have heq : wedgeHeight z = f (wedgeProjection z) :=
        sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right (ne_of_lt ha))
      refine ⟨wedgeProjection z, ⟨hp, hzero⟩, ?_⟩
      rw [wedgeUpper_apply, ← heq, wedgeCoordinates_projection_height]
    · rintro ⟨x, hx, rfl⟩
      exact (hg.mem_iff _).mpr ⟨wedge_upper_mem P f hf hx.1, hx.2⟩
  · let h : E d →ᵃ[ℝ] ℝ := g.comp wedgeLower.toAffineMap
    have hnon : ∀ x ∈ P.toSet, 0 ≤ h x :=
      fun x hx => hg.1 _ (wedge_lower_mem P f hf hx)
    have heval (z : E (d + 1)) : g z = h (wedgeProjection z) := by
      have hv := wedge_affine_vertical g z
      change g.linear wedgeVertical = 0 at ha
      change g z = g (wedgeLower (wedgeProjection z))
      simpa only [ha, mul_zero, add_zero] using hv
    let F := affineZeroFace P h
    have hF : P.IsFace F := affineZeroFace_isFace P h hnon
      ⟨wedgeProjection z₀, hp₀, (heval z₀).symm.trans hz₀g⟩
    refine ⟨.vertical, F, hF, ?_⟩
    ext z
    rw [hg.mem_iff]
    change (z ∈ (wedgePolytope P f hf).toSet ∧ g z = 0) ↔
      z ∈ (wedgePolytope P f hf).toSet ∧
        wedgeProjection z ∈ P.toSet ∧ h (wedgeProjection z) = 0
    rw [heval]
    constructor
    · rintro ⟨hz, hh⟩
      exact ⟨hz, ((mem_wedgePolytope_iff P f hf z).mp hz).1, hh⟩
    · exact fun hz => ⟨hz.1, hz.2.2⟩
  · let h : E d →ᵃ[ℝ] ℝ := g.comp wedgeLower.toAffineMap
    have hnon : ∀ x ∈ P.toSet, 0 ≤ h x :=
      fun x hx => hg.1 _ (wedge_lower_mem P f hf hx)
    have hz₀h : h (wedgeProjection z₀) = 0 := by
      have hv := wedge_affine_vertical g z₀
      have hn := hnon _ hp₀
      change 0 < g.linear wedgeVertical at ha
      change 0 ≤ g (wedgeLower (wedgeProjection z₀)) at hn
      change g (wedgeLower (wedgeProjection z₀)) = 0
      have ht := mul_nonneg ht₀ ha.le
      linarith
    let F := affineZeroFace P h
    have hF : P.IsFace F := affineZeroFace_isFace P h hnon
      ⟨wedgeProjection z₀, hp₀, hz₀h⟩
    refine ⟨.lower, F, hF, ?_⟩
    ext z
    constructor
    · intro hz
      obtain ⟨hzW, hzg⟩ := (hg.mem_iff z).mp hz
      obtain ⟨hp, ht, _⟩ := (mem_wedgePolytope_iff P f hf z).mp hzW
      have hv := wedge_affine_vertical g z
      have hn := hnon _ hp
      change 0 < g.linear wedgeVertical at ha
      change 0 ≤ g (wedgeLower (wedgeProjection z)) at hn
      have hproduct_nonneg := mul_nonneg ht ha.le
      have hzero : g (wedgeLower (wedgeProjection z)) = 0 := by linarith
      have hproduct : wedgeHeight z * g.linear wedgeVertical = 0 := by linarith
      have heq : wedgeHeight z = 0 :=
        (mul_eq_zero.mp hproduct).resolve_right (ne_of_gt ha)
      refine ⟨wedgeProjection z, ⟨hp, hzero⟩, ?_⟩
      simpa only [heq, zero_smul, add_zero] using wedge_split z
    · rintro ⟨x, hx, rfl⟩
      exact (hg.mem_iff _).mpr ⟨wedge_lower_mem P f hf hx.1, hx.2⟩

end Papers.Polytopes

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/WedgeCombinatorics.lean -/




@[expose] public section

/-!
# A wedge depends only on the pointed face lattice

Vertices are labelled by a lower copy of every base vertex and an upper
copy of each vertex outside the zero-height face. This labelling accounts
for the identifications on that face. The complete geometric face
dictionary then transports the ordinary face order.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

def WedgeVertexLabel (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) :=
  VertexType P ⊕ {v : VertexType P // f v.val ≠ 0}

def wedgeVertexPoint (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) :
    WedgeVertexLabel P f → E (d + 1)
  | .inl v => wedgeLower v.val
  | .inr v => wedgeUpper f v.val.val

theorem wedgeVertexPoint_mem
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (v : WedgeVertexLabel P f) : wedgeVertexPoint P f v ∈ (wedgePolytope P f hf).vertices := by
  cases v with
  | inl v => exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ v.property)
  | inr v => exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ v.val.property)

theorem wedgeVertexPoint_injective (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) :
    Function.Injective (wedgeVertexPoint P f) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      exact congrArg Sum.inl (Subtype.ext (wedgeLower_injective h))
    | inr w =>
      exact False.elim (w.property ((wedgeLower_eq_upper_iff f v.val w.val.val).mp h).2)
  | inr v =>
    cases w with
    | inl w =>
      exact False.elim (v.property ((wedgeLower_eq_upper_iff f w.val v.val.val).mp h.symm).2)
    | inr w =>
      exact congrArg Sum.inr (Subtype.ext (Subtype.ext ((wedgeUpper_injective f) h)))

theorem wedgeVertexPoint_surjective
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    ∀ z : VertexType (wedgePolytope P f hf), ∃ v : WedgeVertexLabel P f,
      wedgeVertexPoint P f v = z.val := by
  intro z
  rcases Finset.mem_union.mp z.property with hz | hz
  · obtain ⟨x, hx, h⟩ := Finset.mem_image.mp hz
    exact ⟨.inl ⟨x, hx⟩, h⟩
  · obtain ⟨x, hx, h⟩ := Finset.mem_image.mp hz
    by_cases hzero : f x = 0
    · exact ⟨.inl ⟨x, hx⟩,
        ((wedgeLower_eq_upper_iff f x x).mpr ⟨rfl, hzero⟩).trans h⟩
    · exact ⟨.inr ⟨⟨x, hx⟩, hzero⟩, h⟩

def wedgeVertexLabels
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    WedgeVertexLabel P f ≃ VertexType (wedgePolytope P f hf) :=
  Equiv.ofBijective (fun v => ⟨wedgeVertexPoint P f v, wedgeVertexPoint_mem P f hf v⟩) (by
    constructor
    · intro v w h
      exact wedgeVertexPoint_injective P f (congrArg Subtype.val h)
    · intro z
      obtain ⟨v, hv⟩ := wedgeVertexPoint_surjective P f hf z
      exact ⟨v, Subtype.ext hv⟩)

@[simp] theorem wedgeVertexLabels_val
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (v : WedgeVertexLabel P f) : (wedgeVertexLabels P f hf v).val = wedgeVertexPoint P f v := rfl

def wedgeLabelEquiv
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (f : E d →ᵃ[ℝ] ℝ) (g : E e →ᵃ[ℝ] ℝ) (b : VertexType P ≃ VertexType Q)
    (hzero : ∀ v : VertexType P, f v.val = 0 ↔ g (b v).val = 0) :
    WedgeVertexLabel P f ≃ WedgeVertexLabel Q g :=
  Equiv.sumCongr b (b.subtypeEquiv (fun v => not_congr (hzero v)))

theorem wedge_lower_mem_lower_iff (x : E d) (F : Set (E d)) :
    wedgeLower x ∈ wedgeLower '' F ↔ x ∈ F := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact wedgeLower_injective hxy ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

theorem wedge_upper_mem_upper_iff (f : E d →ᵃ[ℝ] ℝ) (x : E d) (F : Set (E d)) :
    wedgeUpper f x ∈ wedgeUpper f '' F ↔ x ∈ F := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (wedgeUpper_injective f hxy) ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

theorem wedge_lower_mem_upper_iff (f : E d →ᵃ[ℝ] ℝ) (x : E d) (F : Set (E d)) :
    wedgeLower x ∈ wedgeUpper f '' F ↔ x ∈ F ∧ f x = 0 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨rfl, hzero⟩ := (wedgeLower_eq_upper_iff f x y).mp hxy.symm
    exact ⟨hy, hzero⟩
  · rintro ⟨hx, hzero⟩
    exact ⟨x, hx, ((wedgeLower_eq_upper_iff f x x).mpr ⟨rfl, hzero⟩).symm⟩

theorem wedge_upper_mem_lower_iff (f : E d →ᵃ[ℝ] ℝ) (x : E d) (F : Set (E d)) :
    wedgeUpper f x ∈ wedgeLower '' F ↔ x ∈ F ∧ f x = 0 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨rfl, hzero⟩ := (wedgeLower_eq_upper_iff f y x).mp hxy
    exact ⟨hy, hzero⟩
  · rintro ⟨hx, hzero⟩
    exact ⟨x, hx, (wedgeLower_eq_upper_iff f x x).mpr ⟨rfl, hzero⟩⟩

theorem wedge_lower_mem_vertical_iff
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (x : E d) (hx : x ∈ P.toSet) (F : Set (E d)) :
    wedgeLower x ∈ wedgeFaceLift P f hf .vertical F ↔ x ∈ F := by
  change (wedgeLower x ∈ (wedgePolytope P f hf).toSet ∧ wedgeProjection (wedgeLower x) ∈ F) ↔ _
  rw [wedgeProjection_lower, and_iff_right (wedge_lower_mem P f hf hx)]

theorem wedge_upper_mem_vertical_iff
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (x : E d) (hx : x ∈ P.toSet) (F : Set (E d)) :
    wedgeUpper f x ∈ wedgeFaceLift P f hf .vertical F ↔ x ∈ F := by
  change (wedgeUpper f x ∈ (wedgePolytope P f hf).toSet ∧ wedgeProjection (wedgeUpper f x) ∈ F) ↔ _
  rw [wedgeProjection_upper, and_iff_right (wedge_upper_mem P f hf hx)]

theorem wedge_label_incidence_preserved
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (f : E d →ᵃ[ℝ] ℝ) (g : E e →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) (hg : ∀ y ∈ Q.vertices, 0 ≤ g y)
    (b : VertexType P ≃ VertexType Q)
    (hzero : ∀ v : VertexType P, f v.val = 0 ↔ g (b v).val = 0)
    (F : Set (E d)) (G : Set (E e))
    (hinc : ∀ v : VertexType P, (b v).val ∈ G ↔ v.val ∈ F)
    (kind : WedgeFaceKind) (v : WedgeVertexLabel P f) :
    wedgeVertexPoint Q g (wedgeLabelEquiv f g b hzero v) ∈ wedgeFaceLift Q g hg kind G ↔
      wedgeVertexPoint P f v ∈ wedgeFaceLift P f hf kind F := by
  cases v with
  | inl v =>
    cases kind with
    | lower =>
      change wedgeLower (b v).val ∈ wedgeLower '' G ↔ wedgeLower v.val ∈ wedgeLower '' F
      rw [wedge_lower_mem_lower_iff, wedge_lower_mem_lower_iff]
      exact hinc v
    | upper =>
      change wedgeLower (b v).val ∈ wedgeUpper g '' G ↔ wedgeLower v.val ∈ wedgeUpper f '' F
      rw [wedge_lower_mem_upper_iff, wedge_lower_mem_upper_iff]
      exact and_congr (hinc v) (hzero v).symm
    | vertical =>
      change wedgeLower (b v).val ∈ wedgeFaceLift Q g hg .vertical G ↔
        wedgeLower v.val ∈ wedgeFaceLift P f hf .vertical F
      rw [wedge_lower_mem_vertical_iff Q g hg _ (subset_convexHull ℝ _ (b v).property),
        wedge_lower_mem_vertical_iff P f hf _ (subset_convexHull ℝ _ v.property)]
      exact hinc v
  | inr v =>
    cases kind with
    | lower =>
      change wedgeUpper g (b v.val).val ∈ wedgeLower '' G ↔
        wedgeUpper f v.val.val ∈ wedgeLower '' F
      rw [wedge_upper_mem_lower_iff, wedge_upper_mem_lower_iff]
      exact and_congr (hinc v.val) (hzero v.val).symm
    | upper =>
      change wedgeUpper g (b v.val).val ∈ wedgeUpper g '' G ↔
        wedgeUpper f v.val.val ∈ wedgeUpper f '' F
      rw [wedge_upper_mem_upper_iff, wedge_upper_mem_upper_iff]
      exact hinc v.val
    | vertical =>
      change wedgeUpper g (b v.val).val ∈ wedgeFaceLift Q g hg .vertical G ↔
        wedgeUpper f v.val.val ∈ wedgeFaceLift P f hf .vertical F
      rw [wedge_upper_mem_vertical_iff Q g hg _ (subset_convexHull ℝ _ (b v.val).property),
        wedge_upper_mem_vertical_iff P f hf _ (subset_convexHull ℝ _ v.val.property)]
      exact hinc v.val

/-- The original face isomorphism must identify the zero-height faces.
The result is the ordinary face-poset isomorphism of the geometric wedges,
in every pair of ambient dimensions. -/
def wedgeFaceOrderIso
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (f : E d →ᵃ[ℝ] ℝ) (g : E e →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) (hg : ∀ y ∈ Q.vertices, 0 ≤ g y)
    (φ : FaceType P ≃o FaceType Q)
    (hzero : ∀ v : VertexType P, f v.val = 0 ↔ g (imageVertex φ v).val = 0) :
    FaceType (wedgePolytope P f hf) ≃o FaceType (wedgePolytope Q g hg) := by
  let b := vertexEquivOfFaceOrder φ
  let c := wedgeLabelEquiv f g b hzero
  let β := (wedgeVertexLabels P f hf).symm.trans (c.trans (wedgeVertexLabels Q g hg))
  have hlabel (v : WedgeVertexLabel P f) :
      (β (wedgeVertexLabels P f hf v)).val = wedgeVertexPoint Q g (c v) := by
    dsimp only [β, Equiv.trans_apply]
    rw [Equiv.symm_apply_apply]
    rfl
  apply faceOrderIsoOfVertexIncidence _ _ β
  · intro G
    obtain ⟨kind, F, hF, hGF⟩ := wedgeFaceLift_complete P f hf G.property
    let F' := φ ⟨F, hF⟩
    refine ⟨⟨wedgeFaceLift Q g hg kind F'.val, wedgeFaceLift_isFace Q g hg kind F'.property⟩, ?_⟩
    intro z
    obtain ⟨v, rfl⟩ := (wedgeVertexLabels P f hf).surjective z
    rw [hlabel, wedgeVertexLabels_val, hGF]
    exact wedge_label_incidence_preserved f g hf hg b hzero F F'.val
      (fun v => imageVertex_mem_iff φ v ⟨F, hF⟩) kind v
  · intro G
    obtain ⟨kind, F', hF', hGF'⟩ := wedgeFaceLift_complete Q g hg G.property
    let F := φ.symm ⟨F', hF'⟩
    refine ⟨⟨wedgeFaceLift P f hf kind F.val, wedgeFaceLift_isFace P f hf kind F.property⟩, ?_⟩
    intro z
    obtain ⟨v, rfl⟩ := (wedgeVertexLabels P f hf).surjective z
    rw [hlabel, wedgeVertexLabels_val, hGF']
    apply wedge_label_incidence_preserved f g hf hg b hzero F.val F' ?_ kind v
    intro v
    have h := imageVertex_mem_iff φ v F
    rw [show φ F = ⟨F', hF'⟩ from φ.apply_symm_apply _] at h
    exact h

end Papers.Polytopes

end
end
end BundlePart13

section BundlePart14
/- Source: Papers/WedgeEdges.lean -/




@[expose] public section

/-!
# Actual edges of a wedge

Every edge is a lower lifted base edge, an upper lifted base edge, or lies
in a single vertical fibre. Completeness follows from the face dictionary
and the fact that an actual edge has only its two extreme endpoints.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem wedge_lower_vertex (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) {x : E d} (hx : x ∈ P.vertices) :
    wedgeLower x ∈ (wedgePolytope P f hf).vertices :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)

theorem wedge_upper_vertex (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) {x : E d} (hx : x ∈ P.vertices) :
    wedgeUpper f x ∈ (wedgePolytope P f hf).vertices :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)

theorem wedge_projection_vertex (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) {z : E (d + 1)}
    (hz : z ∈ (wedgePolytope P f hf).vertices) : wedgeProjection z ∈ P.vertices := by
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    simpa only [wedgeProjection_lower] using hx
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    simpa only [wedgeProjection_upper] using hx

theorem wedge_lower_step (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) {x y : E d} (hx : x ∈ P.vertices)
    (hxy : GeneralVertexStep P x y) :
    GeneralVertexStep (wedgePolytope P f hf) (wedgeLower x) (wedgeLower y) := by
  obtain ⟨hy, hne, F, hF, hdF, hxF, hyF⟩ := hxy
  refine ⟨wedge_lower_vertex P f hf hy,
    fun h => hne (wedgeLower_injective h), wedgeLower '' F,
    wedgeFaceLift_isFace P f hf .lower hF, ?_, ⟨x, hxF, rfl⟩, ⟨y, hyF, rfl⟩⟩
  change faceDim (wedgeLower.toAffineMap '' F) = 1
  rw [faceDim_image_affine_injective _ wedgeLower_injective, hdF]

theorem wedge_upper_step (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) {x y : E d} (hx : x ∈ P.vertices)
    (hxy : GeneralVertexStep P x y) :
    GeneralVertexStep (wedgePolytope P f hf) (wedgeUpper f x) (wedgeUpper f y) := by
  obtain ⟨hy, hne, F, hF, hdF, hxF, hyF⟩ := hxy
  refine ⟨wedge_upper_vertex P f hf hy,
    fun h => hne (wedgeUpper_injective f h), wedgeUpper f '' F,
    wedgeFaceLift_isFace P f hf .upper hF, ?_, ⟨x, hxF, rfl⟩, ⟨y, hyF, rfl⟩⟩
  rw [faceDim_image_affine_injective _ (wedgeUpper_injective f), hdF]

theorem wedge_projection_vertical_face (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x) {F : Set (E d)} (hF : F ⊆ P.toSet) :
    wedgeProjection '' wedgeFaceLift P f hf .vertical F = F := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  · intro x hx
    exact ⟨wedgeLower x, ⟨wedge_lower_mem P f hf (hF hx), by simpa using hx⟩,
      wedgeProjection_lower x⟩

theorem faceDim_image_affine_le {e : ℕ} (a : E d →ᵃ[ℝ] E e) (S : Set (E d)) :
    faceDim (a '' S) ≤ faceDim S := by
  unfold faceDim
  rw [← a.map_vectorSpan]
  exact Submodule.finrank_map_le _ _

theorem wedge_step_classification
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    {z w : E (d + 1)} (hz : z ∈ (wedgePolytope P f hf).vertices)
    (hzw : GeneralVertexStep (wedgePolytope P f hf) z w) :
    (∃ x y : E d, x ∈ P.vertices ∧ GeneralVertexStep P x y ∧
      z = wedgeLower x ∧ w = wedgeLower y) ∨
    (∃ x y : E d, x ∈ P.vertices ∧ GeneralVertexStep P x y ∧
      z = wedgeUpper f x ∧ w = wedgeUpper f y) ∨
    wedgeProjection z = wedgeProjection w := by
  obtain ⟨hw, hne, G, hG, hdG, hzG, hwG⟩ := hzw
  have hp := wedge_projection_vertex P f hf hz
  have hq := wedge_projection_vertex P f hf hw
  obtain ⟨kind, F, hF, hGF⟩ := wedgeFaceLift_complete P f hf hG
  cases kind with
  | lower =>
    obtain ⟨x, hxF, hzx⟩ : ∃ x ∈ F, wedgeLower x = z := by rw [hGF] at hzG; exact hzG
    obtain ⟨y, hyF, hwy⟩ : ∃ y ∈ F, wedgeLower y = w := by rw [hGF] at hwG; exact hwG
    have hx : x ∈ P.vertices := by simpa only [← hzx, wedgeProjection_lower] using hp
    have hy : y ∈ P.vertices := by simpa only [← hwy, wedgeProjection_lower] using hq
    have hxy : x ≠ y := fun h => hne (hzx.symm.trans ((congrArg wedgeLower h).trans hwy))
    have hdF : faceDim F = 1 := by
      rw [hGF] at hdG
      change faceDim (wedgeLower.toAffineMap '' F) = 1 at hdG
      rwa [faceDim_image_affine_injective _ wedgeLower_injective] at hdG
    exact Or.inl ⟨x, y, hx, ⟨hy, hxy, F, hF, hdF, hxF, hyF⟩, hzx.symm, hwy.symm⟩
  | upper =>
    obtain ⟨x, hxF, hzx⟩ : ∃ x ∈ F, wedgeUpper f x = z := by rw [hGF] at hzG; exact hzG
    obtain ⟨y, hyF, hwy⟩ : ∃ y ∈ F, wedgeUpper f y = w := by rw [hGF] at hwG; exact hwG
    have hx : x ∈ P.vertices := by simpa only [← hzx, wedgeProjection_upper] using hp
    have hy : y ∈ P.vertices := by simpa only [← hwy, wedgeProjection_upper] using hq
    have hxy : x ≠ y := fun h => hne (hzx.symm.trans ((congrArg (wedgeUpper f) h).trans hwy))
    have hdF : faceDim F = 1 := by
      rw [hGF] at hdG
      change faceDim (wedgeUpper f '' F) = 1 at hdG
      rwa [faceDim_image_affine_injective _ (wedgeUpper_injective f)] at hdG
    exact Or.inr (Or.inl ⟨x, y, hx, ⟨hy, hxy, F, hF, hdF, hxF, hyF⟩, hzx.symm, hwy.symm⟩)
  | vertical =>
    by_cases hpq : wedgeProjection z = wedgeProjection w
    · exact Or.inr (Or.inr hpq)
    have hpF : wedgeProjection z ∈ F := (hGF ▸ hzG).2
    have hqF : wedgeProjection w ∈ F := (hGF ▸ hwG).2
    have hlpG : wedgeLower (wedgeProjection z) ∈ G := by
      rw [hGF]
      exact ⟨wedge_lower_mem P f hf (subset_convexHull ℝ _ hp), by simpa using hpF⟩
    have hlqG : wedgeLower (wedgeProjection w) ∈ G := by
      rw [hGF]
      exact ⟨wedge_lower_mem P f hf (subset_convexHull ℝ _ hq), by simpa using hqF⟩
    have hseg := edge_eq_segment (wedgePolytope P f hf) hG hdG hz hw hzG hwG hne
    have hlp : wedgeLower (wedgeProjection z) = z := by
      have h := (vertex_mem_segment_iff (wedgePolytope P f hf) hz hw
        (wedge_lower_vertex P f hf hp)).mp (hseg ▸ hlpG)
      rcases h with h | h
      · exact h
      · exact False.elim (hpq (by simpa only [wedgeProjection_lower] using congrArg wedgeProjection h))
    have hlq : wedgeLower (wedgeProjection w) = w := by
      have h := (vertex_mem_segment_iff (wedgePolytope P f hf) hz hw
        (wedge_lower_vertex P f hf hq)).mp (hseg ▸ hlqG)
      rcases h with h | h
      · exact False.elim (hpq (by simpa only [wedgeProjection_lower] using (congrArg wedgeProjection h).symm))
      · exact h
    have hdim_le : faceDim F ≤ 1 := by
      have hm := faceDim_image_affine_le wedgeProjection.toAffineMap G
      change faceDim (wedgeProjection '' G) ≤ faceDim G at hm
      rw [hdG, hGF, wedge_projection_vertical_face P f hf (face_subset_toSet P hF)] at hm
      exact hm
    have hdF : faceDim F = 1 := by
      by_cases hzdim : faceDim F = 0
      · obtain ⟨v, hFv, _⟩ := punto_di_faccia0_e_vertice P hF hzdim
        rw [hFv] at hpF hqF
        exact False.elim (hpq (hpF.trans hqF.symm))
      · omega
    exact Or.inl ⟨wedgeProjection z, wedgeProjection w, hp,
      ⟨hq, hpq, F, hF, hdF, hpF, hqF⟩, hlp.symm, hlq.symm⟩

end Papers.Polytopes

end
end
end BundlePart14

section BundlePart15
/- Source: Papers/WedgeParallel.lean -/





@[expose] public section

/-!
# Parallel maps and decomposability of a wedge

The forward implication extends a normalized parallel map to both endpoint
lifts. The reverse implication restricts an arbitrary parallel map to the
two distinguished copies of the base. Two common vertices identify their
homothety parameters. Kallay's criterion connects these statements to the
ordinary Minkowski decomposition predicate.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem wedge_ext {z w : E (d + 1)}
    (hp : wedgeProjection z = wedgeProjection w) (ht : wedgeHeight z = wedgeHeight w) : z = w := by
  rw [← wedgeCoordinates_projection_height z, ← wedgeCoordinates_projection_height w]
  exact congrArg wedgeCoordinates (Prod.ext hp ht)

def parallelWedgeMap (f : E d →ᵃ[ℝ] ℝ) (g : E d → E d) : E (d + 1) → E (d + 1) :=
  fun z => wedgeCoordinates (g (wedgeProjection z),
    (wedgeHeight z / f (wedgeProjection z)) * f.linear (g (wedgeProjection z)))

@[simp] theorem parallelWedgeMap_projection (f : E d →ᵃ[ℝ] ℝ) (g : E d → E d)
    (z : E (d + 1)) : wedgeProjection (parallelWedgeMap f g z) = g (wedgeProjection z) := by
  exact wedgeProjection_coordinates _

@[simp] theorem parallelWedgeMap_height (f : E d →ᵃ[ℝ] ℝ) (g : E d → E d)
    (z : E (d + 1)) : wedgeHeight (parallelWedgeMap f g z) =
      (wedgeHeight z / f (wedgeProjection z)) * f.linear (g (wedgeProjection z)) := by
  exact wedgeHeight_coordinates _

@[simp] theorem parallelWedgeMap_lower (f : E d →ᵃ[ℝ] ℝ) (g : E d → E d) (x : E d) :
    parallelWedgeMap f g (wedgeLower x) = wedgeLower (g x) := by
  unfold parallelWedgeMap
  rw [wedgeProjection_lower, wedgeHeight_lower, zero_div, zero_mul, wedgeLower_apply]

theorem parallelWedgeMap_upper (f : E d →ᵃ[ℝ] ℝ) (g : E d → E d) (x : E d)
    (hzero : f x = 0 → f.linear (g x) = 0) :
    parallelWedgeMap f g (wedgeUpper f x) = wedgeCoordinates (g x, f.linear (g x)) := by
  unfold parallelWedgeMap
  rw [wedgeProjection_upper, wedgeHeight_upper]
  by_cases hx : f x = 0
  · rw [hx, zero_div, zero_mul, hzero hx]
  · rw [div_self hx, one_mul]

theorem parallelWedgeMap_vertical (f : E d →ᵃ[ℝ] ℝ) (g : E d → E d)
    {z w : E (d + 1)} (hp : wedgeProjection z = wedgeProjection w) :
    ∃ c : ℝ, parallelWedgeMap f g w - parallelWedgeMap f g z = c • (w - z) := by
  refine ⟨f.linear (g (wedgeProjection z)) / f (wedgeProjection z), ?_⟩
  apply wedge_ext
  · simp only [map_sub, map_smul, parallelWedgeMap_projection, ← hp, sub_self, smul_zero]
  · simp only [map_sub, map_smul, parallelWedgeMap_height, ← hp, smul_eq_mul]
    ring

theorem parallelWedgeMap_parallel
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (g : E d → E d) (hg : IsParallelMap P g)
    (hzero : ∀ x ∈ P.vertices, f x = 0 → f.linear (g x) = 0) :
    IsParallelMap (wedgePolytope P f hf) (parallelWedgeMap f g) := by
  intro z hz w hw hzw
  rcases wedge_step_classification P f hf hz hzw with h | h | h
  · obtain ⟨x, y, hx, hxy, rfl, rfl⟩ := h
    obtain ⟨c, hc⟩ := hg x hx y hxy.1 hxy
    refine ⟨c, ?_⟩
    rw [parallelWedgeMap_lower, parallelWedgeMap_lower, ← map_sub, hc, map_smul, map_sub]
  · obtain ⟨x, y, hx, hxy, rfl, rfl⟩ := h
    obtain ⟨c, hc⟩ := hg x hx y hxy.1 hxy
    refine ⟨c, ?_⟩
    rw [parallelWedgeMap_upper f g y (hzero y hxy.1),
      parallelWedgeMap_upper f g x (hzero x hx)]
    apply wedge_ext
    · simp only [map_sub, map_smul, wedgeProjection_coordinates, wedgeProjection_upper]
      exact hc
    · simp only [map_sub, map_smul, wedgeHeight_coordinates, wedgeHeight_upper, smul_eq_mul]
      have hh := congrArg f.linear hc
      simp only [map_sub, map_smul, smul_eq_mul] at hh
      rw [affine_form_apply f y, affine_form_apply f x]
      nlinarith
  · exact parallelWedgeMap_vertical f g h

theorem wedge_decomposable_of_decomposable
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (hface : (affineZeroFace P f).Nonempty) (hP : MinkowskiDecomposable P) :
    MinkowskiDecomposable (wedgePolytope P f hf) := by
  obtain ⟨g, hg, hnon⟩ := (minkowski_decomposable_iff_parallel_map P).mp hP
  have hF : P.IsFace (affineZeroFace P f) :=
    affineZeroFace_isFace P f (affine_nonneg_on_hull P.vertices f hf) hface
  obtain ⟨v₀, hv₀⟩ := (facePolytope P hF).vertices_nonempty
  obtain ⟨hv₀P, hv₀F⟩ := Finset.mem_filter.mp hv₀
  let g₀ : E d → E d := fun x => g x - g v₀
  have hg₀ : IsParallelMap P g₀ := by
    intro x hx y hy hxy
    obtain ⟨c, hc⟩ := hg x hx y hy hxy
    refine ⟨c, ?_⟩
    change (g y - g v₀) - (g x - g v₀) = _
    calc
      (g y - g v₀) - (g x - g v₀) = g y - g x := by abel
      _ = c • (y - x) := hc
  have hzero : ∀ x ∈ P.vertices, f x = 0 → f.linear (g₀ x) = 0 := by
    intro x hx hfx
    have hxF : x ∈ affineZeroFace P f := ⟨subset_convexHull ℝ _ hx, hfx⟩
    have hconst : ∀ a ∈ affineZeroFace P f, ∀ b ∈ affineZeroFace P f,
        f.linear.toContinuousLinearMap a = f.linear.toContinuousLinearMap b := by
      intro a ha b hb
      have hfa := ha.2
      have hfb := hb.2
      rw [affine_form_apply f a] at hfa
      rw [affine_form_apply f b] at hfb
      change f.linear a = f.linear b
      linarith
    have hc := parallel_constant_on_face hg hF f.linear.toContinuousLinearMap hconst
      hx hv₀P hxF hv₀F
    change f.linear (g x - g v₀) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hc
  apply (minkowski_decomposable_iff_parallel_map _).mpr
  refine ⟨parallelWedgeMap f g₀, parallelWedgeMap_parallel P f hf g₀ hg₀ hzero, ?_⟩
  rintro ⟨a, b, hab⟩
  apply hnon
  refine ⟨a, wedgeProjection b + g v₀, ?_⟩
  intro x hx
  have hh := congrArg wedgeProjection (hab (wedgeLower x) (wedge_lower_vertex P f hf hx))
  simp only [parallelWedgeMap_projection, wedgeProjection_lower, map_add, map_smul,
    wedgeProjection_lower] at hh
  change g x - g v₀ = a • x + wedgeProjection b at hh
  calc
    g x = (g x - g v₀) + g v₀ := by abel
    _ = (a • x + wedgeProjection b) + g v₀ := by rw [hh]
    _ = a • x + (wedgeProjection b + g v₀) := by abel

theorem homothety_of_parallel_of_indecomposable (P : ConvexPolytope d)
    (hP : ¬MinkowskiDecomposable P) (g : E d → E d) (hg : IsParallelMap P g) :
    IsHomothetyOnVertices P g := by
  by_contra hnon
  exact hP ((minkowski_decomposable_iff_parallel_map P).mpr ⟨g, hg, hnon⟩)

theorem wedge_parallel_lower_homothety
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (hP : ¬MinkowskiDecomposable P)
    (g : E (d + 1) → E (d + 1)) (hg : IsParallelMap (wedgePolytope P f hf) g) :
    ∃ a : ℝ, ∃ b : E (d + 1), ∀ x ∈ P.vertices, g (wedgeLower x) = a • wedgeLower x + b := by
  let q : E d → E d := fun x => wedgeProjection (g (wedgeLower x))
  have hq : IsParallelMap P q := by
    intro x hx y hy hxy
    obtain ⟨c, hc⟩ := hg (wedgeLower x) (wedge_lower_vertex P f hf hx)
      (wedgeLower y) (wedge_lower_vertex P f hf hy) (wedge_lower_step P f hf hx hxy)
    refine ⟨c, ?_⟩
    have hh := congrArg wedgeProjection hc
    simpa only [map_sub, map_smul, wedgeProjection_lower] using hh
  obtain ⟨a, b₀, hab⟩ := homothety_of_parallel_of_indecomposable P hP q hq
  obtain ⟨v₀, hv₀⟩ := P.vertices_nonempty
  let b := g (wedgeLower v₀) - a • wedgeLower v₀
  refine ⟨a, b, ?_⟩
  intro x hx
  apply wedge_ext
  · change q x = wedgeProjection (a • wedgeLower x + b)
    dsimp only [b]
    rw [map_add, map_sub, map_smul, map_smul, wedgeProjection_lower, wedgeProjection_lower]
    change q x = a • x + (q v₀ - a • v₀)
    rw [hab x hx, hab v₀ hv₀]
    module
  · have hconst : ∀ z ∈ wedgeLower '' P.toSet, ∀ w ∈ wedgeLower '' P.toSet,
        wedgeHeight.toContinuousLinearMap z = wedgeHeight.toContinuousLinearMap w := by
      rintro z ⟨u, hu, rfl⟩ w ⟨v, hv, rfl⟩
      change wedgeHeight (wedgeLower u) = wedgeHeight (wedgeLower v)
      rw [wedgeHeight_lower, wedgeHeight_lower]
    have heq := parallel_constant_on_face hg (wedge_lower_isFace P f hf)
      wedgeHeight.toContinuousLinearMap hconst (wedge_lower_vertex P f hf hx)
      (wedge_lower_vertex P f hf hv₀)
      ⟨x, subset_convexHull ℝ _ hx, rfl⟩ ⟨v₀, subset_convexHull ℝ _ hv₀, rfl⟩
    change wedgeHeight (g (wedgeLower x)) = wedgeHeight (g (wedgeLower v₀)) at heq
    dsimp only [b]
    rw [map_add, map_sub, map_smul, map_smul, wedgeHeight_lower, wedgeHeight_lower]
    simpa only [smul_zero, zero_add, sub_zero] using heq

def wedgeUpperNormal (f : E d →ᵃ[ℝ] ℝ) : E (d + 1) →ₗ[ℝ] ℝ :=
  f.linear.comp wedgeProjection - wedgeHeight

theorem wedgeUpperNormal_apply (f : E d →ᵃ[ℝ] ℝ) (z : E (d + 1)) :
    wedgeUpperNormal f z = f.linear (wedgeProjection z) - wedgeHeight z := rfl

theorem wedgeUpperNormal_upper (f : E d →ᵃ[ℝ] ℝ) (x : E d) :
    wedgeUpperNormal f (wedgeUpper f x) = -f 0 := by
  rw [wedgeUpperNormal_apply, wedgeProjection_upper, wedgeHeight_upper, affine_form_apply f x]
  ring

theorem wedge_ext_upper {f : E d →ᵃ[ℝ] ℝ} {z w : E (d + 1)}
    (hp : wedgeProjection z = wedgeProjection w)
    (hn : wedgeUpperNormal f z = wedgeUpperNormal f w) : z = w := by
  apply wedge_ext hp
  rw [wedgeUpperNormal_apply, wedgeUpperNormal_apply, hp] at hn
  linarith

theorem wedge_parallel_upper_homothety
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (hP : ¬MinkowskiDecomposable P)
    (g : E (d + 1) → E (d + 1)) (hg : IsParallelMap (wedgePolytope P f hf) g) :
    ∃ a : ℝ, ∃ b : E (d + 1), ∀ x ∈ P.vertices,
      g (wedgeUpper f x) = a • wedgeUpper f x + b := by
  let q : E d → E d := fun x => wedgeProjection (g (wedgeUpper f x))
  have hq : IsParallelMap P q := by
    intro x hx y hy hxy
    obtain ⟨c, hc⟩ := hg (wedgeUpper f x) (wedge_upper_vertex P f hf hx)
      (wedgeUpper f y) (wedge_upper_vertex P f hf hy) (wedge_upper_step P f hf hx hxy)
    refine ⟨c, ?_⟩
    have hh := congrArg wedgeProjection hc
    simpa only [map_sub, map_smul, wedgeProjection_upper] using hh
  obtain ⟨a, b₀, hab⟩ := homothety_of_parallel_of_indecomposable P hP q hq
  obtain ⟨v₀, hv₀⟩ := P.vertices_nonempty
  let b := g (wedgeUpper f v₀) - a • wedgeUpper f v₀
  refine ⟨a, b, ?_⟩
  intro x hx
  apply wedge_ext_upper (f := f)
  · change q x = wedgeProjection (a • wedgeUpper f x + b)
    dsimp only [b]
    rw [map_add, map_sub, map_smul, map_smul, wedgeProjection_upper, wedgeProjection_upper]
    change q x = a • x + (q v₀ - a • v₀)
    rw [hab x hx, hab v₀ hv₀]
    module
  · have hconst : ∀ z ∈ wedgeUpper f '' P.toSet, ∀ w ∈ wedgeUpper f '' P.toSet,
        (wedgeUpperNormal f).toContinuousLinearMap z = (wedgeUpperNormal f).toContinuousLinearMap w := by
      rintro z ⟨u, hu, rfl⟩ w ⟨v, hv, rfl⟩
      change wedgeUpperNormal f (wedgeUpper f u) = wedgeUpperNormal f (wedgeUpper f v)
      rw [wedgeUpperNormal_upper, wedgeUpperNormal_upper]
    have heq := parallel_constant_on_face hg (wedge_upper_isFace P f hf)
      (wedgeUpperNormal f).toContinuousLinearMap hconst (wedge_upper_vertex P f hf hx)
      (wedge_upper_vertex P f hf hv₀)
      ⟨x, subset_convexHull ℝ _ hx, rfl⟩ ⟨v₀, subset_convexHull ℝ _ hv₀, rfl⟩
    dsimp only [b]
    rw [map_add, map_sub, map_smul, map_smul, wedgeUpperNormal_upper, wedgeUpperNormal_upper]
    change wedgeUpperNormal f (g (wedgeUpper f x)) =
      a * (-f 0) + (wedgeUpperNormal f (g (wedgeUpper f v₀)) - a * (-f 0))
    change wedgeUpperNormal f (g (wedgeUpper f x)) =
      wedgeUpperNormal f (g (wedgeUpper f v₀)) at heq
    linarith

theorem wedge_indecomposable_of_indecomposable
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (hP : ¬MinkowskiDecomposable P)
    (hcommon : ∃ u ∈ P.vertices, ∃ v ∈ P.vertices, u ≠ v ∧ f u = 0 ∧ f v = 0) :
    ¬MinkowskiDecomposable (wedgePolytope P f hf) := by
  intro hW
  obtain ⟨g, hg, hnon⟩ := (minkowski_decomposable_iff_parallel_map _).mp hW
  obtain ⟨a, b, hab⟩ := wedge_parallel_lower_homothety P f hf hP g hg
  obtain ⟨c, e, hce⟩ := wedge_parallel_upper_homothety P f hf hP g hg
  obtain ⟨u, hu, v, hv, huv, hfu, hfv⟩ := hcommon
  have huEq := (wedgeLower_eq_upper_iff f u u).mpr ⟨rfl, hfu⟩
  have hvEq := (wedgeLower_eq_upper_iff f v v).mpr ⟨rfl, hfv⟩
  have huParams : a • wedgeLower u + b = c • wedgeLower u + e := by
    rw [← hab u hu, huEq, hce u hu]
  have hvParams : a • wedgeLower v + b = c • wedgeLower v + e := by
    rw [← hab v hv, hvEq, hce v hv]
  obtain ⟨hac, hbe⟩ := homothety_parameters_unique (wedgeLower_injective.ne huv) huParams hvParams
  subst c
  subst e
  apply hnon
  refine ⟨a, b, ?_⟩
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hab x hx
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hce x hx

/-- The wedge preserves ordinary Minkowski decomposability whenever its
collapsed face contains two distinct vertices. This includes every facet
of every full-dimensional polytope of dimension at least two. -/
theorem wedge_decomposable_iff
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (hcommon : ∃ u ∈ P.vertices, ∃ v ∈ P.vertices, u ≠ v ∧ f u = 0 ∧ f v = 0) :
    MinkowskiDecomposable (wedgePolytope P f hf) ↔ MinkowskiDecomposable P := by
  constructor
  · intro hW
    by_contra hP
    exact wedge_indecomposable_of_indecomposable P f hf hP hcommon hW
  · intro hP
    obtain ⟨u, hu, v, hv, huv, hfu, hfv⟩ := hcommon
    exact wedge_decomposable_of_decomposable P f hf ⟨u, subset_convexHull ℝ _ hu, hfu⟩ hP

end Papers.Polytopes

end
end
end BundlePart15

section BundlePart16
/- Source: Papers/ConditionalWedge.lean -/



@[expose] public section

/-!
# The dimension-raising construction for conditional decomposability

A facet with exactly four vertices outside it gives a wedge with four
additional vertices. Its lower facet again has exactly four vertices
outside it. The actual face correspondence and ordinary Minkowski
decomposability are transported in both realizations.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem facet_has_two_vertices (P : ConvexPolytope d) (hP : P.IsFullDim)
    (hd : 2 ≤ d) {F : Set (E d)} (hF : IsFacet P F) :
    ∃ u ∈ P.vertices, ∃ v ∈ P.vertices, u ≠ v ∧ u ∈ F ∧ v ∈ F := by
  obtain ⟨u, hu⟩ := (facePolytope P hF.1).vertices_nonempty
  obtain ⟨huP, huF⟩ := Finset.mem_filter.mp hu
  have hdim : 1 ≤ faceDim F := by
    have hh := hF.2
    change P.dim = d at hP
    omega
  obtain ⟨E, hE, hdE, huE, hEF⟩ := edge_inside_face_at_vertex P hF.1 huP huF hdim
  obtain ⟨v, hv, hvE, hvu, _⟩ := spigolo_segmento P hE hdE huP huE
  exact ⟨u, huP, v, hv, hvu.symm, huF, hEF hvE⟩

theorem zero_face_vertex_filter (P : ConvexPolytope d) (F : Set (E d))
    (f : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace P F f) :
    P.vertices.filter (fun v => f v = 0) = P.vertices.filter (fun v => v ∈ F) := by
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hv, hz⟩
    exact ⟨hv, (hf.mem_iff v).mpr ⟨subset_convexHull ℝ _ hv, hz⟩⟩
  · rintro ⟨hv, hvF⟩
    exact ⟨hv, hf.eq_zero hvF⟩

theorem wedge_lower_vertex_filter
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    (wedgePolytope P f hf).vertices.filter (fun z => z ∈ wedgeLower '' P.toSet) =
      P.vertices.image wedgeLower := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzV, x, hx, hzx⟩ := Finset.mem_filter.mp hz
    have hp := wedge_projection_vertex P f hf hzV
    have hxV : x ∈ P.vertices := by simpa only [← hzx, wedgeProjection_lower] using hp
    exact Finset.mem_image.mpr ⟨x, hxV, hzx⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨wedge_lower_vertex P f hf hx,
      ⟨x, subset_convexHull ℝ _ hx, rfl⟩⟩

theorem wedge_lower_vertex_count
    (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, 0 ≤ f x) :
    ((wedgePolytope P f hf).vertices.filter (fun z => z ∈ wedgeLower '' P.toSet)).card =
      P.vertices.card := by
  rw [wedge_lower_vertex_filter, Finset.card_image_of_injective _ wedgeLower_injective]

theorem wedge_corresponding_realization
    (P Q : ConvexPolytope d) (F : Set (E d)) (hF : P.IsFace F)
    (f : E d →ᵃ[ℝ] ℝ) (hs : SupportsFace P F f)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (hcommon : ∃ u ∈ P.vertices, ∃ v ∈ P.vertices, u ≠ v ∧ u ∈ F ∧ v ∈ F)
    (φ : FaceType P ≃o FaceType Q) :
    ∃ g : E d →ᵃ[ℝ] ℝ, ∃ hg : ∀ x ∈ Q.vertices, 0 ≤ g x,
      CombinatoriallyEquivalent (wedgePolytope P f hf) (wedgePolytope Q g hg) ∧
        (MinkowskiDecomposable (wedgePolytope Q g hg) ↔ MinkowskiDecomposable Q) := by
  obtain ⟨g, hgs⟩ := exists_supportsFace Q (φ ⟨F, hF⟩).property
  have hg : ∀ x ∈ Q.vertices, 0 ≤ g x :=
    fun x hx => hgs.1 x (subset_convexHull ℝ _ hx)
  have hzero (v : VertexType P) : f v.val = 0 ↔ g (imageVertex φ v).val = 0 := by
    have hleft := hs.mem_iff v.val
    have hright := hgs.mem_iff (imageVertex φ v).val
    have hvP : v.val ∈ P.toSet := subset_convexHull ℝ _ v.property
    have hvQ : (imageVertex φ v).val ∈ Q.toSet :=
      subset_convexHull ℝ _ (imageVertex φ v).property
    rw [and_iff_right hvP] at hleft
    rw [and_iff_right hvQ] at hright
    rw [← hleft, ← hright]
    exact (imageVertex_mem_iff φ v ⟨F, hF⟩).symm
  have hcommonQ : ∃ u ∈ Q.vertices, ∃ v ∈ Q.vertices, u ≠ v ∧ g u = 0 ∧ g v = 0 := by
    obtain ⟨u, hu, v, hv, huv, huF, hvF⟩ := hcommon
    let u' := imageVertex φ ⟨u, hu⟩
    let v' := imageVertex φ ⟨v, hv⟩
    refine ⟨u'.val, u'.property, v'.val, v'.property, ?_,
      (hzero ⟨u, hu⟩).mp (hs.eq_zero huF), (hzero ⟨v, hv⟩).mp (hs.eq_zero hvF)⟩
    intro h
    exact huv (congrArg Subtype.val ((vertexEquivOfFaceOrder φ).injective (Subtype.ext h)))
  exact ⟨g, hg, ⟨wedgeFaceOrderIso f g hf hg φ hzero⟩,
    wedge_decomposable_iff Q g hg hcommonQ⟩

theorem wedge_conditionallyDecomposable
    (P : ConvexPolytope d) (F : Set (E d)) (hF : P.IsFace F)
    (f : E d →ᵃ[ℝ] ℝ) (hs : SupportsFace P F f)
    (hf : ∀ x ∈ P.vertices, 0 ≤ f x)
    (hcommon : ∃ u ∈ P.vertices, ∃ v ∈ P.vertices, u ≠ v ∧ u ∈ F ∧ v ∈ F)
    (hP : ConditionallyDecomposable P) : ConditionallyDecomposable (wedgePolytope P f hf) := by
  obtain ⟨⟨Q, ⟨φ⟩, hQ⟩, ⟨R, ⟨ψ⟩, hR⟩⟩ := hP
  obtain ⟨g, hg, hWQ, hQiff⟩ := wedge_corresponding_realization P Q F hF f hs hf hcommon φ
  obtain ⟨k, hk, hWR, hRiff⟩ := wedge_corresponding_realization P R F hF f hs hf hcommon ψ
  exact ⟨⟨wedgePolytope Q g hg, hWQ, hQiff.mpr hQ⟩,
    ⟨wedgePolytope R k hk, hWR, fun h => hR (hRiff.mp h)⟩⟩

/-- The unrestricted geometric step: four outside vertices stay four
outside vertices, while both dimension and total vertex count increase by
the required amounts. -/
theorem conditional_wedge_step
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 2 ≤ d)
    (hconditional : ConditionallyDecomposable P)
    (F : Set (E d)) (hF : IsFacet P F)
    (hfour : P.vertices.card = (P.vertices.filter (fun v => v ∈ F)).card + 4) :
    ∃ W : ConvexPolytope (d + 1), W.IsFullDim ∧ ConditionallyDecomposable W ∧
      W.vertices.card = P.vertices.card + 4 ∧
      ∃ G : Set (E (d + 1)), IsFacet W G ∧
        W.vertices.card = (W.vertices.filter (fun v => v ∈ G)).card + 4 := by
  obtain ⟨f, hs⟩ := exists_supportsFace P hF.1
  have hf : ∀ x ∈ P.vertices, 0 ≤ f x :=
    fun x hx => hs.1 x (subset_convexHull ℝ _ hx)
  have hne : f ≠ 0 := hF.support_ne_zero hs
  have hcommon := facet_has_two_vertices P hP hd hF
  have hcard : (wedgePolytope P f hf).vertices.card = P.vertices.card + 4 := by
    rw [wedgePolytope_card, zero_face_vertex_filter P F f hs]
    omega
  refine ⟨wedgePolytope P f hf,
    wedgePolytope_fullDim P hP f hf (positive_vertex_of_nonzero_support P hP f hf hne),
    wedge_conditionallyDecomposable P F hF.1 f hs hf hcommon hconditional,
    hcard, wedgeLower '' P.toSet, wedge_lower_isFacet P hP f hf hne, ?_⟩
  rw [wedge_lower_vertex_count]
  exact hcard

end Papers.Polytopes

end
end
end BundlePart16

section BundlePart17
/- Source: Papers/ConditionalSharpAttainment.lean -/




@[expose] public section

/-!
# The unrestricted sharpness construction

The explicit eight-vertex base and the geometric wedge step produce a
conditionally decomposable d-polytope with 4d−4 vertices for every d≥3.
This is the attainment part of Theorem 1. The lower-bound part is a
separate claim and is not asserted by this file.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

theorem conditional_wedge_family : ∀ n : ℕ,
    ∃ P : ConvexPolytope (n + 3), P.IsFullDim ∧ ConditionallyDecomposable P ∧
      P.vertices.card = 4 * (n + 3) - 4 ∧
      ∃ F : Set (E (n + 3)), IsFacet P F ∧
        P.vertices.card = (P.vertices.filter (fun v => v ∈ F)).card + 4 := by
  intro n
  induction n with
  | zero =>
    refine ⟨ConditionalEight.polytope 0, ConditionalEight.polytope_fullDim 0,
      ConditionalEight.conditionallyDecomposable, ?_,
      ConditionalEight.face 0 4, ConditionalEight.face_isFacet 0 4,
      ConditionalEight.four_vertices_outside_facet⟩
    exact ConditionalEight.polytope_card 0
  | succ n ih =>
    obtain ⟨P, hP, hc, hn, F, hF, hfour⟩ := ih
    obtain ⟨W, hW, hwc, hwcount, G, hG, hwfour⟩ :=
      conditional_wedge_step P hP (by omega) hc F hF hfour
    refine ⟨W, hW, hwc, ?_, G, hG, hwfour⟩
    rw [hwcount, hn]
    omega

/-- Every dimension in the paper's entire range, with the exact vertex
count and actual decomposable and indecomposable realizations. -/
theorem conditional_decomposability_attainment (d : ℕ) (hd : 3 ≤ d) :
    ∃ P : ConvexPolytope d, P.IsFullDim ∧ ConditionallyDecomposable P ∧
      P.vertices.card = 4 * d - 4 := by
  have h := conditional_wedge_family (d - 3)
  rw [Nat.sub_add_cancel hd] at h
  obtain ⟨P, hP, hc, hn, _⟩ := h
  exact ⟨P, hP, hc, hn⟩

end Papers.Polytopes

end
end
end BundlePart17
