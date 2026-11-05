module
public import consolidated_dev.minkowski_map_core
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

set_option Elab.async false

section BundlePart0
/- Source: Papers/MatchingProjectiveLines.lean -/




@[expose] public section
namespace Papers.Polytopes
open Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification
variable {d : ℕ}
/-- The genuine projective line through two affine points. -/
noncomputable def edgeProjectiveLine (x y : E d) : Submodule ℝ (E d × ℝ) :=
  homogeneousSpan (K := ℝ) ({x,y} : Set (E d))
end Papers.Polytopes


end
end BundlePart0

section BundlePart1
/- Source: Papers/ExposedLineRanks.lean -/
@[expose] public section







/-!
# Homogeneous ranks of actual exposed edge lines
-/

namespace Papers.Polytopes.ExposedLineRanks

open Papers.Polytopes.ExposedEdgeCenters

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem point_injective : Function.Injective (point : V → V × ℝ) :=
  fun _ _ h => congrArg Prod.fst h

theorem point_pair_linearIndependent {x y : V} (hxy : x ≠ y) :
    LinearIndependent ℝ ![point x, point y] := by
  apply (LinearIndependent.pair_iff' (point_ne_zero x)).mpr
  intro a ha
  have has : a = 1 := by
    have h := congrArg Prod.snd ha
    simpa [point] using h
  apply hxy
  have h := congrArg Prod.fst ha
  simpa [point,has] using h

theorem edgeLine_finrank_eq_two {x y : V} (hxy : x ≠ y) :
    Module.finrank ℝ (edgeLine x y) = 2 := by
  have hrange :
      Set.range (![point x, point y] : Fin 2 → V × ℝ) =
        ({point x,point y} : Set (V × ℝ)) := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact ⟨0,rfl⟩
      · rcases Set.mem_singleton_iff.mp hz with rfl
        exact ⟨1,rfl⟩
  have h := finrank_span_eq_card (point_pair_linearIndependent hxy)
  rw [hrange] at h
  change Module.finrank ℝ (Submodule.span ℝ ({point x,point y} : Set (V × ℝ)))=2
  simpa using h

/-- A vertex of one edge which is disjoint from another exposed edge lies
outside the second edge line. -/
theorem vertex_not_mem_other_edgeLine
    (C : Set V) (g : V →ᵃ[ℝ] ℝ) {x u v : V}
    (hx : x ∈ C.extremePoints ℝ) (hu : u ∈ C) (hv : v ∈ C)
    (hgu : g u = 0) (hgv : g v = 0)
    (hzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ u v)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    point x ∉ edgeLine u v := by
  intro hline
  have hgx := affine_eq_zero_on_edgeLine g hgu hgv hline
  rcases (support_zero_iff_endpoint C g hu hv hgu hgv hzero hx).mp hgx with h | h
  · exact hxu h
  · exact hxv h

theorem matching_lines_joint_rank_ge_three
    [FiniteDimensional ℝ V]
    (C : Set V) (g : V →ᵃ[ℝ] ℝ) {x y u v : V}
    (hx : x ∈ C.extremePoints ℝ) (hu : u ∈ C) (hv : v ∈ C)
    (huv : u ≠ v) (hgu : g u = 0) (hgv : g v = 0)
    (hzero : ∀ z ∈ C, g z = 0 ↔ z ∈ segment ℝ u v)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    3 ≤ Module.finrank ℝ ↥(edgeLine x y ⊔ edgeLine u v) := by
  have hdim := edgeLine_finrank_eq_two huv
  by_contra h
  have heq : edgeLine u v = edgeLine x y ⊔ edgeLine u v :=
    Submodule.eq_of_le_of_finrank_le le_sup_right (by omega)
  have hle : edgeLine x y ≤ edgeLine u v := by
    rw [heq]
    exact le_sup_left
  apply vertex_not_mem_other_edgeLine C g hx hu hv hgu hgv hzero hxu hxv
  apply hle
  exact Submodule.subset_span (by simp)

end Papers.Polytopes.ExposedLineRanks


end
end BundlePart1

section BundlePart2
/- Source: Papers/SupportedFaceSpans.lean -/
@[expose] public section




/-!
# Supporting faces are determined by their homogeneous spans

The argument needs only their actual affine support equations. It does not
assume an abstract face-incidence certificate or a separate face-lattice
injectivity axiom.
-/

namespace Papers.Polytopes.SupportedFaceSpans

open Papers.Polytopes.ExposedEdgeCenters

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem homogeneous_span_le_support_kernel
    (F : Set V) (g : V →ᵃ[ℝ] ℝ) (hzero : ∀ x ∈ F, g x = 0) :
    Submodule.span ℝ (point '' F) ≤ (affineForm g).ker := by
  refine Submodule.span_le.mpr ?_
  rintro z ⟨x,hx,rfl⟩
  change affineForm g (point x) = 0
  simpa using hzero x hx

theorem mem_supported_face_iff_mem_body_and_span
    (C F : Set V) (g : V →ᵃ[ℝ] ℝ)
    (hF : ∀ x, x ∈ F ↔ x ∈ C ∧ g x = 0) (x : V) :
    x ∈ F ↔ x ∈ C ∧ point x ∈ Submodule.span ℝ (point '' F) := by
  constructor
  · intro hx
    exact ⟨((hF x).mp hx).1,Submodule.subset_span ⟨x,hx,rfl⟩⟩
  · rintro ⟨hxC,hxspan⟩
    apply (hF x).mpr
    refine ⟨hxC,?_⟩
    have hkernel := homogeneous_span_le_support_kernel F g
      (fun y hy => ((hF y).mp hy).2) hxspan
    simpa using hkernel

theorem supported_faces_eq_of_homogeneous_spans_eq
    (C F G : Set V) (f g : V →ᵃ[ℝ] ℝ)
    (hF : ∀ x, x ∈ F ↔ x ∈ C ∧ f x = 0)
    (hG : ∀ x, x ∈ G ↔ x ∈ C ∧ g x = 0)
    (hspan : Submodule.span ℝ (point '' F) =
      Submodule.span ℝ (point '' G)) :
    F = G := by
  ext x
  rw [mem_supported_face_iff_mem_body_and_span C F f hF,
    mem_supported_face_iff_mem_body_and_span C G g hG, hspan]

/-- Two rank-three face planes containing the same rank-three subspace are
equal, and the genuine supporting faces therefore coincide. -/
theorem supported_faces_eq_of_common_spanning_subspace
    [FiniteDimensional ℝ V]
    (C F G : Set V) (f g : V →ᵃ[ℝ] ℝ)
    (hF : ∀ x, x ∈ F ↔ x ∈ C ∧ f x = 0)
    (hG : ∀ x, x ∈ G ↔ x ∈ C ∧ g x = 0)
    (hFr : Module.finrank ℝ (Submodule.span ℝ (point '' F)) = 3)
    (hGr : Module.finrank ℝ (Submodule.span ℝ (point '' G)) = 3)
    (L : Submodule ℝ (V × ℝ)) (hL : 3 ≤ Module.finrank ℝ L)
    (hLF : L ≤ Submodule.span ℝ (point '' F))
    (hLG : L ≤ Submodule.span ℝ (point '' G)) :
    F = G := by
  have hLF' : L = Submodule.span ℝ (point '' F) :=
    Submodule.eq_of_le_of_finrank_le hLF (by omega)
  have hLG' : L = Submodule.span ℝ (point '' G) :=
    Submodule.eq_of_le_of_finrank_le hLG (by omega)
  exact supported_faces_eq_of_homogeneous_spans_eq C F G f g hF hG
    (hLF'.symm.trans hLG')

end Papers.Polytopes.SupportedFaceSpans


end
end BundlePart2

section BundlePart3
/- Source: Papers/ExposedProjectiveBridge.lean -/





@[expose] public section

/-! Identification of the homogeneous conventions used by the edge geometry. -/

namespace Papers.Polytopes

open Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification

variable {d : ℕ}

theorem exposed_point_eq_homogenize (x : E d) :
    ExposedEdgeCenters.point x = homogenize x := rfl

theorem exposed_edgeLine_eq_edgeProjectiveLine (x y : E d) :
    ExposedEdgeCenters.edgeLine x y = edgeProjectiveLine x y := by
  simp only [ExposedEdgeCenters.edgeLine,edgeProjectiveLine,homogeneousSpan,
    Set.image_pair,ExposedEdgeCenters.point,homogenize]

theorem homogeneousSpan_eq_span_exposed_points (F : Set (E d)) :
    homogeneousSpan (K := ℝ) F = Submodule.span ℝ (ExposedEdgeCenters.point '' F) := rfl


namespace ExposedProjectiveBridge

theorem point_mem_span {F : Set (E d)} {x : E d} (hx : x ∈ F) :
    homogenize x ∈ homogeneousSpan (K := ℝ) F :=
  Submodule.subset_span ⟨x,hx,rfl⟩

theorem line_le_span {F : Set (E d)} {x y : E d} (hx : x ∈ F) (hy : y ∈ F) :
    edgeProjectiveLine x y ≤ homogeneousSpan (K := ℝ) F := by
  change Submodule.span ℝ (homogenize '' ({x,y} : Set (E d))) ≤
    Submodule.span ℝ (homogenize '' F)
  apply Submodule.span_mono
  apply Set.image_mono
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact hx
  · rcases Set.mem_singleton_iff.mp hz with rfl
    exact hy

end ExposedProjectiveBridge

end Papers.Polytopes


end
end BundlePart3

section BundlePart4
/- Source: Papers/HomogeneousFaceSpans.lean -/






@[expose] public section

/-!
# Homogeneous spans of actual polytope faces

The dimension formula and face-plane injectivity are derived from affine
geometry. A genuine face equals the intersection of the body with its affine
span, so two such faces with the same homogeneous span coincide.
-/

noncomputable section

namespace Papers.Polytopes.HomogeneousFaceSpans

open Set Module Papers.Coordinates
open Papers.HomogeneousSpanDimension
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

section General

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem liftPoint_mem_liftSpan_iff_mem_affineSpan
    {S : Set V} {p : V} (hp : p ∈ S) (x : V) :
    liftPoint x ∈ liftSpan S ↔ x ∈ affineSpan ℝ S := by
  have hdir : x - p ∈ vectorSpan ℝ S ↔ x ∈ affineSpan ℝ S := by
    simpa only [direction_affineSpan, vsub_eq_sub] using
      (AffineSubspace.vsub_right_mem_direction_iff_mem (mem_affineSpan ℝ hp) x)
  constructor
  · intro hx
    rw [liftSpan_eq_direction_sup_point hp] at hx
    obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp hx
    obtain ⟨w,hw,rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
    have ha : a = 1 := by
      have h := congrArg Prod.snd huv
      simpa [liftPoint] using h
    have heq : w + p = x := by
      have h := congrArg Prod.fst huv
      simpa [liftPoint,ha] using h
    apply hdir.mp
    rw [← heq,add_sub_cancel_right]
    exact hw
  · intro hx
    rw [liftSpan_eq_direction_sup_point hp]
    refine Submodule.mem_sup.mpr
      ⟨(LinearMap.inl ℝ V ℝ) (x-p),
        Submodule.mem_map.mpr ⟨x-p,hdir.mpr hx,rfl⟩,
        liftPoint p,Submodule.subset_span (Set.mem_singleton _),?_⟩
    ext <;> simp [liftPoint]

end General

variable {d : ℕ}

theorem homogeneousSpan_rank_of_nonempty
    (F : Set (E d)) (hF : F.Nonempty) :
    finrank ℝ (homogeneousSpan (K := ℝ) F) = faceDim F + 1 := by
  change finrank ℝ (liftSpan F) = finrank ℝ (vectorSpan ℝ F) + 1
  exact finrank_liftSpan hF

theorem twoFace_homogeneousSpan_rank
    (F : Set (E d)) (hF : F.Nonempty) (hdim : faceDim F = 2) :
    finrank ℝ (homogeneousSpan (K := ℝ) F) = 3 := by
  rw [homogeneousSpan_rank_of_nonempty F hF,hdim]

theorem affineSpan_eq_of_homogeneousSpan_eq
    (F G : Set (E d)) (hF : F.Nonempty) (hG : G.Nonempty)
    (hspan : homogeneousSpan (K := ℝ) F = homogeneousSpan (K := ℝ) G) :
    affineSpan ℝ F = affineSpan ℝ G := by
  obtain ⟨p,hp⟩ := hF
  obtain ⟨q,hq⟩ := hG
  apply SetLike.coe_injective
  ext x
  change x ∈ affineSpan ℝ F ↔ x ∈ affineSpan ℝ G
  rw [← liftPoint_mem_liftSpan_iff_mem_affineSpan hp x,
    ← liftPoint_mem_liftSpan_iff_mem_affineSpan hq x]
  change homogenize x ∈ homogeneousSpan (K := ℝ) F ↔ homogenize x ∈ homogeneousSpan (K := ℝ) G
  rw [hspan]

theorem actual_mem_face_iff_mem_body_and_homogeneousSpan
    (P : ConvexPolytope d) (F : Set (E d)) (hF : P.IsFace F) (x : E d) :
    x ∈ F ↔ x ∈ P.toSet ∧ homogenize x ∈ homogeneousSpan (K := ℝ) F := by
  obtain ⟨g,hnonneg,hzero⟩ := exists_nonnegative_affine_face_form P F hF
  have hsupport (z : E d) : z ∈ F ↔ z ∈ P.toSet ∧ g z = 0 := by
    constructor
    · intro hzF
      have hzP := face_subset_toSet P hF hzF
      exact ⟨hzP,(hzero z hzP).mpr hzF⟩
    · rintro ⟨hzP,hz⟩
      exact (hzero z hzP).mp hz
  exact SupportedFaceSpans.mem_supported_face_iff_mem_body_and_span
    P.toSet F g hsupport x

theorem actual_vertex_mem_face_of_homogeneousSpan
    (P : ConvexPolytope d) (F : Set (E d)) (hF : P.IsFace F)
    {x : E d} (hx : x ∈ P.vertices)
    (hspan : homogenize x ∈ homogeneousSpan (K := ℝ) F) : x ∈ F :=
  (actual_mem_face_iff_mem_body_and_homogeneousSpan P F hF x).mpr
    ⟨vertex_mem_body_of_mem_vertices P hx,hspan⟩

theorem actual_faces_eq_of_homogeneousSpan_eq
    (P : ConvexPolytope d) (F G : Set (E d))
    (hF : P.IsFace F) (hG : P.IsFace G)
    (hFn : F.Nonempty) (hGn : G.Nonempty)
    (hspan : homogeneousSpan (K := ℝ) F = homogeneousSpan (K := ℝ) G) :
    F = G := by
  ext x
  rw [actual_mem_face_iff_mem_body_and_homogeneousSpan P F hF x,
    actual_mem_face_iff_mem_body_and_homogeneousSpan P G hG x,hspan]

theorem actual_distinct_faces_have_distinct_homogeneousSpan
    (P : ConvexPolytope d) (F G : Set (E d))
    (hF : P.IsFace F) (hG : P.IsFace G)
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hne : F ≠ G) :
    homogeneousSpan (K := ℝ) F ≠ homogeneousSpan (K := ℝ) G :=
  fun h => hne (actual_faces_eq_of_homogeneousSpan_eq P F G hF hG hFn hGn h)

end Papers.Polytopes.HomogeneousFaceSpans


end
end
end BundlePart4

section BundlePart5
/- Source: Papers/ThreeColorPlaneIntersection.lean -/
@[expose] public section




/-!
# Two plane witnesses force collinear projective centers

A projective point is a one-dimensional linear subspace.  The result deliberately
allows equal centers: reconstruction only needs their combined dimension at
most two.
-/

namespace Papers.Polytopes.ThreeColorPlanes

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem plane_intersection_rank_le_two
    (A B : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 3) (hB : Module.finrank ℝ B = 3)
    (hne : A ≠ B) :
    Module.finrank ℝ ↥(A ⊓ B) ≤ 2 := by
  by_contra h
  have hthree : 3 ≤ Module.finrank ℝ ↥(A ⊓ B) := by omega
  have hleft : A ⊓ B = A :=
    Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  have hle : A ≤ B := by
    rw [← hleft]
    exact inf_le_right
  apply hne
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

/-- A common actual edge identifies the entire intersection of two distinct
two-face planes. -/
theorem plane_intersection_eq_common_line
    (A B L : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 3) (hB : Module.finrank ℝ B = 3)
    (hne : A ≠ B)
    (hL : Module.finrank ℝ L = 2) (hLA : L ≤ A) (hLB : L ≤ B) :
    A ⊓ B = L := by
  have hbound := plane_intersection_rank_le_two A B hA hB hne
  exact (Submodule.eq_of_le_of_finrank_le (le_inf hLA hLB) (by omega)).symm

theorem center_le_common_line
    (A B L J : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 3) (hB : Module.finrank ℝ B = 3)
    (hne : A ≠ B)
    (hL : Module.finrank ℝ L = 2) (hLA : L ≤ A) (hLB : L ≤ B)
    (hJA : J ≤ A) (hJB : J ≤ B) :
    J ≤ L := by
  rw [← plane_intersection_eq_common_line A B L hA hB hne hL hLA hLB]
  exact le_inf hJA hJB

/-- The star case: the star vertex and the two reconstructed exterior centers
lie in each of two distinct witnessing two-face planes. -/
theorem three_centers_rank_le_two
    (A B J₀₁ J₀₂ J₁₂ : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 3) (hB : Module.finrank ℝ B = 3)
    (hne : A ≠ B)
    (h₀₁A : J₀₁ ≤ A) (h₀₁B : J₀₁ ≤ B)
    (h₀₂A : J₀₂ ≤ A) (h₀₂B : J₀₂ ≤ B)
    (h₁₂A : J₁₂ ≤ A) (h₁₂B : J₁₂ ≤ B) :
    Module.finrank ℝ ↥(J₀₁ ⊔ J₀₂ ⊔ J₁₂) ≤ 2 := by
  have hle : J₀₁ ⊔ J₀₂ ⊔ J₁₂ ≤ A ⊓ B :=
    sup_le (sup_le (le_inf h₀₁A h₀₁B) (le_inf h₀₂A h₀₂B))
      (le_inf h₁₂A h₁₂B)
  exact (Submodule.finrank_mono hle).trans
    (plane_intersection_rank_le_two A B hA hB hne)

/-- The single-edge case: any one-dimensional subspace of the remaining
edge line is compatible with both reconstructed exterior centers. -/
theorem three_centers_rank_le_two_of_edge_line
    (A B L J₀₁ J₀₂ J₁₂ : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 3) (hB : Module.finrank ℝ B = 3)
    (hne : A ≠ B)
    (hL : Module.finrank ℝ L = 2) (hLA : L ≤ A) (hLB : L ≤ B)
    (h₀₁ : J₀₁ ≤ L)
    (h₀₂A : J₀₂ ≤ A) (h₀₂B : J₀₂ ≤ B)
    (h₁₂A : J₁₂ ≤ A) (h₁₂B : J₁₂ ≤ B) :
    Module.finrank ℝ ↥(J₀₁ ⊔ J₀₂ ⊔ J₁₂) ≤ 2 := by
  apply three_centers_rank_le_two A B J₀₁ J₀₂ J₁₂ hA hB hne
  · exact h₀₁.trans hLA
  · exact h₀₁.trans hLB
  · exact h₀₂A
  · exact h₀₂B
  · exact h₁₂A
  · exact h₁₂B

/-- An off-central edge and the central projective line determine at most one
two-face plane. This is the one exceptional face omitted in the degree count. -/
theorem plane_eq_of_contains_central_line_and_offline_edge
    (D L A B : Submodule ℝ V)
    (hD : Module.finrank ℝ D = 2)
    (hA : Module.finrank ℝ A = 3) (hB : Module.finrank ℝ B = 3)
    (hoff : ¬ L ≤ D)
    (hDA : D ≤ A) (hDB : D ≤ B) (hLA : L ≤ A) (hLB : L ≤ B) :
    A = B := by
  have hlow : 3 ≤ Module.finrank ℝ ↥(D ⊔ L) := by
    by_contra h
    have heq : D = D ⊔ L :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    apply hoff
    rw [heq]
    exact le_sup_right
  have hSA : D ⊔ L = A :=
    Submodule.eq_of_le_of_finrank_le (sup_le hDA hLA) (by omega)
  have hSB : D ⊔ L = B :=
    Submodule.eq_of_le_of_finrank_le (sup_le hDB hLB) (by omega)
  exact hSA.symm.trans hSB

/-- Two distinct two-face planes cannot contain the same two matching edge
lines: their joint homogeneous span already has dimension at least three. -/
theorem plane_eq_of_contains_matching_lines
    (L M A B : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 3) (hB : Module.finrank ℝ B = 3)
    (hLM : 3 ≤ Module.finrank ℝ ↥(L ⊔ M))
    (hLA : L ≤ A) (hLB : L ≤ B) (hMA : M ≤ A) (hMB : M ≤ B) :
    A = B := by
  have hSA : L ⊔ M = A :=
    Submodule.eq_of_le_of_finrank_le (sup_le hLA hMA) (by omega)
  have hSB : L ⊔ M = B :=
    Submodule.eq_of_le_of_finrank_le (sup_le hLB hMB) (by omega)
  exact hSA.symm.trans hSB

end Papers.Polytopes.ThreeColorPlanes


end
end BundlePart5

section BundlePart6
/- Source: Papers/CofacialCounting.lean -/
@[expose] public section



/-!
# The cofacial degree count

All but at most one incident two-face supplies a distinct partner edge.
The geometry proving those two facts is kept separate from this finite count.
-/

namespace Papers.Polytopes.CofacialCounting

variable {I F : Type*}

theorem incident_count_le_degree
    [Fintype I] (G : SimpleGraph I) [DecidableRel G.Adj]
    (i : I) (faces : Finset F) (partner : F → I → Prop)
    (hex : ∀ A ∈ faces, ∃ j, G.Adj i j ∧ partner A j)
    (hunique : ∀ A ∈ faces, ∀ B ∈ faces, ∀ j,
      partner A j → partner B j → A = B) :
    faces.card ≤ G.degree i := by
  classical
  have hg (A : faces) : ∃ j, G.Adj i j ∧ partner A.val j := hex A.val A.property
  let pick : faces → G.neighborSet i :=
    fun A => ⟨Classical.choose (hg A),(Classical.choose_spec (hg A)).1⟩
  have hpick : Function.Injective pick := by
    intro A B h
    apply Subtype.ext
    apply hunique A.val A.property B.val B.property (pick A).val
    · exact (Classical.choose_spec (hg A)).2
    · have hval := congrArg (fun j : G.neighborSet i => j.val) h
      change Classical.choose (hg A) = Classical.choose (hg B) at hval
      change partner B.val (Classical.choose (hg A))
      rw [hval]
      exact (Classical.choose_spec (hg B)).2
  simpa only [Fintype.card_coe,SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective pick hpick

theorem incident_count_le_degree_add_one
    [Fintype I] (G : SimpleGraph I) [DecidableRel G.Adj]
    (i : I) (faces : Finset F) (bad : F → Prop) (partner : F → I → Prop)
    (hbad : ∀ A ∈ faces, ∀ B ∈ faces, bad A → bad B → A = B)
    (hex : ∀ A ∈ faces, ¬ bad A → ∃ j, G.Adj i j ∧ partner A j)
    (hunique : ∀ A ∈ faces, ∀ B ∈ faces, ∀ j,
      partner A j → partner B j → A = B) :
    faces.card ≤ G.degree i + 1 := by
  classical
  let good := faces.filter fun A => ¬ bad A
  let exceptional := faces.filter bad
  have hg (A : good) : ∃ j, G.Adj i j ∧ partner A.val j :=
    hex A.val (Finset.mem_filter.mp A.property).1 (Finset.mem_filter.mp A.property).2
  let pick : good → G.neighborSet i :=
    fun A => ⟨Classical.choose (hg A), (Classical.choose_spec (hg A)).1⟩
  have hpick : Function.Injective pick := by
    intro A B h
    apply Subtype.ext
    apply hunique A.val (Finset.mem_filter.mp A.property).1
      B.val (Finset.mem_filter.mp B.property).1 (pick A).val
    · exact (Classical.choose_spec (hg A)).2
    · have hval := congrArg (fun j : G.neighborSet i => j.val) h
      change Classical.choose (hg A) = Classical.choose (hg B) at hval
      change partner B.val (Classical.choose (hg A))
      rw [hval]
      exact (Classical.choose_spec (hg B)).2
  have hgood : good.card ≤ G.degree i := by
    simpa only [Fintype.card_coe, SimpleGraph.card_neighborSet_eq_degree] using
      Fintype.card_le_of_injective pick hpick
  have hexceptional : exceptional.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro A hA B hB
    exact hbad A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1
      (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2
  have hcover : faces ⊆ good ∪ exceptional := by
    intro A hA
    by_cases h : bad A <;> simp [good, exceptional, hA, h]
  have hcard := (Finset.card_mono hcover).trans (Finset.card_union_le good exceptional)
  omega

/-- A bounded collection of exceptional incident faces can be counted
separately from the injectively chosen cofacial partner edges. -/
theorem incident_count_le_degree_add_bad
    [Fintype I] (G : SimpleGraph I) [DecidableRel G.Adj]
    (i : I) (faces : Finset F) (bad : F → Prop) (partner : F → I → Prop)
    [DecidablePred bad]
    (b : ℕ) (hbad : (faces.filter bad).card ≤ b)
    (hex : ∀ A ∈ faces, ¬ bad A → ∃ j, G.Adj i j ∧ partner A j)
    (hunique : ∀ A ∈ faces, ∀ B ∈ faces, ∀ j,
      partner A j → partner B j → A = B) :
    faces.card ≤ G.degree i + b := by
  classical
  have hg : (faces.filter fun A => ¬ bad A).card ≤ G.degree i := by
    apply incident_count_le_degree G i (faces.filter fun A => ¬ bad A) partner
    · intro A hA
      exact hex A (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2
    · intro A hA B hB j hjA hjB
      exact hunique A (Finset.mem_filter.mp hA).1 B
        (Finset.mem_filter.mp hB).1 j hjA hjB
  have hsplit := Finset.card_filter_add_card_filter_not (s := faces) bad
  omega

theorem cofacial_degree_lower_bound
    [Fintype I] (G : SimpleGraph I) [DecidableRel G.Adj]
    (d : ℕ) (i : I) (faces : Finset F) (bad : F → Prop) (partner : F → I → Prop)
    (hfaces : d - 1 ≤ faces.card)
    (hbad : ∀ A ∈ faces, ∀ B ∈ faces, bad A → bad B → A = B)
    (hex : ∀ A ∈ faces, ¬ bad A → ∃ j, G.Adj i j ∧ partner A j)
    (hunique : ∀ A ∈ faces, ∀ B ∈ faces, ∀ j,
      partner A j → partner B j → A = B) :
    d - 2 ≤ G.degree i := by
  have h := incident_count_le_degree_add_one G i faces bad partner hbad hex hunique
  omega

theorem family_size_lower_bound
    [Fintype I] (G : SimpleGraph I) [DecidableRel G.Adj]
    (d : ℕ) (hd : 2 ≤ d) (i : I) (hdegree : d - 2 ≤ G.degree i) :
    d - 1 ≤ Fintype.card I := by
  have h := G.degree_lt_card_verts i
  omega

end Papers.Polytopes.CofacialCounting


end
end BundlePart6

section BundlePart7
/- Source: Papers/FaceGraphParity.lean -/
@[expose] public section






/-!
# Crossing parity in a two-regular face graph

The parity argument uses only the finite graph of an actual two-face. It does
not require a choice or a formal construction of its boundary cycle.
-/

namespace Papers.Polytopes.FaceGraphParity

open scoped BigOperators

variable {I : Type*}


/-- In a finite graph, the two-dimensional local edge bound and the ordinary
minimum-degree bound give degree exactly two. -/
theorem degree_two_of_minimum_and_no_three [Fintype I]
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hthree : ∀ v a b c, a ≠ b → a ≠ c → b ≠ c →
      G.Adj v a → G.Adj v b → G.Adj v c → False) :
    ∀ v, G.degree v = 2 := by
  classical
  intro v
  have hcard : 1 < (G.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact lt_of_lt_of_le (by decide : 1 < 2) (hmin v)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  have hsub : G.neighborFinset v ⊆ {a,b} := by
    intro c hc
    by_cases hca : c = a
    · simp [hca]
    by_cases hcb : c = b
    · simp [hcb]
    exact (hthree v a b c hab (Ne.symm hca) (Ne.symm hcb)
      ((G.mem_neighborFinset v a).mp ha)
      ((G.mem_neighborFinset v b).mp hb)
      ((G.mem_neighborFinset v c).mp hc)).elim
  have hup : G.degree v ≤ 2 := by
    have h := Finset.card_mono hsub
    simpa [hab, SimpleGraph.card_neighborFinset_eq_degree] using h
  exact le_antisymm hup (hmin v)


theorem neighbor_eq_of_degree_two [Fintype I]
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (u p q r : I) (hpq : p ≠ q) (hup : G.Adj u p) (huq : G.Adj u q)
    (hdegree : G.degree u = 2) (hur : G.Adj u r) :
    r = p ∨ r = q := by
  classical
  have hsub : ({p,q} : Finset I) ⊆ G.neighborFinset u := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxp | hx
    · rw [hxp]
      exact (G.mem_neighborFinset u p).mpr hup
    · have hxq : x = q := Finset.mem_singleton.mp hx
      subst x
      exact (G.mem_neighborFinset u q).mpr huq
  have heq : ({p,q} : Finset I) = G.neighborFinset u :=
    Finset.eq_of_subset_of_card_le hsub (by
      simp [hpq, SimpleGraph.card_neighborFinset_eq_degree, hdegree])
  have hr := (G.mem_neighborFinset u r).mpr hur
  rw [← heq] at hr
  simpa using hr

/-- Each crossing edge is oriented from the chosen side to its complement. -/
abbrev CutEdge (G : SimpleGraph I) (S : Set I) :=
  {xy : I × I // G.Adj xy.1 xy.2 ∧ xy.1 ∈ S ∧ xy.2 ∉ S}

abbrev OutsideNeighbor (G : SimpleGraph I) (S : Set I) (v : S) :=
  {w : I // G.Adj v.val w ∧ w ∉ S}

def cutEdgeEquivSigma (G : SimpleGraph I) (S : Set I) :
    CutEdge G S ≃ Σ v : S, OutsideNeighbor G S v where
  toFun e := ⟨⟨e.val.1, e.property.2.1⟩,
    ⟨e.val.2, e.property.1, e.property.2.2⟩⟩
  invFun e := ⟨(e.1.val, e.2.val), e.2.property.1,
    e.1.property, e.2.property.2⟩
  left_inv := by rintro ⟨⟨v,w⟩, hvw, hv, hw⟩; rfl
  right_inv := by rintro ⟨⟨v,hv⟩,⟨w,hvw,hw⟩⟩; rfl

noncomputable def neighborSplit (G : SimpleGraph I) (S : Set I) (v : S) :
    G.neighborSet v.val ≃
      ((G.induce S).neighborSet v ⊕ OutsideNeighbor G S v) := by
  classical
  exact
    { toFun := fun w =>
        if hw : w.val ∈ S then Sum.inl ⟨⟨w.val, hw⟩, w.property⟩
        else Sum.inr ⟨w.val, w.property, hw⟩
      invFun := fun w => match w with
        | Sum.inl u => ⟨u.val.val, u.property⟩
        | Sum.inr u => ⟨u.val, u.property.1⟩
      left_inv := by
        rintro ⟨w, hw⟩
        by_cases h : w ∈ S <;> simp [h]
      right_inv := by
        intro w
        cases w with
        | inl u => simp [u.val.property]
        | inr u => simp [u.property.2] }

/-- Splitting the degrees along a cut and using the degree-sum formula on the
induced graph proves that every cut has even cardinality. -/
theorem cut_card_even_of_degree_two [Fintype I]
    (G : SimpleGraph I) [DecidableRel G.Adj] (hdegree : ∀ v, G.degree v = 2) (S : Set I) :
    Nat.card (CutEdge G S) % 2 = 0 := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  have hcut :
      Fintype.card (CutEdge G S) =
        ∑ v : S, Fintype.card (OutsideNeighbor G S v) := by
    calc
      Fintype.card (CutEdge G S) =
          Fintype.card (Σ v : S, OutsideNeighbor G S v) :=
        Fintype.card_congr (cutEdgeEquivSigma G S)
      _ = ∑ v : S, Fintype.card (OutsideNeighbor G S v) := by
        simpa only [Finset.univ_sigma_univ, Finset.card_univ] using
          (Finset.card_sigma (Finset.univ : Finset S)
            (fun v => (Finset.univ : Finset (OutsideNeighbor G S v))))
  have hsplit (v : S) :
      G.degree v.val = (G.induce S).degree v +
        Fintype.card (OutsideNeighbor G S v) := by
    simpa only [Fintype.card_sum, SimpleGraph.card_neighborSet_eq_degree] using
      Fintype.card_congr (neighborSplit G S v)
  have hcount :
      2 * Fintype.card S =
        2 * (G.induce S).edgeFinset.card + Fintype.card (CutEdge G S) := by
    calc
      2 * Fintype.card S = ∑ v : S, G.degree v.val := by
        simp [hdegree, Nat.mul_comm]
      _ = ∑ v : S, ((G.induce S).degree v +
          Fintype.card (OutsideNeighbor G S v)) :=
        Finset.sum_congr rfl (fun v _ => hsplit v)
      _ = 2 * (G.induce S).edgeFinset.card + Fintype.card (CutEdge G S) := by
        rw [Finset.sum_add_distrib, (G.induce S).sum_degrees_eq_twice_card_edges,
          ← hcut]
  rw [Nat.card_eq_fintype_card]
  omega

/-- A nonempty cut in a two-regular finite graph contains another edge. -/
theorem exists_other_cut_edge [Fintype I]
    (G : SimpleGraph I) [DecidableRel G.Adj] (hdegree : ∀ v, G.degree v = 2)
    (S : Set I) (e : CutEdge G S) :
    ∃ f : CutEdge G S, f ≠ e := by
  classical
  have hparity := cut_card_even_of_degree_two G hdegree S
  by_contra h
  have hall : ∀ f : CutEdge G S, f = e := by
    intro f
    by_contra hf
    exact h ⟨f, hf⟩
  have huniv : (Finset.univ : Finset (CutEdge G S)) = {e} := by
    ext f
    simp [hall f]
  have hcard : Nat.card (CutEdge G S) = 1 := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, huniv, Finset.card_singleton]
  omega

/-- If the 01 family consists of one edge, both remaining crossing families
occur. This is the parity step used at a star center or at an interior-edge
center. -/
theorem other_two_families_of_unique_zero_one [Fintype I]
    (G : SimpleGraph I) [DecidableRel G.Adj] (hdegree : ∀ v, G.degree v = 2)
    (color : I → Fin 3) (u v : I)
    (huv : G.Adj u v) (hu : color u = 0) (hv : color v = 1)
    (hunique : ∀ x y, G.Adj x y → color x = 0 → color y = 1 →
      x = u ∧ y = v) :
    (∃ x y, G.Adj x y ∧ color x = 0 ∧ color y = 2) ∧
    (∃ x y, G.Adj x y ∧ color x = 1 ∧ color y = 2) := by
  classical
  have oneCut (a b : I) (ca cb cc : Fin 3)
      (hab : G.Adj a b) (ha : color a = ca) (hb : color b = cb)
      (hbc : cb ≠ ca)
      (hcolors : ∀ z : Fin 3, z ≠ ca → z = cb ∨ z = cc)
      (hsole : ∀ x y, G.Adj x y → color x = ca → color y = cb →
        x = a ∧ y = b) :
      ∃ x y, G.Adj x y ∧ color x = ca ∧ color y = cc := by
    let e : CutEdge G {x | color x = ca} :=
      ⟨(a,b), hab, ha, by simpa [hb] using hbc⟩
    obtain ⟨f, hfe⟩ := exists_other_cut_edge G hdegree {x | color x = ca} e
    have hfc : color f.val.1 = ca := f.property.2.1
    rcases hcolors (color f.val.2) f.property.2.2 with hother | hother
    · obtain ⟨hx, hy⟩ := hsole _ _ f.property.1 hfc hother
      have heq : f = e := Subtype.ext (Prod.ext hx hy)
      exact (hfe heq).elim
    · exact ⟨f.val.1, f.val.2, f.property.1, hfc, hother⟩
  constructor
  · exact oneCut u v 0 1 2 huv hu hv (by decide)
      (by intro z hz; omega) hunique
  · apply oneCut v u 1 0 2 huv.symm hv hu (by decide)
      (by intro z hz; omega)
    intro x y hxy hx hy
    obtain ⟨hyu,hxv⟩ := hunique y x hxy.symm hy hx
    exact ⟨hxv,hyu⟩


/-- At a star center u of the 01 family, a two-face whose other two neighbors
of u have colors 0 and 1 has exactly one 01 edge. -/
theorem star_face_unique_zero_one [Fintype I]
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (hdegree : ∀ v, G.degree v = 2)
    (color : I → Fin 3) (u p q : I)
    (hu : color u = 0) (hp : color p = 0) (hq : color q = 1)
    (hup : G.Adj u p) (huq : G.Adj u q)
    (hstar : ∀ x y, G.Adj x y → color x = 0 → color y = 1 →
      x = u ∨ y = u) :
    ∀ x y, G.Adj x y → color x = 0 → color y = 1 →
      x = u ∧ y = q := by
  intro x y hxy hx hy
  have hpq : p ≠ q := by
    intro h
    have := congrArg color h
    omega
  rcases hstar x y hxy hx hy with hxu | hyu
  · subst x
    rcases neighbor_eq_of_degree_two G u p q y hpq hup huq (hdegree u) hxy with
      hyp | hyq
    · subst y
      omega
    · exact ⟨rfl,hyq⟩
  · subst y
    omega

theorem star_face_contains_other_families [Fintype I]
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (hdegree : ∀ v, G.degree v = 2)
    (color : I → Fin 3) (u p q : I)
    (hu : color u = 0) (hp : color p = 0) (hq : color q = 1)
    (hup : G.Adj u p) (huq : G.Adj u q)
    (hstar : ∀ x y, G.Adj x y → color x = 0 → color y = 1 →
      x = u ∨ y = u) :
    (∃ x y, G.Adj x y ∧ color x = 0 ∧ color y = 2) ∧
    (∃ x y, G.Adj x y ∧ color x = 1 ∧ color y = 2) := by
  exact other_two_families_of_unique_zero_one G hdegree color u q huq hu hq
    (star_face_unique_zero_one G hdegree color u p q hu hp hq hup huq hstar)

end Papers.Polytopes.FaceGraphParity


end
end BundlePart7

section BundlePart8
/- Source: Papers/CrossingLineGeometry.lean -/
@[expose] public section




/-!
# Elementary projective line intersections for crossing families

These results are stated for linear subspaces. Actual homogeneous edge lines
have dimension two and actual vertex points have dimension one.
-/

namespace Papers.Polytopes.CrossingLineGeometry

variable {V I : Type*}
variable [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem intersection_rank_one_of_coplanar_distinct_lines
    (A B : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 2) (hB : Module.finrank ℝ B = 2)
    (hspan : Module.finrank ℝ ↥(A ⊔ B) = 3) :
    Module.finrank ℝ ↥(A ⊓ B) = 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  omega

theorem common_point_of_coplanar_distinct_lines
    (A B : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 2) (hB : Module.finrank ℝ B = 2)
    (hspan : Module.finrank ℝ ↥(A ⊔ B) = 3) :
    ∃ J : Submodule ℝ V, Module.finrank ℝ J = 1 ∧ J ≤ A ∧ J ≤ B :=
  ⟨A ⊓ B, intersection_rank_one_of_coplanar_distinct_lines A B hA hB hspan,
    inf_le_left, inf_le_right⟩

/-- This is the d=3 endpoint of the exterior-family forcing argument: two
cofacial matching edges already determine their projective center. -/
theorem concurrence_of_two_lines
    (L : I → Submodule ℝ V) (i j : I)
    (hcover : ∀ k, k = i ∨ k = j)
    (hi : Module.finrank ℝ (L i) = 2)
    (hj : Module.finrank ℝ (L j) = 2)
    (hspan : Module.finrank ℝ ↥(L i ⊔ L j) = 3) :
    ∃ J : Submodule ℝ V, Module.finrank ℝ J = 1 ∧ ∀ k, J ≤ L k := by
  obtain ⟨J, hJ, hJi, hJj⟩ :=
    common_point_of_coplanar_distinct_lines (L i) (L j) hi hj hspan
  refine ⟨J, hJ, ?_⟩
  intro k
  rcases hcover k with rfl | rfl <;> assumption

theorem intersection_eq_shared_point
    (A B S : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 2) (hB : Module.finrank ℝ B = 2)
    (hspan : Module.finrank ℝ ↥(A ⊔ B) = 3)
    (hS : Module.finrank ℝ S = 1) (hSA : S ≤ A) (hSB : S ≤ B) :
    A ⊓ B = S := by
  have hdim := intersection_rank_one_of_coplanar_distinct_lines A B hA hB hspan
  exact (Submodule.eq_of_le_of_finrank_le (le_inf hSA hSB) (by omega)).symm

/-- Two crossing edges incident to the same actual vertex cannot share a
nonvertex center. Thus each nonvertex-centered crossing family is a matching. -/
theorem common_center_eq_shared_vertex
    (A B S J : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 2) (hB : Module.finrank ℝ B = 2)
    (hspan : Module.finrank ℝ ↥(A ⊔ B) = 3)
    (hS : Module.finrank ℝ S = 1) (hSA : S ≤ A) (hSB : S ≤ B)
    (hJ : Module.finrank ℝ J = 1) (hJA : J ≤ A) (hJB : J ≤ B) :
    J = S := by
  have hle : J ≤ S := by
    rw [← intersection_eq_shared_point A B S hA hB hspan hS hSA hSB]
    exact le_inf hJA hJB
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

theorem no_shared_vertex_at_nonvertex_center
    (A B S J : Submodule ℝ V)
    (hA : Module.finrank ℝ A = 2) (hB : Module.finrank ℝ B = 2)
    (hspan : Module.finrank ℝ ↥(A ⊔ B) = 3)
    (hS : Module.finrank ℝ S = 1) (hSA : S ≤ A) (hSB : S ≤ B)
    (hJ : Module.finrank ℝ J = 1) (hJA : J ≤ A) (hJB : J ≤ B)
    (hnot : J ≠ S) : False :=
  hnot (common_center_eq_shared_vertex A B S J hA hB hspan hS hSA hSB
    hJ hJA hJB)

/-- An edge line not contained in the central subspace meets it exactly at its
specified center. Only the edge line, rather than the whole ambient space,
needs to be two-dimensional. -/
theorem central_intersection_eq_center
    (D L J : Submodule ℝ V)
    (hL : Module.finrank ℝ L = 2) (hJ : Module.finrank ℝ J = 1)
    (hJD : J ≤ D) (hJL : J ≤ L) (hoff : ¬ L ≤ D) :
    D ⊓ L = J := by
  have hupper : Module.finrank ℝ ↥(D ⊓ L) ≤ 1 := by
    by_contra h
    have heq : D ⊓ L = L :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
    apply hoff
    rw [← heq]
    exact inf_le_left
  exact (Submodule.eq_of_le_of_finrank_le (le_inf hJD hJL) (by omega)).symm

theorem sup_eq_plane_of_distinct_points
    (D J K : Submodule ℝ V)
    (hD : Module.finrank ℝ D = 2)
    (hJ : Module.finrank ℝ J = 1) (hK : Module.finrank ℝ K = 1)
    (hJD : J ≤ D) (hKD : K ≤ D) (hne : J ≠ K) :
    J ⊔ K = D := by
  have hlow : 2 ≤ Module.finrank ℝ ↥(J ⊔ K) := by
    by_contra h
    have heqJ : J = J ⊔ K :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have hKJ : K ≤ J := by rw [heqJ]; exact le_sup_right
    have heqK : K = J := Submodule.eq_of_le_of_finrank_le hKJ (by omega)
    exact hne heqK.symm
  exact Submodule.eq_of_le_of_finrank_le (sup_le hJD hKD) (by omega)

/-- One support form separates the second neighbors of two incident actual
edges. A common center must then be their shared vertex point. -/
theorem vertex_mem_center_of_separating_form
    (X Y Z : V) (hX : X ≠ 0) (g : V →ₗ[ℝ] ℝ)
    (hgX : g X = 0) (hgY : g Y = 0) (hgZ : g Z ≠ 0)
    (J : Submodule ℝ V) (hJ : Module.finrank ℝ J = 1)
    (hJXY : J ≤ Submodule.span ℝ ({X, Y} : Set V))
    (hJXZ : J ≤ Submodule.span ℝ ({X, Z} : Set V)) :
    X ∈ J := by
  have hker : Submodule.span ℝ ({X, Y} : Set V) ≤ g.ker := by
    refine Submodule.span_le.mpr ?_
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact hgX
    · rcases Set.mem_singleton_iff.mp hv with rfl
      exact hgY
  have hle : J ≤ Submodule.span ℝ ({X} : Set V) := by
    intro v hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hJXZ hv)
    have hz : g v = 0 := hker (hJXY hv)
    have hb0 : b * g Z = 0 := by
      simpa only [map_add, map_smul, smul_eq_mul, hgX, mul_zero, zero_add, hz]
        using congrArg g hab
    have hb : b = 0 := (mul_eq_zero.mp hb0).resolve_right hgZ
    apply Submodule.mem_span_singleton.mpr
    exact ⟨a, by simpa only [hb, zero_smul, add_zero] using hab⟩
  have hdim : Module.finrank ℝ (Submodule.span ℝ ({X} : Set V)) = 1 :=
    finrank_span_singleton hX
  have heq : J = Submodule.span ℝ ({X} : Set V) :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [heq]
  exact Submodule.mem_span_singleton_self X

/-- Arithmetic for forcing exterior families once a central vertex exists. -/
theorem exterior_family_dense_bound
    (d m r s N : ℕ) (hd : 4 ≤ d) (hr : r + 1 = d)
    (hs : 1 ≤ s) (hcount : 2 * m + r + s ≤ N)
    (hN : N ≤ 4 * d - 5) :
    m < 2 * (d - 2) := by
  omega

theorem exterior_family_three_dimensional_bound
    (m r s N : ℕ) (hr : r = 2) (hs : 1 ≤ s)
    (hcount : 2 * m + r + s ≤ N) (hN : N ≤ 7) :
    m ≤ 2 := by
  omega

end Papers.Polytopes.CrossingLineGeometry


end
end BundlePart8

section BundlePart9
/- Source: Papers/ProjectiveFamilyFaces.lean -/
@[expose] public section





/-!
# Crossing families in a two-face

Distinct rank-one centers in the central projective line span that line.
Consequently, a two-face plane which does not contain the central line can
contain edges of only one crossing family. Degree parity supplies the second
edge of that family.
-/

namespace Papers.Polytopes.ProjectiveFamilyFaces

open Papers.Polytopes.CrossingLineGeometry
open Papers.Polytopes.FaceGraphParity

variable {W I J : Type*} [AddCommGroup W] [Module ℝ W]
  [FiniteDimensional ℝ W]

theorem center_index_unique
    (D H : Submodule ℝ W) (hD : Module.finrank ℝ D = 2)
    (center : J → Submodule ℝ W)
    (hrank : ∀ j, Module.finrank ℝ (center j) = 1)
    (hcentral : ∀ j, center j ≤ D)
    (hinjective : Function.Injective center)
    (hproper : ¬ D ≤ H) {i j : J}
    (hi : center i ≤ H) (hj : center j ≤ H) : i = j := by
  by_contra hne
  have hcenter : center i ≠ center j := fun h => hne (hinjective h)
  have hspan := sup_eq_plane_of_distinct_points D (center i) (center j)
    hD (hrank i) (hrank j) (hcentral i) (hcentral j) hcenter
  apply hproper
  rw [← hspan]
  exact sup_le hi hj

/-- All edges of a two-face whose lines carry one of the fixed centers have
the same center label as a chosen crossing edge, unless its plane contains
the central line. -/
theorem edge_labels_constant
    (D H : Submodule ℝ W) (hD : Module.finrank ℝ D = 2)
    (center : J → Submodule ℝ W)
    (hrank : ∀ j, Module.finrank ℝ (center j) = 1)
    (hcentral : ∀ j, center j ≤ D)
    (hinjective : Function.Injective center)
    (hproper : ¬ D ≤ H)
    (edges : Set I) (label : I → J) (line : I → Submodule ℝ W)
    (hcenterLine : ∀ e ∈ edges, center (label e) ≤ line e)
    (hlinePlane : ∀ e ∈ edges, line e ≤ H)
    (e : I) (he : e ∈ edges) :
    ∀ f ∈ edges, label f = label e := by
  intro f hf
  exact center_index_unique D H hD center hrank hcentral hinjective hproper
    ((hcenterLine f hf).trans (hlinePlane f hf))
    ((hcenterLine e he).trans (hlinePlane e he))

/-- A second crossing edge, oriented from color a to color b, follows from
cut parity as soon as all a-crossings have the prescribed other color. -/
theorem second_crossing_edge
    {V C : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ v, G.degree v = 2) (color : V → C)
    (a b : C) (hab : a ≠ b) (u v : V)
    (huv : G.Adj u v) (hu : color u = a) (hv : color v = b)
    (honly : ∀ x y, G.Adj x y → color x = a →
      color y ≠ a → color y = b) :
    ∃ x y, G.Adj x y ∧ color x = a ∧ color y = b ∧
      (x ≠ u ∨ y ≠ v) := by
  classical
  let e : CutEdge G {x | color x = a} :=
    ⟨(u,v), huv, hu, by simpa [hv] using hab.symm⟩
  obtain ⟨f,hfe⟩ := exists_other_cut_edge G hdegree {x | color x = a} e
  have hx : color f.val.1 = a := f.property.2.1
  have hy : color f.val.2 = b :=
    honly _ _ f.property.1 hx f.property.2.2
  refine ⟨f.val.1, f.val.2, f.property.1, hx, hy, ?_⟩
  by_contra h
  push_neg at h
  apply hfe
  exact Subtype.ext (Prod.ext h.1 h.2)

end Papers.Polytopes.ProjectiveFamilyFaces


end
end BundlePart9

section BundlePart10
/- Source: Papers/TwoFaceCrossingParity.lean -/





@[expose] public section

/-!
# Crossing parity for actual two-faces

All graph data in these statements are constructed from the given convex
polytope. No boundary cycle or graph-degree certificate is an input.
-/

noncomputable section

namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem twoFace_contains_other_families_of_unique_crossing
    (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 2)
    (color : P.vertices → Fin 3) (u v : P.vertices)
    (huF : u.val ∈ F) (hvF : v.val ∈ F)
    (huv : GeneralVertexStep P u.val v.val)
    (hu : color u = 0) (hv : color v = 1)
    (hunique : ∀ x y : P.vertices, x.val ∈ F → y.val ∈ F →
      GeneralVertexStep P x.val y.val → color x = 0 → color y = 1 →
      x = u ∧ y = v) :
    (∃ x y : P.vertices, x.val ∈ F ∧ y.val ∈ F ∧
      GeneralVertexStep P x.val y.val ∧ color x = 0 ∧ color y = 2) ∧
    (∃ x y : P.vertices, x.val ∈ F ∧ y.val ∈ F ∧
      GeneralVertexStep P x.val y.val ∧ color x = 1 ∧ color y = 2) := by
  let G := twoFaceVertexGraph P F
  let c : TwoFaceVertexType P F → Fin 3 := fun x => color x.val
  let u' : TwoFaceVertexType P F := ⟨u,huF⟩
  let v' : TwoFaceVertexType P F := ⟨v,hvF⟩
  have hdegree : ∀ x, G.degree x = 2 :=
    fun x => twoFaceVertexGraph_degree_two P F hF hdim x
  have hsole : ∀ x y, G.Adj x y → c x = 0 → c y = 1 →
      x = u' ∧ y = v' := by
    intro x y hxy hx hy
    obtain ⟨hxu,hyv⟩ := hunique x.val y.val x.property y.property hxy hx hy
    exact ⟨Subtype.ext hxu,Subtype.ext hyv⟩
  obtain ⟨h02,h12⟩ :=
    FaceGraphParity.other_two_families_of_unique_zero_one G hdegree c u' v'
      huv hu hv hsole
  constructor
  · obtain ⟨x,y,hxy,hx,hy⟩ := h02
    exact ⟨x.val,y.val,x.property,y.property,hxy,hx,hy⟩
  · obtain ⟨x,y,hxy,hx,hy⟩ := h12
    exact ⟨x.val,y.val,x.property,y.property,hxy,hx,hy⟩

theorem twoFace_star_contains_other_families
    (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 2)
    (color : P.vertices → Fin 3) (u p q : P.vertices)
    (huF : u.val ∈ F) (hpF : p.val ∈ F) (hqF : q.val ∈ F)
    (hu : color u = 0) (hp : color p = 0) (hq : color q = 1)
    (hup : GeneralVertexStep P u.val p.val)
    (huq : GeneralVertexStep P u.val q.val)
    (hstar : ∀ x y : P.vertices,
      GeneralVertexStep P x.val y.val → color x = 0 → color y = 1 →
      x = u ∨ y = u) :
    (∃ x y : P.vertices, x.val ∈ F ∧ y.val ∈ F ∧
      GeneralVertexStep P x.val y.val ∧ color x = 0 ∧ color y = 2) ∧
    (∃ x y : P.vertices, x.val ∈ F ∧ y.val ∈ F ∧
      GeneralVertexStep P x.val y.val ∧ color x = 1 ∧ color y = 2) := by
  let G := twoFaceVertexGraph P F
  let c : TwoFaceVertexType P F → Fin 3 := fun x => color x.val
  let u' : TwoFaceVertexType P F := ⟨u,huF⟩
  let p' : TwoFaceVertexType P F := ⟨p,hpF⟩
  let q' : TwoFaceVertexType P F := ⟨q,hqF⟩
  have hdegree : ∀ x, G.degree x = 2 :=
    fun x => twoFaceVertexGraph_degree_two P F hF hdim x
  have hstar' : ∀ x y, G.Adj x y → c x = 0 → c y = 1 →
      x = u' ∨ y = u' := by
    intro x y hxy hx hy
    exact (hstar x.val y.val hxy hx hy).imp Subtype.ext Subtype.ext
  obtain ⟨h02,h12⟩ :=
    FaceGraphParity.star_face_contains_other_families G hdegree c u' p' q'
      hu hp hq hup huq hstar'
  constructor
  · obtain ⟨x,y,hxy,hx,hy⟩ := h02
    exact ⟨x.val,y.val,x.property,y.property,hxy,hx,hy⟩
  · obtain ⟨x,y,hxy,hx,hy⟩ := h12
    exact ⟨x.val,y.val,x.property,y.property,hxy,hx,hy⟩

theorem twoFace_contains_second_crossing
    {C : Type*} (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 2)
    (color : P.vertices → C) (a b : C) (hab : a ≠ b)
    (u v : P.vertices) (huF : u.val ∈ F) (hvF : v.val ∈ F)
    (huv : GeneralVertexStep P u.val v.val)
    (hu : color u = a) (hv : color v = b)
    (hfamily : ∀ x y : P.vertices, x.val ∈ F → y.val ∈ F →
      GeneralVertexStep P x.val y.val → color x = a → color y ≠ a → color y = b) :
    ∃ x y : P.vertices, x.val ∈ F ∧ y.val ∈ F ∧
      GeneralVertexStep P x.val y.val ∧ color x = a ∧ color y = b ∧
      (x ≠ u ∨ y ≠ v) := by
  let G := twoFaceVertexGraph P F
  let c : TwoFaceVertexType P F → C := fun x => color x.val
  let u' : TwoFaceVertexType P F := ⟨u,huF⟩
  let v' : TwoFaceVertexType P F := ⟨v,hvF⟩
  have hdegree : ∀ x, G.degree x = 2 :=
    fun x => twoFaceVertexGraph_degree_two P F hF hdim x
  obtain ⟨x,y,hxy,hx,hy,hne⟩ :=
    ProjectiveFamilyFaces.second_crossing_edge G hdegree c a b hab u' v'
      huv hu hv (fun x y hxy hx hy =>
        hfamily x.val y.val x.property y.property hxy hx hy)
  refine ⟨x.val,y.val,x.property,y.property,hxy,hx,hy,?_⟩
  exact hne.imp
    (fun hxu h => hxu (Subtype.ext h))
    (fun hyv h => hyv (Subtype.ext h))

end Papers.Polytopes


end
end
end BundlePart10

section BundlePart11
/- Source: Papers/CofacialGeometry.lean -/







@[expose] public section

/-!
# Cofacial geometry for actual crossing edges

Distinct genuine two-faces have distinct homogeneous planes. Hence there is
at most one exceptional face through an off-central edge, and a partner edge
can occur with that edge in at most one two-face.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open ExposedProjectiveBridge HomogeneousFaceSpans ThreeColorPlanes
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem actual_twoFaces_eq_of_central_line_and_offline_edge
    (P : ConvexPolytope d) (F G : Set (E d))
    (hF : P.IsFace F) (hG : P.IsFace G)
    (hFdim : faceDim F = 2) (hGdim : faceDim G = 2)
    (x y : E d) (hxF : x ∈ F) (hyF : y ∈ F)
    (hxG : x ∈ G) (hyG : y ∈ G)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (hoff : ¬ edgeProjectiveLine x y ≤ D)
    (hDF : D ≤ homogeneousSpan (K := ℝ) F) (hDG : D ≤ homogeneousSpan (K := ℝ) G) :
    F = G := by
  apply actual_faces_eq_of_homogeneousSpan_eq P F G hF hG ⟨x,hxF⟩ ⟨x,hxG⟩
  exact plane_eq_of_contains_central_line_and_offline_edge D
    (edgeProjectiveLine x y) (homogeneousSpan (K := ℝ) F) (homogeneousSpan (K := ℝ) G)
    hD (twoFace_homogeneousSpan_rank F ⟨x,hxF⟩ hFdim)
    (twoFace_homogeneousSpan_rank G ⟨x,hxG⟩ hGdim) hoff hDF hDG
    (line_le_span hxF hyF) (line_le_span hxG hyG)

theorem actual_twoFaces_eq_of_two_lines
    (P : ConvexPolytope d) (F G : Set (E d))
    (hF : P.IsFace F) (hG : P.IsFace G)
    (hFn : F.Nonempty) (hGn : G.Nonempty)
    (hFdim : faceDim F = 2) (hGdim : faceDim G = 2)
    (L M : Submodule ℝ (E d × ℝ))
    (hLM : 3 ≤ finrank ℝ ↥(L ⊔ M))
    (hLF : L ≤ homogeneousSpan (K := ℝ) F) (hLG : L ≤ homogeneousSpan (K := ℝ) G)
    (hMF : M ≤ homogeneousSpan (K := ℝ) F) (hMG : M ≤ homogeneousSpan (K := ℝ) G) :
    F = G := by
  apply actual_faces_eq_of_homogeneousSpan_eq P F G hF hG hFn hGn
  exact plane_eq_of_contains_matching_lines L M
    (homogeneousSpan (K := ℝ) F) (homogeneousSpan (K := ℝ) G)
    (twoFace_homogeneousSpan_rank F hFn hFdim)
    (twoFace_homogeneousSpan_rank G hGn hGdim)
    hLM hLF hLG hMF hMG

/-- This also proves the missing coplanar-triangle implication used by dense
concurrence: if three pairwise cofacial matching lines are coplanar, their
witnessing two-faces coincide. -/
theorem actual_twoFaces_eq_of_lines_in_common_rank_three
    (P : ConvexPolytope d) (F G : Set (E d))
    (hF : P.IsFace F) (hG : P.IsFace G)
    (hFn : F.Nonempty) (hGn : G.Nonempty)
    (hFdim : faceDim F = 2) (hGdim : faceDim G = 2)
    (L M N A : Submodule ℝ (E d × ℝ))
    (hLM : 3 ≤ finrank ℝ ↥(L ⊔ M)) (hLN : 3 ≤ finrank ℝ ↥(L ⊔ N))
    (hLF : L ≤ homogeneousSpan (K := ℝ) F) (hMF : M ≤ homogeneousSpan (K := ℝ) F)
    (hLG : L ≤ homogeneousSpan (K := ℝ) G) (hNG : N ≤ homogeneousSpan (K := ℝ) G)
    (hLA : L ≤ A) (hMA : M ≤ A) (hNA : N ≤ A)
    (hA : finrank ℝ A ≤ 3) :
    F = G := by
  have hFspan : L ⊔ M = homogeneousSpan (K := ℝ) F :=
    Submodule.eq_of_le_of_finrank_le (sup_le hLF hMF)
      (by rw [twoFace_homogeneousSpan_rank F hFn hFdim]; exact hLM)
  have hGspan : L ⊔ N = homogeneousSpan (K := ℝ) G :=
    Submodule.eq_of_le_of_finrank_le (sup_le hLG hNG)
      (by rw [twoFace_homogeneousSpan_rank G hGn hGdim]; exact hLN)
  have hFA : homogeneousSpan (K := ℝ) F ≤ A := by
    rw [← hFspan]
    exact sup_le hLA hMA
  have hGA : homogeneousSpan (K := ℝ) G ≤ A := by
    rw [← hGspan]
    exact sup_le hLA hNA
  have hFeq : homogeneousSpan (K := ℝ) F = A :=
    Submodule.eq_of_le_of_finrank_le hFA
      (by rw [twoFace_homogeneousSpan_rank F hFn hFdim]; exact hA)
  have hGeq : homogeneousSpan (K := ℝ) G = A :=
    Submodule.eq_of_le_of_finrank_le hGA
      (by rw [twoFace_homogeneousSpan_rank G hGn hGdim]; exact hA)
  exact actual_faces_eq_of_homogeneousSpan_eq P F G hF hG hFn hGn (hFeq.trans hGeq.symm)

/-- Canonically oriented actual edges between two fixed colors. -/
def CrossingFamily {C : Type*} (P : ConvexPolytope d)
    (color : P.vertices → C) (a b : C) :=
  {e : P.vertices × P.vertices //
    GeneralVertexStep P e.1.val e.2.val ∧ color e.1 = a ∧ color e.2 = b}

noncomputable instance crossingFamilyFintype {C : Type*} (P : ConvexPolytope d)
    (color : P.vertices → C) (a b : C) : Fintype (CrossingFamily P color a b) := by
  unfold CrossingFamily
  infer_instance

namespace CrossingFamily

variable {C : Type*} {P : ConvexPolytope d} {color : P.vertices → C} {a b : C}

def left (e : CrossingFamily P color a b) : P.vertices := e.val.1
def right (e : CrossingFamily P color a b) : P.vertices := e.val.2

theorem isEdge (e : CrossingFamily P color a b) :
    GeneralVertexStep P e.left.val e.right.val := e.property.1

def line (e : CrossingFamily P color a b) : Submodule ℝ (E d × ℝ) :=
  edgeProjectiveLine e.left.val e.right.val

def liesIn (F : Set (E d)) (e : CrossingFamily P color a b) : Prop :=
  e.left.val ∈ F ∧ e.right.val ∈ F

noncomputable def cofacialGraph : SimpleGraph (CrossingFamily P color a b) where
  Adj e f := e ≠ f ∧ ∃ F : Set (E d), P.IsFace F ∧ faceDim F = 2 ∧
    liesIn F e ∧ liesIn F f
  symm := ⟨by
    rintro e f ⟨hne,F,hF,hdim,he,hf⟩
    exact ⟨hne.symm,F,hF,hdim,hf,he⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

theorem cofacial_degree_from_actual_twoFaces
    (e : CrossingFamily P color a b)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (hoff : ¬ e.line ≤ D)
    (hpair : ∀ f : CrossingFamily P color a b, e ≠ f →
      3 ≤ finrank ℝ ↥(e.line ⊔ f.line))
    (hother : ∀ F : Set (E d), P.IsFace F → faceDim F = 2 →
      liesIn F e → ¬ D ≤ homogeneousSpan (K := ℝ) F →
      ∃ f : CrossingFamily P color a b, e ≠ f ∧ liesIn F f) :
    (incidentTwoFaces P e.left.val e.right.val).card ≤
      (cofacialGraph (P := P) (color := color) (a := a) (b := b)).degree e + 1 := by
  let G := cofacialGraph (P := P) (color := color) (a := a) (b := b)
  let faces := incidentTwoFaces P e.left.val e.right.val
  let bad (F : ActualFaceType P) := D ≤ homogeneousSpan (K := ℝ) F.val
  let partner (F : ActualFaceType P) (f : CrossingFamily P color a b) :=
    e ≠ f ∧ liesIn F.val f
  have hmem (F : ActualFaceType P) (hF : F ∈ faces) :
      faceDim F.val = 2 ∧ liesIn F.val e := by
    exact (Finset.mem_filter.mp hF).2
  apply CofacialCounting.incident_count_le_degree_add_one G e faces bad partner
  · intro F hF H hH hbadF hbadH
    apply Subtype.ext
    exact actual_twoFaces_eq_of_central_line_and_offline_edge P F.val H.val
      F.property H.property (hmem F hF).1 (hmem H hH).1
      e.left.val e.right.val (hmem F hF).2.1 (hmem F hF).2.2
      (hmem H hH).2.1 (hmem H hH).2.2 D hD hoff hbadF hbadH
  · intro F hF hgood
    obtain ⟨f,hef,hfF⟩ := hother F.val F.property (hmem F hF).1 (hmem F hF).2 hgood
    exact ⟨f,⟨hef,F.val,F.property,(hmem F hF).1,(hmem F hF).2,hfF⟩,hef,hfF⟩
  · intro F hF H hH f hfF hfH
    apply Subtype.ext
    exact actual_twoFaces_eq_of_two_lines P F.val H.val F.property H.property
      ⟨e.left.val,(hmem F hF).2.1⟩ ⟨e.left.val,(hmem H hH).2.1⟩
      (hmem F hF).1 (hmem H hH).1 e.line f.line (hpair f hfF.1)
      (line_le_span (hmem F hF).2.1 (hmem F hF).2.2)
      (line_le_span (hmem H hH).2.1 (hmem H hH).2.2)
      (line_le_span hfF.2.1 hfF.2.2) (line_le_span hfH.2.1 hfH.2.2)

theorem second_edge_in_twoFace
    (hab : a ≠ b) (e : CrossingFamily P color a b)
    (F : Set (E d)) (hF : P.IsFace F) (hdim : faceDim F = 2)
    (heF : liesIn F e)
    (hfamily : ∀ x y : P.vertices, x.val ∈ F → y.val ∈ F →
      GeneralVertexStep P x.val y.val → color x = a → color y ≠ a → color y = b) :
    ∃ f : CrossingFamily P color a b, e ≠ f ∧ liesIn F f := by
  obtain ⟨x,y,hxF,hyF,hxy,hx,hy,hne⟩ :=
    twoFace_contains_second_crossing P F hF hdim color a b hab e.left e.right
      heF.1 heF.2 e.isEdge e.property.2.1 e.property.2.2 hfamily
  let f : CrossingFamily P color a b := ⟨(x,y),hxy,hx,hy⟩
  refine ⟨f,?_,hxF,hyF⟩
  intro hef
  have hpair := congrArg (fun z : CrossingFamily P color a b => z.val) hef
  rcases hne with hxne | hyne
  · exact hxne (congrArg Prod.fst hpair).symm
  · exact hyne (congrArg Prod.snd hpair).symm

end CrossingFamily
end Papers.Polytopes


end
end
end BundlePart11

section BundlePart12
/- Source: Papers/CrossingMatchings.lean -/
@[expose] public section




/-!
# Crossing matchings from a nonvertex center

The only support information needed is that an actual edge form vanishes at
exactly its two endpoints among the actual extreme points. A common nonvertex
center then makes both endpoint maps injective.
-/

namespace Papers.Polytopes.ExposedEdgeCenters

variable {V I : Type*} [AddCommGroup V] [Module ℝ V]

theorem right_eq_of_same_left_at_nonvertex_center
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (support : I → V →ᵃ[ℝ] ℝ)
    (hsleft : ∀ i, support i (left i) = 0)
    (hsright : ∀ i, support i (right i) = 0)
    (hszero : ∀ i z, z ∈ C.extremePoints ℝ →
      (support i z = 0 ↔ z = left i ∨ z = right i))
    (J : Submodule ℝ (V × ℝ)) (hJ : Module.finrank ℝ J = 1)
    (hline : ∀ i, J ≤ edgeLine (left i) (right i))
    (hnotvertex : ∀ z ∈ C.extremePoints ℝ, point z ∉ J)
    {i j : I} (hleft : left i = left j) :
    right i = right j := by
  by_contra hright
  have hnonzero : support i (right j) ≠ 0 := by
    intro hzero
    rcases (hszero i (right j) (hr j)).mp hzero with h | h
    · exact hne j ((h.trans hleft).symm)
    · exact hright h.symm
  have hleftzero : support i (left j) = 0 := by
    rw [← hleft]
    exact hsleft i
  have hle : J ≤ Submodule.span ℝ ({point (left i)} : Set (V × ℝ)) := by
    intro w hw
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hline j hw)
    have hzero : affineForm (support i) w = 0 :=
      edgeLine_le_ker_affineForm (support i) (hsleft i) (hsright i) (hline i hw)
    have hcoeff : b * support i (right j) = 0 := by
      have heval := congrArg (affineForm (support i)) hab
      simpa only [map_add, map_smul, affineForm_point, smul_eq_mul,
        hleftzero, mul_zero, zero_add, hzero] using heval
    have hb : b = 0 := (mul_eq_zero.mp hcoeff).resolve_right hnonzero
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    simpa only [hb, zero_smul, add_zero, ← hleft] using hab
  have hdim :
      Module.finrank ℝ (Submodule.span ℝ ({point (left i)} : Set (V × ℝ))) = 1 :=
    finrank_span_singleton (point_ne_zero (left i))
  have heq : J = Submodule.span ℝ ({point (left i)} : Set (V × ℝ)) :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hmem : point (left i) ∈ J := by
    rw [heq]
    exact Submodule.mem_span_singleton_self _
  exact hnotvertex (left i) (hl i) hmem

theorem left_eq_of_same_right_at_nonvertex_center
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (support : I → V →ᵃ[ℝ] ℝ)
    (hsleft : ∀ i, support i (left i) = 0)
    (hsright : ∀ i, support i (right i) = 0)
    (hszero : ∀ i z, z ∈ C.extremePoints ℝ →
      (support i z = 0 ↔ z = left i ∨ z = right i))
    (J : Submodule ℝ (V × ℝ)) (hJ : Module.finrank ℝ J = 1)
    (hline : ∀ i, J ≤ edgeLine (left i) (right i))
    (hnotvertex : ∀ z ∈ C.extremePoints ℝ, point z ∉ J)
    {i j : I} (hright : right i = right j) :
    left i = left j := by
  apply right_eq_of_same_left_at_nonvertex_center C right left hr hl
    (fun i => (hne i).symm) support hsright hsleft
    (fun i z hz => (hszero i z hz).trans or_comm) J hJ
    (fun i => by rw [edgeLine_comm]; exact hline i) hnotvertex hright

/-- The actual matching endpoint data, ready to populate EdgeMatching once
the actual edge proof is attached. -/
theorem endpoint_injections_at_nonvertex_center
    (C : Set V) (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (support : I → V →ᵃ[ℝ] ℝ)
    (hsleft : ∀ i, support i (left i) = 0)
    (hsright : ∀ i, support i (right i) = 0)
    (hszero : ∀ i z, z ∈ C.extremePoints ℝ →
      (support i z = 0 ↔ z = left i ∨ z = right i))
    (J : Submodule ℝ (V × ℝ)) (hJ : Module.finrank ℝ J = 1)
    (hline : ∀ i, J ≤ edgeLine (left i) (right i))
    (hnotvertex : ∀ z ∈ C.extremePoints ℝ, point z ∉ J)
    (hinj : Function.Injective fun i => (left i, right i)) :
    Function.Injective left ∧ Function.Injective right := by
  constructor
  · intro i j h
    apply hinj
    exact Prod.ext h (right_eq_of_same_left_at_nonvertex_center C left right
      hl hr hne support hsleft hsright hszero J hJ hline hnotvertex h)
  · intro i j h
    apply hinj
    exact Prod.ext (left_eq_of_same_right_at_nonvertex_center C left right
      hl hr hne support hsleft hsright hszero J hJ hline hnotvertex h) h

theorem endpoint_pairs_disjoint
    (left right : I → V)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hcross : ∀ i j, left i ≠ right j)
    {i j : I} (hij : i ≠ j) :
    Disjoint ({left i, right i} : Set V) {left j, right j} := by
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzi hzj
  rcases hzi with hzi | hzi <;> rcases hzj with hzj | hzj
  · exact hij (hl (hzi.symm.trans hzj))
  · exact hcross i j (hzi.symm.trans hzj)
  · exact hcross j i (hzj.symm.trans hzi)
  · exact hij (hr (hzi.symm.trans hzj))

end Papers.Polytopes.ExposedEdgeCenters


end
end BundlePart12

section BundlePart13
/- Source: Papers/ThreeColorForestGeometry.lean -/
@[expose] public section











/-!
# The geometric forest argument for three homotheties

The algebra below is independent of a particular coordinate presentation of a
polytope.  The application uses homogeneous vertex vectors, their first
coordinate, and the quotient by the two-dimensional parameter direction space.
The two supporting linear forms come from actual incident exposed edges.

This is proof source awaiting compilation; it is not a verification certificate.
-/

namespace Papers.Polytopes.ThreeColorForest

open scoped BigOperators

variable {V W I : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

/-- The two nonnegative supporting forms of two distinct edges at a vertex. -/
structure TwoEdgeSupports (X Y Z T : V) where
  left : V →ₗ[ℝ] ℝ
  right : V →ₗ[ℝ] ℝ
  left_at_X : left X = 0
  left_at_Y : left Y = 0
  left_at_Z : 0 < left Z
  left_at_T : 0 ≤ left T
  right_at_X : right X = 0
  right_at_Z : right Z = 0
  right_at_Y : 0 < right Y
  right_at_T : 0 ≤ right T

/-- Inside the plane of two actual incident edges, a point of the polytope
cannot lie below both edge directions for a linear functional. -/
theorem height_ge_at_two_edges
    {X Y Z T : V} (S : TwoEdgeSupports X Y Z T)
    (first height : V →ₗ[ℝ] ℝ)
    (hX : first X = 1) (hY : first Y = 1)
    (hZ : first Z = 1) (hT : first T = 1)
    (hspan : T ∈ Submodule.span ℝ ({X, Y, Z} : Set V))
    (hXY : height X ≤ height Y) (hXZ : height X ≤ height Z) :
    height X ≤ height T := by
  obtain ⟨a, b, c, hlin⟩ := Submodule.mem_span_triple.mp hspan
  have hsum : a + b + c = 1 := by
    simpa only [map_add, map_smul, smul_eq_mul, hX, hY, hZ, hT,
      mul_one] using congrArg first hlin
  have hleft : c * S.left Z = S.left T := by
    simpa only [map_add, map_smul, smul_eq_mul, S.left_at_X,
      S.left_at_Y, mul_zero, zero_add] using congrArg S.left hlin
  have hright : b * S.right Y = S.right T := by
    simpa only [map_add, map_smul, smul_eq_mul, S.right_at_X,
      S.right_at_Z, mul_zero, zero_add, add_zero] using congrArg S.right hlin
  have hb : 0 ≤ b := by
    nlinarith [S.right_at_Y, S.right_at_T]
  have hc : 0 ≤ c := by
    nlinarith [S.left_at_Z, S.left_at_T]
  have heval : a * height X + b * height Y + c * height Z = height T := by
    simpa only [map_add, map_smul, smul_eq_mul] using congrArg height hlin
  have ha : a = 1 - b - c := by linarith
  rw [ha] at heval
  nlinarith [mul_nonneg hb (sub_nonneg.mpr hXY),
    mul_nonneg hc (sub_nonneg.mpr hXZ)]

/-- Two independent center directions in the incident edge lines put every
central point in the plane of those two edges. -/
theorem central_mem_span_three_of_two_centers
    (D : Submodule ℝ V) {X Y Z T A B : V}
    (hD : D = Submodule.span ℝ ({A, B} : Set V))
    (hA : A ∈ Submodule.span ℝ ({X, Y} : Set V))
    (hB : B ∈ Submodule.span ℝ ({X, Z} : Set V))
    (hT : T ∈ D) :
    T ∈ Submodule.span ℝ ({X, Y, Z} : Set V) := by
  have hle : D ≤ Submodule.span ℝ ({X, Y, Z} : Set V) := by
    rw [hD]
    refine Submodule.span_le.mpr ?_
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact Submodule.span_mono (by intro u hu; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu ⊢; tauto) hA
    · have hvB : v = B := Set.mem_singleton_iff.mp hv
      subst v
      exact Submodule.span_mono (by intro u hu; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu ⊢; tauto) hB
  exact hle hT

/-- A real vector space has a linear coordinate taking any specified nonzero
vector to one. This elementary proof avoids a topological duality assumption. -/
theorem exists_linear_height_eq_one {v : W} (hv : v ≠ 0) :
    ∃ h : W →ₗ[ℝ] ℝ, h v = 1 := by
  classical
  let B := Module.Basis.ofVectorSpace ℝ W
  have hcoord : ∃ i, B.repr v i ≠ 0 := by
    by_contra! h
    apply hv
    apply B.repr.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨(B.repr v i)⁻¹ • B.coord i, ?_⟩
  change (B.repr v i)⁻¹ * B.repr v i = 1
  exact inv_mul_cancel₀ hi

/-- Exterior intersection with the central plane forces the quotient vectors
at the endpoints to belong to the same positive ray. -/
theorem positive_scalar_of_segment_avoids_kernel
    (q : V →ₗ[ℝ] W) (X Y : V)
    (hdep : ∃ c : ℝ, q Y = c • q X)
    (havoid : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      q (a • X + b • Y) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ q Y = c • q X := by
  obtain ⟨c, hc⟩ := hdep
  refine ⟨c, ?_, hc⟩
  by_contra h
  have hcn : c ≤ 0 := le_of_not_gt h
  have hd : 0 < 1 - c := by linarith
  let a : ℝ := -c / (1 - c)
  let b : ℝ := 1 / (1 - c)
  have ha : 0 ≤ a := div_nonneg (neg_nonneg.mpr hcn) hd.le
  have hb : 0 ≤ b := div_nonneg zero_le_one hd.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [ne_of_gt hd] <;> ring
  apply havoid a b ha hb hab
  rw [map_add, map_smul, map_smul, hc, smul_smul, ← add_smul]
  have hz : a + b * c = 0 := by
    dsimp [a, b]
    field_simp [ne_of_gt hd] <;> ring
  rw [hz, zero_smul]

/-- Positive proportionality propagates along actual graph paths. -/
theorem positive_ray_of_reachable (G : SimpleGraph I) (x : I → W)
    (hedge : ∀ {i j}, G.Adj i j →
      ∃ c : ℝ, 0 < c ∧ x j = c • x i)
    {i j : I} (hij : G.Reachable i j) :
    ∃ c : ℝ, 0 < c ∧ x j = c • x i := by
  obtain ⟨p⟩ := hij
  induction p with
  | nil => exact ⟨1, zero_lt_one, by simp⟩
  | @cons u v w h p ih =>
      obtain ⟨a, ha, hxa⟩ := hedge h
      obtain ⟨b, hb, hxb⟩ := ih
      refine ⟨b * a, mul_pos hb ha, ?_⟩
      rw [hxb, hxa, smul_smul]

/-- A component of exterior crossing edges admits a positive quotient height. -/
theorem positive_height_on_component
    (G : SimpleGraph I) (X : I → V) (T : V)
    (q : V →ₗ[ℝ] W) (hT : q T = 0)
    (hq : ∀ i, q (X i) ≠ 0)
    (hedge : ∀ {i j}, G.Adj i j →
      ∃ c : ℝ, 0 < c ∧ q (X j) = c • q (X i))
    (i : I) :
    ∃ h : V →ₗ[ℝ] ℝ, h T = 0 ∧
      ∀ j, G.Reachable i j → 0 < h (X j) := by
  obtain ⟨l, hl⟩ := exists_linear_height_eq_one (hq i)
  refine ⟨l.comp q, by simp [hT], ?_⟩
  intro j hij
  obtain ⟨c, hc, hcx⟩ := positive_ray_of_reachable G (fun k => q (X k)) hedge hij
  change 0 < l (q (X j))
  rw [hcx, map_smul, hl, smul_eq_mul, mul_one]
  exact hc

/-- The minimum-height proof of the forest claim.  It uses two edge supports,
not a planar Jordan curve theorem or an assumption about sections being faces. -/
theorem isAcyclic_of_component_heights
    (G : SimpleGraph I) (X : I → V) (T : V)
    (first : V →ₗ[ℝ] ℝ)
    (hfirst : ∀ i, first (X i) = 1) (hTfirst : first T = 1)
    (hlocal : ∀ x y z, G.Adj x y → G.Adj x z → y ≠ z →
      T ∈ Submodule.span ℝ ({X x, X y, X z} : Set V) ∧
      Nonempty (TwoEdgeSupports (X x) (X y) (X z) T))
    (hheight : ∀ i, ∃ h : V →ₗ[ℝ] ℝ, h T = 0 ∧
      ∀ j, G.Reachable i j → 0 < h (X j)) :
    G.IsAcyclic := by
  classical
  intro u p hp
  obtain ⟨height, hT, hpositive⟩ := hheight u
  have hs : p.support.toFinset.Nonempty :=
    ⟨u, List.mem_toFinset.mpr p.start_mem_support⟩
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image p.support.toFinset (fun i => height (X i)) hs
  have hx' : x ∈ p.support := List.mem_toFinset.mp hx
  let c := p.rotate x hx'
  have hc : c.IsCycle := by
    simpa only [c, SimpleGraph.Walk.isCycle_rotate] using hp
  have hys : c.snd ∈ p.support := by
    apply (p.mem_support_rotate_iff x hx').mp
    exact c.getVert_mem_support 1
  have hzs : c.penultimate ∈ p.support := by
    apply (p.mem_support_rotate_iff x hx').mp
    exact c.getVert_mem_support (c.length - 1)
  obtain ⟨hspan, ⟨S⟩⟩ := hlocal x c.snd c.penultimate
    (c.adj_snd hc.not_nil) (c.adj_penultimate hc.not_nil).symm
    hc.snd_ne_penultimate
  have hge := height_ge_at_two_edges S first height
    (hfirst x) (hfirst c.snd) (hfirst c.penultimate) hTfirst hspan
    (hmin c.snd (List.mem_toFinset.mpr hys))
    (hmin c.penultimate (List.mem_toFinset.mpr hzs))
  have hxpos : 0 < height (X x) :=
    hpositive x (p.takeUntil x hx').reachable
  linarith

/-- Complete linear-geometric forest criterion used for the noncentral
crossing graph in the three-homothety argument. -/
theorem isAcyclic_of_positive_ray_quotient
    (G : SimpleGraph I) (X : I → V) (T : V)
    (first : V →ₗ[ℝ] ℝ)
    (hfirst : ∀ i, first (X i) = 1) (hTfirst : first T = 1)
    (q : V →ₗ[ℝ] W) (hT : q T = 0)
    (hq : ∀ i, q (X i) ≠ 0)
    (hedge : ∀ {i j}, G.Adj i j →
      ∃ c : ℝ, 0 < c ∧ q (X j) = c • q (X i))
    (hlocal : ∀ x y z, G.Adj x y → G.Adj x z → y ≠ z →
      T ∈ Submodule.span ℝ ({X x, X y, X z} : Set V) ∧
      Nonempty (TwoEdgeSupports (X x) (X y) (X z) T)) :
    G.IsAcyclic := by
  apply isAcyclic_of_component_heights G X T first hfirst hTfirst hlocal
  exact positive_height_on_component G X T q hT hq hedge

end Papers.Polytopes.ThreeColorForest


end
end BundlePart13

section BundlePart14
/- Source: Papers/ThreeColorNoTripleConcurrence.lean -/
@[expose] public section






/-!
# Three supporting lines in a polygon have no common projective point

The determinant positivity is supplied by SupportFormIndependence.  The
argument takes place in the three-dimensional homogeneous span of the
two-face, so no coordinate chart or polar polytope is required.
-/

namespace Papers.Polytopes.ThreeColorSupport

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem joint_kernel_eq_zero_of_three_independent
    [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 3)
    (f : Fin 3 → V →ₗ[ℝ] ℝ) (hf : LinearIndependent ℝ f)
    {z : V} (hz : ∀ i, f i z = 0) :
    z = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace ℝ V
  have hdual : Module.finrank ℝ (V →ₗ[ℝ] ℝ) = 3 :=
    (LinearEquiv.finrank_eq B.toDualEquiv.symm).trans hdim
  have htop : Submodule.span ℝ (Set.range f) = ⊤ :=
    hf.span_eq_top_of_card_eq_finrank (by simpa using hdual.symm)
  let evaluation : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun l => l z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hspan : Submodule.span ℝ (Set.range f) ≤ evaluation.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hz i
  have hall : ∀ l : V →ₗ[ℝ] ℝ, l z = 0 := by
    intro l
    exact hspan (by rw [htop]; trivial)
  by_contra hzne
  obtain ⟨l, hl⟩ :=
    Papers.Polytopes.ThreeColorForest.exists_linear_height_eq_one hzne
  have hzero := hall l
  linarith

theorem joint_kernel_eq_zero_of_support_evaluations
    [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 3)
    (f : Fin 3 → V →ₗ[ℝ] ℝ) (p : Fin 3 → V)
    (hzero : ∀ i, f i (p i) = 0)
    (hpositive : ∀ i j, i ≠ j → 0 < f j (p i))
    {z : V} (hz : ∀ i, f i z = 0) :
    z = 0 := by
  exact joint_kernel_eq_zero_of_three_independent hdim f
    (Papers.RationalityTen.three_linearForms_independent_of_evaluations
      f p hzero hpositive) hz

/-- In the actual two-face application, H is its homogeneous span, the three
L_i are supporting edge lines, and p_i are relative-interior edge points. -/
theorem no_common_projective_center
    (H : Submodule ℝ V) [FiniteDimensional ℝ H]
    (hH : Module.finrank ℝ H = 3)
    (L : Fin 3 → Submodule ℝ V) (hLH : ∀ i, L i ≤ H)
    (f : Fin 3 → H →ₗ[ℝ] ℝ) (p : Fin 3 → H)
    (hzero : ∀ i, f i (p i) = 0)
    (hpositive : ∀ i j, i ≠ j → 0 < f j (p i))
    (hvanish : ∀ i z (hz : z ∈ L i), f i ⟨z, hLH i hz⟩ = 0)
    (J : Submodule ℝ V) (hJ : ∀ i, J ≤ L i)
    (hdimJ : Module.finrank ℝ J = 1) :
    False := by
  have hbot : J = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro z hz
    let zH : H := ⟨z, hLH 0 (hJ 0 hz)⟩
    have hzH : zH = 0 := by
      apply joint_kernel_eq_zero_of_support_evaluations hH f p hzero hpositive
      intro i
      exact hvanish i z (hJ i hz)
    have hz0 : z = 0 := congrArg Subtype.val hzH
    simpa [hz0]
  rw [hbot] at hdimJ
  simp at hdimJ

end Papers.Polytopes.ThreeColorSupport


end
end BundlePart14

section BundlePart15
/- Source: Papers/ExposedMatchingConcurrence.lean -/
@[expose] public section




/-!
# Three matching exposed edges cannot concur in a two-face

For matching edges, one endpoint of each edge already gives the strictly
positive off-diagonal support evaluations. No relative-interior construction,
polygon parametrization, or polar duality is required.
-/

namespace Papers.Polytopes.ExposedMatchingConcurrence

open Papers.Polytopes.ExposedEdgeCenters
open Papers.Polytopes.ThreeColorSupport

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V]

theorem three_matching_exposed_edges_not_concurrent
    (C : Set V) (left right : Fin 3 → V)
    (hleft : ∀ i, left i ∈ C.extremePoints ℝ)
    (hright : ∀ i, right i ∈ C.extremePoints ℝ)
    (hdisjoint : ∀ i j, i ≠ j →
      left i ≠ left j ∧ left i ≠ right j)
    (support : Fin 3 → V →ᵃ[ℝ] ℝ)
    (hnonneg : ∀ i x, x ∈ C → 0 ≤ support i x)
    (hzero : ∀ i, ∀ x ∈ C,
      support i x = 0 ↔ x ∈ segment ℝ (left i) (right i))
    (H : Submodule ℝ (V × ℝ)) (hH : Module.finrank ℝ H = 3)
    (hlineH : ∀ i, edgeLine (left i) (right i) ≤ H)
    (J : Submodule ℝ (V × ℝ)) (hJ : Module.finrank ℝ J = 1)
    (hJline : ∀ i, J ≤ edgeLine (left i) (right i)) :
    False := by
  have hlzero (i : Fin 3) : support i (left i) = 0 :=
    (hzero i (left i) (hleft i).1).mpr (left_mem_segment ℝ _ _)
  have hrzero (i : Fin 3) : support i (right i) = 0 :=
    (hzero i (right i) (hright i).1).mpr (right_mem_segment ℝ _ _)
  have hpositive (i j : Fin 3) (hij : i ≠ j) :
      0 < support j (left i) := by
    have hn : support j (left i) ≠ 0 := by
      intro hz
      have hz' := (support_zero_iff_endpoint C (support j)
        (hleft j).1 (hright j).1 (hlzero j) (hrzero j)
        (hzero j) (hleft i)).mp hz
      rcases hz' with h | h
      · exact (hdisjoint i j hij).1 h
      · exact (hdisjoint i j hij).2 h
    exact lt_of_le_of_ne (hnonneg j (left i) (hleft i).1) hn.symm
  let f : Fin 3 → H →ₗ[ℝ] ℝ :=
    fun i => (affineForm (support i)).comp H.subtype
  let p : Fin 3 → H :=
    fun i => ⟨point (left i), hlineH i (Submodule.subset_span (by simp))⟩
  refine no_common_projective_center H hH
    (fun i => edgeLine (left i) (right i)) hlineH f p ?_ ?_ ?_ J hJline hJ
  · intro i
    simpa [f,p] using hlzero i
  · intro i j hij
    simpa [f,p] using hpositive i j hij
  · intro i z hz
    exact edgeLine_le_ker_affineForm (support i) (hlzero i) (hrzero i) hz

end Papers.Polytopes.ExposedMatchingConcurrence


end
end BundlePart15

section BundlePart16
/- Source: Papers/ActualCrossingGeometry.lean -/






@[expose] public section

/-!
# Actual crossing families are matchings at nonvertex centers

All support forms and extreme-point facts are constructed from P. The same
construction supplies the joint-line rank and the prohibition of three
concurrent matching edges in a genuine two-face.
-/

noncomputable section
namespace Papers.Polytopes.CrossingFamily

open Set Module Papers.Coordinates
open Papers.Polytopes.ExposedEdgeCenters
open Papers.Polytopes.ExposedLineRanks
open Papers.Polytopes.ExposedProjectiveBridge
open Papers.Polytopes.HomogeneousFaceSpans
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {C : Type*}
variable {P : ConvexPolytope d} {color : P.vertices → C} {a b : C}

def support (e : CrossingFamily P color a b) : E d →ᵃ[ℝ] ℝ :=
  Classical.choose (exists_nonnegative_affine_edge_form P e.left.property e.isEdge)

theorem support_nonnegative (e : CrossingFamily P color a b)
    (x : E d) (hx : x ∈ P.toSet) : 0 ≤ e.support x :=
  (Classical.choose_spec
    (exists_nonnegative_affine_edge_form P e.left.property e.isEdge)).1 x hx

theorem support_zero_iff_segment (e : CrossingFamily P color a b)
    (x : E d) (hx : x ∈ P.toSet) :
    e.support x = 0 ↔ x ∈ segment ℝ e.left.val e.right.val :=
  (Classical.choose_spec
    (exists_nonnegative_affine_edge_form P e.left.property e.isEdge)).2 x hx

theorem support_left (e : CrossingFamily P color a b) : e.support e.left.val = 0 :=
  (e.support_zero_iff_segment e.left.val
    (vertex_mem_body_of_mem_vertices P e.left.property)).mpr (left_mem_segment ℝ _ _)

theorem support_right (e : CrossingFamily P color a b) : e.support e.right.val = 0 :=
  (e.support_zero_iff_segment e.right.val
    (vertex_mem_body_of_mem_vertices P e.right.property)).mpr (right_mem_segment ℝ _ _)

theorem left_ne_right_of_different_colors (hab : a ≠ b)
    (e f : CrossingFamily P color a b) : e.left.val ≠ f.right.val := by
  intro h
  have hsub : e.left = f.right := Subtype.ext h
  have hc := congrArg color hsub
  exact hab (e.property.2.1.symm.trans (hc.trans f.property.2.2))

theorem endpointPair_injective :
    Function.Injective (fun e : CrossingFamily P color a b => (e.left.val,e.right.val)) := by
  intro e f h
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

theorem line_finrank_eq_two (e : CrossingFamily P color a b) :
    finrank ℝ e.line = 2 := by
  rw [line, ← exposed_edgeLine_eq_edgeProjectiveLine]
  exact edgeLine_finrank_eq_two e.isEdge.2.1

theorem pair_line_rank_ge_three (hab : a ≠ b)
    (e f : CrossingFamily P color a b) (hef : e ≠ f) :
    3 ≤ finrank ℝ ↥(e.line ⊔ f.line) := by
  have hfleft := vertex_mem_body_of_mem_vertices P f.left.property
  have hfright := vertex_mem_body_of_mem_vertices P f.right.property
  by_cases hl : e.left.val = f.left.val
  · have hr : e.right.val ≠ f.right.val := by
      intro hr
      exact hef (endpointPair_injective (Prod.ext hl hr))
    have hcross : e.right.val ≠ f.left.val :=
      (left_ne_right_of_different_colors hab f e).symm
    have h := matching_lines_joint_rank_ge_three (y := e.left.val) P.toSet f.support
      (vertex_mem_body_extremePoints P e.right.property) hfleft hfright
      f.isEdge.2.1 f.support_left f.support_right f.support_zero_iff_segment hcross hr
    rw [edgeLine_comm e.right.val e.left.val] at h
    rw [exposed_edgeLine_eq_edgeProjectiveLine,exposed_edgeLine_eq_edgeProjectiveLine] at h
    exact h
  · have hcross := left_ne_right_of_different_colors hab e f
    have h := matching_lines_joint_rank_ge_three (y := e.right.val) P.toSet f.support
      (vertex_mem_body_extremePoints P e.left.property) hfleft hfright
      f.isEdge.2.1 f.support_left f.support_right f.support_zero_iff_segment hl hcross
    rw [exposed_edgeLine_eq_edgeProjectiveLine,exposed_edgeLine_eq_edgeProjectiveLine] at h
    exact h

theorem endpoint_injections_of_nonvertex_center
    (J : Submodule ℝ (E d × ℝ)) (hJ : finrank ℝ J = 1)
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J) :
    Function.Injective (fun e : CrossingFamily P color a b => e.left.val) ∧
      Function.Injective (fun e : CrossingFamily P color a b => e.right.val) := by
  refine endpoint_injections_at_nonvertex_center P.toSet
    (fun e : CrossingFamily P color a b => e.left.val)
    (fun e : CrossingFamily P color a b => e.right.val)
    (fun e => vertex_mem_body_extremePoints P e.left.property)
    (fun e => vertex_mem_body_extremePoints P e.right.property)
    (fun e => e.isEdge.2.1) support support_left support_right ?_ J hJ ?_ ?_
    endpointPair_injective
  · intro e x hx
    exact support_zero_iff_endpoint P.toSet e.support
      (vertex_mem_body_of_mem_vertices P e.left.property)
      (vertex_mem_body_of_mem_vertices P e.right.property)
      e.support_left e.support_right e.support_zero_iff_segment hx
  · intro e
    rw [exposed_edgeLine_eq_edgeProjectiveLine]
    exact hcenter e
  · intro x hx
    have hxV : x ∈ P.vertices := by
      change x ∈ (P.vertices : Set (E d))
      rw [P.vertices_eq_extremePoints]
      exact hx
    exact hnotvertex x hxV

theorem endpoint_pairs_disjoint_of_nonvertex_center
    (hab : a ≠ b) (J : Submodule ℝ (E d × ℝ)) (hJ : finrank ℝ J = 1)
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J)
    (e f : CrossingFamily P color a b) (hef : e ≠ f) :
    Disjoint ({e.left.val,e.right.val} : Set (E d)) {f.left.val,f.right.val} := by
  obtain ⟨hl,hr⟩ := endpoint_injections_of_nonvertex_center J hJ hcenter hnotvertex
  exact endpoint_pairs_disjoint
    (fun e : CrossingFamily P color a b => e.left.val)
    (fun e : CrossingFamily P color a b => e.right.val)
    hl hr (left_ne_right_of_different_colors hab) hef

theorem no_three_in_actual_twoFace
    (hab : a ≠ b) (J : Submodule ℝ (E d × ℝ)) (hJ : finrank ℝ J = 1)
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J)
    (F : Set (E d)) (hF : P.IsFace F) (hdim : faceDim F = 2)
    (e : Fin 3 → CrossingFamily P color a b) (hinj : Function.Injective e)
    (hlies : ∀ i, liesIn F (e i)) : False := by
  obtain ⟨hl,hr⟩ := endpoint_injections_of_nonvertex_center J hJ hcenter hnotvertex
  refine ExposedMatchingConcurrence.three_matching_exposed_edges_not_concurrent
    P.toSet (fun i => (e i).left.val) (fun i => (e i).right.val)
    (fun i => vertex_mem_body_extremePoints P (e i).left.property)
    (fun i => vertex_mem_body_extremePoints P (e i).right.property) ?_
    (fun i => (e i).support)
    (fun i x hx => (e i).support_nonnegative x hx)
    (fun i x hx => (e i).support_zero_iff_segment x hx)
    (homogeneousSpan (K := ℝ) F) (twoFace_homogeneousSpan_rank F hF.2 hdim) ?_ J hJ ?_
  · intro i j hij
    constructor
    · intro h
      exact hij (hinj (hl h))
    · exact left_ne_right_of_different_colors hab (e i) (e j)
  · intro i
    rw [exposed_edgeLine_eq_edgeProjectiveLine]
    exact line_le_span (hlies i).1 (hlies i).2
  · intro i
    rw [exposed_edgeLine_eq_edgeProjectiveLine]
    exact hcenter (e i)

end Papers.Polytopes.CrossingFamily


end
end
end BundlePart16

section BundlePart17
/- Source: Papers/DenseGraphClosure.lean -/
@[expose] public section




/-!
# A dense graph has no proper multi-vertex set seen at most once from outside

This is the finite counting step in projective concurrence. It applies to
any finite simple graph and does not assume triangle connectivity.
-/

namespace Papers.Polytopes.DenseGraphClosure

open Papers.Polytopes.FaceGraphParity
open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem eq_univ_of_outside_neighbors_unique
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (k : ℕ) (hdegree : ∀ i, k ≤ G.degree i)
    (hdense : Fintype.card I < 2 * k)
    (S : Set I) (hS : 2 ≤ Nat.card S)
    (hunique : ∀ v ∉ S, ∀ x ∈ S, ∀ y ∈ S,
      G.Adj v x → G.Adj v y → x = y) :
    S = Set.univ := by
  classical
  have hS' : 2 ≤ Fintype.card S := by
    simpa only [Nat.card_eq_fintype_card] using hS
  have hpartition : Fintype.card S + Fintype.card ↥(Sᶜ) = Fintype.card I := by
    have hle : Fintype.card S ≤ Fintype.card I :=
      Fintype.card_le_of_injective (fun x : S => x.val) Subtype.val_injective
    have hc := Fintype.card_subtype_compl (fun x : I => x ∈ S)
    change Fintype.card ↥(Sᶜ) = Fintype.card I - Fintype.card S at hc
    simp only [← Nat.card_eq_fintype_card] at *
    omega
  have hsplit (T : Set I) (v : T) :
      G.degree v.val = (G.induce T).degree v +
        Fintype.card (OutsideNeighbor G T v) := by
    simpa only [Fintype.card_sum,SimpleGraph.card_neighborSet_eq_degree] using
      Fintype.card_congr (neighborSplit G T v)
  apply Set.eq_univ_of_forall
  intro v
  by_contra hv
  let vv : ↥(Sᶜ) := ⟨v,hv⟩
  have houtside : Fintype.card (OutsideNeighbor G Sᶜ vv) ≤ 1 := by
    apply Fintype.card_le_one_iff_subsingleton.mpr
    refine ⟨?_⟩
    intro x y
    apply Subtype.ext
    have hxS : x.val ∈ S := by simpa only [Set.mem_compl_iff,not_not] using x.property.2
    have hyS : y.val ∈ S := by simpa only [Set.mem_compl_iff,not_not] using y.property.2
    exact hunique v hv x.val hxS y.val hyS x.property.1 y.property.1
  have hdegcomp := (G.induce Sᶜ).degree_lt_card_verts vv
  have hsplitcomp : G.degree v = (G.induce Sᶜ).degree vv +
      Fintype.card (OutsideNeighbor G Sᶜ vv) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card,vv] using hsplit Sᶜ vv
  have hkcomp : k ≤ Fintype.card ↥(Sᶜ) := by
    have hk := hdegree v
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at *
    omega
  have hsmall : Fintype.card S < k := by omega
  let outMap : CutEdge G S → ↥(Sᶜ) :=
    fun e => ⟨e.val.2,e.property.2.2⟩
  have houtMap : Function.Injective outMap := by
    intro e f hef
    have heq : e.val.2 = f.val.2 := congrArg Subtype.val hef
    have hleft : e.val.1 = f.val.1 := by
      apply hunique e.val.2 e.property.2.2 e.val.1 e.property.2.1 f.val.1 f.property.2.1
      · exact e.property.1.symm
      · rw [heq]
        exact f.property.1.symm
    exact Subtype.ext (Prod.ext hleft heq)
  have hupper : Fintype.card (CutEdge G S) ≤ Fintype.card ↥(Sᶜ) :=
    Fintype.card_le_of_injective outMap houtMap
  have hcut :
      Fintype.card (CutEdge G S) =
        ∑ v : S, Fintype.card (OutsideNeighbor G S v) := by
    calc
      Fintype.card (CutEdge G S) =
          Fintype.card (Σ v : S, OutsideNeighbor G S v) :=
        Fintype.card_congr (cutEdgeEquivSigma G S)
      _ = ∑ v : S, Fintype.card (OutsideNeighbor G S v) := by
        simpa only [Finset.univ_sigma_univ,Finset.card_univ] using
          (Finset.card_sigma (Finset.univ : Finset S)
            (fun v => (Finset.univ : Finset (OutsideNeighbor G S v))))
  have hlower_each (w : S) :
      k + 1 - Fintype.card S ≤ Fintype.card (OutsideNeighbor G S w) := by
    have hinner := (G.induce S).degree_lt_card_verts w
    have hsp := hsplit S w
    have hk := hdegree w.val
    omega
  have hlower :
      Fintype.card S * (k + 1 - Fintype.card S) ≤ Fintype.card (CutEdge G S) := by
    rw [hcut]
    calc
      Fintype.card S * (k + 1 - Fintype.card S) =
          ∑ _w : S, (k + 1 - Fintype.card S) := by simp
      _ ≤ ∑ w : S, Fintype.card (OutsideNeighbor G S w) :=
        Finset.sum_le_sum (fun w _ => hlower_each w)
  let m := k - Fintype.card S
  have hm : 0 < m := by omega
  have hkm : k = Fintype.card S + m := by omega
  have hsub : k + 1 - Fintype.card S = m + 1 := by omega
  rw [hsub] at hlower
  have hproduct : 2 * m ≤ Fintype.card S * m :=
    Nat.mul_le_mul_right m hS'
  nlinarith

end Papers.Polytopes.DenseGraphClosure


end
end BundlePart17

section BundlePart18
/- Source: Papers/TwoLineConcurrence.lean -/
@[expose] public section




/-! The two-line endpoint needed for three-dimensional crossing families. -/

namespace Papers.Polytopes.TwoLineConcurrence

open Papers.Polytopes.CrossingLineGeometry

variable {I V : Type*} [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V]

theorem pair_exhaustion_of_degree_one
    [Fintype I] (G : SimpleGraph I) [DecidableRel G.Adj]
    (i : I) (hdegree : 1 ≤ G.degree i) (hcard : Fintype.card I ≤ 2) :
    ∃ j, G.Adj i j ∧ ∀ k, k = i ∨ k = j := by
  classical
  have hnonempty : (G.neighborFinset i).Nonempty := by
    apply Finset.card_pos.mp
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨j,hj⟩ := hnonempty
  have hij : G.Adj i j := (G.mem_neighborFinset i j).mp hj
  have heq : ({i,j} : Finset I) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
      simpa [hij.ne] using hcard)
  refine ⟨j,hij,?_⟩
  intro k
  have hk : k ∈ ({i,j} : Finset I) := by rw [heq]; exact Finset.mem_univ k
  simpa using hk

theorem concurrent_of_two_vertices_and_degree
    [Fintype I] [Nonempty I]
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (L : I → Submodule ℝ V)
    (hline : ∀ i, Module.finrank ℝ (L i) = 2)
    (hpair : ∀ i j, i ≠ j → 3 ≤ Module.finrank ℝ ↥(L i ⊔ L j))
    (hcofacial : ∀ i j, G.Adj i j → Module.finrank ℝ ↥(L i ⊔ L j) ≤ 3)
    (hdegree : ∀ i, 1 ≤ G.degree i)
    (hcard : Fintype.card I ≤ 2) :
    ∃ J : Submodule ℝ V, Module.finrank ℝ J = 1 ∧ ∀ i, J ≤ L i := by
  classical
  let i : I := Classical.choice inferInstance
  obtain ⟨j,hij,hcover⟩ := pair_exhaustion_of_degree_one G i (hdegree i) hcard
  have hspan : Module.finrank ℝ ↥(L i ⊔ L j) = 3 :=
    le_antisymm (hcofacial i j hij) (hpair i j hij.ne)
  exact concurrence_of_two_lines L i j hcover (hline i) (hline j) hspan

end Papers.Polytopes.TwoLineConcurrence


end
end BundlePart18

section BundlePart19
/- Source: Papers/CanonicalFamilyConcurrence.lean -/





@[expose] public section

/-!
# Concurrence of a dense actual crossing family

The proof uses the canonical crossing-family type and its actual cofacial
graph. It needs no auxiliary EdgeMatching record. The no-three property is
a statement about genuine two-faces and is transported combinatorially.
-/

noncomputable section
namespace Papers.Polytopes.CrossingFamily

open Set Module Papers.Coordinates
open ExposedProjectiveBridge HomogeneousFaceSpans CrossingLineGeometry
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {C : Type*}
variable {P : ConvexPolytope d} {color : P.vertices → C} {a b : C}

theorem cofacial_pair_span_le_three
    (e f : CrossingFamily P color a b)
    (h : (cofacialGraph (P := P) (color := color) (a := a) (b := b)).Adj e f) :
    finrank ℝ ↥(e.line ⊔ f.line) ≤ 3 := by
  obtain ⟨hef,F,hF,hdim,heF,hfF⟩ := h
  have hle : e.line ⊔ f.line ≤ homogeneousSpan F :=
    sup_le (line_le_span heF.1 heF.2) (line_le_span hfF.1 hfF.2)
  have hr := Submodule.finrank_mono hle
  rwa [twoFace_homogeneousSpan_rank F hF.2 hdim] at hr

theorem concurrent_of_dense_actual_cofacial_graph
    (hab : a ≠ b) (k : ℕ) (hk : 1 ≤ k)
    (hdegree : ∀ e : CrossingFamily P color a b,
      k ≤ (cofacialGraph (P := P) (color := color) (a := a) (b := b)).degree e)
    (hdense : Fintype.card (CrossingFamily P color a b) < 2 * k)
    (hno3 : ∀ F : Set (E d), P.IsFace F → faceDim F = 2 →
      ∀ t : Fin 3 → CrossingFamily P color a b, Function.Injective t →
        (∀ i, liesIn F (t i)) → False)
    (e : CrossingFamily P color a b) :
    ∃ J : Submodule ℝ (E d × ℝ), finrank ℝ J = 1 ∧
      ∀ f : CrossingFamily P color a b, J ≤ f.line := by
  let I := CrossingFamily P color a b
  let G := cofacialGraph (P := P) (color := color) (a := a) (b := b)
  have hn : (G.neighborFinset e).Nonempty := by
    apply Finset.card_pos.mp
    have h : k≤G.degree e := hdegree e
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
      (show 0 < G.degree e by omega)
  obtain ⟨f,hf⟩ := hn
  have hef : G.Adj e f := (G.mem_neighborFinset e f).mp hf
  have hspan : finrank ℝ ↥(e.line ⊔ f.line) = 3 :=
    le_antisymm (cofacial_pair_span_le_three e f hef)
      (pair_line_rank_ge_three hab e f hef.1)
  obtain ⟨J,hJ,hJe,hJf⟩ := common_point_of_coplanar_distinct_lines
    e.line f.line e.line_finrank_eq_two f.line_finrank_eq_two hspan
  let S : Set I := {i | J ≤ i.line}
  have hS : 2 ≤ Nat.card S := by
    let se : S := ⟨e,hJe⟩
    let sf : S := ⟨f,hJf⟩
    have hne : se ≠ sf := fun h => hef.1 (congrArg Subtype.val h)
    have hc := Finset.card_mono (Finset.subset_univ ({se,sf} : Finset S))
    have hc2 : ({se,sf} : Finset S).card=2 := by simp [hne]
    rw [hc2,Finset.card_univ] at hc
    simpa only [Nat.card_eq_fintype_card] using hc
  have hclosed : ∀ v ∉ S, ∀ x ∈ S, ∀ y ∈ S,
      G.Adj v x → G.Adj v y → x = y := by
    intro v hv x hx y hy hvx hvy
    by_contra hxy
    obtain ⟨hvxne,F,hF,hFdim,hvF,hxF⟩ := hvx
    obtain ⟨hvyne,H,hH,hHdim,hvH,hyH⟩ := hvy
    have hlow : 3 ≤ finrank ℝ ↥(v.line ⊔ J) := by
      by_contra h
      have heq : v.line = v.line ⊔ J :=
        Submodule.eq_of_le_of_finrank_le le_sup_left
          (by have hd := v.line_finrank_eq_two; omega)
      apply hv
      change J ≤ v.line
      rw [heq]
      exact le_sup_right
    have hJF : J ≤ homogeneousSpan F :=
      hx.trans (line_le_span hxF.1 hxF.2)
    have hJH : J ≤ homogeneousSpan H :=
      hy.trans (line_le_span hyH.1 hyH.2)
    have hFH : F = H :=
      actual_twoFaces_eq_of_two_lines P F H hF hH hF.2 hH.2 hFdim hHdim
        v.line J hlow (line_le_span hvF.1 hvF.2) (line_le_span hvH.1 hvH.2) hJF hJH
    have hyF : liesIn F y := by rw [hFH]; exact hyH
    let t : Fin 3 → I := ![v,x,y]
    have hinj : Function.Injective t := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [t]
    apply hno3 F hF hFdim t hinj
    intro i
    fin_cases i
    · exact hvF
    · exact hxF
    · exact hyF
  have heqS : S = Set.univ :=
    DenseGraphClosure.eq_univ_of_outside_neighbors_unique G k hdegree hdense S hS hclosed
  refine ⟨J,hJ,?_⟩
  intro i
  have hi : i ∈ S := by rw [heqS]; trivial
  exact hi

theorem concurrent_of_at_most_two_actual_edges
    (hab : a ≠ b)
    (hdegree : ∀ e : CrossingFamily P color a b,
      1 ≤ (cofacialGraph (P := P) (color := color) (a := a) (b := b)).degree e)
    (hcard : Fintype.card (CrossingFamily P color a b) ≤ 2)
    (e : CrossingFamily P color a b) :
    ∃ J : Submodule ℝ (E d × ℝ), finrank ℝ J = 1 ∧
      ∀ f : CrossingFamily P color a b, J ≤ f.line := by
  letI : Nonempty (CrossingFamily P color a b) := ⟨e⟩
  exact TwoLineConcurrence.concurrent_of_two_vertices_and_degree
    (cofacialGraph (P := P) (color := color) (a := a) (b := b))
    (fun e => e.line) line_finrank_eq_two (pair_line_rank_ge_three hab)
    cofacial_pair_span_le_three hdegree hcard

end Papers.Polytopes.CrossingFamily


end
end
end BundlePart19

section BundlePart20
/- Source: Papers/CrossingFamilyTransport.lean -/





@[expose] public section

/-!
# Crossing families under a genuine face-order isomorphism

Colors are pulled through the vertex equivalence extracted from the face
order.  All edges, two-faces, incidences, cardinalities, and cofacial
degrees are transported without assuming a geometric realization of the
original projective centers.
-/

noncomputable section
namespace Papers.Polytopes.CrossingFamilyTransport

open Set Module
open Papers.ActualFaceOrder
open Papers.Polytopes
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {n m : ℕ} {C : Type*}
variable {P : ConvexPolytope n} {Q : ConvexPolytope m}

def colorAlong (e : FaceObject P ≃o FaceObject Q) (color : P.vertices → C) :
    Q.vertices → C :=
  fun v => color ((vertexEquiv e).symm v)

def crossingEquiv (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C) :
    CrossingFamily P color a b ≃ CrossingFamily Q (colorAlong e color) a b where
  toFun f := ⟨(vertexEquiv e f.left,vertexEquiv e f.right),by
    refine ⟨edge_forward e f.left f.right f.isEdge,?_,?_⟩
    · simpa only [colorAlong,Equiv.symm_apply_apply,CrossingFamily.left] using f.property.2.1
    · simpa only [colorAlong,Equiv.symm_apply_apply,CrossingFamily.right] using f.property.2.2⟩
  invFun f := ⟨((vertexEquiv e).symm f.left,(vertexEquiv e).symm f.right),by
    refine ⟨?_,f.property.2.1,f.property.2.2⟩
    apply (edge_iff e _ _).mp
    simpa only [Equiv.apply_symm_apply] using f.isEdge⟩
  left_inv f := by
    apply Subtype.ext
    exact Prod.ext ((vertexEquiv e).symm_apply_apply f.left)
      ((vertexEquiv e).symm_apply_apply f.right)
  right_inv f := by
    apply Subtype.ext
    exact Prod.ext ((vertexEquiv e).apply_symm_apply f.left)
      ((vertexEquiv e).apply_symm_apply f.right)

@[simp] theorem crossingEquiv_left (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C) (f : CrossingFamily P color a b) :
    (crossingEquiv e color a b f).left = vertexEquiv e f.left := rfl

@[simp] theorem crossingEquiv_right (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C) (f : CrossingFamily P color a b) :
    (crossingEquiv e color a b f).right = vertexEquiv e f.right := rfl

@[simp] theorem crossingEquiv_symm_left (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C)
    (f : CrossingFamily Q (colorAlong e color) a b) :
    ((crossingEquiv e color a b).symm f).left =
      (vertexEquiv e).symm f.left := rfl

@[simp] theorem crossingEquiv_symm_right (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C)
    (f : CrossingFamily Q (colorAlong e color) a b) :
    ((crossingEquiv e color a b).symm f).right =
      (vertexEquiv e).symm f.right := rfl

theorem liesIn_image_iff (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C) (F : FaceObject P)
    (f : CrossingFamily P color a b) :
    CrossingFamily.liesIn (e F).val (crossingEquiv e color a b f) ↔
      CrossingFamily.liesIn F.val f :=
  and_congr (vertex_mem_face_iff e f.left F) (vertex_mem_face_iff e f.right F)

theorem cofacial_iff (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C) (f g : CrossingFamily P color a b) :
    (CrossingFamily.cofacialGraph (P := Q) (color := colorAlong e color)
      (a := a) (b := b)).Adj
        (crossingEquiv e color a b f) (crossingEquiv e color a b g) ↔
    (CrossingFamily.cofacialGraph (P := P) (color := color)
      (a := a) (b := b)).Adj f g := by
  constructor
  · rintro ⟨hfg,F,hF,hFdim,hfF,hgF⟩
    let FF : FaceObject Q := ⟨F,hF⟩
    let GG := e.symm FF
    refine ⟨fun heq => hfg (congrArg (crossingEquiv e color a b) heq),
      GG.val,GG.property,?_,?_,?_⟩
    · exact (faceDim_image e.symm FF).trans hFdim
    · apply (liesIn_image_iff e color a b GG f).mp
      simpa only [GG,e.apply_symm_apply] using hfF
    · apply (liesIn_image_iff e color a b GG g).mp
      simpa only [GG,e.apply_symm_apply] using hgF
  · rintro ⟨hfg,F,hF,hFdim,hfF,hgF⟩
    let FF : FaceObject P := ⟨F,hF⟩
    refine ⟨fun heq => hfg ((crossingEquiv e color a b).injective heq),
      (e FF).val,(e FF).property,?_,
      (liesIn_image_iff e color a b FF f).mpr hfF,
      (liesIn_image_iff e color a b FF g).mpr hgF⟩
    exact (faceDim_image e FF).trans hFdim

def cofacialIso (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C) :
    CrossingFamily.cofacialGraph (P := P) (color := color) (a := a) (b := b) ≃g
      CrossingFamily.cofacialGraph (P := Q) (color := colorAlong e color)
        (a := a) (b := b) where
  toEquiv := crossingEquiv e color a b
  map_rel_iff' := by intro f g; exact cofacial_iff e color a b f g

theorem family_card_eq (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C) :
    Fintype.card (CrossingFamily P color a b) =
      Fintype.card (CrossingFamily Q (colorAlong e color) a b) :=
  Fintype.card_congr (crossingEquiv e color a b)

theorem degree_eq (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C) (f : CrossingFamily P color a b) :
    (CrossingFamily.cofacialGraph (P := Q) (color := colorAlong e color)
      (a := a) (b := b)).degree (crossingEquiv e color a b f) =
    (CrossingFamily.cofacialGraph (P := P) (color := color)
      (a := a) (b := b)).degree f :=
  (cofacialIso e color a b).degree_eq f

theorem minimum_degree_transport (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C) (k : ℕ)
    (h : ∀ f : CrossingFamily P color a b,
      k ≤ (CrossingFamily.cofacialGraph (P := P) (color := color)
        (a := a) (b := b)).degree f) :
    ∀ f : CrossingFamily Q (colorAlong e color) a b,
      k ≤ (CrossingFamily.cofacialGraph (P := Q) (color := colorAlong e color)
        (a := a) (b := b)).degree f := by
  intro f
  obtain ⟨g,rfl⟩ := (crossingEquiv e color a b).surjective f
  rw [degree_eq]
  exact h g

theorem no_three_transport (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C)
    (h : ∀ F : Set (E n), P.IsFace F → faceDim F = 2 →
      ∀ t : Fin 3 → CrossingFamily P color a b, Function.Injective t →
        (∀ i, CrossingFamily.liesIn F (t i)) → False) :
    ∀ F : Set (E m), Q.IsFace F → faceDim F = 2 →
      ∀ t : Fin 3 → CrossingFamily Q (colorAlong e color) a b, Function.Injective t →
        (∀ i, CrossingFamily.liesIn F (t i)) → False := by
  intro F hF hdim t hinj ht
  let FF : FaceObject Q := ⟨F,hF⟩
  let GG := e.symm FF
  let u : Fin 3 → CrossingFamily P color a b :=
    fun i => (crossingEquiv e color a b).symm (t i)
  have hu : Function.Injective u :=
    (crossingEquiv e color a b).symm.injective.comp hinj
  apply h GG.val GG.property ((faceDim_image e.symm FF).trans hdim) u hu
  intro i
  apply (liesIn_image_iff e color a b GG (u i)).mp
  simpa only [GG,u,e.apply_symm_apply,Equiv.apply_symm_apply] using ht i

theorem left_injective_transport (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C)
    (h : Function.Injective (fun f : CrossingFamily P color a b => f.left)) :
    Function.Injective
      (fun f : CrossingFamily Q (colorAlong e color) a b => f.left) := by
  intro f g hfg
  apply (crossingEquiv e color a b).symm.injective
  apply h
  change (vertexEquiv e).symm f.left = (vertexEquiv e).symm g.left
  exact congrArg (vertexEquiv e).symm hfg

theorem right_injective_transport (e : FaceObject P ≃o FaceObject Q)
    (color : P.vertices → C) (a b : C)
    (h : Function.Injective (fun f : CrossingFamily P color a b => f.right)) :
    Function.Injective
      (fun f : CrossingFamily Q (colorAlong e color) a b => f.right) := by
  intro f g hfg
  apply (crossingEquiv e color a b).symm.injective
  apply h
  change (vertexEquiv e).symm f.right = (vertexEquiv e).symm g.right
  exact congrArg (vertexEquiv e).symm hfg

end Papers.Polytopes.CrossingFamilyTransport

end
end
end BundlePart20

section BundlePart21
/- Source: Papers/TwoColorReconstruction.lean -/





@[expose] public section

/-!
# Reconstructing two homotheties from a projective center

The center is a nonzero vector in the genuine homogeneous line of every
edge crossing the two color classes.  Finite and infinite centers are
handled by the same formula.  Each color contains two distinct actual
vertices, which proves that the resulting parallel map is nontrivial.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem edgeProjectiveLine_coefficients {x y : E d} {q : E d × ℝ}
    (hq : q ∈ edgeProjectiveLine x y) :
    ∃ a b : ℝ, a • x + b • y = q.1 ∧ a + b = q.2 := by
  rw [edgeProjectiveLine, homogeneousSpan, Set.image_pair,
    Submodule.mem_span_pair] at hq
  obtain ⟨a, b, hab⟩ := hq
  refine ⟨a, b, ?_, ?_⟩
  · simpa [homogenize] using congrArg Prod.fst hab
  · simpa [homogenize] using congrArg Prod.snd hab

def twoColorCenterMap (color : E d → Bool) (q : E d × ℝ) (x : E d) : E d :=
  if color x then (-q.2) • x + q.1 else 0

theorem twoColorCenterMap_parallel (P : ConvexPolytope d)
    (color : E d → Bool) (q : E d × ℝ)
    (hcenter : ∀ x ∈ P.vertices, ∀ y,
      GeneralVertexStep P x y → color x ≠ color y →
      q ∈ edgeProjectiveLine x y) :
    IsParallelMap P (twoColorCenterMap color q) := by
  intro x hx y hy hxy
  by_cases hcx : color x = true <;> by_cases hcy : color y = true
  · refine ⟨-q.2, ?_⟩
    simp only [twoColorCenterMap, hcx, hcy, Bool.true_eq, ↓reduceIte]
    module
  · have hcy' : color y = false := Bool.eq_false_iff.mpr hcy
    obtain ⟨a, b, hqv, hqs⟩ :=
      edgeProjectiveLine_coefficients (hcenter x hx y hxy (by rw [hcx, hcy']; decide))
    refine ⟨-b, ?_⟩
    simp only [twoColorCenterMap, hcx, hcy', Bool.true_eq, ↓reduceIte]
    ext i
    change (0:ℝ)-(-q.2*x i+q.1 i)=(-b)*(y i-x i)
    have hvi : a*x i+b*y i=q.1 i := congrArg (fun z : E d => z i) hqv
    rw [← hvi,← hqs]
    ring
  · have hcx' : color x = false := Bool.eq_false_iff.mpr hcx
    obtain ⟨a, b, hqv, hqs⟩ :=
      edgeProjectiveLine_coefficients (hcenter x hx y hxy (by rw [hcx', hcy]; decide))
    refine ⟨-a, ?_⟩
    simp only [twoColorCenterMap, hcx', hcy, Bool.true_eq, ↓reduceIte]
    ext i
    change (-q.2*y i+q.1 i)-(0:ℝ)=(-a)*(y i-x i)
    have hvi : a*x i+b*y i=q.1 i := congrArg (fun z : E d => z i) hqv
    rw [← hvi,← hqs]
    ring
  · refine ⟨0, ?_⟩
    simp [twoColorCenterMap, hcx, hcy]

theorem twoColorCenterMap_nontrivial (P : ConvexPolytope d)
    (color : E d → Bool) (q : E d × ℝ) (hq : q ≠ 0)
    (hfalse : ∃ u ∈ P.vertices, ∃ v ∈ P.vertices,
      u ≠ v ∧ color u = false ∧ color v = false)
    (htrue : ∃ u ∈ P.vertices, ∃ v ∈ P.vertices,
      u ≠ v ∧ color u = true ∧ color v = true) :
    ¬ IsHomothetyOnVertices P (twoColorCenterMap color q) := by
  obtain ⟨u, hu, v, hv, huv, hcu, hcv⟩ := hfalse
  obtain ⟨x, hx, y, hy, hxy, hcx, hcy⟩ := htrue
  rintro ⟨a, b, hab⟩
  have hu' : a • u + b = (0 : ℝ) • u + 0 := by
    simpa [twoColorCenterMap, hcu] using (hab u hu).symm
  have hv' : a • v + b = (0 : ℝ) • v + 0 := by
    simpa [twoColorCenterMap, hcv] using (hab v hv).symm
  have ha0 : a = 0 ∧ b = 0 := homothety_parameters_unique huv hu' hv'
  rcases ha0 with ⟨rfl, rfl⟩
  have hx' : (-q.2) • x + q.1 = (0 : ℝ) • x + 0 := by
    simpa [twoColorCenterMap, hcx] using hab x hx
  have hy' : (-q.2) • y + q.1 = (0 : ℝ) • y + 0 := by
    simpa [twoColorCenterMap, hcy] using hab y hy
  obtain ⟨hs, hz⟩ := homothety_parameters_unique hxy hx' hy'
  apply hq
  exact Prod.ext hz (neg_eq_zero.mp hs)

theorem decomposable_of_two_color_projective_center (P : ConvexPolytope d)
    (color : E d → Bool) (q : E d × ℝ) (hq : q ≠ 0)
    (hfalse : ∃ u ∈ P.vertices, ∃ v ∈ P.vertices,
      u ≠ v ∧ color u = false ∧ color v = false)
    (htrue : ∃ u ∈ P.vertices, ∃ v ∈ P.vertices,
      u ≠ v ∧ color u = true ∧ color v = true)
    (hcenter : ∀ x ∈ P.vertices, ∀ y,
      GeneralVertexStep P x y → color x ≠ color y →
      q ∈ edgeProjectiveLine x y) :
    MinkowskiDecomposable P := by
  apply (minkowski_decomposable_iff_parallel_map P).mpr
  exact ⟨twoColorCenterMap color q,
    twoColorCenterMap_parallel P color q hcenter,
    twoColorCenterMap_nontrivial P color q hq hfalse htrue⟩

end Papers.Polytopes

end
end
end BundlePart21

section BundlePart22
/- Source: Papers/HomothetyCenterReconstruction.lean -/



@[expose] public section

/-!
# Parallel maps from compatible homothety centers

This is the algebraic reconstruction step.  The projective incidence
hypotheses refer to spans of actual endpoints, and no assumptions about
coordinates of a later realization are built into the definition.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

def homothetyLabelMap (label : E d → I) (p : I → ℝ × E d) (x : E d) : E d :=
  (p (label x)).1 • x + (p (label x)).2

def differenceCenterVector (a b : ℝ × E d) : E d × ℝ :=
  (-(b.2 - a.2), b.1 - a.1)

theorem homothetyLabelMap_parallel (P : ConvexPolytope d)
    (label : E d → I) (p : I → ℝ × E d)
    (hcenters : ∀ x ∈ P.vertices, ∀ y, GeneralVertexStep P x y →
      label x ≠ label y →
      differenceCenterVector (p (label x)) (p (label y)) ∈ edgeProjectiveLine x y) :
    IsParallelMap P (homothetyLabelMap label p) := by
  intro x hx y hy hxy
  by_cases hlabel : label x = label y
  · refine ⟨(p (label x)).1, ?_⟩
    simp only [homothetyLabelMap, ← hlabel]
    module
  · obtain ⟨a, b, hv, hs⟩ :=
      edgeProjectiveLine_coefficients (hcenters x hx y hxy hlabel)
    change a • x + b • y = -((p (label y)).2 - (p (label x)).2) at hv
    change a + b = (p (label y)).1 - (p (label x)).1 at hs
    have hb : (p (label y)).2 - (p (label x)).2 = -(a • x + b • y) := by
      rw [hv]
      simp
    refine ⟨(p (label x)).1 + a, ?_⟩
    calc
      homothetyLabelMap label p y - homothetyLabelMap label p x =
          (p (label x)).1 • (y - x) +
          ((p (label y)).1 - (p (label x)).1) • y +
          ((p (label y)).2 - (p (label x)).2) := by
        unfold homothetyLabelMap
        module
      _ = ((p (label x)).1 + a) • (y - x) := by
        rw [← hs, hb]
        module

theorem homothetyLabelMap_nontrivial (P : ConvexPolytope d)
    (label : E d → I) (p : I → ℝ × E d)
    (hclasses : ∀ i : I, ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      x ≠ y ∧ label x = i ∧ label y = i)
    (hdistinct : ∃ i j, p i ≠ p j) :
    ¬ IsHomothetyOnVertices P (homothetyLabelMap label p) := by
  rintro ⟨a, b, hab⟩
  have heq (i : I) : p i = (a, b) := by
    obtain ⟨x, hx, y, hy, hxy, hix, hiy⟩ := hclasses i
    have hx' : (p i).1 • x + (p i).2 = a • x + b := by
      simpa only [homothetyLabelMap, hix] using hab x hx
    have hy' : (p i).1 • y + (p i).2 = a • y + b := by
      simpa only [homothetyLabelMap, hiy] using hab y hy
    obtain ⟨ha, hb⟩ := homothety_parameters_unique hxy hx' hy'
    exact Prod.ext ha hb
  obtain ⟨i, j, hij⟩ := hdistinct
  exact hij ((heq i).trans (heq j).symm)

theorem decomposable_of_compatible_homothety_centers (P : ConvexPolytope d)
    (label : E d → I) (p : I → ℝ × E d)
    (hclasses : ∀ i : I, ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      x ≠ y ∧ label x = i ∧ label y = i)
    (hdistinct : ∃ i j, p i ≠ p j)
    (hcenters : ∀ x ∈ P.vertices, ∀ y, GeneralVertexStep P x y →
      label x ≠ label y →
      differenceCenterVector (p (label x)) (p (label y)) ∈ edgeProjectiveLine x y) :
    MinkowskiDecomposable P :=
  (minkowski_decomposable_iff_parallel_map P).mpr
    ⟨homothetyLabelMap label p, homothetyLabelMap_parallel P label p hcenters,
      homothetyLabelMap_nontrivial P label p hclasses hdistinct⟩

def centerParameters (q : E d × ℝ) : ℝ × E d := (q.2, -q.1)

theorem centerParameters_injective :
    Function.Injective (centerParameters : (E d × ℝ) → ℝ × E d) := by
  intro q r h
  exact Prod.ext (neg_injective (congrArg Prod.snd h)) (congrArg Prod.fst h)

theorem differenceCenterVector_centerParameters (q r : E d × ℝ) :
    differenceCenterVector (centerParameters q) (centerParameters r) = r - q := by
  apply Prod.ext
  · change -(-r.1- -q.1)=r.1-q.1
    abel
  · rfl

end Papers.Polytopes

end
end
end BundlePart22

section BundlePart23
/- Source: Papers/ProjectiveLineNormalization.lean -/







@[expose] public section

/-!
# A projective line cut by a supporting hyperplane

Normalizing two homogeneous points by a linear form makes their
difference span the intersection of their line with the form's kernel.
This gives the compatible-center construction without an appeal to
Desargues' theorem.
-/

namespace Papers.ProjectiveNormalization
open Submodule

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

def normalize (ell : W →ₗ[K] K) (x : W) : W := (ell x)⁻¹ • x

theorem normalize_apply (ell : W →ₗ[K] K) {x : W} (hx : ell x ≠ 0) :
    ell (normalize ell x) = 1 := by
  simp [normalize, hx]

theorem pair_span_inf_kernel (ell : W →ₗ[K] K) {x y : W}
    (hx : ell x ≠ 0) (hy : ell y ≠ 0) :
    span K ({x, y} : Set W) ⊓ LinearMap.ker ell =
      K ∙ (normalize ell x - normalize ell y) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a, b, hab⟩ := mem_span_pair.mp hz.1
    have hcoeff : a * ell x + b * ell y = 0 := by
      have he := congrArg ell hab
      simpa only [map_add, map_smul, smul_eq_mul, LinearMap.mem_ker.mp hz.2] using he
    have ha : (a * ell x) * (ell x)⁻¹ = a := by
      field_simp
    have hb : -((a * ell x) * (ell y)⁻¹) = b := by
      have hdiv : b = -(a * ell x) / ell y := by
        apply (eq_div_iff hy).mpr
        linear_combination hcoeff
      simpa only [div_eq_mul_inv, neg_mul] using hdiv.symm
    apply mem_span_singleton.mpr
    refine ⟨a * ell x, ?_⟩
    calc
      (a * ell x) • (normalize ell x - normalize ell y) =
          a • x + b • y := by
        rw [normalize,normalize,smul_sub,smul_smul,smul_smul,ha]
        rw [sub_eq_add_neg,← neg_smul,hb]
      _ = z := hab
  · apply (span_singleton_le_iff_mem _ _).mpr
    constructor
    · exact Submodule.sub_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · change ell (normalize ell x-normalize ell y)=0
      rw [map_sub,normalize_apply ell hx,normalize_apply ell hy,sub_self]

theorem normalized_difference_mem_center [FiniteDimensional K W]
    (ell : W →ₗ[K] K) {x y : W}
    (hx : ell x ≠ 0) (hy : ell y ≠ 0)
    (J : Submodule K W) (hdim : Module.finrank K J = 1)
    (hline : J ≤ span K ({x, y} : Set W))
    (hzero : J ≤ LinearMap.ker ell) :
    normalize ell x - normalize ell y ∈ J := by
  let v := normalize ell x - normalize ell y
  by_cases hv : v = 0
  · change v ∈ J
    simpa only [hv] using J.zero_mem
  have hsub : J ≤ K ∙ v := by
    rw [show K ∙ v = span K ({x, y} : Set W) ⊓ LinearMap.ker ell from
      (pair_span_inf_kernel ell hx hy).symm]
    exact le_inf hline hzero
  have hdim' : Module.finrank K (K ∙ v) = 1 := finrank_span_singleton hv
  have heq : J = K ∙ v :=
    Submodule.eq_of_le_of_finrank_eq hsub (hdim.trans hdim'.symm)
  change v ∈ J
  rw [heq]
  exact Submodule.subset_span (by simp)

end Papers.ProjectiveNormalization

end
end BundlePart23

section BundlePart24
/- Source: Papers/SupportingCenterReconstruction.lean -/





@[expose] public section

/-!
# Simplex reconstruction using a supporting form

A support form vanishing on the first simplex face is nonzero at every
vertex of the disjoint second face.  Normalize the latter homogeneous
vertices by this form.  Their differences lie at the forced centers,
providing compatible homothety parameters directly.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module Papers.Coordinates Papers.ProjectiveNormalization
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

def supportHomogeneousForm (g : E d →ᵃ[ℝ] ℝ) : (E d × ℝ) →ₗ[ℝ] ℝ :=
  g.linear.comp (LinearMap.fst ℝ (E d) ℝ) +
    (g 0) • (LinearMap.snd ℝ (E d) ℝ)

theorem supportHomogeneousForm_homogenize (g : E d →ᵃ[ℝ] ℝ) (x : E d) :
    supportHomogeneousForm g (homogenize x) = g x := by
  simp only [supportHomogeneousForm, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.smul_apply, LinearMap.snd_apply,
    homogenize, smul_eq_mul, mul_one]
  exact (affine_form_apply g x).symm

theorem line_le_support_kernel (g : E d →ᵃ[ℝ] ℝ) {x y : E d}
    (hx : g x = 0) (hy : g y = 0) :
    edgeProjectiveLine x y ≤ LinearMap.ker (supportHomogeneousForm g) := by
  rw [edgeProjectiveLine, homogeneousSpan, Set.image_pair]
  apply Submodule.span_le.mpr
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · change supportHomogeneousForm g (homogenize x)=0
    rwa [supportHomogeneousForm_homogenize]
  · have he : z = homogenize y := Set.mem_singleton_iff.mp hz
    subst z
    change supportHomogeneousForm g (homogenize y)=0
    rwa [supportHomogeneousForm_homogenize]

theorem normalize_homogenize_injective (ell : (E d × ℝ) →ₗ[ℝ] ℝ)
    {x y : E d} (hx : ell (homogenize x) ≠ 0) (hy : ell (homogenize y) ≠ 0)
    (h : ProjectiveNormalization.normalize ell (homogenize x) = ProjectiveNormalization.normalize ell (homogenize y)) : x = y := by
  have hs := congrArg Prod.snd h
  have he : ell (homogenize x) = ell (homogenize y) := by
    apply inv_injective
    simpa [ProjectiveNormalization.normalize, homogenize] using hs
  have hv := congrArg (fun z : E d × ℝ => ell (homogenize x) • z) h
  have hh : homogenize (K := ℝ) x = homogenize (K := ℝ) y := by
    simpa only [ProjectiveNormalization.normalize, ← he, smul_smul, mul_inv_cancel₀ hx, one_smul] using hv
  exact congrArg Prod.fst hh

theorem decomposable_of_supporting_center_data
    (P : ConvexPolytope d) (label : E d → I)
    (g : E d →ᵃ[ℝ] ℝ) (A B : I → E d)
    (J : I → I → Submodule ℝ (E d × ℝ))
    (hA : ∀ i, g (A i) = 0)
    (hB : ∀ i, 0 < g (B i))
    (hlabelB : ∀ i, label (B i) = i)
    (hclasses : ∀ i : I, ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      x ≠ y ∧ label x = i ∧ label y = i)
    (hI : ∃ i j : I, i ≠ j)
    (hdim : ∀ i j, i ≠ j → finrank ℝ (J i j) = 1)
    (hfirst : ∀ i j, i ≠ j → J i j ≤ edgeProjectiveLine (A i) (A j))
    (hsecond : ∀ i j, i ≠ j → J i j ≤ edgeProjectiveLine (B i) (B j))
    (hcross : ∀ x ∈ P.vertices, ∀ y, GeneralVertexStep P x y →
      label x ≠ label y → J (label x) (label y) ≤ edgeProjectiveLine x y) :
    MinkowskiDecomposable P := by
  let ell := supportHomogeneousForm g
  let q : I → E d × ℝ := fun i => ProjectiveNormalization.normalize ell (homogenize (B i))
  let p : I → ℝ × E d := fun i => ((q i).2, -(q i).1)
  have hn (i : I) : ell (homogenize (B i)) ≠ 0 := by
    rw [show ell = supportHomogeneousForm g from rfl,
      supportHomogeneousForm_homogenize]
    exact ne_of_gt (hB i)
  have hdiff (i j : I) (hij : i ≠ j) : q i - q j ∈ J i j := by
    apply normalized_difference_mem_center ell (hn i) (hn j) (J i j) (hdim i j hij)
    · simpa only [edgeProjectiveLine, homogeneousSpan, Set.image_pair] using hsecond i j hij
    · exact (hfirst i j hij).trans (line_le_support_kernel g (hA i) (hA j))
  have hcenter (i j : I) :
      differenceCenterVector (p i) (p j) = q j - q i := by
    exact differenceCenterVector_centerParameters (q i) (q j)
  apply decomposable_of_compatible_homothety_centers P label p hclasses
  · obtain ⟨i, j, hij⟩ := hI
    refine ⟨i, j, ?_⟩
    intro he
    have hq : q i = q j := by
      apply Prod.ext
      · exact neg_injective (congrArg Prod.snd he)
      · exact congrArg Prod.fst he
    have hB' : B i = B j := normalize_homogenize_injective ell (hn i) (hn j) hq
    apply hij
    calc
      i = label (B i) := (hlabelB i).symm
      _ = label (B j) := congrArg label hB'
      _ = j := hlabelB j
  · intro x hx y hxy hlabel
    apply hcross x hx y hxy hlabel
    rw [hcenter]
    have hh := (J (label x) (label y)).neg_mem (hdiff (label x) (label y) hlabel)
    simpa only [neg_sub] using hh

end Papers.Polytopes

end
end
end BundlePart24
