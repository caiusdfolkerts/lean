import cubical_indecomposability.evaluations
import cubical_indecomposability.separation
import cubical_indecomposability.cube_data
import papers.finite_hull_certificates
import papers.polytope_targets
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The exact data as an ordinary convex polytope

The vertex set is the range of the 144 rational coordinate vectors.  Every
point is proved extreme by supporting forms that separate it from the other
143 points.  Faces below are exposed faces of their real convex hull.
-/

noncomputable section

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

namespace CubicalIndecomposability

/-- Rational affine coordinates obtained by dehomogenizing the integral data. -/
def pQ (v : Fin 144) (i : Fin 4) : ℚ :=
  (q v i.castSucc : ℚ) / (q v 4 : ℚ)

/-- The same point in ordinary real Euclidean four-space. -/
def p (v : Fin 144) : E 4 :=
  WithLp.toLp 2 (fun i : Fin 4 => (q v i.castSucc : ℝ) / (q v 4 : ℝ))

@[simp] theorem p_apply (v : Fin 144) (i : Fin 4) :
    p v i = (q v i.castSucc : ℝ) / (q v 4 : ℝ) := rfl

/-- Negate the source normals so that all inequalities have the form
`offset f ≤ form f x`. -/
def form (f : Fin 130) : E 4 →L[ℝ] ℝ :=
  (-(normal f 0 : ℝ)) • EuclideanSpace.proj 0 +
  (-(normal f 1 : ℝ)) • EuclideanSpace.proj 1 +
  (-(normal f 2 : ℝ)) • EuclideanSpace.proj 2 +
  (-(normal f 3 : ℝ)) • EuclideanSpace.proj 3

def offset (f : Fin 130) : ℝ := (normal f 4 : ℝ)

theorem form_apply (f : Fin 130) (x : E 4) :
    form f x =
      -(normal f 0 : ℝ) * x 0 - (normal f 1 : ℝ) * x 1 -
        (normal f 2 : ℝ) * x 2 - (normal f 3 : ℝ) * x 3 := by
  simp [form] <;> ring

theorem homogeneous_last_real_pos (v : Fin 144) : 0 < (q v 4 : ℝ) := by
  exact_mod_cast homogeneous_last_pos v

theorem support_identity (f : Fin 130) (v : Fin 144) :
    form f (p v) - offset f =
      (slackNumerator f v : ℝ) / (q v 4 : ℝ) := by
  have hd : (q v 4 : ℝ) ≠ 0 := ne_of_gt (homogeneous_last_real_pos v)
  have h0 : (0 : Fin 4).castSucc = (0 : Fin 5) := rfl
  have h1 : (1 : Fin 4).castSucc = (1 : Fin 5) := rfl
  have h2 : (2 : Fin 4).castSucc = (2 : Fin 5) := rfl
  have h3 : (3 : Fin 4).castSucc = (3 : Fin 5) := rfl
  rw [form_apply]
  simp only [p_apply, h0, h1, h2, h3, offset, slackNumerator,
    Int.cast_neg, Int.cast_add, Int.cast_mul]
  field_simp [hd] <;> ring

/-- All 18,720 exact supporting inequalities. -/
theorem support_nonneg (f : Fin 130) (v : Fin 144) :
    offset f ≤ form f (p v) := by
  have hs : 0 ≤ (slackNumerator f v : ℝ) := by
    exact_mod_cast (supportData f v).1
  have h := div_nonneg hs (homogeneous_last_real_pos v).le
  rw [← support_identity] at h
  exact sub_nonneg.mp h

/-- Equality holds precisely at the eight claimed vertices of a facet. -/
theorem support_eq_iff (f : Fin 130) (v : Fin 144) :
    form f (p v) = offset f ↔ incident f v := by
  have hd : (q v 4 : ℝ) ≠ 0 := ne_of_gt (homogeneous_last_real_pos v)
  rw [← sub_eq_zero, support_identity]
  simpa only [div_eq_zero_iff, hd, or_false, Int.cast_eq_zero] using (supportData f v).2

theorem separatingSupports (v w : Fin 144) (hvw : v ≠ w) :
    ∃ f : Fin 130, form f (p v) = offset f ∧ offset f < form f (p w) := by
  obtain ⟨hv, hw⟩ := separatingData v w hvw
  refine ⟨separatingWitness v w, (support_eq_iff _ _).mpr hv,
    lt_of_le_of_ne (support_nonneg _ _) ?_⟩
  intro heq
  exact hw ((support_eq_iff _ _).mp heq.symm)

theorem p_injective : Function.Injective p :=
  separatingSupports_injective p form offset separatingSupports

/-- The actual convex hull, with a proof that its listed points are exactly
its extreme vertices. -/
def polytope : ConvexPolytope 4 :=
  polytopeOfSeparatingSupports p (by decide) form offset support_nonneg separatingSupports

@[simp] theorem polytope_vertices :
    polytope.vertices = Finset.univ.image p := rfl

theorem vertex_mem (v : Fin 144) : p v ∈ polytope.vertices := by
  rw [polytope_vertices]
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

theorem vertices_card : polytope.vertices.card = 144 :=
  polytopeOfSeparatingSupports_card p (by decide) form offset support_nonneg separatingSupports

theorem rational_coordinates : RationalCoordinates polytope := by
  intro x hx i
  rw [polytope_vertices] at hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  refine ⟨pQ v i, ?_⟩
  simp [pQ, p]

/-- The exposed subset belonging to one supporting inequality.  The fact
that this is a facet is proved later from the complete face certificate. -/
def facet (f : Fin 130) : Set (E 4) :=
  minimumFace polytope (form f) (offset f)

theorem facet_isFace (f : Fin 130) : polytope.IsFace (facet f) := by
  apply minimumFace_isFace
  · intro x hx
    rw [polytope_vertices] at hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact support_nonneg f v
  · have hv : incident f (cubeVertex f 0) := by
      change cubeVertex f 0 ∈ facetLabels f
      rw [← cubeVertex_image f]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    exact ⟨p (cubeVertex f 0), vertex_mem _, (support_eq_iff _ _).mpr hv⟩

@[simp] theorem vertex_mem_facet_iff (f : Fin 130) (v : Fin 144) :
    p v ∈ facet f ↔ incident f v := by
  change (p v ∈ polytope.toSet ∧ form f (p v) = offset f) ↔ incident f v
  rw [support_eq_iff]
  exact and_iff_right (subset_convexHull ℝ _ (vertex_mem v))

theorem facet_eq_hull (f : Fin 130) :
    facet f = convexHull ℝ (p '' (facetLabels f : Set (Fin 144))) := by
  rw [face_eq_hull_vertices polytope (facet_isFace f)]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter, polytope_vertices,
    Finset.mem_image, Finset.mem_univ, true_and, Set.mem_image]
  constructor
  · rintro ⟨⟨v, rfl⟩, hv⟩
    exact ⟨v, (vertex_mem_facet_iff f v).mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, (vertex_mem_facet_iff f v).mpr hv⟩

end CubicalIndecomposability

