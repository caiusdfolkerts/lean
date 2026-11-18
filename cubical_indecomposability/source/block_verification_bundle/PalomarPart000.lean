module

public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Module
public import verification_bundle
@[expose] public section

noncomputable section

/-!
# Consolidated verification sources

Generated only to avoid repeatedly loading the same pinned Mathlib files.
Public theorem statements and proofs preserve their original content.
See BlockVerificationBundle.sources.json for exact source ranges, hashes, and private
helper alpha-renamings, topological source order, and scope adjustments.
-/

/- Original source: CubicalIndecomposability/DeformationDimension.lean -/
section VerificationSource000






/-!
# The paper's deformation space modulo translations

This companion to the main verification gives the literal vector-space
meaning of `D(P)` used in Section 2 of the paper. A redrawing is an assignment
to the actual vertices satisfying parallelism on the actual geometric edges.
The deformation space is its quotient by constant assignments.

For a polytope with two distinct vertices, dimension one is equivalent to
the redrawing-rigidity condition used in the main proof. Consequently the
general summand criterion has exactly the hypothesis of the paper's Lemma 2.
-/

set_option autoImplicit false

noncomputable section

namespace Papers.Polytopes

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

/-- The vertices as a type, with no extraneous ambient points. -/
abbrev Vertex (P : ConvexPolytope d) := {x : E d // x ∈ P.vertices}

/-- All parallel vertex assignments, before quotienting by translations. -/
def redrawingSpace (P : ConvexPolytope d) :
    Submodule ℝ (Vertex P → E d) where
  carrier := {h | ∀ u v : Vertex P, GeneralVertexStep P u v →
    ∃ a : ℝ, h v - h u = a • ((v : E d) - (u : E d))}
  zero_mem' := by
    intro u v _
    exact ⟨0, by simp⟩
  add_mem' := by
    intro h k hh hk u v huv
    obtain ⟨a, ha⟩ := hh u v huv
    obtain ⟨b, hb⟩ := hk u v huv
    refine ⟨a + b, ?_⟩
    change (h v + k v) - (h u + k u) = _
    calc
      _ = (h v - h u) + (k v - k u) := by abel
      _ = (a + b) • ((v : E d) - (u : E d)) := by rw [ha, hb, add_smul]
  smul_mem' := by
    intro a h hh u v huv
    obtain ⟨b, hb⟩ := hh u v huv
    refine ⟨a * b, ?_⟩
    change a • h v - a • h u = _
    rw [← smul_sub, hb, smul_smul]

/-- A translation, regarded as a parallel redrawing. -/
def translationMap (P : ConvexPolytope d) : E d →ₗ[ℝ] redrawingSpace P where
  toFun b := ⟨fun _ => b, by intro u v _; exact ⟨0, by simp⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The subspace of translations inside the redrawing space. -/
def translationSpace (P : ConvexPolytope d) : Submodule ℝ (redrawingSpace P) :=
  (translationMap P).range

/-- Pointwise application of a redrawing is its underlying vertex assignment. -/
instance (P : ConvexPolytope d) :
    CoeFun (redrawingSpace P) (fun _ => Vertex P → E d) :=
  ⟨Subtype.val⟩

theorem translationMap_injective (P : ConvexPolytope d) :
    Function.Injective (translationMap P) := by
  intro b c hbc
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  exact congrArg (fun h : redrawingSpace P => h ⟨v, hv⟩) hbc

theorem translationSpace_finrank (P : ConvexPolytope d) :
    Module.finrank ℝ (translationSpace P) = d := by
  calc
    Module.finrank ℝ (translationSpace P) = Module.finrank ℝ (E d) :=
      LinearMap.finrank_range_of_inj (translationMap_injective P)
    _ = d := by simp only [finrank_euclideanSpace, Fintype.card_fin]

/-- The quotient vector space denoted by the calligraphic `D(P)` in the paper. -/
abbrev DeformationSpace (P : ConvexPolytope d) :=
  redrawingSpace P ⧸ translationSpace P

/-- The quotient is finite-dimensional because the polytope has finitely
many vertices and each assignment takes values in finite-dimensional space. -/
theorem deformationSpace_finiteDimensional (P : ConvexPolytope d) :
    FiniteDimensional ℝ (DeformationSpace P) := by
  classical
  infer_instance

/-- The dimension denoted by `D(P)` in the paper. -/
def deformationDimension (P : ConvexPolytope d) : ℕ :=
  Module.finrank ℝ (DeformationSpace P)

/-- Quotienting removes exactly the ambient translation dimension. -/
theorem redrawingSpace_finrank (P : ConvexPolytope d) :
    Module.finrank ℝ (redrawingSpace P) = deformationDimension P + d := by
  classical
  have h := (translationSpace P).finrank_quotient_add_finrank
  change deformationDimension P + Module.finrank ℝ (translationSpace P) =
    Module.finrank ℝ (redrawingSpace P) at h
  rw [translationSpace_finrank P] at h
  exact h.symm

/-- The identity assignment is a parallel redrawing. -/
def positionRedrawing (P : ConvexPolytope d) : redrawingSpace P :=
  ⟨fun v => v, by intro u v _; exact ⟨1, by simp⟩⟩

/-- The distinguished homothety class in the quotient. -/
def homothetyClass (P : ConvexPolytope d) : DeformationSpace P :=
  Submodule.Quotient.mk (positionRedrawing P)

theorem homothetyClass_ne_zero (P : ConvexPolytope d)
    (hnonpoint : ∃ x ∈ P.vertices, ∃ y ∈ P.vertices, x ≠ y) :
    homothetyClass P ≠ 0 := by
  intro hzero
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero (translationSpace P)).mp hzero
  obtain ⟨x, hx, y, hy, hxy⟩ := hnonpoint
  have hx' := congrArg (fun h : redrawingSpace P => h ⟨x, hx⟩) hb
  have hy' := congrArg (fun h : redrawingSpace P => h ⟨y, hy⟩) hb
  change b = x at hx'
  change b = y at hy'
  exact hxy (hx'.symm.trans hy')

/-- Quotient equality means that the two assignments differ by a translation. -/
theorem class_eq_smul_iff (P : ConvexPolytope d)
    (h : redrawingSpace P) (a : ℝ) :
    (Submodule.Quotient.mk h : DeformationSpace P) = a • homothetyClass P ↔
      ∃ b : E d, ∀ v : Vertex P, h v = a • (v : E d) + b := by
  change Submodule.Quotient.mk h = Submodule.Quotient.mk (a • positionRedrawing P) ↔ _
  rw [Submodule.Quotient.eq]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, fun v => ?_⟩
    have he := congrArg (fun k : redrawingSpace P => k v) hb
    change b = h v - a • (v : E d) at he
    rw [he]
    abel
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext v
    change b = h v - a • (v : E d)
    rw [hb v]
    abel

/-- A nonpoint polytope has a one-dimensional deformation space precisely
when every vertex assignment is a homothety and a translation. -/
theorem deformationDimension_eq_one_iff (P : ConvexPolytope d)
    (hnonpoint : ∃ x ∈ P.vertices, ∃ y ∈ P.vertices, x ≠ y) :
    deformationDimension P = 1 ↔
      ∀ h : redrawingSpace P, ∃ a : ℝ, ∃ b : E d,
        ∀ v : Vertex P, h v = a • (v : E d) + b := by
  rw [deformationDimension,
    finrank_eq_one_iff_of_nonzero' (homothetyClass P)
      (homothetyClass_ne_zero P hnonpoint)]
  constructor
  · intro hspan h
    obtain ⟨a, ha⟩ := hspan (Submodule.Quotient.mk h)
    exact ⟨a, (class_eq_smul_iff P h a).mp ha.symm⟩
  · intro hrigid q
    refine Submodule.Quotient.induction_on (translationSpace P) q ?_
    intro h
    obtain ⟨a, b, hb⟩ := hrigid h
    exact ⟨a, ((class_eq_smul_iff P h a).mpr ⟨b, hb⟩).symm⟩

/-- The quotient-space condition implies the ambient-map rigidity criterion.
The one-point case is handled directly, so there is no extra hypothesis. -/
theorem parallel_rigid_of_deformationDimension_eq_one (P : ConvexPolytope d)
    (hD : deformationDimension P = 1) :
    ∀ f : E d → E d, IsParallelMap P f → IsHomothetyOnVertices P f := by
  intro f hf
  by_cases hnonpoint : ∃ x ∈ P.vertices, ∃ y ∈ P.vertices, x ≠ y
  · let h : redrawingSpace P := ⟨fun v => f v,
      fun u v huv => hf u u.property v v.property huv⟩
    obtain ⟨a, b, hb⟩ := (deformationDimension_eq_one_iff P hnonpoint).mp hD h
    exact ⟨a, b, fun v hv => hb ⟨v, hv⟩⟩
  · obtain ⟨x, hx⟩ := P.vertices_nonempty
    refine ⟨0, f x, fun v hv => ?_⟩
    have hvx : v = x := by
      by_contra hne
      exact hnonpoint ⟨v, hv, x, hx, hne⟩
    simp [hvx]

/-- Ambient maps and genuine vertex assignments give the same rigidity
criterion: any assignment extends to the ambient space. -/
theorem deformationDimension_eq_one_of_parallel_rigid (P : ConvexPolytope d)
    (hnonpoint : ∃ x ∈ P.vertices, ∃ y ∈ P.vertices, x ≠ y)
    (hrigid : ∀ f : E d → E d, IsParallelMap P f → IsHomothetyOnVertices P f) :
    deformationDimension P = 1 := by
  classical
  apply (deformationDimension_eq_one_iff P hnonpoint).mpr
  intro h
  let f : E d → E d := fun x => if hx : x ∈ P.vertices then h ⟨x, hx⟩ else 0
  have hf : IsParallelMap P f := by
    intro x hx y hy hxy
    simpa only [f, dif_pos hx, dif_pos hy] using h.property ⟨x, hx⟩ ⟨y, hy⟩ hxy
  obtain ⟨a, b, hab⟩ := hrigid f hf
  refine ⟨a, b, fun v => ?_⟩
  simpa only [f, dif_pos v.property] using hab v v.property

end Papers.Polytopes

namespace CubicalIndecomposability

open Set
open scoped Pointwise
open LeanEval.Geometry.PlatonicClassification
open Papers.Polytopes

/-- Lemma 2 of the paper, including arbitrary convex summands and the
complementary scale and translation. -/
theorem lemma_two {d : ℕ} (P : ConvexPolytope d)
    (hD : deformationDimension P = 1)
    (A B : Set (E d)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hP : P.toSet = A + B) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ ∃ b : E d,
      A = (fun x : E d => r • x + b) '' P.toSet ∧
      B = (fun x : E d => (1 - r) • x - b) '' P.toSet :=
  convex_summands_homothetic P
    (parallel_rigid_of_deformationDimension_eq_one P hD) A B hA hB hP

/-- The explicit witness has precisely the homothety line modulo translations. -/
theorem deformation_dimension : deformationDimension polytope = 1 :=
  deformationDimension_eq_one_of_parallel_rigid polytope polytope_nonpoint
    parallel_redrawings_homothetic

/-- Four translations and one uniform scale are the full redrawing space. -/
theorem redrawing_dimension : Module.finrank ℝ (redrawingSpace polytope) = 5 := by
  rw [redrawingSpace_finrank, deformation_dimension]

end CubicalIndecomposability
end
end VerificationSource000

/- Original source: CubicalIndecomposability/FaceRestrictions.lean -/
section VerificationSource001


/-!
# Restriction of deformation spaces to actual faces

The restriction map is defined on vertex assignments and then descends to
the quotient by translations. A face determines a polytope when this quotient
map is injective, exactly as in Section 2 of the paper. The final lemma turns
explicit difference-coordinate identities into an upper bound for the
dimension of a restriction image.
-/

set_option autoImplicit false

noncomputable section

namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} (P : ConvexPolytope d) {F : Set (E d)} (hF : P.IsFace F)

/-- A vertex of a face is an actual vertex of the original polytope. -/
def faceVertex (v : Vertex (facePolytope P hF)) : Vertex P :=
  ⟨v, (Finset.mem_filter.mp v.property).1⟩

theorem faceVertex_mem (v : Vertex (facePolytope P hF)) :
    (faceVertex P hF v : E d) ∈ F :=
  (Finset.mem_filter.mp v.property).2

/-- Restriction respects actual exposed edges, hence parallelism. -/
def redrawingRestriction :
    redrawingSpace P →ₗ[ℝ] redrawingSpace (facePolytope P hF) where
  toFun h := ⟨fun v => h (faceVertex P hF v), by
    intro u v huv
    obtain ⟨hv, hne, e, he, hde, hue, hve⟩ := huv
    exact h.property (faceVertex P hF u) (faceVertex P hF v)
      ⟨(Finset.mem_filter.mp hv).1, hne, e,
        isFace_of_facePolytope P hF he, hde, hue, hve⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem redrawingRestriction_apply (h : redrawingSpace P)
    (v : Vertex (facePolytope P hF)) :
    redrawingRestriction P hF h v = h (faceVertex P hF v) := rfl

@[simp] theorem redrawingRestriction_translation (b : E d) :
    redrawingRestriction P hF (translationMap P b) =
      translationMap (facePolytope P hF) b := rfl

/-- The linear restriction map on redrawings modulo translations. -/
def deformationRestriction :
    DeformationSpace P →ₗ[ℝ] DeformationSpace (facePolytope P hF) :=
  (translationSpace P).mapQ (translationSpace (facePolytope P hF))
    (redrawingRestriction P hF) (by
      rintro h ⟨b, rfl⟩
      exact ⟨b, rfl⟩)

@[simp] theorem deformationRestriction_mk (h : redrawingSpace P) :
    deformationRestriction P hF (Submodule.Quotient.mk h) =
      Submodule.Quotient.mk (redrawingRestriction P hF h) := rfl

/-- The precise quotient-space definition of a determining face. -/
def FaceDetermines : Prop := Function.Injective (deformationRestriction P hF)

/-- It suffices to recover a redrawing that vanishes identically on the face. -/
theorem determines_of_zero_restriction
    (hzero : ∀ h : redrawingSpace P, redrawingRestriction P hF h = 0 → h = 0) :
    FaceDetermines P hF := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (translationSpace P) q
  change (Submodule.Quotient.mk (redrawingRestriction P hF h) :
    DeformationSpace (facePolytope P hF)) = 0 at hq
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero (translationSpace (facePolytope P hF))).mp hq
  have hz : redrawingRestriction P hF (h - translationMap P b) = 0 := by
    rw [map_sub, redrawingRestriction_translation, ← hb, sub_self]
  apply (Submodule.Quotient.mk_eq_zero (translationSpace P)).mpr
  exact ⟨b, (sub_eq_zero.mp (hzero _ hz)).symm⟩

/-- Pointwise form of the determining-face criterion. -/
theorem determines_of_vanishing
    (hzero : ∀ h : redrawingSpace P,
      (∀ u : Vertex (facePolytope P hF), h (faceVertex P hF u) = 0) →
      ∀ v : Vertex P, h v = 0) :
    FaceDetermines P hF := by
  apply determines_of_zero_restriction P hF
  intro h hr
  apply Subtype.ext
  funext v
  apply hzero h ?_ v
  intro u
  exact congrArg (fun k : redrawingSpace (facePolytope P hF) => k u) hr

variable {P hF}

/-- A coordinate difference is a linear functional on full redrawings. -/
def redrawingDifference (P : ConvexPolytope d) (u v : Vertex P) (i : Fin d) :
    redrawingSpace P →ₗ[ℝ] ℝ where
  toFun h := h v i - h u i
  map_add' h k := by
    change (h v + k v) i - (h u + k u) i = _
    simp only [PiLp.add_apply]
    ring
  map_smul' a h := by
    change (a • h v) i - (a • h u) i = _
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Coordinate differences are unchanged by translation, so they descend. -/
def deformationDifference (P : ConvexPolytope d) (u v : Vertex P) (i : Fin d) :
    DeformationSpace P →ₗ[ℝ] ℝ :=
  (translationSpace P).liftQ (redrawingDifference P u v i) (by
    rintro h ⟨b, rfl⟩
    change b i - b i = 0
    exact sub_self _)

@[simp] theorem deformationDifference_mk (P : ConvexPolytope d)
    (u v : Vertex P) (i : Fin d) (h : redrawingSpace P) :
    deformationDifference P u v i (Submodule.Quotient.mk h) = h v i - h u i := rfl

/-- `k` translation-invariant coordinates that determine every restricted
assignment give a genuine `k`-dimensional upper bound on the quotient image. -/
theorem restriction_rank_le_of_difference_determination
    (P : ConvexPolytope d) {F : Set (E d)} (hF : P.IsFace F) {k : ℕ}
    (anchor : Vertex (facePolytope P hF))
    (vertices : Fin k → Vertex (facePolytope P hF))
    (coordinates : Fin k → Fin d)
    (hdet : ∀ h : redrawingSpace P,
      (∀ j : Fin k,
        h (faceVertex P hF (vertices j)) (coordinates j) -
          h (faceVertex P hF anchor) (coordinates j) = 0) →
      ∀ v : Vertex (facePolytope P hF),
        h (faceVertex P hF v) = h (faceVertex P hF anchor)) :
    Module.finrank ℝ (deformationRestriction P hF).range ≤ k := by
  classical
  let Q := facePolytope P hF
  let coordinatesMap : DeformationSpace Q →ₗ[ℝ] (Fin k → ℝ) :=
    LinearMap.pi fun j => deformationDifference Q anchor (vertices j) (coordinates j)
  let imageCoordinates : (deformationRestriction P hF).range →ₗ[ℝ] (Fin k → ℝ) :=
    coordinatesMap.comp (deformationRestriction P hF).range.subtype
  have hinj : Function.Injective imageCoordinates := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    obtain ⟨q, hq⟩ := z.property
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (translationSpace P) q
    have hz' : coordinatesMap
        (Submodule.Quotient.mk (redrawingRestriction P hF h)) = 0 := by
      change coordinatesMap z.val = 0 at hz
      rw [← hq] at hz
      exact hz
    have heval (j : Fin k) :
        h (faceVertex P hF (vertices j)) (coordinates j) -
          h (faceVertex P hF anchor) (coordinates j) = 0 := by
      exact congrArg (fun x : Fin k → ℝ => x j) hz'
    apply Subtype.ext
    rw [← hq]
    change (Submodule.Quotient.mk (redrawingRestriction P hF h) : DeformationSpace Q) = 0
    apply (Submodule.Quotient.mk_eq_zero (translationSpace Q)).mpr
    refine ⟨h (faceVertex P hF anchor), ?_⟩
    apply Subtype.ext
    funext v
    exact (hdet h heval v).symm
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

end Papers.Polytopes
end
end VerificationSource001

/- Original source: CubicalIndecomposability/ProjectiveGeometry.lean -/
section VerificationSource002



/-!
# Homogeneous projectivities and affine interface maps

A projectivity is represented by an invertible real linear map in one higher
dimension. Its action in the affine chart is division by the last coordinate.
Positivity is a property of that actual denominator on the specified set.

The normalized block used for Proposition 5 already has affine interfaces and
an affine cubical facet. The identity projectivity therefore witnesses the
paper's two projective assertions. These definitions retain their ordinary
mathematical meaning; invertibility is part of the type.
-/

set_option autoImplicit false

noncomputable section

namespace Papers.Polytopes

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- An invertible homogeneous representative of a real projectivity. -/
abbrev HomogeneousProjectivity (d : ℕ) := E (d + 1) ≃ₗ[ℝ] E (d + 1)

/-- Embed the affine chart by appending the homogeneous coordinate one. -/
def homogeneousPoint {d : ℕ} (x : E d) : E (d + 1) :=
  WithLp.toLp 2 (Fin.lastCases 1 (fun i => x i))

/-- The denominator of a projectivity in the chosen affine chart. -/
def projectiveDenominator {d : ℕ} (T : HomogeneousProjectivity d) (x : E d) : ℝ :=
  T (homogeneousPoint x) (Fin.last d)

/-- The usual affine-chart action of an invertible homogeneous map. -/
def projectiveApply {d : ℕ} (T : HomogeneousProjectivity d) (x : E d) : E d :=
  WithLp.toLp 2 (fun i =>
    T (homogeneousPoint x) i.castSucc / projectiveDenominator T x)

def ProjectivelyPositiveOn {d : ℕ} (T : HomogeneousProjectivity d) (S : Set (E d)) : Prop :=
  ∀ x ∈ S, 0 < projectiveDenominator T x

@[simp] theorem projectiveDenominator_id {d : ℕ} (x : E d) :
    projectiveDenominator (LinearEquiv.refl ℝ (E (d + 1))) x = 1 := by
  simp [projectiveDenominator, homogeneousPoint]

@[simp] theorem projectiveApply_id {d : ℕ} (x : E d) :
    projectiveApply (LinearEquiv.refl ℝ (E (d + 1))) x = x := by
  ext i
  simp [projectiveApply, projectiveDenominator, homogeneousPoint]

theorem projectiveApply_id_fun {d : ℕ} :
    projectiveApply (LinearEquiv.refl ℝ (E (d + 1))) = (fun x : E d => x) :=
  funext projectiveApply_id

theorem projectivelyPositiveOn_id {d : ℕ} (S : Set (E d)) :
    ProjectivelyPositiveOn (LinearEquiv.refl ℝ (E (d + 1))) S := by
  intro x _
  simp

/-- Proposition 5(iv): one positive projectivity makes the interfaces
affinely equivalent, with their common face fixed pointwise. -/
def HasAffineInterfaceNormalization (P : ConvexPolytope 4)
    (F H Q : Set (E 4)) : Prop :=
  ∃ T : HomogeneousProjectivity 4, ProjectivelyPositiveOn T P.toSet ∧
    ∃ e : E 4 ≃ᵃ[ℝ] E 4,
      e '' (projectiveApply T '' F) = projectiveApply T '' H ∧
      ∀ x ∈ projectiveApply T '' Q, e x = x

/-- A nondegenerate parallelepiped is an injective affine image of a cube;
Proposition 5(v) permits an invertible projective change before that image. -/
def ProjectivelyParallelepiped (G : Set (E 4)) : Prop :=
  ∃ T : HomogeneousProjectivity 4, ProjectivelyPositiveOn T G ∧
    ∃ e : E 3 →ᵃ[ℝ] E 4, Function.Injective e ∧
      projectiveApply T '' G = e '' (standardCube 3).toSet

theorem affine_interface_normalization_of_affine
    (P : ConvexPolytope 4) (F H Q : Set (E 4))
    (e : E 4 ≃ᵃ[ℝ] E 4) (he : e '' F = H)
    (hfix : ∀ x ∈ Q, e x = x) :
    HasAffineInterfaceNormalization P F H Q := by
  refine ⟨LinearEquiv.refl ℝ (E 5), projectivelyPositiveOn_id _, e, ?_, ?_⟩
  · simpa only [projectiveApply_id_fun, Set.image_id'] using he
  · simpa only [projectiveApply_id_fun, Set.image_id'] using hfix

theorem projectivelyParallelepiped_of_affine (G : Set (E 4))
    (e : E 3 →ᵃ[ℝ] E 4) (hinj : Function.Injective e)
    (he : G = e '' (standardCube 3).toSet) : ProjectivelyParallelepiped G := by
  refine ⟨LinearEquiv.refl ℝ (E 5), projectivelyPositiveOn_id _, e, hinj, ?_⟩
  simpa only [projectiveApply_id_fun, Set.image_id'] using he

section AffineShear

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A rank-one affine shear, written without choosing coordinates. -/
def affineShearMap (l : V →ₗ[ℝ] ℝ) (v : V) (c : ℝ) : V →ᵃ[ℝ] V where
  toFun x := x + (l x + c) • v
  linear := LinearMap.id + l.smulRight v
  map_vadd' p x := by
    change (x + p) + (l (x + p) + c) • v =
      (x + l x • v) + (p + (l p + c) • v)
    rw [map_add]
    module

/-- If the shear direction lies in the kernel of its linear functional,
subtracting the same displacement is the inverse map. -/
def affineShear (l : V →ₗ[ℝ] ℝ) (v : V) (c : ℝ) (hv : l v = 0) : V ≃ᵃ[ℝ] V := by
  let inverse : V → V := fun x => x - (l x + c) • v
  have hleft : Function.LeftInverse inverse (affineShearMap l v c) := by
    intro x
    change x + (l x + c) • v - (l (x + (l x + c) • v) + c) • v = x
    simp [map_add, map_smul, hv]
  have hright : Function.RightInverse inverse (affineShearMap l v c) := by
    intro x
    change x - (l x + c) • v + (l (x - (l x + c) • v) + c) • v = x
    simp [map_sub, map_smul, hv]
  exact AffineEquiv.ofBijective ⟨hleft.injective, hright.surjective⟩

@[simp] theorem affineShear_apply (l : V →ₗ[ℝ] ℝ) (v : V) (c : ℝ)
    (hv : l v = 0) (x : V) : affineShear l v c hv x = x + (l x + c) • v := rfl

end AffineShear

end Papers.Polytopes
end
end VerificationSource002

/- Original source: CubicalIndecomposability/ElementaryRedrawings.lean -/
section VerificationSource003




/-!
# An affinely independent four-cycle

Lemma 3(i) of the paper is independent of convexity. Four affinely
independent points have no nonzero affine relation. Summing the four
edge equations therefore forces their four real scale factors to agree.
Integrating the first three equations gives one common translation.

The statements below hold in every real module, hence in every real
Euclidean dimension. The edge multipliers are arbitrary real numbers.
-/

set_option autoImplicit false

noncomputable section

namespace CubicalIndecomposability

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- On an affinely independent four-cycle, all four edge scale factors
of a parallel redrawing coincide. No sign or nonzero condition is imposed. -/
theorem four_cycle_edge_scalars_eq
    (p h : Fin 4 → V) (hp : AffineIndependent ℝ p) (a : Fin 4 → ℝ)
    (h01 : h 1 - h 0 = a 0 • (p 1 - p 0))
    (h12 : h 2 - h 1 = a 1 • (p 2 - p 1))
    (h23 : h 3 - h 2 = a 2 • (p 3 - p 2))
    (h30 : h 0 - h 3 = a 3 • (p 0 - p 3)) :
    ∀ i : Fin 4, a i = a 0 := by
  classical
  have hcycle :
      a 0 • (p 1 - p 0) + a 1 • (p 2 - p 1) +
        a 2 • (p 3 - p 2) + a 3 • (p 0 - p 3) = 0 := by
    rw [← h01, ← h12, ← h23, ← h30]
    abel
  let w : Fin 4 → ℝ := ![a 3 - a 0, a 0 - a 1, a 1 - a 2, a 2 - a 3]
  have hw : (∑ i : Fin 4, w i) = 0 := by
    simp [w, Fin.sum_univ_succ] <;> ring
  have hwp : (∑ i : Fin 4, w i • p i) = 0 := by
    calc
      _ = a 0 • (p 1 - p 0) + a 1 • (p 2 - p 1) +
          a 2 • (p 3 - p 2) + a 3 • (p 0 - p 3) := by
        simp [w, Fin.sum_univ_succ] <;> module
      _ = 0 := hcycle
  have hweights : ∀ i : Fin 4, w i = 0 := by
    intro i
    exact hp.eq_zero_of_sum_eq_zero hw hwp i (Finset.mem_univ i)
  have ha01 : a 0 = a 1 := sub_eq_zero.mp (by simpa [w] using hweights 1)
  have ha12 : a 1 = a 2 := sub_eq_zero.mp (by simpa [w] using hweights 2)
  have ha23 : a 2 = a 3 := sub_eq_zero.mp (by simpa [w] using hweights 3)
  intro i
  fin_cases i
  · rfl
  · exact ha01.symm
  · exact (ha01.trans ha12).symm
  · exact ((ha01.trans ha12).trans ha23).symm

/-- The explicit homothety formula after the four edge scales agree. -/
theorem four_cycle_redrawing_formula
    (p h : Fin 4 → V) (hp : AffineIndependent ℝ p) (a : Fin 4 → ℝ)
    (h01 : h 1 - h 0 = a 0 • (p 1 - p 0))
    (h12 : h 2 - h 1 = a 1 • (p 2 - p 1))
    (h23 : h 3 - h 2 = a 2 • (p 3 - p 2))
    (h30 : h 0 - h 3 = a 3 • (p 0 - p 3)) :
    ∀ i : Fin 4, h i = a 0 • p i + (h 0 - a 0 • p 0) := by
  have ha := four_cycle_edge_scalars_eq p h hp a h01 h12 h23 h30
  rw [ha 1] at h12
  rw [ha 2] at h23
  intro i
  fin_cases i
  · change h 0 = a 0 • p 0 + (h 0 - a 0 • p 0)
    abel
  · calc
      h 1 = (h 1 - h 0) + h 0 := by abel
      _ = a 0 • (p 1 - p 0) + h 0 := by rw [h01]
      _ = a 0 • p 1 + (h 0 - a 0 • p 0) := by module
  · calc
      h 2 = (h 2 - h 1) + (h 1 - h 0) + h 0 := by abel
      _ = a 0 • (p 2 - p 1) + a 0 • (p 1 - p 0) + h 0 := by rw [h12, h01]
      _ = a 0 • p 2 + (h 0 - a 0 • p 0) := by module
  · calc
      h 3 = (h 3 - h 2) + (h 2 - h 1) + (h 1 - h 0) + h 0 := by abel
      _ = a 0 • (p 3 - p 2) + a 0 • (p 2 - p 1) +
          a 0 • (p 1 - p 0) + h 0 := by rw [h23, h12, h01]
      _ = a 0 • p 3 + (h 0 - a 0 • p 0) := by module

/-- Lemma 3(i): every parallel redrawing of an affinely independent
four-cycle is a homothety and a translation. Addition on `Fin 4` is
cyclic, so the quantified edges are 01, 12, 23, and 30. -/
theorem lemma_three_one
    (p h : Fin 4 → V) (hp : AffineIndependent ℝ p)
    (hparallel : ∀ i : Fin 4, ∃ a : ℝ,
      h (i + 1) - h i = a • (p (i + 1) - p i)) :
    ∃ a : ℝ, ∃ b : V, ∀ i : Fin 4, h i = a • p i + b := by
  classical
  choose a ha using hparallel
  refine ⟨a 0, h 0 - a 0 • p 0, ?_⟩
  apply four_cycle_redrawing_formula p h hp a
  · simpa using ha 0
  · simpa using ha 1
  · simpa using ha 2
  · simpa using ha 3

end CubicalIndecomposability
end
end VerificationSource003

/- Original source: CubicalIndecomposability/NeighborRedrawings.lean -/
section VerificationSource004



/-!
# The two-neighbor rule for parallel redrawings

Lemma 3(ii) of the paper is a consequence of extremality alone: three
distinct vertices of a convex polytope cannot lie on one affine line.
Accordingly, the two directions from a vertex to two distinct neighbors
have no common nonzero vector.  Both the ambient-map and vertex-assignment
formulations below use the actual geometric edge relation.
-/

set_option autoImplicit false

noncomputable section

namespace Papers.Polytopes

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

/-- The direction lines from one actual vertex to two other distinct actual
vertices intersect only at zero.  Adjacency is not needed for this geometric
fact. -/
theorem vertex_direction_intersection_eq_zero (P : ConvexPolytope d)
    {x y z w : E d} (hx : x ∈ P.vertices) (hy : y ∈ P.vertices)
    (hz : z ∈ P.vertices) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hwy : ∃ a : ℝ, w = a • (y - x))
    (hwz : ∃ b : ℝ, w = b • (z - x)) : w = 0 := by
  by_contra hw
  obtain ⟨a, ha⟩ := hwy
  obtain ⟨b, hb⟩ := hwz
  have ha0 : a ≠ 0 := by
    intro h
    exact hw (by simpa only [h, zero_smul] using ha)
  have hb0 : b ≠ 0 := by
    intro h
    exact hw (by simpa only [h, zero_smul] using hb)
  apply vertices_not_collinear P hx hy hz hxy hxz hyz
  apply (collinear_iff_of_mem (show x ∈ ({x, y, z} : Set (E d)) by simp)).mpr
  refine ⟨w, ?_⟩
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with hqx | hqy | hqz
  · subst q
    exact ⟨0, by simp⟩
  · subst q
    refine ⟨a⁻¹, ?_⟩
    change y = a⁻¹ • w + x
    rw [ha, inv_smul_smul₀ ha0, sub_add_cancel]
  · subst q
    refine ⟨b⁻¹, ?_⟩
    change z = b⁻¹ • w + x
    rw [hb, inv_smul_smul₀ hb0, sub_add_cancel]

/-- **Lemma 3(ii), ambient-map formulation.** A parallel redrawing which
vanishes at two distinct neighbors of a vertex also vanishes at that vertex. -/
theorem IsParallelMap.zero_of_two_neighbors {P : ConvexPolytope d}
    {f : E d → E d} (hf : IsParallelMap P f) {x y z : E d}
    (hx : x ∈ P.vertices) (hxy : GeneralVertexStep P x y)
    (hxz : GeneralVertexStep P x z) (hyz : y ≠ z)
    (hy : f y = 0) (hz : f z = 0) : f x = 0 := by
  obtain ⟨a, ha⟩ := hf x hx y hxy.1 hxy
  obtain ⟨b, hb⟩ := hf x hx z hxz.1 hxz
  apply neg_eq_zero.mp
  apply vertex_direction_intersection_eq_zero P hx hxy.1 hxz.1
    hxy.2.1 hxz.2.1 hyz
  · exact ⟨a, by simpa only [hy, zero_sub] using ha⟩
  · exact ⟨b, by simpa only [hz, zero_sub] using hb⟩

/-- **Lemma 3(ii), vertex-assignment formulation.** This applies directly
to the redrawing space whose quotient defines the paper's `D(P)`. -/
theorem redrawing_zero_of_two_neighbors {P : ConvexPolytope d}
    (h : redrawingSpace P) {x y z : Vertex P}
    (hxy : GeneralVertexStep P x y) (hxz : GeneralVertexStep P x z)
    (hyz : y ≠ z) (hy : h y = 0) (hz : h z = 0) : h x = 0 := by
  obtain ⟨a, ha⟩ := h.property x y hxy
  obtain ⟨b, hb⟩ := h.property x z hxz
  have hyz' : (y : E d) ≠ (z : E d) := fun h => hyz (Subtype.ext h)
  apply neg_eq_zero.mp
  apply vertex_direction_intersection_eq_zero P x.property y.property z.property
    hxy.2.1 hxz.2.1 hyz'
  · exact ⟨a, by simpa only [hy, zero_sub] using ha⟩
  · exact ⟨b, by simpa only [hz, zero_sub] using hb⟩

end Papers.Polytopes
end
end VerificationSource004

/- Original source: CubicalIndecomposability/Block/Data.lean -/
section VerificationSource005


/-!
# Exact data for the normalized 32-vertex block

This is the rational block in Proposition 5, after the paper's normalization.
The source preparation stores inward normals; `normal` is their negative, so
the supporting convention agrees with the 144-vertex construction:
`normal[f][0] * x + ... + normal[f][3] * t + normal[f][4] ≤ 0`.
All coordinates and labels below are explicit constants.  Their required
properties are proved by kernel reduction and ordinary convex geometry.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

def bundle_13b5da25e7_qTable : ℕ → (Fin 5 → ℤ) :=
  fun index =>
    if index < 16 then
      if index < 8 then
        if index < 4 then
          if index < 2 then
            if index < 1 then
              ![0, 0, 0, 51, 44]
            else
              ![0, 0, 0, 0, 1]
          else
            if index < 3 then
              ![272, -17, -17, 408, 420]
            else
              ![1, 0, 0, 0, 1]
        else
          if index < 6 then
            if index < 5 then
              ![0, 121, 0, 102, 88]
            else
              ![0, 1, 0, 0, 1]
          else
            if index < 7 then
              ![544, 1121, -34, 816, 840]
            else
              ![1, 1, 0, 0, 1]
      else
        if index < 12 then
          if index < 10 then
            if index < 9 then
              ![0, 0, 51, 51, 44]
            else
              ![0, 0, 1, 0, 1]
          else
            if index < 11 then
              ![272, -17, 510, 408, 420]
            else
              ![1, 0, 1, 0, 1]
        else
          if index < 14 then
            if index < 13 then
              ![0, 121, 102, 102, 88]
            else
              ![0, 1, 1, 0, 1]
          else
            if index < 15 then
              ![544, 1121, 1020, 816, 840]
            else
              ![1, 1, 1, 0, 1]
    else
      if index < 24 then
        if index < 20 then
          if index < 18 then
            if index < 17 then
              ![106344, -106344, -106344, 248829, 270380]
            else
              ![2499, -2499, -2499, 4998, 7342]
          else
            if index < 19 then
              ![1021370, -840665, -840665, 1946364, 2161442]
            else
              ![4220, -2499, -2499, 4998, 7342]
        else
          if index < 22 then
            if index < 21 then
              ![612612, 3096445, -612612, 2081514, 2116708]
            else
              ![102, 701, -102, 204, 584]
          else
            if index < 23 then
              ![9059368, 24668895, -4777918, 15835296, 17156752]
            else
              ![3196, 4907, -714, 1428, 4088]
      else
        if index < 28 then
          if index < 26 then
            if index < 25 then
              ![306306, -306306, 1813815, 1040757, 1058354]
            else
              ![51, -51, 408, 102, 292]
          else
            if index < 27 then
              ![4529684, -2388959, 14443030, 7917648, 8578376]
            else
              ![1598, -357, 2856, 714, 2044]
        else
          if index < 30 then
            if index < 29 then
              ![612612, 3096445, 3627630, 2081514, 2116708]
            else
              ![102, 701, 816, 204, 584]
          else
            if index < 31 then
              ![9059368, 24668895, 28886060, 15835296, 17156752]
            else
              ![3196, 4907, 5712, 1428, 4088]

def q (i : Fin 32) : Fin 5 → ℤ := bundle_13b5da25e7_qTable i.val

def bundle_13b5da25e7_normalTable : ℕ → (Fin 5 → ℤ) :=
  fun index =>
    if index < 12 then
      if index < 6 then
        if index < 3 then
          if index < 1 then
            ![-1, 0, 0, 0, 0]
          else
            if index < 2 then
              ![0, 0, 0, -1, 0]
            else
              ![102, 0, 0, 37, -102]
        else
          if index < 4 then
            ![51, 0, 0, 176, -204]
          else
            if index < 5 then
              ![0, -13932, 774, -2908, -2499]
            else
              ![0, 0, 26316, -13138, -32181]
      else
        if index < 9 then
          if index < 7 then
            ![0, 105264, 0, -43582, -111129]
          else
            if index < 8 then
              ![0, 710532, -11276406, -2335124, -2006697]
            else
              ![-1, -1, 0, 0, 0]
        else
          if index < 10 then
            ![-102, 0, 51, -7, -51]
          else
            if index < 11 then
              ![-17, 34, 0, -11, -34]
            else
              ![-1, 0, -1, 0, 0]
    else
      if index < 18 then
        if index < 15 then
          if index < 13 then
            ![0, -2, 0, -1, 0]
          else
            if index < 14 then
              ![0, 0, 51, -58, -51]
            else
              ![0, 68, 0, -39, -68]
        else
          if index < 16 then
            ![0, 0, -2, -1, 0]
          else
            if index < 17 then
              ![357, -204, 0, 121, -357]
            else
              ![357, 0, 102, 107, -459]
      else
        if index < 21 then
          if index < 19 then
            ![357, 408, 0, -11, -765]
          else
            if index < 20 then
              ![357, 0, -204, 121, -357]
            else
              ![1241, -1564, 0, 4620, -5355]
        else
          if index < 22 then
            ![3723, 0, 2346, 13538, -18411]
          else
            if index < 23 then
              ![1241, 3128, 0, 3608, -8483]
            else
              ![1241, 0, -1564, 4620, -5355]

def normal (i : Fin 24) : Fin 5 → ℤ := bundle_13b5da25e7_normalTable i.val

def bundle_13b5da25e7_facetLabelsTable : ℕ → (Finset (Fin 32)) :=
  fun index =>
    if index < 12 then
      if index < 6 then
        if index < 3 then
          if index < 1 then
            {0, 1, 4, 5, 8, 9, 12, 13}
          else
            if index < 2 then
              {1, 3, 5, 7, 9, 11, 13, 15}
            else
              {2, 3, 6, 7, 10, 11, 14, 15}
        else
          if index < 4 then
            {0, 2, 4, 6, 8, 10, 12, 14}
          else
            if index < 5 then
              {16, 17, 18, 19, 24, 25, 26, 27}
            else
              {24, 25, 26, 27, 28, 29, 30, 31}
      else
        if index < 9 then
          if index < 7 then
            {20, 21, 22, 23, 28, 29, 30, 31}
          else
            if index < 8 then
              {16, 17, 18, 19, 20, 21, 22, 23}
            else
              {0, 1, 8, 9, 16, 17, 24, 25}
        else
          if index < 10 then
            {8, 9, 12, 13, 24, 25, 28, 29}
          else
            if index < 11 then
              {4, 5, 12, 13, 20, 21, 28, 29}
            else
              {0, 1, 4, 5, 16, 17, 20, 21}
    else
      if index < 18 then
        if index < 15 then
          if index < 13 then
            {1, 3, 9, 11, 17, 19, 25, 27}
          else
            if index < 14 then
              {9, 11, 13, 15, 25, 27, 29, 31}
            else
              {5, 7, 13, 15, 21, 23, 29, 31}
        else
          if index < 16 then
            {1, 3, 5, 7, 17, 19, 21, 23}
          else
            if index < 17 then
              {2, 3, 10, 11, 18, 19, 26, 27}
            else
              {10, 11, 14, 15, 26, 27, 30, 31}
      else
        if index < 21 then
          if index < 19 then
            {6, 7, 14, 15, 22, 23, 30, 31}
          else
            if index < 20 then
              {2, 3, 6, 7, 18, 19, 22, 23}
            else
              {0, 2, 8, 10, 16, 18, 24, 26}
        else
          if index < 22 then
            {8, 10, 12, 14, 24, 26, 28, 30}
          else
            if index < 23 then
              {4, 6, 12, 14, 20, 22, 28, 30}
            else
              {0, 2, 4, 6, 16, 18, 20, 22}

def facetLabels (i : Fin 24) : Finset (Fin 32) := bundle_13b5da25e7_facetLabelsTable i.val

def incident (f : Fin 24) (v : Fin 32) : Prop := v ∈ facetLabels f

instance (f : Fin 24) (v : Fin 32) : Decidable (incident f v) :=
  inferInstanceAs (Decidable (v ∈ facetLabels f))

def bundle_13b5da25e7_cubeVertexTable : ℕ → (Fin 8 → Fin 32) :=
  fun index =>
    if index < 12 then
      if index < 6 then
        if index < 3 then
          if index < 1 then
            ![0, 1, 4, 5, 8, 9, 12, 13]
          else
            if index < 2 then
              ![1, 3, 5, 7, 9, 11, 13, 15]
            else
              ![2, 3, 6, 7, 10, 11, 14, 15]
        else
          if index < 4 then
            ![0, 2, 4, 6, 8, 10, 12, 14]
          else
            if index < 5 then
              ![16, 17, 18, 19, 24, 25, 26, 27]
            else
              ![24, 25, 26, 27, 28, 29, 30, 31]
      else
        if index < 9 then
          if index < 7 then
            ![20, 21, 22, 23, 28, 29, 30, 31]
          else
            if index < 8 then
              ![16, 17, 18, 19, 20, 21, 22, 23]
            else
              ![0, 1, 8, 9, 16, 17, 24, 25]
        else
          if index < 10 then
            ![8, 9, 12, 13, 24, 25, 28, 29]
          else
            if index < 11 then
              ![4, 5, 12, 13, 20, 21, 28, 29]
            else
              ![0, 1, 4, 5, 16, 17, 20, 21]
    else
      if index < 18 then
        if index < 15 then
          if index < 13 then
            ![1, 3, 9, 11, 17, 19, 25, 27]
          else
            if index < 14 then
              ![9, 11, 13, 15, 25, 27, 29, 31]
            else
              ![5, 7, 13, 15, 21, 23, 29, 31]
        else
          if index < 16 then
            ![1, 3, 5, 7, 17, 19, 21, 23]
          else
            if index < 17 then
              ![2, 3, 10, 11, 18, 19, 26, 27]
            else
              ![10, 11, 14, 15, 26, 27, 30, 31]
      else
        if index < 21 then
          if index < 19 then
            ![6, 7, 14, 15, 22, 23, 30, 31]
          else
            if index < 20 then
              ![2, 3, 6, 7, 18, 19, 22, 23]
            else
              ![0, 2, 8, 10, 16, 18, 24, 26]
        else
          if index < 22 then
            ![8, 10, 12, 14, 24, 26, 28, 30]
          else
            if index < 23 then
              ![4, 6, 12, 14, 20, 22, 28, 30]
            else
              ![0, 2, 4, 6, 16, 18, 20, 22]

def cubeVertex (i : Fin 24) : Fin 8 → Fin 32 := bundle_13b5da25e7_cubeVertexTable i.val

def bundle_13b5da25e7_neighborFacetTable : ℕ → (Fin 6 → Fin 24) :=
  fun index =>
    if index < 12 then
      if index < 6 then
        if index < 3 then
          if index < 1 then
            ![3, 1, 8, 10, 11, 9]
          else
            if index < 2 then
              ![0, 2, 12, 14, 15, 13]
            else
              ![3, 1, 16, 18, 19, 17]
        else
          if index < 4 then
            ![0, 2, 20, 22, 23, 21]
          else
            if index < 5 then
              ![20, 12, 8, 16, 7, 5]
            else
              ![21, 13, 9, 17, 4, 6]
      else
        if index < 9 then
          if index < 7 then
            ![22, 14, 10, 18, 7, 5]
          else
            if index < 8 then
              ![23, 15, 11, 19, 4, 6]
            else
              ![20, 12, 11, 9, 0, 4]
        else
          if index < 10 then
            ![21, 13, 8, 10, 0, 5]
          else
            if index < 11 then
              ![22, 14, 11, 9, 0, 6]
            else
              ![23, 15, 8, 10, 0, 7]
    else
      if index < 18 then
        if index < 15 then
          if index < 13 then
            ![8, 16, 15, 13, 1, 4]
          else
            if index < 14 then
              ![9, 17, 12, 14, 1, 5]
            else
              ![10, 18, 15, 13, 1, 6]
        else
          if index < 16 then
            ![11, 19, 12, 14, 1, 7]
          else
            if index < 17 then
              ![20, 12, 19, 17, 2, 4]
            else
              ![21, 13, 16, 18, 2, 5]
      else
        if index < 21 then
          if index < 19 then
            ![22, 14, 19, 17, 2, 6]
          else
            if index < 20 then
              ![23, 15, 16, 18, 2, 7]
            else
              ![8, 16, 23, 21, 3, 4]
        else
          if index < 22 then
            ![9, 17, 20, 22, 3, 5]
          else
            if index < 23 then
              ![10, 18, 23, 21, 3, 6]
            else
              ![11, 19, 20, 22, 3, 7]

def neighborFacet (i : Fin 24) : Fin 6 → Fin 24 := bundle_13b5da25e7_neighborFacetTable i.val

def bundle_13b5da25e7_edgeVertexTable : ℕ → (Fin 2 → Fin 32) :=
  fun index =>
    if index < 40 then
      if index < 20 then
        if index < 10 then
          if index < 5 then
            if index < 2 then
              if index < 1 then
                ![0, 1]
              else
                ![0, 2]
            else
              if index < 3 then
                ![0, 4]
              else
                if index < 4 then
                  ![0, 8]
                else
                  ![0, 16]
          else
            if index < 7 then
              if index < 6 then
                ![1, 3]
              else
                ![1, 5]
            else
              if index < 8 then
                ![1, 9]
              else
                if index < 9 then
                  ![1, 17]
                else
                  ![2, 3]
        else
          if index < 15 then
            if index < 12 then
              if index < 11 then
                ![2, 6]
              else
                ![2, 10]
            else
              if index < 13 then
                ![2, 18]
              else
                if index < 14 then
                  ![3, 7]
                else
                  ![3, 11]
          else
            if index < 17 then
              if index < 16 then
                ![3, 19]
              else
                ![4, 5]
            else
              if index < 18 then
                ![4, 6]
              else
                if index < 19 then
                  ![4, 12]
                else
                  ![4, 20]
      else
        if index < 30 then
          if index < 25 then
            if index < 22 then
              if index < 21 then
                ![5, 7]
              else
                ![5, 13]
            else
              if index < 23 then
                ![5, 21]
              else
                if index < 24 then
                  ![6, 7]
                else
                  ![6, 14]
          else
            if index < 27 then
              if index < 26 then
                ![6, 22]
              else
                ![7, 15]
            else
              if index < 28 then
                ![7, 23]
              else
                if index < 29 then
                  ![8, 9]
                else
                  ![8, 10]
        else
          if index < 35 then
            if index < 32 then
              if index < 31 then
                ![8, 12]
              else
                ![8, 24]
            else
              if index < 33 then
                ![9, 11]
              else
                if index < 34 then
                  ![9, 13]
                else
                  ![9, 25]
          else
            if index < 37 then
              if index < 36 then
                ![10, 11]
              else
                ![10, 14]
            else
              if index < 38 then
                ![10, 26]
              else
                if index < 39 then
                  ![11, 15]
                else
                  ![11, 27]
    else
      if index < 60 then
        if index < 50 then
          if index < 45 then
            if index < 42 then
              if index < 41 then
                ![12, 13]
              else
                ![12, 14]
            else
              if index < 43 then
                ![12, 28]
              else
                if index < 44 then
                  ![13, 15]
                else
                  ![13, 29]
          else
            if index < 47 then
              if index < 46 then
                ![14, 15]
              else
                ![14, 30]
            else
              if index < 48 then
                ![15, 31]
              else
                if index < 49 then
                  ![16, 17]
                else
                  ![16, 18]
        else
          if index < 55 then
            if index < 52 then
              if index < 51 then
                ![16, 20]
              else
                ![16, 24]
            else
              if index < 53 then
                ![17, 19]
              else
                if index < 54 then
                  ![17, 21]
                else
                  ![17, 25]
          else
            if index < 57 then
              if index < 56 then
                ![18, 19]
              else
                ![18, 22]
            else
              if index < 58 then
                ![18, 26]
              else
                if index < 59 then
                  ![19, 23]
                else
                  ![19, 27]
      else
        if index < 70 then
          if index < 65 then
            if index < 62 then
              if index < 61 then
                ![20, 21]
              else
                ![20, 22]
            else
              if index < 63 then
                ![20, 28]
              else
                if index < 64 then
                  ![21, 23]
                else
                  ![21, 29]
          else
            if index < 67 then
              if index < 66 then
                ![22, 23]
              else
                ![22, 30]
            else
              if index < 68 then
                ![23, 31]
              else
                if index < 69 then
                  ![24, 25]
                else
                  ![24, 26]
        else
          if index < 75 then
            if index < 72 then
              if index < 71 then
                ![24, 28]
              else
                ![25, 27]
            else
              if index < 73 then
                ![25, 29]
              else
                if index < 74 then
                  ![26, 27]
                else
                  ![26, 30]
          else
            if index < 77 then
              if index < 76 then
                ![27, 31]
              else
                ![28, 29]
            else
              if index < 78 then
                ![28, 30]
              else
                if index < 79 then
                  ![29, 31]
                else
                  ![30, 31]

def edgeVertex (i : Fin 80) : Fin 2 → Fin 32 := bundle_13b5da25e7_edgeVertexTable i.val

def squareBit (k : Fin 6) (b : Fin 8) : Prop :=
  b.val / (2 ^ (k.val / 2)) % 2 = k.val % 2

instance (k : Fin 6) (b : Fin 8) : Decidable (squareBit k b) :=
  inferInstanceAs (Decidable (b.val / (2 ^ (k.val / 2)) % 2 = k.val % 2))

def slackNumerator (f : Fin 24) (v : Fin 32) : ℤ :=
  -(normal f 0 * q v 0 + normal f 1 * q v 1 + normal f 2 * q v 2 +
    normal f 3 * q v 3 + normal f 4 * q v 4)

end CubicalIndecomposability.Block
end VerificationSource005

/- Original source: CubicalIndecomposability/Block/Evaluations.lean -/
section VerificationSource006


set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

/-- All homogeneous denominators are positive. -/
theorem homogeneous_last_pos : ∀ v : Fin 32, 0 < q v 4 := by decide +kernel

/-- Exact support inequalities and their equality loci for all 24×32 pairs. -/
theorem supportData : ∀ (f : Fin 24) (v : Fin 32),
    0 ≤ slackNumerator f v ∧ (slackNumerator f v = 0 ↔ incident f v) := by
  decide +kernel

end CubicalIndecomposability.Block
end VerificationSource006

/- Original source: CubicalIndecomposability/Block/SeparatingWitness.lean -/
section VerificationSource007


set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

/-- A candidate separating facet; every required property is checked in `Separation`. -/
def separatingWitness (v w : Fin 32) : Fin 24 :=
    if v.val < 16 then
      if v.val < 8 then
        if v.val < 4 then
          if v.val < 2 then
            if v.val < 1 then
              (if incident 0 w then (if incident 8 w then 23 else 8) else 0)
            else
              (if incident 0 w then (if incident 8 w then 15 else 8) else 0)
          else
            if v.val < 3 then
              (if incident 2 w then (if incident 16 w then 23 else 16) else 2)
            else
              (if incident 1 w then (if incident 12 w then 19 else 12) else 1)
        else
          if v.val < 6 then
            if v.val < 5 then
              (if incident 0 w then (if incident 10 w then 23 else 10) else 0)
            else
              (if incident 0 w then (if incident 10 w then 15 else 10) else 0)
          else
            if v.val < 7 then
              (if incident 2 w then (if incident 18 w then 23 else 18) else 2)
            else
              (if incident 1 w then (if incident 14 w then 19 else 14) else 1)
      else
        if v.val < 12 then
          if v.val < 10 then
            if v.val < 9 then
              (if incident 0 w then (if incident 8 w then 21 else 8) else 0)
            else
              (if incident 0 w then (if incident 8 w then 13 else 8) else 0)
          else
            if v.val < 11 then
              (if incident 2 w then (if incident 16 w then 21 else 16) else 2)
            else
              (if incident 1 w then (if incident 12 w then 17 else 12) else 1)
        else
          if v.val < 14 then
            if v.val < 13 then
              (if incident 0 w then (if incident 9 w then 22 else 9) else 0)
            else
              (if incident 0 w then (if incident 9 w then 14 else 9) else 0)
          else
            if v.val < 15 then
              (if incident 2 w then (if incident 17 w then 22 else 17) else 2)
            else
              (if incident 1 w then (if incident 13 w then 18 else 13) else 1)
    else
      if v.val < 24 then
        if v.val < 20 then
          if v.val < 18 then
            if v.val < 17 then
              (if incident 4 w then (if incident 8 w then 23 else 8) else 4)
            else
              (if incident 4 w then (if incident 8 w then 15 else 8) else 4)
          else
            if v.val < 19 then
              (if incident 4 w then (if incident 16 w then 23 else 16) else 4)
            else
              (if incident 4 w then (if incident 12 w then 19 else 12) else 4)
        else
          if v.val < 22 then
            if v.val < 21 then
              (if incident 6 w then (if incident 10 w then 23 else 10) else 6)
            else
              (if incident 6 w then (if incident 10 w then 15 else 10) else 6)
          else
            if v.val < 23 then
              (if incident 6 w then (if incident 18 w then 23 else 18) else 6)
            else
              (if incident 6 w then (if incident 14 w then 19 else 14) else 6)
      else
        if v.val < 28 then
          if v.val < 26 then
            if v.val < 25 then
              (if incident 4 w then (if incident 8 w then 21 else 8) else 4)
            else
              (if incident 4 w then (if incident 8 w then 13 else 8) else 4)
          else
            if v.val < 27 then
              (if incident 4 w then (if incident 16 w then 21 else 16) else 4)
            else
              (if incident 4 w then (if incident 12 w then 17 else 12) else 4)
        else
          if v.val < 30 then
            if v.val < 29 then
              (if incident 5 w then (if incident 9 w then 22 else 9) else 5)
            else
              (if incident 5 w then (if incident 9 w then 14 else 9) else 5)
          else
            if v.val < 31 then
              (if incident 5 w then (if incident 17 w then 22 else 17) else 5)
            else
              (if incident 5 w then (if incident 13 w then 18 else 13) else 5)

end CubicalIndecomposability.Block
end VerificationSource007

/- Original source: CubicalIndecomposability/Block/Separation.lean -/
section VerificationSource008


set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

/-- Distinct labels are strictly separated by one active supporting form. -/
theorem separatingData : ∀ (v w : Fin 32), v ≠ w →
    incident (separatingWitness v w) v ∧ ¬incident (separatingWitness v w) w := by
  decide +kernel

end CubicalIndecomposability.Block
end VerificationSource008

/- Original source: CubicalIndecomposability/Block/CubeData.lean -/
section VerificationSource009


/-! Exact integer arithmetic and finite incidences, checked by Lean's kernel.
`decide +kernel` below proves closed propositions by reduction.  It invokes no native
oracle and introduces no mathematical assumptions.  Row lemmas keep the
kernel reduction and subsequent rebuilds small.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

theorem cubeVertex_injective : ∀ f : Fin 24, Function.Injective (cubeVertex f) := by decide +kernel

theorem cubeVertex_image : ∀ f : Fin 24, Finset.univ.image (cubeVertex f) = facetLabels f := by decide +kernel

theorem neighbor_incidence : ∀ (f : Fin 24) (k : Fin 6) (b : Fin 8),
    incident (neighborFacet f k) (cubeVertex f b) ↔ squareBit k b := by decide +kernel

theorem neighborFacet_ne : ∀ (f : Fin 24) (k : Fin 6), neighborFacet f k ≠ f := by decide +kernel

end CubicalIndecomposability.Block
end VerificationSource009

/- Original source: CubicalIndecomposability/Block/Realization.lean -/
section VerificationSource010





/-!
# The exact data as an ordinary convex polytope

The vertex set is the range of the 32 rational coordinate vectors.  Every
point is proved extreme by supporting forms that separate it from the other
31 points.  Faces below are exposed faces of their real convex hull.
-/

noncomputable section

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

namespace CubicalIndecomposability.Block

/-- Rational affine coordinates obtained by dehomogenizing the integral data. -/
def pQ (v : Fin 32) (i : Fin 4) : ℚ :=
  (q v i.castSucc : ℚ) / (q v 4 : ℚ)

/-- The same point in ordinary real Euclidean four-space. -/
def p (v : Fin 32) : E 4 :=
  WithLp.toLp 2 (fun i : Fin 4 => (q v i.castSucc : ℝ) / (q v 4 : ℝ))

@[simp] theorem p_apply (v : Fin 32) (i : Fin 4) :
    p v i = (q v i.castSucc : ℝ) / (q v 4 : ℝ) := rfl

/-- Negate the source normals so that all inequalities have the form
`offset f ≤ form f x`. -/
def form (f : Fin 24) : E 4 →L[ℝ] ℝ :=
  (-(normal f 0 : ℝ)) • EuclideanSpace.proj 0 +
  (-(normal f 1 : ℝ)) • EuclideanSpace.proj 1 +
  (-(normal f 2 : ℝ)) • EuclideanSpace.proj 2 +
  (-(normal f 3 : ℝ)) • EuclideanSpace.proj 3

def offset (f : Fin 24) : ℝ := (normal f 4 : ℝ)

theorem form_apply (f : Fin 24) (x : E 4) :
    form f x =
      -(normal f 0 : ℝ) * x 0 - (normal f 1 : ℝ) * x 1 -
        (normal f 2 : ℝ) * x 2 - (normal f 3 : ℝ) * x 3 := by
  simp [form] <;> ring

theorem homogeneous_last_real_pos (v : Fin 32) : 0 < (q v 4 : ℝ) := by
  exact_mod_cast homogeneous_last_pos v

theorem support_identity (f : Fin 24) (v : Fin 32) :
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

/-- All 768 exact supporting inequalities. -/
theorem support_nonneg (f : Fin 24) (v : Fin 32) :
    offset f ≤ form f (p v) := by
  have hs : 0 ≤ (slackNumerator f v : ℝ) := by
    exact_mod_cast (supportData f v).1
  have h := div_nonneg hs (homogeneous_last_real_pos v).le
  rw [← support_identity] at h
  exact sub_nonneg.mp h

/-- Equality holds precisely at the eight claimed vertices of a facet. -/
theorem support_eq_iff (f : Fin 24) (v : Fin 32) :
    form f (p v) = offset f ↔ incident f v := by
  have hd : (q v 4 : ℝ) ≠ 0 := ne_of_gt (homogeneous_last_real_pos v)
  rw [← sub_eq_zero, support_identity]
  simpa only [div_eq_zero_iff, hd, or_false, Int.cast_eq_zero] using (supportData f v).2

theorem separatingSupports (v w : Fin 32) (hvw : v ≠ w) :
    ∃ f : Fin 24, form f (p v) = offset f ∧ offset f < form f (p w) := by
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

theorem vertex_mem (v : Fin 32) : p v ∈ polytope.vertices := by
  rw [polytope_vertices]
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

theorem vertices_card : polytope.vertices.card = 32 :=
  polytopeOfSeparatingSupports_card p (by decide) form offset support_nonneg separatingSupports

theorem rational_coordinates : RationalCoordinates polytope := by
  intro x hx i
  rw [polytope_vertices] at hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  refine ⟨pQ v i, ?_⟩
  simp [pQ, p]

/-- The exposed subset belonging to one supporting inequality.  The fact
that this is a facet is proved later from the complete face certificate. -/
def facet (f : Fin 24) : Set (E 4) :=
  minimumFace polytope (form f) (offset f)

theorem facet_isFace (f : Fin 24) : polytope.IsFace (facet f) := by
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

@[simp] theorem vertex_mem_facet_iff (f : Fin 24) (v : Fin 32) :
    p v ∈ facet f ↔ incident f v := by
  change (p v ∈ polytope.toSet ∧ form f (p v) = offset f) ↔ incident f v
  rw [support_eq_iff]
  exact and_iff_right (subset_convexHull ℝ _ (vertex_mem v))

theorem facet_eq_hull (f : Fin 24) :
    facet f = convexHull ℝ (p '' (facetLabels f : Set (Fin 32))) := by
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

end CubicalIndecomposability.Block

end
end VerificationSource010

/- Original source: CubicalIndecomposability/Block/FaceData.lean -/
section VerificationSource011


/-!
# The normalized block's finite face catalogue

The 209 nonempty entries have proposed ranks with counts 32, 80, 72, 24, 1.
Full strict flags and supporting-row intersections supply independently
checked geometric certificates; the generic completeness proof establishes
that no actual face is omitted. Generated by generate_block_faces.py.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable section
namespace CubicalIndecomposability.Block

def bundle_bce6a6d7ae_faceMasks : ℕ → Finset (Fin 32) :=
  fun index =>
    if index < 104 then
      if index < 52 then
        if index < 26 then
          if index < 13 then
            if index < 6 then
              if index < 3 then
                if index < 1 then
                  {0}
                else
                  if index < 2 then
                    {1}
                  else
                    {2}
              else
                if index < 4 then
                  {3}
                else
                  if index < 5 then
                    {4}
                  else
                    {5}
            else
              if index < 9 then
                if index < 7 then
                  {6}
                else
                  if index < 8 then
                    {7}
                  else
                    {8}
              else
                if index < 11 then
                  if index < 10 then
                    {9}
                  else
                    {10}
                else
                  if index < 12 then
                    {11}
                  else
                    {12}
          else
            if index < 19 then
              if index < 16 then
                if index < 14 then
                  {13}
                else
                  if index < 15 then
                    {14}
                  else
                    {15}
              else
                if index < 17 then
                  {16}
                else
                  if index < 18 then
                    {17}
                  else
                    {18}
            else
              if index < 22 then
                if index < 20 then
                  {19}
                else
                  if index < 21 then
                    {20}
                  else
                    {21}
              else
                if index < 24 then
                  if index < 23 then
                    {22}
                  else
                    {23}
                else
                  if index < 25 then
                    {24}
                  else
                    {25}
        else
          if index < 39 then
            if index < 32 then
              if index < 29 then
                if index < 27 then
                  {26}
                else
                  if index < 28 then
                    {27}
                  else
                    {28}
              else
                if index < 30 then
                  {29}
                else
                  if index < 31 then
                    {30}
                  else
                    {31}
            else
              if index < 35 then
                if index < 33 then
                  {0, 1}
                else
                  if index < 34 then
                    {0, 2}
                  else
                    {0, 4}
              else
                if index < 37 then
                  if index < 36 then
                    {0, 8}
                  else
                    {0, 16}
                else
                  if index < 38 then
                    {1, 3}
                  else
                    {1, 5}
          else
            if index < 45 then
              if index < 42 then
                if index < 40 then
                  {1, 9}
                else
                  if index < 41 then
                    {1, 17}
                  else
                    {2, 3}
              else
                if index < 43 then
                  {2, 6}
                else
                  if index < 44 then
                    {2, 10}
                  else
                    {2, 18}
            else
              if index < 48 then
                if index < 46 then
                  {3, 7}
                else
                  if index < 47 then
                    {3, 11}
                  else
                    {3, 19}
              else
                if index < 50 then
                  if index < 49 then
                    {4, 5}
                  else
                    {4, 6}
                else
                  if index < 51 then
                    {4, 12}
                  else
                    {4, 20}
      else
        if index < 78 then
          if index < 65 then
            if index < 58 then
              if index < 55 then
                if index < 53 then
                  {5, 7}
                else
                  if index < 54 then
                    {5, 13}
                  else
                    {5, 21}
              else
                if index < 56 then
                  {6, 7}
                else
                  if index < 57 then
                    {6, 14}
                  else
                    {6, 22}
            else
              if index < 61 then
                if index < 59 then
                  {7, 15}
                else
                  if index < 60 then
                    {7, 23}
                  else
                    {8, 9}
              else
                if index < 63 then
                  if index < 62 then
                    {8, 10}
                  else
                    {8, 12}
                else
                  if index < 64 then
                    {8, 24}
                  else
                    {9, 11}
          else
            if index < 71 then
              if index < 68 then
                if index < 66 then
                  {9, 13}
                else
                  if index < 67 then
                    {9, 25}
                  else
                    {10, 11}
              else
                if index < 69 then
                  {10, 14}
                else
                  if index < 70 then
                    {10, 26}
                  else
                    {11, 15}
            else
              if index < 74 then
                if index < 72 then
                  {11, 27}
                else
                  if index < 73 then
                    {12, 13}
                  else
                    {12, 14}
              else
                if index < 76 then
                  if index < 75 then
                    {12, 28}
                  else
                    {13, 15}
                else
                  if index < 77 then
                    {13, 29}
                  else
                    {14, 15}
        else
          if index < 91 then
            if index < 84 then
              if index < 81 then
                if index < 79 then
                  {14, 30}
                else
                  if index < 80 then
                    {15, 31}
                  else
                    {16, 17}
              else
                if index < 82 then
                  {16, 18}
                else
                  if index < 83 then
                    {16, 20}
                  else
                    {16, 24}
            else
              if index < 87 then
                if index < 85 then
                  {17, 19}
                else
                  if index < 86 then
                    {17, 21}
                  else
                    {17, 25}
              else
                if index < 89 then
                  if index < 88 then
                    {18, 19}
                  else
                    {18, 22}
                else
                  if index < 90 then
                    {18, 26}
                  else
                    {19, 23}
          else
            if index < 97 then
              if index < 94 then
                if index < 92 then
                  {19, 27}
                else
                  if index < 93 then
                    {20, 21}
                  else
                    {20, 22}
              else
                if index < 95 then
                  {20, 28}
                else
                  if index < 96 then
                    {21, 23}
                  else
                    {21, 29}
            else
              if index < 100 then
                if index < 98 then
                  {22, 23}
                else
                  if index < 99 then
                    {22, 30}
                  else
                    {23, 31}
              else
                if index < 102 then
                  if index < 101 then
                    {24, 25}
                  else
                    {24, 26}
                else
                  if index < 103 then
                    {24, 28}
                  else
                    {25, 27}
    else
      if index < 156 then
        if index < 130 then
          if index < 117 then
            if index < 110 then
              if index < 107 then
                if index < 105 then
                  {25, 29}
                else
                  if index < 106 then
                    {26, 27}
                  else
                    {26, 30}
              else
                if index < 108 then
                  {27, 31}
                else
                  if index < 109 then
                    {28, 29}
                  else
                    {28, 30}
            else
              if index < 113 then
                if index < 111 then
                  {29, 31}
                else
                  if index < 112 then
                    {30, 31}
                  else
                    {0, 1, 4, 5}
              else
                if index < 115 then
                  if index < 114 then
                    {0, 1, 8, 9}
                  else
                    {0, 1, 16, 17}
                else
                  if index < 116 then
                    {0, 2, 4, 6}
                  else
                    {0, 2, 8, 10}
          else
            if index < 123 then
              if index < 120 then
                if index < 118 then
                  {0, 2, 16, 18}
                else
                  if index < 119 then
                    {0, 4, 8, 12}
                  else
                    {0, 4, 16, 20}
              else
                if index < 121 then
                  {0, 8, 16, 24}
                else
                  if index < 122 then
                    {1, 3, 5, 7}
                  else
                    {1, 3, 9, 11}
            else
              if index < 126 then
                if index < 124 then
                  {1, 3, 17, 19}
                else
                  if index < 125 then
                    {1, 5, 9, 13}
                  else
                    {1, 5, 17, 21}
              else
                if index < 128 then
                  if index < 127 then
                    {1, 9, 17, 25}
                  else
                    {2, 3, 6, 7}
                else
                  if index < 129 then
                    {2, 3, 10, 11}
                  else
                    {2, 3, 18, 19}
        else
          if index < 143 then
            if index < 136 then
              if index < 133 then
                if index < 131 then
                  {2, 6, 10, 14}
                else
                  if index < 132 then
                    {2, 6, 18, 22}
                  else
                    {2, 10, 18, 26}
              else
                if index < 134 then
                  {3, 7, 11, 15}
                else
                  if index < 135 then
                    {3, 7, 19, 23}
                  else
                    {3, 11, 19, 27}
            else
              if index < 139 then
                if index < 137 then
                  {4, 5, 12, 13}
                else
                  if index < 138 then
                    {4, 5, 20, 21}
                  else
                    {4, 6, 12, 14}
              else
                if index < 141 then
                  if index < 140 then
                    {4, 6, 20, 22}
                  else
                    {4, 12, 20, 28}
                else
                  if index < 142 then
                    {5, 7, 13, 15}
                  else
                    {5, 7, 21, 23}
          else
            if index < 149 then
              if index < 146 then
                if index < 144 then
                  {5, 13, 21, 29}
                else
                  if index < 145 then
                    {6, 7, 14, 15}
                  else
                    {6, 7, 22, 23}
              else
                if index < 147 then
                  {6, 14, 22, 30}
                else
                  if index < 148 then
                    {7, 15, 23, 31}
                  else
                    {8, 9, 12, 13}
            else
              if index < 152 then
                if index < 150 then
                  {8, 9, 24, 25}
                else
                  if index < 151 then
                    {8, 10, 12, 14}
                  else
                    {8, 10, 24, 26}
              else
                if index < 154 then
                  if index < 153 then
                    {8, 12, 24, 28}
                  else
                    {9, 11, 13, 15}
                else
                  if index < 155 then
                    {9, 11, 25, 27}
                  else
                    {9, 13, 25, 29}
      else
        if index < 182 then
          if index < 169 then
            if index < 162 then
              if index < 159 then
                if index < 157 then
                  {10, 11, 14, 15}
                else
                  if index < 158 then
                    {10, 11, 26, 27}
                  else
                    {10, 14, 26, 30}
              else
                if index < 160 then
                  {11, 15, 27, 31}
                else
                  if index < 161 then
                    {12, 13, 28, 29}
                  else
                    {12, 14, 28, 30}
            else
              if index < 165 then
                if index < 163 then
                  {13, 15, 29, 31}
                else
                  if index < 164 then
                    {14, 15, 30, 31}
                  else
                    {16, 17, 18, 19}
              else
                if index < 167 then
                  if index < 166 then
                    {16, 17, 20, 21}
                  else
                    {16, 17, 24, 25}
                else
                  if index < 168 then
                    {16, 18, 20, 22}
                  else
                    {16, 18, 24, 26}
          else
            if index < 175 then
              if index < 172 then
                if index < 170 then
                  {17, 19, 21, 23}
                else
                  if index < 171 then
                    {17, 19, 25, 27}
                  else
                    {18, 19, 22, 23}
              else
                if index < 173 then
                  {18, 19, 26, 27}
                else
                  if index < 174 then
                    {20, 21, 22, 23}
                  else
                    {20, 21, 28, 29}
            else
              if index < 178 then
                if index < 176 then
                  {20, 22, 28, 30}
                else
                  if index < 177 then
                    {21, 23, 29, 31}
                  else
                    {22, 23, 30, 31}
              else
                if index < 180 then
                  if index < 179 then
                    {24, 25, 26, 27}
                  else
                    {24, 25, 28, 29}
                else
                  if index < 181 then
                    {24, 26, 28, 30}
                  else
                    {25, 27, 29, 31}
        else
          if index < 195 then
            if index < 188 then
              if index < 185 then
                if index < 183 then
                  {26, 27, 30, 31}
                else
                  if index < 184 then
                    {28, 29, 30, 31}
                  else
                    {0, 1, 4, 5, 8, 9, 12, 13}
              else
                if index < 186 then
                  {0, 1, 4, 5, 16, 17, 20, 21}
                else
                  if index < 187 then
                    {0, 1, 8, 9, 16, 17, 24, 25}
                  else
                    {0, 2, 4, 6, 8, 10, 12, 14}
            else
              if index < 191 then
                if index < 189 then
                  {0, 2, 4, 6, 16, 18, 20, 22}
                else
                  if index < 190 then
                    {0, 2, 8, 10, 16, 18, 24, 26}
                  else
                    {1, 3, 5, 7, 9, 11, 13, 15}
              else
                if index < 193 then
                  if index < 192 then
                    {1, 3, 5, 7, 17, 19, 21, 23}
                  else
                    {1, 3, 9, 11, 17, 19, 25, 27}
                else
                  if index < 194 then
                    {2, 3, 6, 7, 10, 11, 14, 15}
                  else
                    {2, 3, 6, 7, 18, 19, 22, 23}
          else
            if index < 202 then
              if index < 198 then
                if index < 196 then
                  {2, 3, 10, 11, 18, 19, 26, 27}
                else
                  if index < 197 then
                    {4, 5, 12, 13, 20, 21, 28, 29}
                  else
                    {4, 6, 12, 14, 20, 22, 28, 30}
              else
                if index < 200 then
                  if index < 199 then
                    {5, 7, 13, 15, 21, 23, 29, 31}
                  else
                    {6, 7, 14, 15, 22, 23, 30, 31}
                else
                  if index < 201 then
                    {8, 9, 12, 13, 24, 25, 28, 29}
                  else
                    {8, 10, 12, 14, 24, 26, 28, 30}
            else
              if index < 205 then
                if index < 203 then
                  {9, 11, 13, 15, 25, 27, 29, 31}
                else
                  if index < 204 then
                    {10, 11, 14, 15, 26, 27, 30, 31}
                  else
                    {16, 17, 18, 19, 20, 21, 22, 23}
              else
                if index < 207 then
                  if index < 206 then
                    {16, 17, 18, 19, 24, 25, 26, 27}
                  else
                    {20, 21, 22, 23, 28, 29, 30, 31}
                else
                  if index < 208 then
                    {24, 25, 26, 27, 28, 29, 30, 31}
                  else
                    Finset.univ

def bundle_bce6a6d7ae_flags : ℕ → Fin 5 → Fin 209 :=
  fun index =>
    if index < 104 then
      if index < 52 then
        if index < 26 then
          if index < 13 then
            if index < 6 then
              if index < 3 then
                if index < 1 then
                  ![0, 32, 112, 184, 208]
                else
                  if index < 2 then
                    ![1, 32, 112, 184, 208]
                  else
                    ![2, 33, 115, 187, 208]
              else
                if index < 4 then
                  ![3, 37, 121, 190, 208]
                else
                  if index < 5 then
                    ![4, 34, 112, 184, 208]
                  else
                    ![5, 38, 112, 184, 208]
            else
              if index < 9 then
                if index < 7 then
                  ![6, 42, 115, 187, 208]
                else
                  if index < 8 then
                    ![7, 45, 121, 190, 208]
                  else
                    ![8, 35, 113, 184, 208]
              else
                if index < 11 then
                  if index < 10 then
                    ![9, 39, 113, 184, 208]
                  else
                    ![10, 43, 116, 187, 208]
                else
                  if index < 12 then
                    ![11, 46, 122, 190, 208]
                  else
                    ![12, 50, 118, 184, 208]
          else
            if index < 19 then
              if index < 16 then
                if index < 14 then
                  ![13, 53, 124, 184, 208]
                else
                  if index < 15 then
                    ![14, 56, 130, 187, 208]
                  else
                    ![15, 58, 133, 190, 208]
              else
                if index < 17 then
                  ![16, 36, 114, 185, 208]
                else
                  if index < 18 then
                    ![17, 40, 114, 185, 208]
                  else
                    ![18, 44, 117, 188, 208]
            else
              if index < 22 then
                if index < 20 then
                  ![19, 47, 123, 191, 208]
                else
                  if index < 21 then
                    ![20, 51, 119, 185, 208]
                  else
                    ![21, 54, 125, 185, 208]
              else
                if index < 24 then
                  if index < 23 then
                    ![22, 57, 131, 188, 208]
                  else
                    ![23, 59, 134, 191, 208]
                else
                  if index < 25 then
                    ![24, 63, 120, 186, 208]
                  else
                    ![25, 66, 126, 186, 208]
        else
          if index < 39 then
            if index < 32 then
              if index < 29 then
                if index < 27 then
                  ![26, 69, 132, 189, 208]
                else
                  if index < 28 then
                    ![27, 71, 135, 192, 208]
                  else
                    ![28, 74, 140, 196, 208]
              else
                if index < 30 then
                  ![29, 76, 143, 196, 208]
                else
                  if index < 31 then
                    ![30, 78, 146, 197, 208]
                  else
                    ![31, 79, 147, 198, 208]
            else
              if index < 35 then
                if index < 33 then
                  ![0, 32, 112, 184, 208]
                else
                  if index < 34 then
                    ![0, 33, 115, 187, 208]
                  else
                    ![0, 34, 112, 184, 208]
              else
                if index < 37 then
                  if index < 36 then
                    ![0, 35, 113, 184, 208]
                  else
                    ![0, 36, 114, 185, 208]
                else
                  if index < 38 then
                    ![1, 37, 121, 190, 208]
                  else
                    ![1, 38, 112, 184, 208]
          else
            if index < 45 then
              if index < 42 then
                if index < 40 then
                  ![1, 39, 113, 184, 208]
                else
                  if index < 41 then
                    ![1, 40, 114, 185, 208]
                  else
                    ![2, 41, 127, 193, 208]
              else
                if index < 43 then
                  ![2, 42, 115, 187, 208]
                else
                  if index < 44 then
                    ![2, 43, 116, 187, 208]
                  else
                    ![2, 44, 117, 188, 208]
            else
              if index < 48 then
                if index < 46 then
                  ![3, 45, 121, 190, 208]
                else
                  if index < 47 then
                    ![3, 46, 122, 190, 208]
                  else
                    ![3, 47, 123, 191, 208]
              else
                if index < 50 then
                  if index < 49 then
                    ![4, 48, 112, 184, 208]
                  else
                    ![4, 49, 115, 187, 208]
                else
                  if index < 51 then
                    ![4, 50, 118, 184, 208]
                  else
                    ![4, 51, 119, 185, 208]
      else
        if index < 78 then
          if index < 65 then
            if index < 58 then
              if index < 55 then
                if index < 53 then
                  ![5, 52, 121, 190, 208]
                else
                  if index < 54 then
                    ![5, 53, 124, 184, 208]
                  else
                    ![5, 54, 125, 185, 208]
              else
                if index < 56 then
                  ![6, 55, 127, 193, 208]
                else
                  if index < 57 then
                    ![6, 56, 130, 187, 208]
                  else
                    ![6, 57, 131, 188, 208]
            else
              if index < 61 then
                if index < 59 then
                  ![7, 58, 133, 190, 208]
                else
                  if index < 60 then
                    ![7, 59, 134, 191, 208]
                  else
                    ![8, 60, 113, 184, 208]
              else
                if index < 63 then
                  if index < 62 then
                    ![8, 61, 116, 187, 208]
                  else
                    ![8, 62, 118, 184, 208]
                else
                  if index < 64 then
                    ![8, 63, 120, 186, 208]
                  else
                    ![9, 64, 122, 190, 208]
          else
            if index < 71 then
              if index < 68 then
                if index < 66 then
                  ![9, 65, 124, 184, 208]
                else
                  if index < 67 then
                    ![9, 66, 126, 186, 208]
                  else
                    ![10, 67, 128, 193, 208]
              else
                if index < 69 then
                  ![10, 68, 130, 187, 208]
                else
                  if index < 70 then
                    ![10, 69, 132, 189, 208]
                  else
                    ![11, 70, 133, 190, 208]
            else
              if index < 74 then
                if index < 72 then
                  ![11, 71, 135, 192, 208]
                else
                  if index < 73 then
                    ![12, 72, 136, 184, 208]
                  else
                    ![12, 73, 138, 187, 208]
              else
                if index < 76 then
                  if index < 75 then
                    ![12, 74, 140, 196, 208]
                  else
                    ![13, 75, 141, 190, 208]
                else
                  if index < 77 then
                    ![13, 76, 143, 196, 208]
                  else
                    ![14, 77, 144, 193, 208]
        else
          if index < 91 then
            if index < 84 then
              if index < 81 then
                if index < 79 then
                  ![14, 78, 146, 197, 208]
                else
                  if index < 80 then
                    ![15, 79, 147, 198, 208]
                  else
                    ![16, 80, 114, 185, 208]
              else
                if index < 82 then
                  ![16, 81, 117, 188, 208]
                else
                  if index < 83 then
                    ![16, 82, 119, 185, 208]
                  else
                    ![16, 83, 120, 186, 208]
            else
              if index < 87 then
                if index < 85 then
                  ![17, 84, 123, 191, 208]
                else
                  if index < 86 then
                    ![17, 85, 125, 185, 208]
                  else
                    ![17, 86, 126, 186, 208]
              else
                if index < 89 then
                  if index < 88 then
                    ![18, 87, 129, 194, 208]
                  else
                    ![18, 88, 131, 188, 208]
                else
                  if index < 90 then
                    ![18, 89, 132, 189, 208]
                  else
                    ![19, 90, 134, 191, 208]
          else
            if index < 97 then
              if index < 94 then
                if index < 92 then
                  ![19, 91, 135, 192, 208]
                else
                  if index < 93 then
                    ![20, 92, 137, 185, 208]
                  else
                    ![20, 93, 139, 188, 208]
              else
                if index < 95 then
                  ![20, 94, 140, 196, 208]
                else
                  if index < 96 then
                    ![21, 95, 142, 191, 208]
                  else
                    ![21, 96, 143, 196, 208]
            else
              if index < 100 then
                if index < 98 then
                  ![22, 97, 145, 194, 208]
                else
                  if index < 99 then
                    ![22, 98, 146, 197, 208]
                  else
                    ![23, 99, 147, 198, 208]
              else
                if index < 102 then
                  if index < 101 then
                    ![24, 100, 149, 186, 208]
                  else
                    ![24, 101, 151, 189, 208]
                else
                  if index < 103 then
                    ![24, 102, 152, 200, 208]
                  else
                    ![25, 103, 154, 192, 208]
    else
      if index < 156 then
        if index < 130 then
          if index < 117 then
            if index < 110 then
              if index < 107 then
                if index < 105 then
                  ![25, 104, 155, 200, 208]
                else
                  if index < 106 then
                    ![26, 105, 157, 195, 208]
                  else
                    ![26, 106, 158, 201, 208]
              else
                if index < 108 then
                  ![27, 107, 159, 202, 208]
                else
                  if index < 109 then
                    ![28, 108, 160, 196, 208]
                  else
                    ![28, 109, 161, 197, 208]
            else
              if index < 113 then
                if index < 111 then
                  ![29, 110, 162, 198, 208]
                else
                  if index < 112 then
                    ![30, 111, 163, 199, 208]
                  else
                    ![0, 32, 112, 184, 208]
              else
                if index < 115 then
                  if index < 114 then
                    ![0, 32, 113, 184, 208]
                  else
                    ![0, 32, 114, 185, 208]
                else
                  if index < 116 then
                    ![0, 33, 115, 187, 208]
                  else
                    ![0, 33, 116, 187, 208]
          else
            if index < 123 then
              if index < 120 then
                if index < 118 then
                  ![0, 33, 117, 188, 208]
                else
                  if index < 119 then
                    ![0, 34, 118, 184, 208]
                  else
                    ![0, 34, 119, 185, 208]
              else
                if index < 121 then
                  ![0, 35, 120, 186, 208]
                else
                  if index < 122 then
                    ![1, 37, 121, 190, 208]
                  else
                    ![1, 37, 122, 190, 208]
            else
              if index < 126 then
                if index < 124 then
                  ![1, 37, 123, 191, 208]
                else
                  if index < 125 then
                    ![1, 38, 124, 184, 208]
                  else
                    ![1, 38, 125, 185, 208]
              else
                if index < 128 then
                  if index < 127 then
                    ![1, 39, 126, 186, 208]
                  else
                    ![2, 41, 127, 193, 208]
                else
                  if index < 129 then
                    ![2, 41, 128, 193, 208]
                  else
                    ![2, 41, 129, 194, 208]
        else
          if index < 143 then
            if index < 136 then
              if index < 133 then
                if index < 131 then
                  ![2, 42, 130, 187, 208]
                else
                  if index < 132 then
                    ![2, 42, 131, 188, 208]
                  else
                    ![2, 43, 132, 189, 208]
              else
                if index < 134 then
                  ![3, 45, 133, 190, 208]
                else
                  if index < 135 then
                    ![3, 45, 134, 191, 208]
                  else
                    ![3, 46, 135, 192, 208]
            else
              if index < 139 then
                if index < 137 then
                  ![4, 48, 136, 184, 208]
                else
                  if index < 138 then
                    ![4, 48, 137, 185, 208]
                  else
                    ![4, 49, 138, 187, 208]
              else
                if index < 141 then
                  if index < 140 then
                    ![4, 49, 139, 188, 208]
                  else
                    ![4, 50, 140, 196, 208]
                else
                  if index < 142 then
                    ![5, 52, 141, 190, 208]
                  else
                    ![5, 52, 142, 191, 208]
          else
            if index < 149 then
              if index < 146 then
                if index < 144 then
                  ![5, 53, 143, 196, 208]
                else
                  if index < 145 then
                    ![6, 55, 144, 193, 208]
                  else
                    ![6, 55, 145, 194, 208]
              else
                if index < 147 then
                  ![6, 56, 146, 197, 208]
                else
                  if index < 148 then
                    ![7, 58, 147, 198, 208]
                  else
                    ![8, 60, 148, 184, 208]
            else
              if index < 152 then
                if index < 150 then
                  ![8, 60, 149, 186, 208]
                else
                  if index < 151 then
                    ![8, 61, 150, 187, 208]
                  else
                    ![8, 61, 151, 189, 208]
              else
                if index < 154 then
                  if index < 153 then
                    ![8, 62, 152, 200, 208]
                  else
                    ![9, 64, 153, 190, 208]
                else
                  if index < 155 then
                    ![9, 64, 154, 192, 208]
                  else
                    ![9, 65, 155, 200, 208]
      else
        if index < 182 then
          if index < 169 then
            if index < 162 then
              if index < 159 then
                if index < 157 then
                  ![10, 67, 156, 193, 208]
                else
                  if index < 158 then
                    ![10, 67, 157, 195, 208]
                  else
                    ![10, 68, 158, 201, 208]
              else
                if index < 160 then
                  ![11, 70, 159, 202, 208]
                else
                  if index < 161 then
                    ![12, 72, 160, 196, 208]
                  else
                    ![12, 73, 161, 197, 208]
            else
              if index < 165 then
                if index < 163 then
                  ![13, 75, 162, 198, 208]
                else
                  if index < 164 then
                    ![14, 77, 163, 199, 208]
                  else
                    ![16, 80, 164, 204, 208]
              else
                if index < 167 then
                  if index < 166 then
                    ![16, 80, 165, 185, 208]
                  else
                    ![16, 80, 166, 186, 208]
                else
                  if index < 168 then
                    ![16, 81, 167, 188, 208]
                  else
                    ![16, 81, 168, 189, 208]
          else
            if index < 175 then
              if index < 172 then
                if index < 170 then
                  ![17, 84, 169, 191, 208]
                else
                  if index < 171 then
                    ![17, 84, 170, 192, 208]
                  else
                    ![18, 87, 171, 194, 208]
              else
                if index < 173 then
                  ![18, 87, 172, 195, 208]
                else
                  if index < 174 then
                    ![20, 92, 173, 204, 208]
                  else
                    ![20, 92, 174, 196, 208]
            else
              if index < 178 then
                if index < 176 then
                  ![20, 93, 175, 197, 208]
                else
                  if index < 177 then
                    ![21, 95, 176, 198, 208]
                  else
                    ![22, 97, 177, 199, 208]
              else
                if index < 180 then
                  if index < 179 then
                    ![24, 100, 178, 205, 208]
                  else
                    ![24, 100, 179, 200, 208]
                else
                  if index < 181 then
                    ![24, 101, 180, 201, 208]
                  else
                    ![25, 103, 181, 202, 208]
        else
          if index < 195 then
            if index < 188 then
              if index < 185 then
                if index < 183 then
                  ![26, 105, 182, 203, 208]
                else
                  if index < 184 then
                    ![28, 108, 183, 206, 208]
                  else
                    ![0, 32, 112, 184, 208]
              else
                if index < 186 then
                  ![0, 32, 112, 185, 208]
                else
                  if index < 187 then
                    ![0, 32, 113, 186, 208]
                  else
                    ![0, 33, 115, 187, 208]
            else
              if index < 191 then
                if index < 189 then
                  ![0, 33, 115, 188, 208]
                else
                  if index < 190 then
                    ![0, 33, 116, 189, 208]
                  else
                    ![1, 37, 121, 190, 208]
              else
                if index < 193 then
                  if index < 192 then
                    ![1, 37, 121, 191, 208]
                  else
                    ![1, 37, 122, 192, 208]
                else
                  if index < 194 then
                    ![2, 41, 127, 193, 208]
                  else
                    ![2, 41, 127, 194, 208]
          else
            if index < 202 then
              if index < 198 then
                if index < 196 then
                  ![2, 41, 128, 195, 208]
                else
                  if index < 197 then
                    ![4, 48, 136, 196, 208]
                  else
                    ![4, 49, 138, 197, 208]
              else
                if index < 200 then
                  if index < 199 then
                    ![5, 52, 141, 198, 208]
                  else
                    ![6, 55, 144, 199, 208]
                else
                  if index < 201 then
                    ![8, 60, 148, 200, 208]
                  else
                    ![8, 61, 150, 201, 208]
            else
              if index < 205 then
                if index < 203 then
                  ![9, 64, 153, 202, 208]
                else
                  if index < 204 then
                    ![10, 67, 156, 203, 208]
                  else
                    ![16, 80, 164, 204, 208]
              else
                if index < 207 then
                  if index < 206 then
                    ![16, 80, 164, 205, 208]
                  else
                    ![20, 92, 173, 206, 208]
                else
                  if index < 208 then
                    ![24, 100, 178, 207, 208]
                  else
                    ![0, 32, 112, 184, 208]

def bundle_bce6a6d7ae_supports : ℕ → Finset (Fin 24) :=
  fun index =>
    if index < 104 then
      if index < 52 then
        if index < 26 then
          if index < 13 then
            if index < 6 then
              if index < 3 then
                if index < 1 then
                  {0, 8, 23}
                else
                  if index < 2 then
                    {0, 8, 15}
                  else
                    {2, 16, 23}
              else
                if index < 4 then
                  {1, 12, 19}
                else
                  if index < 5 then
                    {0, 10, 23}
                  else
                    {0, 10, 15}
            else
              if index < 9 then
                if index < 7 then
                  {2, 18, 23}
                else
                  if index < 8 then
                    {1, 14, 19}
                  else
                    {0, 8, 21}
              else
                if index < 11 then
                  if index < 10 then
                    {0, 8, 13}
                  else
                    {2, 16, 21}
                else
                  if index < 12 then
                    {1, 12, 17}
                  else
                    {0, 9, 22}
          else
            if index < 19 then
              if index < 16 then
                if index < 14 then
                  {0, 9, 14}
                else
                  if index < 15 then
                    {2, 17, 22}
                  else
                    {1, 13, 18}
              else
                if index < 17 then
                  {4, 8, 23}
                else
                  if index < 18 then
                    {4, 8, 15}
                  else
                    {4, 16, 23}
            else
              if index < 22 then
                if index < 20 then
                  {4, 12, 19}
                else
                  if index < 21 then
                    {6, 10, 23}
                  else
                    {6, 10, 15}
              else
                if index < 24 then
                  if index < 23 then
                    {6, 18, 23}
                  else
                    {6, 14, 19}
                else
                  if index < 25 then
                    {4, 8, 21}
                  else
                    {4, 8, 13}
        else
          if index < 39 then
            if index < 32 then
              if index < 29 then
                if index < 27 then
                  {4, 16, 21}
                else
                  if index < 28 then
                    {4, 12, 17}
                  else
                    {5, 9, 22}
              else
                if index < 30 then
                  {5, 9, 14}
                else
                  if index < 31 then
                    {5, 17, 22}
                  else
                    {5, 13, 18}
            else
              if index < 35 then
                if index < 33 then
                  {0, 8, 11}
                else
                  if index < 34 then
                    {3, 20, 23}
                  else
                    {0, 23}
              else
                if index < 37 then
                  if index < 36 then
                    {0, 20}
                  else
                    {8, 23}
                else
                  if index < 38 then
                    {1, 12, 15}
                  else
                    {0, 15}
          else
            if index < 45 then
              if index < 42 then
                if index < 40 then
                  {0, 12}
                else
                  if index < 41 then
                    {8, 15}
                  else
                    {2, 16, 19}
              else
                if index < 43 then
                  {2, 23}
                else
                  if index < 44 then
                    {2, 20}
                  else
                    {16, 23}
            else
              if index < 48 then
                if index < 46 then
                  {1, 19}
                else
                  if index < 47 then
                    {1, 16}
                  else
                    {12, 19}
              else
                if index < 50 then
                  if index < 49 then
                    {0, 10, 11}
                  else
                    {3, 22, 23}
                else
                  if index < 51 then
                    {0, 22}
                  else
                    {10, 23}
      else
        if index < 78 then
          if index < 65 then
            if index < 58 then
              if index < 55 then
                if index < 53 then
                  {1, 14, 15}
                else
                  if index < 54 then
                    {0, 14}
                  else
                    {10, 15}
              else
                if index < 56 then
                  {2, 18, 19}
                else
                  if index < 57 then
                    {2, 22}
                  else
                    {18, 23}
            else
              if index < 61 then
                if index < 59 then
                  {1, 18}
                else
                  if index < 60 then
                    {14, 19}
                  else
                    {0, 8, 9}
              else
                if index < 63 then
                  if index < 62 then
                    {3, 20, 21}
                  else
                    {0, 21}
                else
                  if index < 64 then
                    {8, 21}
                  else
                    {1, 12, 13}
          else
            if index < 71 then
              if index < 68 then
                if index < 66 then
                  {0, 13}
                else
                  if index < 67 then
                    {8, 13}
                  else
                    {2, 16, 17}
              else
                if index < 69 then
                  {2, 21}
                else
                  if index < 70 then
                    {16, 21}
                  else
                    {1, 17}
            else
              if index < 74 then
                if index < 72 then
                  {12, 17}
                else
                  if index < 73 then
                    {0, 9, 10}
                  else
                    {3, 21, 22}
              else
                if index < 76 then
                  if index < 75 then
                    {9, 22}
                  else
                    {1, 13, 14}
                else
                  if index < 77 then
                    {9, 14}
                  else
                    {2, 17, 18}
        else
          if index < 91 then
            if index < 84 then
              if index < 81 then
                if index < 79 then
                  {17, 22}
                else
                  if index < 80 then
                    {13, 18}
                  else
                    {4, 11}
              else
                if index < 82 then
                  {4, 23}
                else
                  if index < 83 then
                    {7, 11, 23}
                  else
                    {4, 8, 20}
            else
              if index < 87 then
                if index < 85 then
                  {4, 15}
                else
                  if index < 86 then
                    {7, 11, 15}
                  else
                    {4, 8, 12}
              else
                if index < 89 then
                  if index < 88 then
                    {4, 19}
                  else
                    {7, 19, 23}
                else
                  if index < 90 then
                    {4, 16, 20}
                  else
                    {7, 15, 19}
          else
            if index < 97 then
              if index < 94 then
                if index < 92 then
                  {4, 12, 16}
                else
                  if index < 93 then
                    {6, 11}
                  else
                    {6, 23}
              else
                if index < 95 then
                  {6, 10, 22}
                else
                  if index < 96 then
                    {6, 15}
                  else
                    {6, 10, 14}
            else
              if index < 100 then
                if index < 98 then
                  {6, 19}
                else
                  if index < 99 then
                    {6, 18, 22}
                  else
                    {6, 14, 18}
              else
                if index < 102 then
                  if index < 101 then
                    {4, 9}
                  else
                    {4, 21}
                else
                  if index < 103 then
                    {5, 9, 21}
                  else
                    {4, 13}
    else
      if index < 156 then
        if index < 130 then
          if index < 117 then
            if index < 110 then
              if index < 107 then
                if index < 105 then
                  {5, 9, 13}
                else
                  if index < 106 then
                    {4, 17}
                  else
                    {5, 17, 21}
              else
                if index < 108 then
                  {5, 13, 17}
                else
                  if index < 109 then
                    {5, 10}
                  else
                    {5, 22}
            else
              if index < 113 then
                if index < 111 then
                  {5, 14}
                else
                  if index < 112 then
                    {5, 18}
                  else
                    {0, 11}
              else
                if index < 115 then
                  if index < 114 then
                    {0, 8}
                  else
                    {8, 11}
                else
                  if index < 116 then
                    {3, 23}
                  else
                    {3, 20}
          else
            if index < 123 then
              if index < 120 then
                if index < 118 then
                  {20, 23}
                else
                  if index < 119 then
                    {0, 3}
                  else
                    {11, 23}
              else
                if index < 121 then
                  {8, 20}
                else
                  if index < 122 then
                    {1, 15}
                  else
                    {1, 12}
            else
              if index < 126 then
                if index < 124 then
                  {12, 15}
                else
                  if index < 125 then
                    {0, 1}
                  else
                    {11, 15}
              else
                if index < 128 then
                  if index < 127 then
                    {8, 12}
                  else
                    {2, 19}
                else
                  if index < 129 then
                    {2, 16}
                  else
                    {16, 19}
        else
          if index < 143 then
            if index < 136 then
              if index < 133 then
                if index < 131 then
                  {2, 3}
                else
                  if index < 132 then
                    {19, 23}
                  else
                    {16, 20}
              else
                if index < 134 then
                  {1, 2}
                else
                  if index < 135 then
                    {15, 19}
                  else
                    {12, 16}
            else
              if index < 139 then
                if index < 137 then
                  {0, 10}
                else
                  if index < 138 then
                    {10, 11}
                  else
                    {3, 22}
              else
                if index < 141 then
                  if index < 140 then
                    {22, 23}
                  else
                    {10, 22}
                else
                  if index < 142 then
                    {1, 14}
                  else
                    {14, 15}
          else
            if index < 149 then
              if index < 146 then
                if index < 144 then
                  {10, 14}
                else
                  if index < 145 then
                    {2, 18}
                  else
                    {18, 19}
              else
                if index < 147 then
                  {18, 22}
                else
                  if index < 148 then
                    {14, 18}
                  else
                    {0, 9}
            else
              if index < 152 then
                if index < 150 then
                  {8, 9}
                else
                  if index < 151 then
                    {3, 21}
                  else
                    {20, 21}
              else
                if index < 154 then
                  if index < 153 then
                    {9, 21}
                  else
                    {1, 13}
                else
                  if index < 155 then
                    {12, 13}
                  else
                    {9, 13}
      else
        if index < 182 then
          if index < 169 then
            if index < 162 then
              if index < 159 then
                if index < 157 then
                  {2, 17}
                else
                  if index < 158 then
                    {16, 17}
                  else
                    {17, 21}
              else
                if index < 160 then
                  {13, 17}
                else
                  if index < 161 then
                    {9, 10}
                  else
                    {21, 22}
            else
              if index < 165 then
                if index < 163 then
                  {13, 14}
                else
                  if index < 164 then
                    {17, 18}
                  else
                    {4, 7}
              else
                if index < 167 then
                  if index < 166 then
                    {7, 11}
                  else
                    {4, 8}
                else
                  if index < 168 then
                    {7, 23}
                  else
                    {4, 20}
          else
            if index < 175 then
              if index < 172 then
                if index < 170 then
                  {7, 15}
                else
                  if index < 171 then
                    {4, 12}
                  else
                    {7, 19}
              else
                if index < 173 then
                  {4, 16}
                else
                  if index < 174 then
                    {6, 7}
                  else
                    {6, 10}
            else
              if index < 178 then
                if index < 176 then
                  {6, 22}
                else
                  if index < 177 then
                    {6, 14}
                  else
                    {6, 18}
              else
                if index < 180 then
                  if index < 179 then
                    {4, 5}
                  else
                    {5, 9}
                else
                  if index < 181 then
                    {5, 21}
                  else
                    {5, 13}
        else
          if index < 195 then
            if index < 188 then
              if index < 185 then
                if index < 183 then
                  {5, 17}
                else
                  if index < 184 then
                    {5, 6}
                  else
                    {0}
              else
                if index < 186 then
                  {11}
                else
                  if index < 187 then
                    {8}
                  else
                    {3}
            else
              if index < 191 then
                if index < 189 then
                  {23}
                else
                  if index < 190 then
                    {20}
                  else
                    {1}
              else
                if index < 193 then
                  if index < 192 then
                    {15}
                  else
                    {12}
                else
                  if index < 194 then
                    {2}
                  else
                    {19}
          else
            if index < 202 then
              if index < 198 then
                if index < 196 then
                  {16}
                else
                  if index < 197 then
                    {10}
                  else
                    {22}
              else
                if index < 200 then
                  if index < 199 then
                    {14}
                  else
                    {18}
                else
                  if index < 201 then
                    {9}
                  else
                    {21}
            else
              if index < 205 then
                if index < 203 then
                  {13}
                else
                  if index < 204 then
                    {17}
                  else
                    {7}
              else
                if index < 207 then
                  if index < 206 then
                    {4}
                  else
                    {6}
                else
                  if index < 208 then
                    {5}
                  else
                    ∅

def bundle_bce6a6d7ae_lowerFaces : ℕ → Finset (Fin 209) :=
  fun index =>
    if index < 104 then
      if index < 52 then
        if index < 26 then
          if index < 13 then
            if index < 6 then
              if index < 3 then
                if index < 1 then
                  ∅
                else
                  if index < 2 then
                    ∅
                  else
                    ∅
              else
                if index < 4 then
                  ∅
                else
                  if index < 5 then
                    ∅
                  else
                    ∅
            else
              if index < 9 then
                if index < 7 then
                  ∅
                else
                  if index < 8 then
                    ∅
                  else
                    ∅
              else
                if index < 11 then
                  if index < 10 then
                    ∅
                  else
                    ∅
                else
                  if index < 12 then
                    ∅
                  else
                    ∅
          else
            if index < 19 then
              if index < 16 then
                if index < 14 then
                  ∅
                else
                  if index < 15 then
                    ∅
                  else
                    ∅
              else
                if index < 17 then
                  ∅
                else
                  if index < 18 then
                    ∅
                  else
                    ∅
            else
              if index < 22 then
                if index < 20 then
                  ∅
                else
                  if index < 21 then
                    ∅
                  else
                    ∅
              else
                if index < 24 then
                  if index < 23 then
                    ∅
                  else
                    ∅
                else
                  if index < 25 then
                    ∅
                  else
                    ∅
        else
          if index < 39 then
            if index < 32 then
              if index < 29 then
                if index < 27 then
                  ∅
                else
                  if index < 28 then
                    ∅
                  else
                    ∅
              else
                if index < 30 then
                  ∅
                else
                  if index < 31 then
                    ∅
                  else
                    ∅
            else
              if index < 35 then
                if index < 33 then
                  {0, 1}
                else
                  if index < 34 then
                    {0, 2}
                  else
                    {0, 4}
              else
                if index < 37 then
                  if index < 36 then
                    {0, 8}
                  else
                    {0, 16}
                else
                  if index < 38 then
                    {1, 3}
                  else
                    {1, 5}
          else
            if index < 45 then
              if index < 42 then
                if index < 40 then
                  {1, 9}
                else
                  if index < 41 then
                    {1, 17}
                  else
                    {2, 3}
              else
                if index < 43 then
                  {2, 6}
                else
                  if index < 44 then
                    {2, 10}
                  else
                    {2, 18}
            else
              if index < 48 then
                if index < 46 then
                  {3, 7}
                else
                  if index < 47 then
                    {3, 11}
                  else
                    {3, 19}
              else
                if index < 50 then
                  if index < 49 then
                    {4, 5}
                  else
                    {4, 6}
                else
                  if index < 51 then
                    {4, 12}
                  else
                    {4, 20}
      else
        if index < 78 then
          if index < 65 then
            if index < 58 then
              if index < 55 then
                if index < 53 then
                  {5, 7}
                else
                  if index < 54 then
                    {5, 13}
                  else
                    {5, 21}
              else
                if index < 56 then
                  {6, 7}
                else
                  if index < 57 then
                    {6, 14}
                  else
                    {6, 22}
            else
              if index < 61 then
                if index < 59 then
                  {7, 15}
                else
                  if index < 60 then
                    {7, 23}
                  else
                    {8, 9}
              else
                if index < 63 then
                  if index < 62 then
                    {8, 10}
                  else
                    {8, 12}
                else
                  if index < 64 then
                    {8, 24}
                  else
                    {9, 11}
          else
            if index < 71 then
              if index < 68 then
                if index < 66 then
                  {9, 13}
                else
                  if index < 67 then
                    {9, 25}
                  else
                    {10, 11}
              else
                if index < 69 then
                  {10, 14}
                else
                  if index < 70 then
                    {10, 26}
                  else
                    {11, 15}
            else
              if index < 74 then
                if index < 72 then
                  {11, 27}
                else
                  if index < 73 then
                    {12, 13}
                  else
                    {12, 14}
              else
                if index < 76 then
                  if index < 75 then
                    {12, 28}
                  else
                    {13, 15}
                else
                  if index < 77 then
                    {13, 29}
                  else
                    {14, 15}
        else
          if index < 91 then
            if index < 84 then
              if index < 81 then
                if index < 79 then
                  {14, 30}
                else
                  if index < 80 then
                    {15, 31}
                  else
                    {16, 17}
              else
                if index < 82 then
                  {16, 18}
                else
                  if index < 83 then
                    {16, 20}
                  else
                    {16, 24}
            else
              if index < 87 then
                if index < 85 then
                  {17, 19}
                else
                  if index < 86 then
                    {17, 21}
                  else
                    {17, 25}
              else
                if index < 89 then
                  if index < 88 then
                    {18, 19}
                  else
                    {18, 22}
                else
                  if index < 90 then
                    {18, 26}
                  else
                    {19, 23}
          else
            if index < 97 then
              if index < 94 then
                if index < 92 then
                  {19, 27}
                else
                  if index < 93 then
                    {20, 21}
                  else
                    {20, 22}
              else
                if index < 95 then
                  {20, 28}
                else
                  if index < 96 then
                    {21, 23}
                  else
                    {21, 29}
            else
              if index < 100 then
                if index < 98 then
                  {22, 23}
                else
                  if index < 99 then
                    {22, 30}
                  else
                    {23, 31}
              else
                if index < 102 then
                  if index < 101 then
                    {24, 25}
                  else
                    {24, 26}
                else
                  if index < 103 then
                    {24, 28}
                  else
                    {25, 27}
    else
      if index < 156 then
        if index < 130 then
          if index < 117 then
            if index < 110 then
              if index < 107 then
                if index < 105 then
                  {25, 29}
                else
                  if index < 106 then
                    {26, 27}
                  else
                    {26, 30}
              else
                if index < 108 then
                  {27, 31}
                else
                  if index < 109 then
                    {28, 29}
                  else
                    {28, 30}
            else
              if index < 113 then
                if index < 111 then
                  {29, 31}
                else
                  if index < 112 then
                    {30, 31}
                  else
                    {32, 34, 38, 48}
              else
                if index < 115 then
                  if index < 114 then
                    {32, 35, 39, 60}
                  else
                    {32, 36, 40, 80}
                else
                  if index < 116 then
                    {33, 34, 42, 49}
                  else
                    {33, 35, 43, 61}
          else
            if index < 123 then
              if index < 120 then
                if index < 118 then
                  {33, 36, 44, 81}
                else
                  if index < 119 then
                    {34, 35, 50, 62}
                  else
                    {34, 36, 51, 82}
              else
                if index < 121 then
                  {35, 36, 63, 83}
                else
                  if index < 122 then
                    {37, 38, 45, 52}
                  else
                    {37, 39, 46, 64}
            else
              if index < 126 then
                if index < 124 then
                  {37, 40, 47, 84}
                else
                  if index < 125 then
                    {38, 39, 53, 65}
                  else
                    {38, 40, 54, 85}
              else
                if index < 128 then
                  if index < 127 then
                    {39, 40, 66, 86}
                  else
                    {41, 42, 45, 55}
                else
                  if index < 129 then
                    {41, 43, 46, 67}
                  else
                    {41, 44, 47, 87}
        else
          if index < 143 then
            if index < 136 then
              if index < 133 then
                if index < 131 then
                  {42, 43, 56, 68}
                else
                  if index < 132 then
                    {42, 44, 57, 88}
                  else
                    {43, 44, 69, 89}
              else
                if index < 134 then
                  {45, 46, 58, 70}
                else
                  if index < 135 then
                    {45, 47, 59, 90}
                  else
                    {46, 47, 71, 91}
            else
              if index < 139 then
                if index < 137 then
                  {48, 50, 53, 72}
                else
                  if index < 138 then
                    {48, 51, 54, 92}
                  else
                    {49, 50, 56, 73}
              else
                if index < 141 then
                  if index < 140 then
                    {49, 51, 57, 93}
                  else
                    {50, 51, 74, 94}
                else
                  if index < 142 then
                    {52, 53, 58, 75}
                  else
                    {52, 54, 59, 95}
          else
            if index < 149 then
              if index < 146 then
                if index < 144 then
                  {53, 54, 76, 96}
                else
                  if index < 145 then
                    {55, 56, 58, 77}
                  else
                    {55, 57, 59, 97}
              else
                if index < 147 then
                  {56, 57, 78, 98}
                else
                  if index < 148 then
                    {58, 59, 79, 99}
                  else
                    {60, 62, 65, 72}
            else
              if index < 152 then
                if index < 150 then
                  {60, 63, 66, 100}
                else
                  if index < 151 then
                    {61, 62, 68, 73}
                  else
                    {61, 63, 69, 101}
              else
                if index < 154 then
                  if index < 153 then
                    {62, 63, 74, 102}
                  else
                    {64, 65, 70, 75}
                else
                  if index < 155 then
                    {64, 66, 71, 103}
                  else
                    {65, 66, 76, 104}
      else
        if index < 182 then
          if index < 169 then
            if index < 162 then
              if index < 159 then
                if index < 157 then
                  {67, 68, 70, 77}
                else
                  if index < 158 then
                    {67, 69, 71, 105}
                  else
                    {68, 69, 78, 106}
              else
                if index < 160 then
                  {70, 71, 79, 107}
                else
                  if index < 161 then
                    {72, 74, 76, 108}
                  else
                    {73, 74, 78, 109}
            else
              if index < 165 then
                if index < 163 then
                  {75, 76, 79, 110}
                else
                  if index < 164 then
                    {77, 78, 79, 111}
                  else
                    {80, 81, 84, 87}
              else
                if index < 167 then
                  if index < 166 then
                    {80, 82, 85, 92}
                  else
                    {80, 83, 86, 100}
                else
                  if index < 168 then
                    {81, 82, 88, 93}
                  else
                    {81, 83, 89, 101}
          else
            if index < 175 then
              if index < 172 then
                if index < 170 then
                  {84, 85, 90, 95}
                else
                  if index < 171 then
                    {84, 86, 91, 103}
                  else
                    {87, 88, 90, 97}
              else
                if index < 173 then
                  {87, 89, 91, 105}
                else
                  if index < 174 then
                    {92, 93, 95, 97}
                  else
                    {92, 94, 96, 108}
            else
              if index < 178 then
                if index < 176 then
                  {93, 94, 98, 109}
                else
                  if index < 177 then
                    {95, 96, 99, 110}
                  else
                    {97, 98, 99, 111}
              else
                if index < 180 then
                  if index < 179 then
                    {100, 101, 103, 105}
                  else
                    {100, 102, 104, 108}
                else
                  if index < 181 then
                    {101, 102, 106, 109}
                  else
                    {103, 104, 107, 110}
        else
          if index < 195 then
            if index < 188 then
              if index < 185 then
                if index < 183 then
                  {105, 106, 107, 111}
                else
                  if index < 184 then
                    {108, 109, 110, 111}
                  else
                    {112, 113, 118, 124, 136, 148}
              else
                if index < 186 then
                  {112, 114, 119, 125, 137, 165}
                else
                  if index < 187 then
                    {113, 114, 120, 126, 149, 166}
                  else
                    {115, 116, 118, 130, 138, 150}
            else
              if index < 191 then
                if index < 189 then
                  {115, 117, 119, 131, 139, 167}
                else
                  if index < 190 then
                    {116, 117, 120, 132, 151, 168}
                  else
                    {121, 122, 124, 133, 141, 153}
              else
                if index < 193 then
                  if index < 192 then
                    {121, 123, 125, 134, 142, 169}
                  else
                    {122, 123, 126, 135, 154, 170}
                else
                  if index < 194 then
                    {127, 128, 130, 133, 144, 156}
                  else
                    {127, 129, 131, 134, 145, 171}
          else
            if index < 202 then
              if index < 198 then
                if index < 196 then
                  {128, 129, 132, 135, 157, 172}
                else
                  if index < 197 then
                    {136, 137, 140, 143, 160, 174}
                  else
                    {138, 139, 140, 146, 161, 175}
              else
                if index < 200 then
                  if index < 199 then
                    {141, 142, 143, 147, 162, 176}
                  else
                    {144, 145, 146, 147, 163, 177}
                else
                  if index < 201 then
                    {148, 149, 152, 155, 160, 179}
                  else
                    {150, 151, 152, 158, 161, 180}
            else
              if index < 205 then
                if index < 203 then
                  {153, 154, 155, 159, 162, 181}
                else
                  if index < 204 then
                    {156, 157, 158, 159, 163, 182}
                  else
                    {164, 165, 167, 169, 171, 173}
              else
                if index < 207 then
                  if index < 206 then
                    {164, 166, 168, 170, 172, 178}
                  else
                    {173, 174, 175, 176, 177, 183}
                else
                  if index < 208 then
                    {178, 179, 180, 181, 182, 183}
                  else
                    {184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207}

def bundle_bce6a6d7ae_cubeCodes : ℕ → Fin 27 → Fin 209 :=
  fun index =>
    if index < 12 then
      if index < 6 then
        if index < 3 then
          if index < 1 then
            ![184, 118, 124, 113, 35, 39, 136, 50, 53, 112, 34, 38, 32, 0, 1, 48, 4, 5, 148, 62, 65, 60, 8, 9, 72, 12, 13]
          else
            if index < 2 then
              ![190, 124, 133, 122, 39, 46, 141, 53, 58, 121, 38, 45, 37, 1, 3, 52, 5, 7, 153, 65, 70, 64, 9, 11, 75, 13, 15]
            else
              ![193, 130, 133, 128, 43, 46, 144, 56, 58, 127, 42, 45, 41, 2, 3, 55, 6, 7, 156, 68, 70, 67, 10, 11, 77, 14, 15]
        else
          if index < 4 then
            ![187, 118, 130, 116, 35, 43, 138, 50, 56, 115, 34, 42, 33, 0, 2, 49, 4, 6, 150, 62, 68, 61, 8, 10, 73, 12, 14]
          else
            if index < 5 then
              ![205, 168, 170, 166, 83, 86, 172, 89, 91, 164, 81, 84, 80, 16, 17, 87, 18, 19, 178, 101, 103, 100, 24, 25, 105, 26, 27]
            else
              ![207, 180, 181, 179, 102, 104, 182, 106, 107, 178, 101, 103, 100, 24, 25, 105, 26, 27, 183, 109, 110, 108, 28, 29, 111, 30, 31]
      else
        if index < 9 then
          if index < 7 then
            ![206, 175, 176, 174, 94, 96, 177, 98, 99, 173, 93, 95, 92, 20, 21, 97, 22, 23, 183, 109, 110, 108, 28, 29, 111, 30, 31]
          else
            if index < 8 then
              ![204, 167, 169, 165, 82, 85, 171, 88, 90, 164, 81, 84, 80, 16, 17, 87, 18, 19, 173, 93, 95, 92, 20, 21, 97, 22, 23]
            else
              ![186, 120, 126, 114, 36, 40, 149, 63, 66, 113, 35, 39, 32, 0, 1, 60, 8, 9, 166, 83, 86, 80, 16, 17, 100, 24, 25]
        else
          if index < 10 then
            ![200, 152, 155, 149, 63, 66, 160, 74, 76, 148, 62, 65, 60, 8, 9, 72, 12, 13, 179, 102, 104, 100, 24, 25, 108, 28, 29]
          else
            if index < 11 then
              ![196, 140, 143, 137, 51, 54, 160, 74, 76, 136, 50, 53, 48, 4, 5, 72, 12, 13, 174, 94, 96, 92, 20, 21, 108, 28, 29]
            else
              ![185, 119, 125, 114, 36, 40, 137, 51, 54, 112, 34, 38, 32, 0, 1, 48, 4, 5, 165, 82, 85, 80, 16, 17, 92, 20, 21]
    else
      if index < 18 then
        if index < 15 then
          if index < 13 then
            ![192, 126, 135, 123, 40, 47, 154, 66, 71, 122, 39, 46, 37, 1, 3, 64, 9, 11, 170, 86, 91, 84, 17, 19, 103, 25, 27]
          else
            if index < 14 then
              ![202, 155, 159, 154, 66, 71, 162, 76, 79, 153, 65, 70, 64, 9, 11, 75, 13, 15, 181, 104, 107, 103, 25, 27, 110, 29, 31]
            else
              ![198, 143, 147, 142, 54, 59, 162, 76, 79, 141, 53, 58, 52, 5, 7, 75, 13, 15, 176, 96, 99, 95, 21, 23, 110, 29, 31]
        else
          if index < 16 then
            ![191, 125, 134, 123, 40, 47, 142, 54, 59, 121, 38, 45, 37, 1, 3, 52, 5, 7, 169, 85, 90, 84, 17, 19, 95, 21, 23]
          else
            if index < 17 then
              ![195, 132, 135, 129, 44, 47, 157, 69, 71, 128, 43, 46, 41, 2, 3, 67, 10, 11, 172, 89, 91, 87, 18, 19, 105, 26, 27]
            else
              ![203, 158, 159, 157, 69, 71, 163, 78, 79, 156, 68, 70, 67, 10, 11, 77, 14, 15, 182, 106, 107, 105, 26, 27, 111, 30, 31]
      else
        if index < 21 then
          if index < 19 then
            ![199, 146, 147, 145, 57, 59, 163, 78, 79, 144, 56, 58, 55, 6, 7, 77, 14, 15, 177, 98, 99, 97, 22, 23, 111, 30, 31]
          else
            if index < 20 then
              ![194, 131, 134, 129, 44, 47, 145, 57, 59, 127, 42, 45, 41, 2, 3, 55, 6, 7, 171, 88, 90, 87, 18, 19, 97, 22, 23]
            else
              ![189, 120, 132, 117, 36, 44, 151, 63, 69, 116, 35, 43, 33, 0, 2, 61, 8, 10, 168, 83, 89, 81, 16, 18, 101, 24, 26]
        else
          if index < 22 then
            ![201, 152, 158, 151, 63, 69, 161, 74, 78, 150, 62, 68, 61, 8, 10, 73, 12, 14, 180, 102, 106, 101, 24, 26, 109, 28, 30]
          else
            if index < 23 then
              ![197, 140, 146, 139, 51, 57, 161, 74, 78, 138, 50, 56, 49, 4, 6, 73, 12, 14, 175, 94, 98, 93, 20, 22, 109, 28, 30]
            else
              ![188, 119, 131, 117, 36, 44, 139, 51, 57, 115, 34, 42, 33, 0, 2, 49, 4, 6, 167, 82, 88, 81, 16, 18, 93, 20, 22]

def faceMask (i : Fin 209) : Finset (Fin 32) := bundle_bce6a6d7ae_faceMasks i.val

def faceRank (i : Fin 209) : Fin 5 :=
  if i.val < 32 then 0 else
  if i.val < 112 then 1 else
  if i.val < 184 then 2 else
  if i.val < 208 then 3 else 4

def faceFlag (i : Fin 209) : Fin 5 → Fin 209 := bundle_bce6a6d7ae_flags i.val

def supportRows (i : Fin 209) : Finset (Fin 24) := bundle_bce6a6d7ae_supports i.val

def lowerFacets (i : Fin 209) : Finset (Fin 209) := bundle_bce6a6d7ae_lowerFaces i.val

def codeFace (f : Fin 24) : Fin 27 → Fin 209 := bundle_bce6a6d7ae_cubeCodes f.val

end CubicalIndecomposability.Block
end
end VerificationSource011

/- Original source: CubicalIndecomposability/Block/FaceDataChecks/Pairing.lean -/

end -- global noncomputable section
end -- global public section
