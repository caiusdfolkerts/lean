import verification_bundle
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Module

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
