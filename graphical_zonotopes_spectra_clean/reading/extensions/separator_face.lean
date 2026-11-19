module

public import Verified.PolyhedralFace
import all Verified.PolyhedralFace
import all verified.main

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
# The separator relation space as the span of an actual minimal face

This optional extension combines Theorem 5.4's exact tight-kernel isomorphism
with the ordinary minimal-face theorem for a finite inequality cone. The ambient
cone below is literally the supermodular cone in `graphicalFunctionSpace G`.
-/

noncomputable section
open scoped Classical

namespace GraphicalZonotopes.Separator

section Ordered

variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- The canonical tight face through the positively glued graphical function.
The theorem below proves that it is the actual least convex face containing it. -/
def gluedMinimalFace (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) : Set (graphicalFunctionSpace G) :=
  Polyhedral.tightFace (contextRow G) (functionEquiv h (gluedCoordinates f z lam))

/-- The exact relation-space interpretation of the actual minimal face.

The hypotheses are the literal private-kernel equalities of Theorem 5.4. The
conclusion includes universal minimality among all convex extreme subsets of
the genuine supermodular cone, a linear isomorphism of its span with the response
relation space, and the corresponding affine-dimension identity.
-/
theorem positive_response_gluing_minimal_face (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ)
    (hlam : ∀ j, 0 < lam j) (hf : ∀ j, f j ≠ 0)
    (hi : ∀ j r, 0 ≤ (rowData h).internal j r (f j))
    (hprivate : ∀ j, (rowData h).privateKernelSpace f (conditionalMin h f) j =
      Submodule.span ℝ {f j})
    (hclose : (rowData h).Closure (conditionalMin h f) z lam) :
    IsLeast {F : Set (graphicalFunctionSpace G) |
        Convex ℝ F ∧ IsExtreme ℝ {q | Supermodular q.1} F ∧
          functionEquiv h (gluedCoordinates f z lam) ∈ F}
        (gluedMinimalFace h f z lam) ∧
      Nonempty ((Submodule.span ℝ (gluedMinimalFace h f z lam)) ≃ₗ[ℝ]
        LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))) ∧
      Module.finrank ℝ (vectorSpan ℝ (gluedMinimalFace h f z lam)) =
        Module.finrank ℝ (LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))) := by
  have hline : ∀ j g, (rowData h).PrivateKernel f (conditionalMin h f) j g →
      ∃ c : ℝ, g = c • f j :=
    fun j => (Gluing.privateKernelSpace_eq_span_iff
      (rowData h) f (conditionalMin h f) j).mp (hprivate j)
  have hp : Polyhedral.Nonnegative (contextRow G)
      (functionEquiv h (gluedCoordinates f z lam)) :=
    (supermodular_iff_boundarySlacks_nonnegative G _).mp
      (glued_supermodular h f z lam hlam hf hi hline hclose)
  have hcone : Polyhedral.nonnegativeCone (contextRow G) =
      {q : graphicalFunctionSpace G | Supermodular q.1} := by
    ext q
    exact (supermodular_iff_boundarySlacks_nonnegative G q).symm
  have hleast := Polyhedral.tightFace_isLeast hp
  rw [hcone] at hleast
  have hequiv : (Submodule.span ℝ (gluedMinimalFace h f z lam)) ≃ₗ[ℝ]
      LinearMap.ker ((rowData h).relationLinear (conditionalMin h f)) :=
    (LinearEquiv.ofEq _ _ (Polyhedral.span_tightFace_eq_tightKernel hp)).trans
      (graphicalTightRelationEquiv h f z lam hlam hf hi hline hclose)
  refine ⟨hleast, ⟨hequiv⟩, ?_⟩
  change Module.finrank ℝ (vectorSpan ℝ
    (Polyhedral.tightFace (contextRow G) (functionEquiv h (gluedCoordinates f z lam)))) = _
  rw [Polyhedral.vectorSpan_tightFace_eq_tightKernel hp]
  exact graphical_tight_finrank_eq_relation_finrank h f z lam hlam hf hi hline hclose

end Ordered

/-- The ordinary-face interpretation on every finite vertex type. The order
used to orient unordered edges is chosen internally, exactly as in the finite
version of Theorem 5.4; it is not additional structure on the input graph. -/
theorem positive_response_gluing_minimal_face_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ {J : Type*} [Fintype J] [DecidableEq J]
      {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}
      (h : Partition G B A)
      (f : ∀ j, privateIndex G B A j → ℝ)
      (z : boundaryIndex G B → ℝ) (lam : J → ℝ),
      (∀ j, 0 < lam j) → (∀ j, f j ≠ 0) →
      (∀ j r, 0 ≤ (rowData h).internal j r (f j)) →
      (∀ j, (rowData h).privateKernelSpace f (conditionalMin h f) j =
        Submodule.span ℝ {f j}) →
      (rowData h).Closure (conditionalMin h f) z lam →
      IsLeast {F : Set (graphicalFunctionSpace G) |
          Convex ℝ F ∧ IsExtreme ℝ {q | Supermodular q.1} F ∧
            functionEquiv h (gluedCoordinates f z lam) ∈ F}
          (gluedMinimalFace h f z lam) ∧
        Nonempty ((Submodule.span ℝ (gluedMinimalFace h f z lam)) ≃ₗ[ℝ]
          LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))) ∧
        Module.finrank ℝ (vectorSpan ℝ (gluedMinimalFace h f z lam)) =
          Module.finrank ℝ (LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))) := by
  letI : LinearOrder V := finiteVertexOrder V
  intro J _ _ G B A h f z lam hlam hf hi hprivate hclose
  exact positive_response_gluing_minimal_face h f z lam hlam hf hi hprivate hclose

end GraphicalZonotopes.Separator
