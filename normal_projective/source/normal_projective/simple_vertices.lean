module
public import normal_projective.halfspace_faces
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.SetTheory.Cardinal.Finite
/-! # Simple halfspace vertices and all feasible maximal tight systems -/
@[expose] public section
noncomputable section
open Set Matrix
namespace NormalProjective
variable {d : ℕ} {ι : Type*} [Fintype ι]

def IsSimpleHalfspace (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ) : Prop :=
  ∀ x ∈ (halfspaceRegion f h).extremePoints ℝ, Nat.card (ActiveFacet f h x) = d

theorem tight_minor_unique
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ) (I : Fin d ↪ ι)
    (hdet : (facetCoefficientMatrix (fun j => f (I j))).det ≠ 0)
    {x y : Fin d → ℝ}
    (hx : ∀ j, f (I j) x = h (I j)) (hy : ∀ j, f (I j) y = h (I j)) :
    x = y := by
  apply Matrix.mulVec_injective_of_det_ne_zero hdet
  rw [facetCoefficientMatrix_mulVec, facetCoefficientMatrix_mulVec]
  funext j
  exact (hx j).trans (hy j).symm

theorem nonsingular_tight_minor_is_vertex
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ) (I : Fin d ↪ ι)
    (hdet : (facetCoefficientMatrix (fun j => f (I j))).det ≠ 0)
    {x : Fin d → ℝ} (hx : x ∈ halfspaceRegion f h)
    (hI : ∀ j, f (I j) x = h (I j)) :
    x ∈ (halfspaceRegion f h).extremePoints ℝ := by
  have heq : tightFace f h (Set.range I) = {x} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      exact tight_minor_unique f h I hdet
        (fun j => hy.2 (I j) ⟨j, rfl⟩) hI
    · rintro rfl
      exact ⟨hx, fun i ⟨j, hij⟩ => hij ▸ hI j⟩
  have hf := (tightFace_isExposed f h (Set.range I)).isExtreme
  rw [heq] at hf
  exact isExtreme_singleton.mp hf

theorem simple_active_minor_spans
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hs : IsSimpleHalfspace f h) {x : Fin d → ℝ}
    (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ)
    (I : Fin d ↪ ι) (hI : ∀ j, f (I j) x = h (I j)) :
    (Set.range I = activeFacetSet f h x) ∧
      (facetCoefficientMatrix (fun j => f (I j))).det ≠ 0 := by
  classical
  let a : Fin d → ActiveFacet f h x := fun j => ⟨I j, hI j⟩
  have ha : Function.Injective a := by
    intro i j hij
    exact I.injective (congrArg Subtype.val hij)
  have hcard : Nat.card (Fin d) = Nat.card (ActiveFacet f h x) := by
    rw [hs x hx]
    simp
  have hsurj : Function.Surjective a :=
    ((Nat.bijective_iff_injective_and_card a).mpr ⟨ha, hcard⟩).2
  have hrange : Set.range I = activeFacetSet f h x := by
    ext i
    constructor
    · rintro ⟨j, rfl⟩
      exact hI j
    · intro hi
      obtain ⟨j, hj⟩ := hsurj ⟨i, hi⟩
      exact ⟨j, congrArg Subtype.val hj⟩
  refine ⟨hrange, ?_⟩
  apply facetCoefficientMatrix_det_ne_zero
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · have hr : Set.range (fun j => f (I j)) =
        Set.range (fun i : ActiveFacet f h x => f i.val) := by
      ext z
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨a j, rfl⟩
      · rintro ⟨i, rfl⟩
        obtain ⟨j, rfl⟩ := hsurj i
        exact ⟨j, rfl⟩
    rw [hr, active_normals_span_dual f h hx]
  · simp [Subspace.dual_finrank_eq]

/-- In a compact simple polytope every feasible set of d tight facets is a vertex,
its active matrix is nonsingular, and every other inequality is strict. -/
theorem simple_feasible_minor
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hs : IsSimpleHalfspace f h)
    (I : Fin d ↪ ι) {x : Fin d → ℝ} (hx : x ∈ halfspaceRegion f h)
    (hI : ∀ j, f (I j) x = h (I j)) :
    x ∈ (halfspaceRegion f h).extremePoints ℝ ∧
      (facetCoefficientMatrix (fun j => f (I j))).det ≠ 0 ∧
      ∀ i, i ∉ Set.range I → f i x < h i := by
  have hF := tightFace_isExposed f h (Set.range I)
  have hxF : x ∈ tightFace f h (Set.range I) :=
    ⟨hx, fun i ⟨j, hij⟩ => hij ▸ hI j⟩
  obtain ⟨v, hv⟩ := (hF.isCompact hc).extremePoints_nonempty ⟨x, hxF⟩
  have hvP := hF.isExtreme.extremePoints_subset_extremePoints hv
  have hvI : ∀ j, f (I j) v = h (I j) := fun j => hv.1.2 (I j) ⟨j, rfl⟩
  obtain ⟨hrange, hdet⟩ := simple_active_minor_spans f h hs hvP I hvI
  have hxv : x = v := tight_minor_unique f h I hdet hI hvI
  subst v
  refine ⟨hvP, hdet, fun i hi => ?_⟩
  apply lt_of_le_of_ne (hx i)
  intro heq
  apply hi
  rw [hrange]
  exact heq

end NormalProjective

