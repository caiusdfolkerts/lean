module

public import Continuation.CycleBounds.FanNumerical
public import Continuation.CycleBounds.ArrangementGeometry

@[expose] public section

/-! # Geometric dimensions of actual fan-arrangement strata

The right side of Proposition6.8 is the dimension of the affine hull of the
literal lifted arrangement stratum. The active-kernel formula is proved by an
explicit linear equivalence and relative openness of the cell.
-/

noncomputable section
namespace PaperVerification.ToricGeometry.SmoothCompleteFan
open Unimodular.CycleBounds Unimodular.SeriesParallel
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (F : SmoothCompleteFan n)

def thomsenForms (u : F.rays) : Ambient n →ₗ[ℝ] ℝ :=
  dotProductEquiv ℝ (Fin n) (embed n u.val)

/-- The actual lifted periodic-arrangement stratum of the covector representative. -/
def thomsenStratum (θ : Module.Dual ℝ (Ambient n)) : Set (Ambient n) :=
  integerStratum F.thomsenForms ((dotProductEquiv ℝ (Fin n)).symm θ)

/-- Its ordinary affine-geometric dimension. -/
def thomsenStratumDimension (θ : Module.Dual ℝ (Ambient n)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (F.thomsenStratum θ)).direction

theorem thomsenForms_swap (x : Ambient n) (u : F.rays) :
    dotProductEquiv ℝ (Fin n) x (F.thomsenRayFamily u) = F.thomsenForms u x := by
  change dotProduct x (embed n u.val) = dotProduct (embed n u.val) x
  exact dotProduct_comm _ _

theorem thomsenForms_center (θ : Module.Dual ℝ (Ambient n)) (u : F.rays) :
    F.thomsenForms u ((dotProductEquiv ℝ (Fin n)).symm θ) = θ (F.thomsenRayFamily u) := by
  rw [← F.thomsenForms_swap, LinearEquiv.apply_symm_apply]

/-- Every representative in a lifted stratum gives exactly the same Thomsen
coefficients on every ray. -/
theorem thomsenCoefficients_eq_of_mem_stratum (θ : Module.Dual ℝ (Ambient n))
    {x : Ambient n} (hx : x ∈ F.thomsenStratum θ) (u : F.rays) :
    F.thomsenCoefficients (dotProductEquiv ℝ (Fin n) x) u.val =
      F.thomsenCoefficients θ u.val := by
  have h := ceil_eq_of_mem_integerStratum F.thomsenForms hx u
  rw [F.thomsenForms_center] at h
  simpa only [thomsenCoefficients, ← F.thomsenForms_swap, thomsenRayFamily] using h

/-- The covector and parameter-coordinate descriptions of the active tangent
space agree by an actual linear equivalence. -/
def thomsenDirectionEquiv (θ : Module.Dual ℝ (Ambient n)) :
    integerStratumDirection F.thomsenForms ((dotProductEquiv ℝ (Fin n)).symm θ) ≃ₗ[ℝ]
      F.thomsenDirection θ where
  toFun d := ⟨dotProductEquiv ℝ (Fin n) d.val, by
    intro u hu
    rw [F.thomsenForms_swap]
    exact d.property u (by rwa [F.thomsenForms_center])⟩
  invFun φ := ⟨(dotProductEquiv ℝ (Fin n)).symm φ.val, by
    intro u hu
    rw [F.thomsenForms_center] at hu
    rw [← F.thomsenForms_swap, LinearEquiv.apply_symm_apply]
    exact φ.property u hu⟩
  left_inv d := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ _
  right_inv φ := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ _
  map_add' d e := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r d := by apply Subtype.ext; exact map_smul _ _ _

/-- The graph proof's active-kernel dimension is exactly the geometric stratum
 dimension, including every lower-dimensional and zero-dimensional cell. -/
theorem thomsenDirection_finrank (θ : Module.Dual ℝ (Ambient n)) :
    Module.finrank ℝ (F.thomsenDirection θ) = F.thomsenStratumDimension θ := by
  rw [thomsenStratumDimension, thomsenStratum, finrank_integerStratum]
  exact (F.thomsenDirectionEquiv θ).finrank_eq.symm

/-- The dimension does not depend on which integral translate of a torus
stratum is chosen as its lift. -/
theorem thomsenStratumDimension_add_lattice (θ : Module.Dual ℝ (Ambient n))
    (m : Lattice n) :
    F.thomsenStratumDimension (θ + dotProductEquiv ℝ (Fin n) (embed n m)) =
      F.thomsenStratumDimension θ := by
  unfold thomsenStratumDimension thomsenStratum
  rw [map_add, LinearEquiv.symm_apply_apply]
  apply finrank_integerStratum_add_of_integral
  intro u
  refine ⟨integerPairing u.val m, ?_⟩
  exact normalRay_pairing_lattice u.val m

/-- The numerical wall conclusion with the actual geometric stratum dimension. -/
theorem thomsen_wall_slack_le_stratum_dimension {V : Type*} [Fintype V]
    (G : IncidenceGraph V F.rays) (hG : G.edges = Set.univ) (hK : ¬G.HasK4Minor)
    (δ : Lattice n →ₗ[ℤ] (V → ℤ)) (hinj : Function.Injective δ)
    (hδ : ∀ u : F.rays, δ u.val = Pi.single (G.source u) 1 - Pi.single (G.target u) 1)
    (θ : Module.Dual ℝ (Ambient n)) (s : F.fullCones) (w : F.rays) :
    F.thomsenCoefficients θ w.val +
      integerPairing w.val (F.cartierLatticePoint (F.thomsenCoefficients θ) s) ≤
        (F.thomsenStratumDimension θ : ℤ) := by
  rw [← F.thomsenDirection_finrank]
  exact F.thomsen_wall_slack_le_direction_integral G hG hK δ hinj hδ θ s w

#print axioms thomsenDirection_finrank
#print axioms thomsen_wall_slack_le_stratum_dimension
end PaperVerification.ToricGeometry.SmoothCompleteFan
