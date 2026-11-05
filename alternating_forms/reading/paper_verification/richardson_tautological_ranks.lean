module

public import PaperVerification.RichardsonSchemeComparison
public import PaperVerification.AlternatingFormsAmbientSectionFrames

/-!
# The Richardson minors on the actual ambient tautological bundle

The rows in the determinantal equations are actual sections of the
incidence-kernel bundle.  Their ambient coordinate projections give the
literal rank minors used to define the independent Richardson scheme.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n : ℕ}

/-- Projection of the actual ambient tautological bundle to any chosen
coordinate subspace.  The two flags use the prefix and suffix choices. -/
def ambientTautologicalProjection (C : Set (Fin n)) :
    tautologicalKernel (t := t) (emptyAlternatingTuple (K := K) (n := n)) ⟶
      SheafModulePowers.structurePower (ambientGrassmannian (K := K) t n) C :=
  Pi.lift fun c ↦ tautologicalCoordinateFunctional emptyAlternatingTuple c.val

/-- Each component is the literal ambient coordinate of the tautological
inclusion, so this is the usual coordinate-flag projection. -/
theorem ambientTautologicalProjection_coordinate (C : Set (Fin n)) (c : C) :
    ambientTautologicalProjection (K := K) (t := t) C ≫
      Pi.π (fun _ : C ↦ SheafOfModules.unit
        (ambientGrassmannian (K := K) t n).ringCatSheaf) c =
      tautologicalCoordinateFunctional (t := t) emptyAlternatingTuple c.val := by
  unfold ambientTautologicalProjection
  exact Pi.lift_comp_π _ c

/-- A minor of a coordinate projection of the actual local tautological
frame, with arbitrary selected rows and columns. -/
def ambientTautologicalRankMinor (p : PluckerIndex (t + 2) n) (q : ℕ)
    (rows : Fin q → Fin (t + 2)) (cols : Fin q → Fin n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    Γ(ambientGrassmannian (K := K) t n, U) :=
  Matrix.det fun i j ↦ tautologicalSectionCoordinates emptyAlternatingTuple U
    (tautologicalRowSection p emptyAlternatingTuple U hU (rows i)) (cols j)

/-- Exact coefficient comparison for every rank minor, on every subopen
of the actual ambient chart.  No passage to reduced schemes or field-valued
points occurs. -/
theorem ambientTautologicalRankMinor_eq (p : PluckerIndex (t + 2) n) (q : ℕ)
    (rows : Fin q → Fin (t + 2)) (cols : Fin q → Fin n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    ambientTautologicalRankMinor p q rows cols U hU =
      tautologicalLocalPolynomialHom p emptyAlternatingTuple U hU
        ((pluckerChartMatrix p).submatrix rows cols).det := by
  unfold ambientTautologicalRankMinor
  simp only [tautologicalRowSection_coordinates, tautologicalLocalMatrix]
  exact ((tautologicalLocalPolynomialHom p emptyAlternatingTuple U hU).map_det
    ((pluckerChartMatrix p).submatrix rows cols)).symm

end PaperVerification.AlternatingForms
