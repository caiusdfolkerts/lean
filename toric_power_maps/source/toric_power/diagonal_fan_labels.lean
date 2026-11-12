module

public import ToricPower.DiagonalCellWeights
public import ToricPower.DivisorWeightGeometry
public import ToricPower.FanRayPrimitive
public import ToricPower.GeometricCore
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Fan coordinates, diagonal labels, and the actual toric product

These are the literal fan-character coordinates and divisor coefficient
labels used by the global cellular sheaf complex. Keeping the pure labels
and the scheme product separate from the sheaf matrix construction lets
its local geometric comparisons use only their mathematical dependencies.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical BigOperators

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V} (fan : Fan latticeMap)

/-- Coordinates and a finite enumeration exist for every actual fan;
these choices add no geometric hypothesis. -/
theorem exists_fanArrangementCoordinates :
    ∃ n s : ℕ, Nonempty (Module.Basis (Fin n) ℤ (N →+ ℤ)) ∧
      Nonempty (Fin s ≃ fan.Ray) := by
  letI : Fintype fan.Ray := Fintype.ofFinite _
  exact ⟨Module.finrank ℤ N, Fintype.card fan.Ray,
    ⟨latticeCharacterBasis fan.lattice⟩, ⟨(Fintype.equivFin fan.Ray).symm⟩⟩

variable {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ))
  (rays : Fin s ≃ fan.Ray)

/-- The integer arrangement matrix consists of the actual primitive-ray
pairings in the chosen full character-lattice basis. -/
def fanArrangementMatrix : Fin s → Fin n → ℤ :=
  fun ρ j => basis j (fanRayPrimitiveGenerator fan (rays ρ))

theorem fanArrangementMatrix_character (a : Fin n → ℤ) (ρ : fan.Ray) :
    rayPairing (fanArrangementMatrix fan basis rays) a (rays.symm ρ) =
      basis.equivFun.symm a (fanRayPrimitiveGenerator fan ρ) := by
  simp [fanArrangementMatrix, rayPairing, Module.Basis.equivFun_symm_apply,
    AddMonoidHom.smul_apply, mul_comm]

/-- The left divisor is literally the paper's `L(-x)`. -/
def diagonalLeftCoefficients {d : ℕ}
    (c : NormalizedCell (fanArrangementMatrix fan basis rays) d) : fan.Ray → ℤ :=
  fun ρ => -reflectedCeiling (fanArrangementMatrix fan basis rays) c.val (rays.symm ρ)

/-- The right divisor is literally the paper's `L(x)`. -/
def diagonalRightCoefficients {d : ℕ}
    (c : NormalizedCell (fanArrangementMatrix fan basis rays) d) : fan.Ray → ℤ :=
  fun ρ => -c.val.val.1 (.inl (rays.symm ρ))

theorem diagonalLeftCoefficients_at_point {d : ℕ}
    (c : NormalizedCell (fanArrangementMatrix fan basis rays) d)
    {x : Fin n → ℝ}
    (hx : x ∈ IntegralArrangement.cell
      (augmentedForms (fanArrangementMatrix fan basis rays)) c.val.val.1 c.val.val.2)
    (ρ : fan.Ray) :
    diagonalLeftCoefficients fan basis rays c ρ =
      -⌈-integralRowForm (fanArrangementMatrix fan basis rays) (rays.symm ρ) x⌉ := by
  rw [diagonalLeftCoefficients, reflectedCeiling_eq_ceil _ _ hx]

theorem diagonalRightCoefficients_at_point {d : ℕ}
    (c : NormalizedCell (fanArrangementMatrix fan basis rays) d)
    {x : Fin n → ℝ}
    (hx : x ∈ IntegralArrangement.cell
      (augmentedForms (fanArrangementMatrix fan basis rays)) c.val.val.1 c.val.val.2)
    (ρ : fan.Ray) :
    diagonalRightCoefficients fan basis rays c ρ =
      -⌈integralRowForm (fanArrangementMatrix fan basis rays) (rays.symm ρ) x⌉ := by
  unfold diagonalRightCoefficients
  congr 1
  exact (ceil_eq_of_mem_cell _ _ _ hx (.inl (rays.symm ρ))).symm

/-- The actual scheme product over the coefficient field. -/
abbrev toricDiagonalProduct : Scheme :=
  pullback fan.algebraicRealizationStructureMap fan.algebraicRealizationStructureMap

def toricDiagonalFirst : toricDiagonalProduct fan ⟶ fan.algebraicRealization :=
  pullback.fst _ _

def toricDiagonalSecond : toricDiagonalProduct fan ⟶ fan.algebraicRealization :=
  pullback.snd _ _

instance toricDiagonalProductOver : (toricDiagonalProduct fan).Over (Spec (.of ℂ)) :=
  OverClass.ofHom (toricDiagonalFirst fan ≫ fan.algebraicRealizationStructureMap)

end ToricPower
