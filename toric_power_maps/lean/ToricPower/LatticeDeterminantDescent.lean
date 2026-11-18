module

public import ToricPower.LatticeFractionalPoint
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Int.Lemmas

/-!
# Strict determinant decrease under fractional stellar replacement

The determinant is measured in a fixed integral basis. Its real scalar
extension agrees with the determinant of the actual real vectors. Thus
replacing one member of a real basis by a vector with coordinate strictly
between zero and one strictly decreases the positive integer absolute
determinant. The lattice point is constructed, not assumed.
-/

@[expose] public noncomputable section
open TauCeti.Toric

namespace ToricPower.FanSubdivision

variable {N V κ : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} [Fintype κ] [DecidableEq κ]

/-- Integer determinants commute with the given, actual scalar extension. -/
theorem integralBasis_det_real (lattice : IsIntegralLattice i)
    (basis : Module.Basis κ ℤ N) (vectors : κ → N) :
    (lattice.isBaseChange.basis basis).det (fun k => i (vectors k)) =
      (basis.det vectors : ℝ) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Int.cast_det]
  congr 1
  ext a b
  exact lattice.isBaseChange.basis_repr_comp_apply basis (vectors b) a

/-- One-column replacement computes the determinant by the corresponding
coordinate in the original real basis. -/
theorem realBasis_det_update (background realBasis : Module.Basis κ ℝ V)
    (j : κ) (x : V) :
    background.det (Function.update realBasis j x) =
      realBasis.repr x j * background.det realBasis := by
  have same : Module.Basis.mk realBasis.linearIndependent realBasis.span_eq.ge = realBasis := by
    ext k
    exact Module.Basis.mk_apply _ _ _
  have formula := LinearMap.congr_fun
    (background.det_smul_mk_coord_eq_det_update realBasis.linearIndependent
      realBasis.span_eq.ge j) x
  rw [same] at formula
  simpa only [LinearMap.smul_apply, Module.Basis.coord_apply,
    MultilinearMap.toLinearMap_apply, AlternatingMap.coe_multilinearMap,
    smul_eq_mul, mul_comm] using formula.symm

/-- A nonzero replacement coordinate gives another actual real basis. -/
theorem realBasis_update_independent (realBasis : Module.Basis κ ℝ V)
    (j : κ) (x : V) (nonzero : realBasis.repr x j ≠ 0) :
    LinearIndependent ℝ (Function.update realBasis j x) := by
  apply (realBasis.is_basis_iff_det.mpr ?_).1
  apply isUnit_iff_ne_zero.mpr
  rw [realBasis_det_update, realBasis.det_self, mul_one]
  exact nonzero

theorem integralBasis_det_ne_zero (lattice : IsIntegralLattice i)
    (basis : Module.Basis κ ℤ N) (realBasis : Module.Basis κ ℝ V)
    (vectors : κ → N) (image : ∀ k, realBasis k = i (vectors k)) :
    basis.det vectors ≠ 0 := by
  have imageFamily : (fun k => i (vectors k)) = realBasis := funext fun k => (image k).symm
  have nonzero := (lattice.isBaseChange.basis basis).isUnit_det realBasis
  rw [← imageFamily, integralBasis_det_real lattice basis vectors] at nonzero
  exact fun zero => nonzero.ne_zero (by rw [zero, Int.cast_zero])

theorem integralBasis_det_update (lattice : IsIntegralLattice i)
    (basis : Module.Basis κ ℤ N) (realBasis : Module.Basis κ ℝ V)
    (vectors : κ → N) (image : ∀ k, realBasis k = i (vectors k))
    (j : κ) (q : N) :
    (basis.det (Function.update vectors j q) : ℝ) =
      realBasis.repr (i q) j * (basis.det vectors : ℝ) := by
  rw [← integralBasis_det_real lattice basis (Function.update vectors j q),
    ← integralBasis_det_real lattice basis vectors]
  have family : (fun k => i (Function.update vectors j q k)) =
      Function.update realBasis j (i q) := by
    funext k
    by_cases equal : k = j
    · subst k
      simp
    · simp [Function.update_of_ne equal, image]
  rw [family]
  have original : (fun k => i (vectors k)) = realBasis := funext fun k => (image k).symm
  rw [original]
  exact realBasis_det_update _ _ _ _

/-- The exact strict multiplicity decrease used in regular subdivision. -/
theorem integralBasis_natAbs_det_update_lt (lattice : IsIntegralLattice i)
    (basis : Module.Basis κ ℤ N) (realBasis : Module.Basis κ ℝ V)
    (vectors : κ → N) (image : ∀ k, realBasis k = i (vectors k))
    (j : κ) (q : N) (positive : 0 < realBasis.repr (i q) j)
    (small : realBasis.repr (i q) j < 1) :
    (basis.det (Function.update vectors j q)).natAbs < (basis.det vectors).natAbs := by
  have equation := integralBasis_det_update lattice basis realBasis vectors image j q
  have nonzero : (basis.det vectors : ℝ) ≠ 0 := by
    exact_mod_cast integralBasis_det_ne_zero lattice basis realBasis vectors image
  have coordinateSquare : (realBasis.repr (i q) j)^2 < 1 := by nlinarith
  have strictly : (basis.det (Function.update vectors j q) : ℝ)^2 <
      (basis.det vectors : ℝ)^2 := by
    rw [equation, mul_pow]
    simpa only [one_mul] using
      mul_lt_mul_of_pos_right coordinateSquare (sq_pos_of_ne_zero nonzero)
  apply Int.natAbs_lt_iff_sq_lt.mpr
  exact_mod_cast strictly

/-- Determinant larger than one constructs a primitive integral point
whose coordinates in the original real basis all lie in `[0,1)`. -/
theorem exists_primitive_fractional_of_det_large (lattice : IsIntegralLattice i)
    (basis : Module.Basis κ ℤ N) (realBasis : Module.Basis κ ℝ V)
    (vectors : κ → N) (image : ∀ k, realBasis k = i (vectors k))
    (large : 1 < (basis.det vectors).natAbs) :
    ∃ q : N, TauCeti.IsPrimitive q ∧ q ≠ 0 ∧ ∀ k,
      0 ≤ realBasis.repr (i q) k ∧ realBasis.repr (i q) k < 1 := by
  apply exists_primitive_integral_fractional_coordinates lattice realBasis vectors image
  intro spanning
  have independent : LinearIndependent ℤ vectors := by
    apply LinearIndependent.of_comp i.toIntLinearMap
    have realIndependent : LinearIndependent ℝ (i ∘ vectors) := by
      convert realBasis.linearIndependent using 1
      exact funext fun k => (image k).symm
    exact realIndependent.restrict_scalars' ℤ
  have unit := basis.is_basis_iff_det.mp ⟨independent, spanning⟩
  have one : (basis.det vectors).natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp unit
  omega

end ToricPower.FanSubdivision
end
