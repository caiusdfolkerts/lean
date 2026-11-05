module

public import PaperVerification.AlternatingFormsChart
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.Abel

/-!
# The odd chart equations over arbitrary coefficient algebras

The square constant coefficient block in the odd isotropic chart is the
map proved invertible in `AlternatingFormsChart`.  Here its invertibility
is extended to every commutative algebra over the ground field, including
polynomial rings and nonreduced quotient rings.  The extension is an actual
base change of a proved linear equivalence, not an assumed determinant.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped TensorProduct

section CoordinateBaseChange

variable {K R α β : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Extend a finite coordinate equivalence to an arbitrary coefficient
algebra by the ordinary tensor-product base change. -/
def coordinateScalarExtendEquiv (e : (α → K) ≃ₗ[K] (β → K)) :
    (α → R) ≃ₗ[R] (β → R) :=
  (TensorProduct.piScalarRight K R R α).symm.trans
    ((e.baseChange K R _ _).trans (TensorProduct.piScalarRight K R R β))

theorem coordinateScalarExtendEquiv_single
    (e : (α → K) ≃ₗ[K] (β → K)) (i : α) (j : β) :
    coordinateScalarExtendEquiv (R := R) e (Pi.single i 1) j =
      algebraMap K R (e (Pi.single i 1) j) := by
  simp only [coordinateScalarExtendEquiv, LinearEquiv.trans_apply,
    TensorProduct.piScalarRight_symm_single, LinearEquiv.baseChange_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Algebra.smul_def, mul_one]

end CoordinateBaseChange

section RingChart

variable {R S : Type*} [CommRing R] [CommRing S]

theorem chartPad_add_ring {k : ℕ}
    (T U : Fin k → Fin (k + 1) → R) (i j : ℕ) :
    chartPad (T + U) i j = chartPad T i j + chartPad U i j := by
  simp only [chartPad]
  split_ifs <;> simp

theorem chartPad_smul_ring {k : ℕ} (c : R)
    (T : Fin k → Fin (k + 1) → R) (i j : ℕ) :
    chartPad (c • T) i j = c • chartPad T i j := by
  simp only [chartPad]
  split_ifs <;> simp

theorem chartPad_map_ring {k : ℕ} (φ : R →+* S)
    (T : Fin k → Fin (k + 1) → R) (i j : ℕ) :
    chartPad (fun a b => φ (T a b)) i j = φ (chartPad T i j) := by
  simp only [chartPad]
  split_ifs <;> simp

abbrev OddChartHead (r : ℕ) := Fin r × Fin (r + 1)
abbrev OddChartEquation (r : ℕ) := StrictPairs (r + 1) ⊕ StrictPairs (r + 1)

/-- The same padded difference map with flattened coordinates.  The
definition is valid over arbitrary commutative rings. -/
def oddChartFlatMap (r : ℕ) :
    (OddChartHead r → R) →ₗ[R] (OddChartEquation r → R) where
  toFun T := Sum.elim
    (fun p => chartPad (fun a b => T (a,b)) p.val.1.val p.val.2.val -
      chartPad (fun a b => T (a,b)) p.val.2.val p.val.1.val)
    (fun p => chartPad (fun a b => T (a,b)) (p.val.1.val + 1) p.val.2.val -
      chartPad (fun a b => T (a,b)) (p.val.2.val + 1) p.val.1.val)
  map_add' T U := by
    funext z
    cases z <;> dsimp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
    all_goals
      change chartPad ((fun a b => T (a,b)) + (fun a b => U (a,b))) _ _ -
          chartPad ((fun a b => T (a,b)) + (fun a b => U (a,b))) _ _ = _
      rw [chartPad_add_ring, chartPad_add_ring]
      abel
  map_smul' c T := by
    funext z
    cases z <;> dsimp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply]
    all_goals
      change chartPad (c • (fun a b => T (a,b))) _ _ -
          chartPad (c • (fun a b => T (a,b))) _ _ = _
      rw [chartPad_smul_ring, chartPad_smul_ring]
      exact (smul_sub c _ _).symm

theorem oddChartFlatMap_map (r : ℕ) (φ : R →+* S)
    (T : OddChartHead r → R) (z : OddChartEquation r) :
    oddChartFlatMap r (fun i => φ (T i)) z = φ (oddChartFlatMap r T z) := by
  cases z <;>
    simp only [oddChartFlatMap, LinearMap.coe_mk, AddHom.coe_mk,
      Sum.elim_inl, Sum.elim_inr, chartPad_map_ring, map_sub]

end RingChart

section AlgebraChart

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- Flatten the already proved field-valued chart equivalence. -/
def oddChartFlatEquiv (r : ℕ) :
    (OddChartHead r → K) ≃ₗ[K] (OddChartEquation r → K) :=
  (LinearEquiv.curry K K (Fin r) (Fin (r+1))).trans
    ((chartEquiv r).trans
      (LinearEquiv.sumArrowLequivProdArrow (StrictPairs (r+1))
        (StrictPairs (r+1)) K K).symm)

theorem oddChartFlatEquiv_apply (r : ℕ) (T : OddChartHead r → K) :
    oddChartFlatEquiv r T = oddChartFlatMap r T := by
  funext z
  cases z <;> rfl

/-- A proved inverse for the constant coefficient block over every
commutative algebra over `K`. -/
def oddChartFlatEquivOver (r : ℕ) :
    (OddChartHead r → R) ≃ₗ[R] (OddChartEquation r → R) :=
  coordinateScalarExtendEquiv (oddChartFlatEquiv (K := K) r)

theorem oddChartFlatEquivOver_toLinearMap (r : ℕ) :
    (oddChartFlatEquivOver (K := K) (R := R) r).toLinearMap =
      oddChartFlatMap r := by
  apply (Pi.basisFun R (OddChartHead r)).ext
  intro i
  funext z
  simp only [Pi.basisFun_apply, oddChartFlatEquivOver,
    LinearEquiv.coe_coe, coordinateScalarExtendEquiv_single,
    oddChartFlatEquiv_apply]
  have hs : (Pi.single i (1 : R) : OddChartHead r → R) =
      fun j => algebraMap K R (((Pi.single i (1 : K)) : OddChartHead r → K) j) := by
    funext j
    simp [Pi.single_apply]
  rw [hs, oddChartFlatMap_map]

theorem oddChartFlatEquivOver_apply (r : ℕ) (T : OddChartHead r → R) :
    oddChartFlatEquivOver (K := K) (R := R) r T = oddChartFlatMap r T :=
  congrArg (fun L : (OddChartHead r → R) →ₗ[R] (OddChartEquation r → R) => L T)
    (oddChartFlatEquivOver_toLinearMap r)

include K in
theorem oddChartFlatMap_bijective_over (r : ℕ) :
    Function.Bijective (oddChartFlatMap (R := R) r) := by
  rw [← oddChartFlatEquivOver_toLinearMap (K := K) (R := R) r]
  exact (oddChartFlatEquivOver r).bijective

/-- Unflattened equations: the inverse remains available over polynomial
rings and over the actual isotropic chart quotient ring. -/
def oddChartEquivOver (r : ℕ) :
    (Fin r → Fin (r+1) → R) ≃ₗ[R]
      ((StrictPairs (r+1) → R) × (StrictPairs (r+1) → R)) :=
  (LinearEquiv.curry R R (Fin r) (Fin (r+1))).symm.trans
    ((oddChartFlatEquivOver (K := K) r).trans
      (LinearEquiv.sumArrowLequivProdArrow (StrictPairs (r+1))
        (StrictPairs (r+1)) R R))

theorem oddChartEquivOver_apply (r : ℕ) (T : Fin r → Fin (r+1) → R) :
    oddChartEquivOver (K := K) r T =
      (fun p => chartPad T p.val.1.val p.val.2.val -
          chartPad T p.val.2.val p.val.1.val,
       fun p => chartPad T (p.val.1.val+1) p.val.2.val -
          chartPad T (p.val.2.val+1) p.val.1.val) := by
  simp only [oddChartEquivOver, LinearEquiv.trans_apply,
    oddChartFlatEquivOver_apply]
  rfl

end AlgebraChart

end PaperVerification.AlternatingForms
