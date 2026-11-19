module

public import paper_verification.literal003
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Data.Nat.Choose.Basic
public import paper_verification.literal001
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Order.Interval.Finset.Nat
public import paper_verification.literal002
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.List.Pairwise
public import Mathlib.Order.MinMax
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Linarith
public import paper_verification.literal000
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Tactic.Abel
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.List.Chain
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.RingTheory.Regular.RegularSequence

set_option Elab.async false

section TAF_LiteralSource_0222
/- Original module: PaperVerification.AlternatingFormsPathDenominator -/


/-!
# The signed path matching polynomial and the printed determinant

The denominator for a path with n vertices satisfies P₀=P₁=1 and
Pₙ₊₂=Pₙ₊₁-zPₙ.  Its coefficients are proved, for all n and j, to be
(-1)^j choose(n-j,j).  The reciprocal coefficient determinant therefore
becomes exactly the binomial Hessenberg matrix printed in Theorem 1.1.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Classical

namespace PaperVerification.AlternatingForms.PathDeterminant

def pathDenominator : ℕ → PowerSeries ℤ
  | 0 => 1
  | 1 => 1
  | n+2 => pathDenominator (n+1) - PowerSeries.X * pathDenominator n

@[simp] theorem pathDenominator_zero : pathDenominator 0 = 1 := rfl
@[simp] theorem pathDenominator_one : pathDenominator 1 = 1 := rfl

theorem pathDenominator_recurrence (n : ℕ) :
    pathDenominator (n+2) = pathDenominator (n+1) - PowerSeries.X * pathDenominator n := rfl

theorem pathDenominator_coeff (n j : ℕ) :
    PowerSeries.coeff j (pathDenominator n) = (-1 : ℤ)^j * ((n-j).choose j : ℤ) := by
  induction n using Nat.twoStepInduction generalizing j with
  | zero =>
      cases j <;> simp [pathDenominator]
  | one =>
      cases j with
      | zero => simp [pathDenominator]
      | succ j =>
          have he : 1-(j+1) = 0 := by omega
          simp [pathDenominator, he]
  | more n h0 h1 =>
      cases j with
      | zero => simp only [pathDenominator_recurrence, map_sub,
          PowerSeries.coeff_zero_X_mul, sub_zero, h1, pow_zero, Nat.sub_zero,
          Nat.choose_zero_right, Nat.cast_one, mul_one]
      | succ j =>
          rw [pathDenominator_recurrence, map_sub, PowerSeries.coeff_succ_X_mul, h1, h0]
          by_cases hj : j ≤ n
          · rw [show n+1-(j+1)=n-j by omega, show n+2-(j+1)=n-j+1 by omega,
              Nat.choose_succ_succ, Nat.cast_add]
            simp only [pow_succ]
            ring
          · have h0' : n-j=0 := by omega
            have h1' : n+1-(j+1)=0 := by omega
            have h2' : n+2-(j+1)<j+1 := by omega
            have h2'' : (n+1-j).choose (j+1) = 0 :=
              Nat.choose_eq_zero_of_lt (by omega)
            have hj0 : j ≠ 0 := by omega
            have hz : Nat.choose 0 j = 0 := Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj0)
            simp [h0', h1', Nat.choose_eq_zero_of_lt h2', h2'', hz]

@[simp] theorem pathDenominator_constantCoeff (n : ℕ) :
    (pathDenominator n).constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, pathDenominator_coeff]
  simp

/-- Replacement z↦z², as an actual power-series algebra homomorphism. -/
def expandedPathDenominator (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.expand 2 (by decide) (pathDenominator n)

@[simp] theorem expandedPathDenominator_zero : expandedPathDenominator 0 = 1 := by
  simp [expandedPathDenominator]

@[simp] theorem expandedPathDenominator_one : expandedPathDenominator 1 = 1 := by
  simp [expandedPathDenominator]

theorem expandedPathDenominator_recurrence (n : ℕ) :
    expandedPathDenominator (n+2) = expandedPathDenominator (n+1) -
      PowerSeries.X^2 * expandedPathDenominator n := by
  simp only [expandedPathDenominator, pathDenominator_recurrence, map_sub, map_mul,
    PowerSeries.expand_X]

@[simp] theorem expandedPathDenominator_constantCoeff (n : ℕ) :
    (expandedPathDenominator n).constantCoeff = 1 := by
  simp only [expandedPathDenominator, PowerSeries.constantCoeff_expand,
    pathDenominator_constantCoeff]

theorem expandedPathDenominator_inverse (n : ℕ) :
    PowerSeries.invOfUnit (expandedPathDenominator n) 1 =
      PowerSeries.expand 2 (by decide) (PowerSeries.invOfUnit (pathDenominator n) 1) := by
  let φ := PowerSeries.expand 2 (by decide) (PowerSeries.invOfUnit (pathDenominator n) 1)
  have hm : expandedPathDenominator n * φ = 1 := by
    dsimp only [φ]
    rw [expandedPathDenominator, ← map_mul,
      PowerSeries.mul_invOfUnit _ 1 (pathDenominator_constantCoeff n), map_one]
  calc
    PowerSeries.invOfUnit (expandedPathDenominator n) 1 =
        PowerSeries.invOfUnit (expandedPathDenominator n) 1 * 1 := (mul_one _).symm
    _ = PowerSeries.invOfUnit (expandedPathDenominator n) 1 *
        (expandedPathDenominator n * φ) := by rw [hm]
    _ = φ := by
      rw [← mul_assoc, PowerSeries.invOfUnit_mul _ 1
        (expandedPathDenominator_constantCoeff n), one_mul]

theorem expandedPathDenominator_inverse_coeff (n s : ℕ) :
    PowerSeries.coeff (2*s) (PowerSeries.invOfUnit (expandedPathDenominator n) 1) =
      PowerSeries.coeff s (PowerSeries.invOfUnit (pathDenominator n) 1) := by
  rw [expandedPathDenominator_inverse, PowerSeries.coeff_expand_mul]

/-- Ordinary binomial coefficients outside their printed integer range are
zero.  The guard retains the negative-bottom case instead of truncating it
to a spurious coefficient choose(_,0)=1. -/
@[expose]
def paperMatrix (w s : ℕ) : Matrix (Fin s) (Fin s) ℤ :=
  fun i j => if i.val ≤ j.val+1 then
    ((w+i.val-j.val).choose (j.val+1-i.val) : ℤ) else 0

theorem inverseCoefficientMatrix_pathDenominator (w s : ℕ) :
    PowerSeriesInverseDeterminant.inverseCoefficientMatrix (pathDenominator (w+1)) s =
      paperMatrix w s := by
  ext i j
  by_cases hij : i.val ≤ j.val+1
  · simp only [PowerSeriesInverseDeterminant.inverseCoefficientMatrix, paperMatrix,
      hij, if_true, pathDenominator_coeff]
    have htop : w+1-(j.val+1-i.val)=w+i.val-j.val := by omega
    rw [htop]
    have hsign : (-1 : ℤ)^i.val * ((-1 : ℤ)^(j.val+1) *
        (-1 : ℤ)^(j.val+1-i.val)) = 1 := by
      rw [← pow_add, ← pow_add, show i.val+(j.val+1+(j.val+1-i.val))=2*(j.val+1) by omega,
        pow_mul]
      simp
    calc
      (-1 : ℤ)^i.val * ((-1 : ℤ)^(j.val+1) *
          ((-1 : ℤ)^(j.val+1-i.val) * ((w+i.val-j.val).choose (j.val+1-i.val) : ℤ))) =
        ((-1 : ℤ)^i.val * ((-1 : ℤ)^(j.val+1) * (-1 : ℤ)^(j.val+1-i.val))) *
          ((w+i.val-j.val).choose (j.val+1-i.val) : ℤ) := by ring
      _ = _ := by rw [hsign, one_mul]
  · simp only [PowerSeriesInverseDeterminant.inverseCoefficientMatrix, paperMatrix,
      hij, if_false, mul_zero]

theorem pathDenominator_inverse_coeff_eq_det (w s : ℕ) :
    PowerSeries.coeff s (PowerSeries.invOfUnit (pathDenominator (w+1)) 1) =
      (paperMatrix w s).det := by
  rw [PowerSeriesInverseDeterminant.coeff_inverse_eq_det _ (pathDenominator_constantCoeff _),
    inverseCoefficientMatrix_pathDenominator]

end PaperVerification.AlternatingForms.PathDeterminant
end
end
end TAF_LiteralSource_0222

section TAF_LiteralSource_0223
/- Original module: PaperVerification.AlternatingFormsPathDeterminant -/


/-!
# The printed determinant counts the actual strip walks

An explicit continuant row certifies the inverse endpoint entry of the
path-graph resolvent.  Its coefficients count Mathlib's actual graph walks.
Together with the finite triangular-matrix adjugate calculation, this gives
the complete determinant identity in Theorem 1.1, in all parameter sizes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Classical

namespace PaperVerification.AlternatingForms.PathDeterminant

def previous {w : ℕ} (j : Fin (w+1)) : Fin (w+1) :=
  ⟨j.val-1, (Nat.sub_le _ _).trans_lt j.isLt⟩

def next {w : ℕ} (j : Fin (w+1)) (hj : j.val < w) : Fin (w+1) :=
  ⟨j.val+1, Nat.succ_lt_succ hj⟩

theorem path_neighbor_sum {R : Type*} [CommRing R] (w : ℕ)
    (j : Fin (w+1)) (f : Fin (w+1) → R) :
    (∑ i : Fin (w+1), if i.val+1=j.val ∨ j.val+1=i.val then f i else 0) =
      (if h : 0 < j.val then f (previous j) else 0) +
      (if h : j.val < w then f (next j h) else 0) := by
  have hs (i : Fin (w+1)) :
      (if i.val+1=j.val ∨ j.val+1=i.val then f i else 0) =
        (if i.val+1=j.val then f i else 0) +
        (if j.val+1=i.val then f i else 0) := by
    by_cases h₁ : i.val+1=j.val
    · have h₂ : ¬j.val+1=i.val := by omega
      simp [h₁, h₂]
    · by_cases h₂ : j.val+1=i.val <;> simp [h₁, h₂]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hj : 0 < j.val
    · rw [dif_pos hj]
      have hv (i : Fin (w+1)) : i.val+1=j.val ↔ i=previous j := by
        constructor
        · intro hi
          apply Fin.ext
          dsimp [previous]
          omega
        · rintro rfl
          dsimp [previous]
          omega
      simp_rw [hv]
      simp
    · have hz (i : Fin (w+1)) : ¬i.val+1=j.val := by omega
      simp [hz, hj]
  · by_cases hj : j.val < w
    · rw [dif_pos hj]
      have hv (i : Fin (w+1)) : j.val+1=i.val ↔ i=next j hj := by
        constructor
        · intro hi
          apply Fin.ext
          exact hi.symm
        · rintro rfl
          rfl
      simp_rw [hv]
      simp
    · have hz (i : Fin (w+1)) : ¬j.val+1=i.val := by have hi := i.isLt; omega
      simp [hz, hj]

theorem vecMul_pathMatrix {R : Type*} [CommRing R] (w : ℕ)
    (row : Fin (w+1) → R) (j : Fin (w+1)) :
    (row ᵥ* (SimpleGraph.pathGraph (w+1)).adjMatrix R) j =
      (if h : 0 < j.val then row (previous j) else 0) +
      (if h : j.val < w then row (next j h) else 0) := by
  simp only [Matrix.vecMul, dotProduct, SimpleGraph.adjMatrix_apply,
    SimpleGraph.pathGraph_adj, mul_ite, mul_one, mul_zero]
  exact path_neighbor_sum w j row

def pathMatrix (w : ℕ) : Matrix (Fin (w+1)) (Fin (w+1)) ℤ :=
  (SimpleGraph.pathGraph (w+1)).adjMatrix ℤ

theorem pathMatrix_map_C (w : ℕ) :
    (pathMatrix w).map (PowerSeries.C (R := ℤ)) =
      (SimpleGraph.pathGraph (w+1)).adjMatrix (PowerSeries ℤ) := by
  ext i j
  simp only [pathMatrix, Matrix.map_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

theorem row_resolvent_apply (w : ℕ) (row : Fin (w+1) → PowerSeries ℤ)
    (j : Fin (w+1)) :
    (row ᵥ* MatrixPowerSeries.resolventMatrix (pathMatrix w)) j =
      row j - PowerSeries.X *
        ((if h : 0 < j.val then row (previous j) else 0) +
         (if h : j.val < w then row (next j h) else 0)) := by
  rw [MatrixPowerSeries.resolventMatrix, Matrix.vecMul_sub, Matrix.vecMul_one,
    Matrix.vecMul_smul, pathMatrix_map_C]
  change row j - PowerSeries.X *
    (row ᵥ* (SimpleGraph.pathGraph (w+1)).adjMatrix (PowerSeries ℤ)) j = _
  rw [vecMul_pathMatrix]

def pathRow (w : ℕ) (j : Fin (w+1)) : PowerSeries ℤ :=
  PowerSeries.X^j.val * expandedPathDenominator (w-j.val)

@[simp] theorem pathRow_last (w : ℕ) : pathRow w (Fin.last w) = PowerSeries.X^w := by
  simp [pathRow]

theorem pathRow_resolvent (w : ℕ) :
    pathRow w ᵥ* MatrixPowerSeries.resolventMatrix (pathMatrix w) =
      Pi.single 0 (expandedPathDenominator (w+1)) := by
  funext j
  rw [row_resolvent_apply]
  by_cases hj0 : j=0
  · subst j
    cases w with
    | zero => simp [pathRow]
    | succ w =>
        have H : expandedPathDenominator (w+1) - PowerSeries.X *
            (PowerSeries.X * expandedPathDenominator w) = expandedPathDenominator (w+2) := by
          rw [expandedPathDenominator_recurrence]
          ring
        simpa [pathRow, previous, next] using H
  · have hjv : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
    have hjp : 0 < j.val := Nat.pos_of_ne_zero hjv
    have hrhs : (Pi.single (0 : Fin (w+1)) (expandedPathDenominator (w+1)) :
        Fin (w+1) → PowerSeries ℤ) j = 0 := by
      simp [Pi.single_apply, hj0, Ne.symm hj0]
    rw [hrhs]
    by_cases hjw : j.val < w
    · have hk0 : w-j.val = (w-j.val-1)+1 := by omega
      have hkm : w-(j.val-1) = (w-j.val-1)+2 := by omega
      have hkp : w-(j.val+1) = w-j.val-1 := by omega
      have hp0 : (PowerSeries.X : PowerSeries ℤ)^j.val =
          PowerSeries.X^(j.val-1)*PowerSeries.X := by
        conv_lhs => rw [show j.val=(j.val-1)+1 by omega, pow_succ]
      have hp1 : (PowerSeries.X : PowerSeries ℤ)^(j.val+1) =
          PowerSeries.X^(j.val-1)*PowerSeries.X^2 := by
        rw [pow_succ, hp0]
        ring
      have H : (PowerSeries.X : PowerSeries ℤ)^j.val * expandedPathDenominator (w-j.val) -
          PowerSeries.X *
            (PowerSeries.X^(j.val-1)*expandedPathDenominator (w-(j.val-1)) +
             PowerSeries.X^(j.val+1)*expandedPathDenominator (w-(j.val+1))) = 0 := by
        rw [hk0, hkm, hkp, expandedPathDenominator_recurrence, hp0, hp1]
        ring
      simpa [pathRow, previous, next, hjp, hjw] using H
    · have hjlast : j.val=w := by have hj := j.isLt; omega
      have hp : (PowerSeries.X : PowerSeries ℤ)^j.val =
          PowerSeries.X^(j.val-1)*PowerSeries.X := by
        conv_lhs => rw [show j.val=(j.val-1)+1 by omega, pow_succ]
      have hk0 : w-j.val=0 := by omega
      have hkm : w-(j.val-1)=1 := by omega
      have H : (PowerSeries.X : PowerSeries ℤ)^j.val * expandedPathDenominator (w-j.val) -
          PowerSeries.X * (PowerSeries.X^(j.val-1)*expandedPathDenominator (w-(j.val-1))) = 0 := by
        rw [hk0, hkm, expandedPathDenominator_zero, expandedPathDenominator_one,
          mul_one, mul_one, hp]
        ring
      simpa [pathRow, previous, next, hjp, hjw] using H

theorem pathMatrix_power_endpoint (w s : ℕ) :
    (pathMatrix w^(w+2*s)) 0 (Fin.last w) =
      PowerSeries.coeff s (PowerSeries.invOfUnit (pathDenominator (w+1)) 1) := by
  have h := MatrixPowerSeries.power_entry_of_row_certificate (pathMatrix w) (pathRow w)
    (expandedPathDenominator (w+1)) 0 (Fin.last w) w
    (pathRow_resolvent w) (pathRow_last w) (expandedPathDenominator_constantCoeff _) (2*s)
  rw [expandedPathDenominator_inverse_coeff] at h
  simpa only [Nat.add_comm (2*s) w] using h

/-- The full unrestricted walk count is connected to the finite determinant. -/
theorem walkCount_eq_determinant (w s : ℕ) :
    (StripWalks.walkCount w (w+2*s) : ℤ) = (paperMatrix w s).det := by
  have hc := SimpleGraph.adjMatrix_pow_apply_eq_card_walk
    (G := SimpleGraph.pathGraph (w+1)) (α := ℤ) (w+2*s) 0 (Fin.last w)
  have he : (StripWalks.walkCount w (w+2*s) : ℤ) =
      (pathMatrix w^(w+2*s)) 0 (Fin.last w) := hc.symm
  rw [he, pathMatrix_power_endpoint, pathDenominator_inverse_coeff_eq_det]

/-- The exact determinant identity printed in Theorem 1.1, including s=0.
The hypothesis only ensures that the printed endpoint width is nonnegative. -/
theorem paperWalkCount_determinant (n s : ℕ) (hs : 2*s ≤ n+2) :
    (StripWalks.paperWalkCount n s : ℤ) = (paperMatrix (n+2-2*s) s).det := by
  have h := walkCount_eq_determinant (n+2-2*s) s
  simpa only [StripWalks.paperWalkCount, Nat.sub_add_cancel hs] using h

end PaperVerification.AlternatingForms.PathDeterminant
end
end
end TAF_LiteralSource_0223

section TAF_LiteralSource_0224
/- Original module: PaperVerification.AlternatingFormsGenericHilbertCoordinates -/


/-!
# Generic exterior Hilbert certificates in arbitrary vector spaces

Every displayed coordinate system is a basis of the actual second exterior
power.  Replacing the vector space by a linearly equivalent one transports
that basis, the original two generated ideals, and every quotient degree.
The parameter polynomial is unchanged because the coefficient vectors are
unchanged in these corresponding bases.  The dimension-one boundary is
handled for every pair of forms, since its second exterior power is zero.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators Classical

variable {K M N I : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [Fintype I] [DecidableEq I]

/-- The coefficient points parametrize every actual pair of two-forms
uniquely.  This supplies the explicit equivalence behind the generic
coefficient-space formulation. -/
def orbitPairCoordinateEquiv (b₂ : Module.Basis I K (⋀[K]^2 M)) :
    ((I ⊕ I) → K) ≃ₗ[K] ((⋀[K]^2 M) × (⋀[K]^2 M)) :=
  (LinearEquiv.sumArrowLequivProdArrow I I K K).trans
    (b₂.equivFun.symm.prodCongr b₂.equivFun.symm)

@[simp] theorem orbitPairCoordinateEquiv_apply
    (b₂ : Module.Basis I K (⋀[K]^2 M)) (y : (I ⊕ I) → K) :
    orbitPairCoordinateEquiv b₂ y = orbitFormsFromCoordinates b₂ y := by
  apply Prod.ext <;>
    simp [orbitPairCoordinateEquiv, orbitFormsFromCoordinates,
      Module.Basis.equivFun_symm_apply]

theorem orbitFormsFromCoordinates_bijective (b₂ : Module.Basis I K (⋀[K]^2 M)) :
    Function.Bijective (orbitFormsFromCoordinates b₂) := by
  have he : orbitFormsFromCoordinates b₂ = fun y => orbitPairCoordinateEquiv b₂ y := by
    funext y
    exact (orbitPairCoordinateEquiv_apply b₂ y).symm
  rw [he]
  exact (orbitPairCoordinateEquiv b₂).bijective

theorem orbitFormsFromCoordinates_map (e : M ≃ₗ[K] N)
    (b₂ : Module.Basis I K (⋀[K]^2 M)) (y : (I ⊕ I) → K) :
    orbitFormsFromCoordinates (b₂.map (orbitExteriorPowerEquiv e 2)) y =
      (exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).1,
       exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).2) := by
  simp only [orbitFormsFromCoordinates, Module.Basis.map_apply,
    orbitExteriorPowerEquiv_apply, map_sum, map_smul]

theorem orbitFormsFromCoordinates_map_finrank (e : M ≃ₗ[K] N)
    (b₂ : Module.Basis I K (⋀[K]^2 M)) (y : (I ⊕ I) → K) (s : ℕ) :
    Module.finrank K (ExteriorQuotientDegree
      (orbitFormsFromCoordinates (b₂.map (orbitExteriorPowerEquiv e 2)) y).1
      (orbitFormsFromCoordinates (b₂.map (orbitExteriorPowerEquiv e 2)) y).2 s) =
    Module.finrank K (ExteriorQuotientDegree
      (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) := by
  rw [orbitFormsFromCoordinates_map]
  exact (exteriorQuotientDegreeMapEquiv e
    (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s).finrank_eq.symm

section CharacteristicZero

variable [CharZero K] [FiniteDimensional K M]

theorem exteriorQuotientDegree_zero_finrank (f g : ⋀[K]^2 M) :
    Module.finrank K (ExteriorQuotientDegree f g 0) = 1 := by
  have h := ((exteriorDegreeRelations f g 0).quotEquivOfEqBot
    (exteriorDegreeRelations_eq_bot f g (by decide))).finrank_eq
  exact h.trans (by rw [exteriorPower.finrank_eq, Nat.choose_zero_right])

/-- The full even-dimensional formula in any vector space of that dimension.
The nonzero polynomial is on all coefficients in an actual exterior basis. -/
theorem even_generic_paperHilbert_in_vector_space (k : ℕ)
    (hdim : Module.finrank K M = 2*k) :
    ∃ b₂ : Module.Basis (EvenOrbitSlot k) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (EvenOrbitSlot k ⊕ EvenOrbitSlot k) K, Q ≠ 0 ∧
        ∀ y : (EvenOrbitSlot k ⊕ EvenOrbitSlot k) → K, eval y Q ≠ 0 →
          (∀ s : ℕ, s ≤ k →
            Module.finrank K (ExteriorQuotientDegree
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) =
                StripWalks.paperWalkCount (2*k) s) ∧
          (∀ s : ℕ, k < s →
            Module.finrank K (ExteriorQuotientDegree
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) = 0) := by
  let e : (EvenOrbitMode k → K) ≃ₗ[K] M := LinearEquiv.ofFinrankEq _ _ (by
    simpa only [EvenOrbitMode, Module.finrank_fintype_fun_eq_card,
      Fintype.card_prod, Fintype.card_fin] using hdim.symm)
  obtain ⟨Q, hQ, h⟩ := even_actual_generic_paperHilbert (K := K) k
  refine ⟨(evenOrbitExteriorBasis k).map (orbitExteriorPowerEquiv e 2), Q, hQ, ?_⟩
  intro y hy
  obtain ⟨hlow, hhigh⟩ := h y hy
  constructor
  · intro s hs
    rw [orbitFormsFromCoordinates_map_finrank]
    exact hlow s hs
  · intro s hs
    rw [orbitFormsFromCoordinates_map_finrank]
    exact hhigh s hs

/-- The full odd-dimensional formula for dimensions at least three in every
vector space, with every natural exterior degree retained. -/
theorem odd_generic_paperHilbert_in_vector_space (t : ℕ)
    (hdim : Module.finrank K M = 2*(t+1)+1) :
    ∃ b₂ : Module.Basis (OddOrbitSlot t) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (OddOrbitSlot t ⊕ OddOrbitSlot t) K, Q ≠ 0 ∧
        ∀ y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K, eval y Q ≠ 0 →
          (∀ s : ℕ, Module.finrank K (ExteriorQuotientDegree
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) =
              StripWalks.paperWalkCount (2*(t+1)+1) s) ∧
          (∀ s : ℕ, t+2 < s →
            Module.finrank K (ExteriorQuotientDegree
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) = 0) := by
  let e : (OddOrbitMode t → K) ≃ₗ[K] M := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin, hdim]
    omega)
  obtain ⟨Q, hQ, h⟩ := odd_actual_generic_paperHilbert (K := K) t
  refine ⟨(oddOrbitExteriorBasis t).map (orbitExteriorPowerEquiv e 2), Q, hQ, ?_⟩
  intro y hy
  obtain ⟨hall, hhigh⟩ := h y hy
  constructor
  · intro s
    rw [orbitFormsFromCoordinates_map_finrank]
    exact hall s
  · intro s hs
    rw [orbitFormsFromCoordinates_map_finrank]
    exact hhigh s hs

theorem one_dimensional_coordinate_paperHilbert
    (f g : ⋀[K]^2 (Fin 1 → K)) (s : ℕ) :
    Module.finrank K (ExteriorQuotientDegree f g s) = StripWalks.paperWalkCount 1 s := by
  letI : Subsingleton (⋀[K]^2 (Fin 1 → K)) := Module.finrank_zero_iff.mp (by
    rw [exteriorPower.finrank_eq, Module.finrank_fin_fun]
    decide)
  have hf : f = oddPathFirstQuadratic (Pi.basisFun K (Fin (2*0+1))) :=
    Subsingleton.elim _ _
  have hg : g = oddPathSecondQuadratic (Pi.basisFun K (Fin (2*0+1))) :=
    Subsingleton.elim _ _
  rw [hf, hg]
  exact oddExteriorQuotientDegree_finrank_eq_paperWalkCount 0 s

/-- The dimension-one case holds for all pairs, including the only pair of
zero quadratic forms, so no odd-dimensional boundary is omitted. -/
theorem one_dimensional_paperHilbert (hdim : Module.finrank K M = 1)
    (f g : ⋀[K]^2 M) (s : ℕ) :
    Module.finrank K (ExteriorQuotientDegree f g s) = StripWalks.paperWalkCount 1 s := by
  let e : M ≃ₗ[K] (Fin 1 → K) := LinearEquiv.ofFinrankEq _ _ (by
    rw [hdim, Module.finrank_fin_fun])
  exact (exteriorQuotientDegreeMapEquiv e f g s).finrank_eq.trans
    (one_dimensional_coordinate_paperHilbert _ _ s)

/-- The actual quotient walk formula for every dimension in an arbitrary
vector space.  The existential coordinate index is finite and its vectors
are a genuine basis of the complete second exterior power.  Thus the
nonzero polynomial cuts out a principal open in the full space of pairs,
not in a restricted family.  The binomial determinant identity is a
separate combinatorial correspondence. -/
theorem generic_exterior_walk_hilbert (n : ℕ) (hdim : Module.finrank K M = n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          ∀ y : (ι ⊕ ι) → K, eval y Q ≠ 0 →
            (∀ s : ℕ, s ≤ (n+1)/2 →
              Module.finrank K (ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) =
                  StripWalks.paperWalkCount n s) ∧
            (∀ s : ℕ, (n+1)/2 < s →
              Module.finrank K (ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) = 0) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2*k ∨ n = 2*k+1 := ⟨n/2, by omega⟩
  rcases hk with rfl | rfl
  · obtain ⟨b₂, Q, hQ, h⟩ := even_generic_paperHilbert_in_vector_space k hdim
    refine ⟨EvenOrbitSlot k, inferInstance, b₂, Q, hQ, ?_⟩
    intro y hy
    simpa only [show (2*k+1)/2 = k by omega] using h y hy
  · cases k with
    | zero =>
        let b₂ := Module.finBasis K (⋀[K]^2 M)
        refine ⟨Fin (Module.finrank K (⋀[K]^2 M)), inferInstance, b₂, 1,
          one_ne_zero, ?_⟩
        intro y hy
        constructor
        · intro s hs
          exact one_dimensional_paperHilbert hdim _ _ s
        · intro s hs
          rw [one_dimensional_paperHilbert hdim]
          exact paperWalkCount_odd_above_cutoff 0 s (by omega)
    | succ t =>
        obtain ⟨b₂, Q, hQ, h⟩ := odd_generic_paperHilbert_in_vector_space t hdim
        refine ⟨OddOrbitSlot t, inferInstance, b₂, Q, hQ, ?_⟩
        intro y hy
        obtain ⟨hall, hhigh⟩ := h y hy
        refine ⟨fun s _ => hall s, ?_⟩
        intro s hs
        exact hhigh s (by omega)

/-- The full coefficient statement of Theorem 1.1: the constant coefficient
is one, each positive coefficient in the entire printed range is both the
actual strip-walk number and the printed binomial determinant, and every
higher coefficient is zero.  One nonempty principal open controls all
degrees simultaneously in the full space of pairs of exterior forms. -/
theorem paper_theorem_1_1 (n : ℕ) (hdim : Module.finrank K M = n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          (∃ y : (ι ⊕ ι) → K, eval y Q ≠ 0) ∧
          ∀ y : (ι ⊕ ι) → K, eval y Q ≠ 0 →
            Module.finrank K (ExteriorQuotientDegree
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 0) = 1 ∧
            (∀ s : ℕ, 1 ≤ s → s ≤ (n+1)/2 →
              Module.finrank K (ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) =
                  StripWalks.paperWalkCount n s ∧
              (Module.finrank K (ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) : ℤ) =
                  (PathDeterminant.paperMatrix (n+2-2*s) s).det) ∧
            (∀ s : ℕ, (n+1)/2 < s →
              Module.finrank K (ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) = 0) := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  obtain ⟨ι, fin, h⟩ := generic_exterior_walk_hilbert (K := K) (M := M) n hdim
  letI := fin
  obtain ⟨b₂, Q, hQ, h⟩ := h
  refine ⟨ι, fin, b₂, Q, hQ, ?_, ?_⟩
  · by_contra hn
    apply hQ
    apply MvPolynomial.funext
    intro y
    rw [map_zero]
    by_contra hy
    exact hn ⟨y, hy⟩
  · intro y hy
    obtain ⟨hlow, hhigh⟩ := h y hy
    refine ⟨exteriorQuotientDegree_zero_finrank _ _, ?_, hhigh⟩
    intro s hspos hs
    refine ⟨hlow s hs, ?_⟩
    rw [hlow s hs]
    exact PathDeterminant.paperWalkCount_determinant n s (by omega)

end CharacteristicZero

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0224

section TAF_LiteralSource_0225
/- Original module: PaperVerification.FiniteHilbertSeries -/


/-!
# A finite Hilbert-series formula and its exact coefficient meaning

This elementary equivalence retains the constant coefficient, every positive
coefficient through the specified cutoff, and every coefficient beyond it.
It allows a graded dimension calculation to be restated as the literal
finite power-series identity used in the paper.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.FiniteHilbertSeries

open scoped BigOperators PowerSeries

@[expose]
def expression (a : ℕ → ℕ) (d : ℕ) : ℕ⟦X⟧ :=
  1 + ∑ s ∈ Finset.Icc 1 d, PowerSeries.C (a s) * PowerSeries.X ^ s

theorem coeff_expression (a : ℕ → ℕ) (d s : ℕ) :
    PowerSeries.coeff s (expression a d) =
      (if s = 0 then 1 else 0) + (if 1 ≤ s ∧ s ≤ d then a s else 0) := by
  simp only [expression, map_add, map_sum, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_Icc]

/-- Equality to the displayed finite series is equivalent to all three
parts of the coefficient statement; no degree is omitted. -/
theorem mk_eq_expression_iff (h a : ℕ → ℕ) (d : ℕ) :
    PowerSeries.mk h = expression a d ↔
      h 0 = 1 ∧
      (∀ s, 1 ≤ s → s ≤ d → h s = a s) ∧
      (∀ s, d < s → h s = 0) := by
  constructor
  · intro heq
    have hc (s : ℕ) : h s = PowerSeries.coeff s (expression a d) := by
      rw [← heq, PowerSeries.coeff_mk]
    refine ⟨?_, ?_, ?_⟩
    · simpa [coeff_expression] using hc 0
    · intro s hs hd
      have hs0 : s ≠ 0 := by omega
      simpa [coeff_expression, hs0, hs, hd] using hc s
    · intro s hd
      have hs0 : s ≠ 0 := by omega
      have hs : ¬ s ≤ d := Nat.not_le.mpr hd
      simpa [coeff_expression, hs0, hs] using hc s
  · rintro ⟨h0, hlo, hhi⟩
    apply PowerSeries.ext
    intro s
    rw [PowerSeries.coeff_mk, coeff_expression]
    by_cases hs0 : s = 0
    · subst s
      simpa using h0
    · have hs : 1 ≤ s := by omega
      by_cases hd : s ≤ d
      · simpa [hs0, hs, hd] using hlo s hs hd
      · simpa [hs0, hd] using hhi s (Nat.lt_of_not_ge hd)

end PaperVerification.FiniteHilbertSeries
end
end
end TAF_LiteralSource_0225

section TAF_LiteralSource_0226
/- Original module: PaperVerification.AlternatingFormsHilbertSeries -/


/-!
# Theorem 1.1 as an equality of formal Hilbert series

The coefficients in `exteriorPairHilbertSeries` are the dimensions of the
actual homogeneous pieces of the quotient by the two exterior forms.  The
coefficient theorem and the displayed finite series are rigorously equivalent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators Classical PowerSeries

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

@[expose]
def exteriorPairHilbertSeries (f g : ⋀[K]^2 M) : ℕ⟦X⟧ :=
  PowerSeries.mk fun s => Module.finrank K (ExteriorQuotientDegree f g s)

@[expose]
def paperExteriorHilbertSeries (n : ℕ) : ℕ⟦X⟧ :=
  FiniteHilbertSeries.expression (StripWalks.paperWalkCount n) ((n+1)/2)

theorem exteriorPairHilbertSeries_eq_iff (f g : ⋀[K]^2 M) (n : ℕ) :
    exteriorPairHilbertSeries f g = paperExteriorHilbertSeries n ↔
      Module.finrank K (ExteriorQuotientDegree f g 0) = 1 ∧
      (∀ s, 1 ≤ s → s ≤ (n+1)/2 →
        Module.finrank K (ExteriorQuotientDegree f g s) = StripWalks.paperWalkCount n s) ∧
      (∀ s, (n+1)/2 < s → Module.finrank K (ExteriorQuotientDegree f g s) = 0) :=
  FiniteHilbertSeries.mk_eq_expression_iff _ _ _

/-- The exact power-series formula of Theorem 1.1 on a nonempty principal
open in the complete coefficient space of pairs of exterior two-forms. -/
theorem paper_theorem_1_1_hilbertSeries [CharZero K] [FiniteDimensional K M]
    (n : ℕ) (hdim : Module.finrank K M = n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          (∃ y : (ι ⊕ ι) → K, eval y Q ≠ 0) ∧
          ∀ y : (ι ⊕ ι) → K, eval y Q ≠ 0 →
            exteriorPairHilbertSeries
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 =
                paperExteriorHilbertSeries n := by
  obtain ⟨ι, fin, h⟩ := paper_theorem_1_1 (K := K) (M := M) n hdim
  letI := fin
  obtain ⟨b₂, Q, hQ, hnonempty, h⟩ := h
  refine ⟨ι, fin, b₂, Q, hQ, hnonempty, ?_⟩
  intro y hy
  obtain ⟨h0, hlo, hhi⟩ := h y hy
  exact (exteriorPairHilbertSeries_eq_iff _ _ n).mpr
    ⟨h0, fun s hs hd => (hlo s hs hd).1, hhi⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0226

section TAF_LiteralSource_0227
/- Original module: PaperVerification.WeightedInitialFlat -/


/-!
# Flatness of the literal weighted Rees image

The parameter acts by the ordinary polynomial variable in `(P/Q)[t]`.
Every nonzero scalar polynomial has a unit coefficient after extension from
the original field, so it remains a nonzerodivisor even when `P/Q` has zero
divisors.  The actual image algebra is therefore torsion-free over `K[t]`,
and hence flat.  No reducedness, primality, or flatness premise is used.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.WeightedInitialFiber

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- The structure map of the actual one-parameter algebra. -/
@[expose]
def reesParameterMap (Q : Ideal P) (w : σ → ℕ) :
    Polynomial K →ₐ[K] reesAlgebra Q w := Polynomial.aeval (reesParameter Q w)

instance reesAlgebra_polynomialAlgebra (Q : Ideal P) (w : σ → ℕ) :
    Algebra (Polynomial K) (reesAlgebra Q w) :=
  (reesParameterMap Q w).toRingHom.toAlgebra

instance reesAlgebra_parameterTower (Q : Ideal P) (w : σ → ℕ) :
    IsScalarTower K (Polynomial K) (reesAlgebra Q w) :=
  IsScalarTower.of_algHom (reesParameterMap Q w)

theorem reesParameterMap_val (Q : Ideal P) (w : σ → ℕ) (f : Polynomial K) :
    (reesParameterMap Q w f).val=Polynomial.map (algebraMap K (P ⧸ Q)) f := by
  have he : (reesAlgebra Q w).val.comp (reesParameterMap Q w)=
      Polynomial.mapAlg K (P ⧸ Q) := by
    apply Polynomial.algHom_ext
    change (reesParameterMap Q w Polynomial.X).val=
      Polynomial.map (algebraMap K (P ⧸ Q)) Polynomial.X
    rw [reesParameterMap,Polynomial.aeval_X,Polynomial.map_X]
    exact reesMap_X Q w
  exact DFunLike.congr_fun he f

theorem reesPolynomial_smul_val (Q : Ideal P) (w : σ → ℕ)
    (f : Polynomial K) (a : reesAlgebra Q w) :
    (f • a).val=Polynomial.map (algebraMap K (P ⧸ Q)) f*a.val := by
  change ((reesParameterMap Q w f)*a).val=_
  rw [Subalgebra.coe_mul,reesParameterMap_val]

/-- A nonzero polynomial over the original field remains regular after
coefficient extension to any algebra, including a nonreduced quotient. -/
theorem scalarPolynomial_regular {A : Type*} [CommRing A] [Algebra K A]
    (f : Polynomial K) (hf : f≠0) :
    Polynomial.map (algebraMap K A) f∈nonZeroDivisors (Polynomial A) := by
  have hc : f.coeff f.natDegree≠0 := by
    simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hf
  have hu : IsUnit (algebraMap K A (f.coeff f.natDegree)) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap K A)
  apply Polynomial.mem_nonZeroDivisors_of_coeff_mem f.natDegree
  simpa only [Polynomial.coeff_map] using hu.mem_nonZeroDivisors

instance reesAlgebra_isTorsionFree (Q : Ideal P) (w : σ → ℕ) :
    Module.IsTorsionFree (Polynomial K) (reesAlgebra Q w) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro f a hfa
  by_cases hf : f=0
  · exact Or.inl hf
  · have hz : Polynomial.map (algebraMap K (P ⧸ Q)) f*a.val=0 := by
      simpa only [reesPolynomial_smul_val,ZeroMemClass.coe_zero] using
        congrArg Subtype.val hfa
    exact Or.inr (Subtype.ext ((scalarPolynomial_regular f hf).1 a.val hz))

/-- The actual family with the previously proved weighted-initial special
fiber is flat over the polynomial parameter ring. -/
instance reesAlgebra_flat (Q : Ideal P) (w : σ → ℕ) :
    Module.Flat (Polynomial K) (reesAlgebra Q w) := inferInstance

end PaperVerification.WeightedInitialFiber
end
end
end TAF_LiteralSource_0227

section TAF_LiteralSource_0228
/- Original module: PaperVerification.WeightedInitialGeneralFiber -/


/-!
# Every nonzero fiber of the actual weighted Rees family

The fiber map is ordinary evaluation of the parameter.  Its kernel is
proved by lifting to `P[Y]`, subtracting a normalized homogenization of an
actual relation, and dividing by `Y-c`.  This identifies every nonzero
fiber with the original quotient, rather than merely identifying one fiber
or assuming isotriviality.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.WeightedInitialFiber

open scoped BigOperators
open MvPolynomial

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

def scalarEval {A : Type*} [CommRing A] [Algebra K A] (c : K) :
    Polynomial A →ₐ[K] A where
  toRingHom := Polynomial.evalRingHom (algebraMap K A c)
  commutes' a := by
    change Polynomial.eval (algebraMap K A c)
      (Polynomial.C (algebraMap K A a)) = algebraMap K A a
    exact Polynomial.eval_C

@[simp] theorem scalarEval_C {A : Type*} [CommRing A] [Algebra K A]
    (c : K) (a : A) : scalarEval c (Polynomial.C a)=a := Polynomial.eval_C

@[simp] theorem scalarEval_X {A : Type*} [CommRing A] [Algebra K A]
    (c : K) : scalarEval c (Polynomial.X : Polynomial A)=algebraMap K A c :=
  Polynomial.eval_X

theorem scalarEval_monomial {A : Type*} [CommRing A] [Algebra K A]
    (c : K) (j : ℕ) (a : A) : scalarEval c (Polynomial.monomial j a)=c^j • a := by
  change (Polynomial.monomial j a).eval (algebraMap K A c)=_
  rw [Polynomial.eval_monomial]
  rw [Algebra.smul_def,map_pow,mul_comm]

def weightScale (w : σ → ℕ) (c : K) : P →ₐ[K] P :=
  MvPolynomial.aeval (fun i => c^w i • X i)

@[simp] theorem weightScale_X (w : σ → ℕ) (c : K) (i : σ) :
    weightScale w c (X i : P)=c^w i • X i :=
  MvPolynomial.aeval_X (fun j : σ => c^w j • (X j : P)) i

theorem weightScale_one (w : σ → ℕ) : weightScale (K := K) w 1=AlgHom.id K P := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [weightScale_X,one_pow,one_smul,AlgHom.id_apply]

theorem weightScale_comp (w : σ → ℕ) (c d : K) :
    (weightScale w c).comp (weightScale w d)=weightScale w (c*d) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply,weightScale_X,map_smul,smul_smul,mul_pow]
  rw [mul_comm]

theorem weightScale_inv_cancel (w : σ → ℕ) (c : K) (hc : c≠0) (p : P) :
    weightScale w c⁻¹ (weightScale w c p)=p := by
  have he := DFunLike.congr_fun (weightScale_comp w c⁻¹ c) p
  simpa only [AlgHom.comp_apply,inv_mul_cancel₀ hc,weightScale_one,AlgHom.id_apply] using he

theorem weightScale_cancel_inv (w : σ → ℕ) (c : K) (hc : c≠0) (p : P) :
    weightScale w c (weightScale w c⁻¹ p)=p := by
  have he := DFunLike.congr_fun (weightScale_comp w c c⁻¹) p
  simpa only [AlgHom.comp_apply,mul_inv_cancel₀ hc,weightScale_one,AlgHom.id_apply] using he

theorem weightScale_homogeneous (w : σ → ℕ) (c : K) (p : P) (d : ℕ)
    (hp : p.IsWeightedHomogeneous w d) : weightScale w c p=c^d • p := by
  simpa only [weightScale,Algebra.smul_def,←map_pow,MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X_left_apply] using hp.aeval_pow_mul (MvPolynomial.C c) MvPolynomial.X

theorem scalarEval_scaledQuotient (Q : Ideal P) (w : σ → ℕ) (c : K) (p : P) :
    scalarEval c (scaledQuotient Q w p)=Ideal.Quotient.mkₐ K Q (weightScale w c p) := by
  have he : (scalarEval c).comp (scaledQuotient Q w)=
      (Ideal.Quotient.mkₐ K Q).comp (weightScale w c) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [scaledQuotient,scaledPolynomial,AlgHom.comp_apply,aeval_X,map_mul,map_pow,
      Polynomial.coe_mapAlgHom,Polynomial.map_C,Polynomial.map_X,scalarEval_C,scalarEval_X,
      weightScale_X,map_smul,Algebra.smul_def,map_pow]
    rw [mul_comm,(Ideal.Quotient.mkₐ K Q).commutes c] <;> rfl
  exact DFunLike.congr_fun he p

def reesEvaluation (Q : Ideal P) (w : σ → ℕ) (c : K) :
    reesAlgebra Q w →ₐ[K] P ⧸ Q := (scalarEval c).comp (reesAlgebra Q w).val

theorem reesEvaluation_cover (Q : Ideal P) (w : σ → ℕ) (c : K) (g : Polynomial P) :
    reesEvaluation Q w c (reesCover Q w g)=
      Ideal.Quotient.mkₐ K Q (weightScale w c (scalarEval c g)) := by
  induction g using Polynomial.induction_on' with
  | add g h hg hh => simp only [map_add,hg,hh]
  | monomial j p =>
      change scalarEval c (reesMap Q w (Polynomial.monomial j p))=_
      rw [reesMap_monomial,map_mul,map_pow,scalarEval_X,scalarEval_scaledQuotient,
        scalarEval_monomial,map_smul,map_smul]
      calc
        _ = algebraMap K (P ⧸ Q) (c^j) *
            Ideal.Quotient.mkₐ K Q (weightScale w c p) := by
          rw [map_pow,mul_comm]
        _ = c^j • Ideal.Quotient.mkₐ K Q (weightScale w c p) :=
          (Algebra.smul_def (c^j)
            (Ideal.Quotient.mkₐ K Q (weightScale w c p))).symm

theorem reesEvaluation_surjective (Q : Ideal P) (w : σ → ℕ)
    (c : K) (hc : c≠0) : Function.Surjective (reesEvaluation Q w c) := by
  intro a
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective K Q a
  refine ⟨reesCover Q w (Polynomial.C (weightScale w c⁻¹ p)),?_⟩
  rw [reesEvaluation_cover,scalarEval_C,weightScale_cancel_inv w c hc]

theorem homogenize_scalarEval (w : σ → ℕ) (p : P) (d : ℕ) (hp : WeightBound w d p)
    (c : K) (hc : c≠0) :
    scalarEval c (homogenize w p d)=c^d • weightScale w c⁻¹ p := by
  rw [homogenize,map_sum]
  calc
    _ = ∑ j∈Finset.range (d+1),c^d • weightScale w c⁻¹
        (weightedHomogeneousComponent w j p) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [scalarEval_monomial,weightScale_homogeneous w c⁻¹ _ j
        (weightedHomogeneousComponent_isWeightedHomogeneous j p),smul_smul]
      congr 1
      have hle : j≤d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [pow_sub₀ c hc hle,inv_pow]
    _ = _ := by
      rw [←Finset.smul_sum,←map_sum,sum_components_of_bound w p d hp]

abbrev ParameterFiber (Q : Ideal P) (w : σ → ℕ) (c : K) :=
  reesAlgebra Q w ⧸ Ideal.span
    ({reesParameter Q w-algebraMap K (reesAlgebra Q w) c} : Set (reesAlgebra Q w))

theorem reesEvaluation_ker (Q : Ideal P) (w : σ → ℕ) (c : K) (hc : c≠0) :
    RingHom.ker (reesEvaluation Q w c).toRingHom=
      Ideal.span ({reesParameter Q w-algebraMap K (reesAlgebra Q w) c} :
        Set (reesAlgebra Q w)) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨g,hg⟩ := reesCover_surjective Q w a
    let p : P := weightScale w c (scalarEval c g)
    have hp : p∈Q := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change Ideal.Quotient.mkₐ K Q (weightScale w c (scalarEval c g))=0
      rw [←reesEvaluation_cover Q w c g,hg]
      exact ha
    let d := weightedTotalDegree w p
    let H : Polynomial P := (c⁻¹)^d • homogenize w p d
    have hH : reesCover Q w H=0 := by
      apply Subtype.ext
      change reesMap Q w H=0
      dsimp only [H]
      rw [map_smul,reesMap_homogenize Q w p d (weightBound_total w p),
        show Ideal.Quotient.mkₐ K Q p=0 from Ideal.Quotient.eq_zero_iff_mem.mpr hp]
      simp only [Polynomial.C_0,zero_mul,smul_zero,ZeroMemClass.coe_zero]
    have hEval : scalarEval c H=scalarEval c g := by
      dsimp only [H]
      rw [map_smul,homogenize_scalarEval w p d (weightBound_total w p) c hc,
        smul_smul,←mul_pow,inv_mul_cancel₀ hc,one_pow,one_smul]
      exact weightScale_inv_cancel w c hc (scalarEval c g)
    have hdvd : Polynomial.X-Polynomial.C (MvPolynomial.C c) ∣ g-H := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change scalarEval c (g-H)=0
      rw [map_sub,hEval,sub_self]
    obtain ⟨u,hu⟩ := hdvd
    have he : a=(reesParameter Q w-algebraMap K (reesAlgebra Q w) c)*reesCover Q w u := by
      rw [←hg,←sub_zero (reesCover Q w g),←hH,←map_sub,hu,map_mul,map_sub]
      congr 2
      exact (reesCover Q w).commutes c
    rw [he,mul_comm]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    rintro _ rfl
    change reesEvaluation Q w c (reesParameter Q w-algebraMap K (reesAlgebra Q w) c)=0
    rw [map_sub,AlgHom.commutes]
    change scalarEval c (reesMap Q w Polynomial.X)-_=0
    rw [reesMap_X,scalarEval_X,sub_self]

/-- Every actual nonzero parameter fiber is the original quotient algebra. -/
def nonzeroFiberEquiv (Q : Ideal P) (w : σ → ℕ) (c : K) (hc : c≠0) :
    ParameterFiber Q w c ≃ₐ[K] P ⧸ Q :=
  (Ideal.quotientEquivAlgOfEq K (reesEvaluation_ker Q w c hc).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (reesEvaluation_surjective Q w c hc))

end PaperVerification.WeightedInitialFiber
end
end
end TAF_LiteralSource_0228

section TAF_LiteralSource_0229
/- Original module: PaperVerification.AlternatingFormsOddFlatFamily -/


/-!
# The literal Richardson flat family for the canonical odd pencil

The algebra is the image generated by the parameter and the weighted
original Plücker coordinates.  Its flatness, special Richardson fiber,
and every nonzero original fiber are supplied by the proved algebraic
constructions, with no geometric flatness hypothesis.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open PaperVerification.WeightedInitialFiber
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

abbrev OddRichardsonFamily (k t : ℕ) :=
  reesAlgebra (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
    (pluckerVertexWeight (oddNatVertexWeight k))

/-- The actual special fiber, with its literal Richardson presentation. -/
def oddRichardsonSpecialFiberEquiv (k t : ℕ) (hs : t+2≤k+1) :
    ZeroFiber (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (pluckerVertexWeight (oddNatVertexWeight k)) ≃ₐ[K]
    MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
      intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) :=
  (initialQuotientEquiv _ _).symm.trans
    (Ideal.quotientEquivAlgOfEq K (odd_isotropic_initial_eq_interval k t hs))

/-- Every nonzero fiber is the original canonical isotropic Plücker ring. -/
def oddRichardsonNonzeroFiberEquiv (k t : ℕ) (c : K) (hc : c≠0) :
    ParameterFiber (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (pluckerVertexWeight (oddNatVertexWeight k)) c ≃ₐ[K]
    MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) :=
  nonzeroFiberEquiv _ _ c hc

/-- The exact affine-ring flat-degeneration clause, for the whole range
`2 ≤ s ≤ k+1` with `s=t+2`. The first member is the literal weighted image
algebra, rather than an abstract family supplied as a premise. -/
theorem odd_richardson_flat_family (k t : ℕ) (hs : t+2≤k+1) :
    Module.Flat (Polynomial K) (OddRichardsonFamily (K := K) k t) ∧
    Nonempty (ZeroFiber
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (pluckerVertexWeight (oddNatVertexWeight k)) ≃ₐ[K]
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
        intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)) ∧
    ∀ c : K,c≠0 → Nonempty (ParameterFiber
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (pluckerVertexWeight (oddNatVertexWeight k)) c ≃ₐ[K]
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) :=
  ⟨inferInstance,⟨oddRichardsonSpecialFiberEquiv k t hs⟩,
    fun c hc => ⟨oddRichardsonNonzeroFiberEquiv k t c hc⟩⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0229

section TAF_LiteralSource_0230
/- Original module: PaperVerification.AlternatingFormsHibiInterval -/


/-!
# The actual interval lattice and finite meet-join sorting

The elements are increasing coordinate tuples in the displayed interval.
Meet and join are literal coordinatewise minimum and maximum. Insertion
sorting replaces each adjacent comparison by meet and join, preserves the
length, and produces a genuine componentwise chain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

variable {s n : ℕ} (α β : Fin s → Fin n)

@[expose]
def IntervalIndex := {I : PluckerIndex s n // ∀ i,α i≤I.val i ∧ I.val i≤β i}

instance : Fintype (IntervalIndex α β) := by
  classical
  unfold IntervalIndex PluckerIndex
  infer_instance
instance : PartialOrder (IntervalIndex α β) := by
  unfold IntervalIndex PluckerIndex
  infer_instance

@[expose]
def meet (I J : IntervalIndex α β) : IntervalIndex α β :=
  ⟨⟨fun i => min (I.val.val i) (J.val.val i),by
    intro i j hij
    exact lt_min ((min_le_left _ _).trans_lt (I.val.property hij))
      ((min_le_right _ _).trans_lt (J.val.property hij))⟩,by
    intro i
    exact ⟨le_min (I.property i).1 (J.property i).1,
      (min_le_left _ _).trans (I.property i).2⟩⟩

@[expose]
def join (I J : IntervalIndex α β) : IntervalIndex α β :=
  ⟨⟨fun i => max (I.val.val i) (J.val.val i),by
    intro i j hij
    exact max_lt ((I.val.property hij).trans_le (le_max_left _ _))
      ((J.val.property hij).trans_le (le_max_right _ _))⟩,by
    intro i
    exact ⟨(I.property i).1.trans (le_max_left _ _),
      max_le (I.property i).2 (J.property i).2⟩⟩

theorem meet_le_left (I J : IntervalIndex α β) : meet α β I J≤I :=
  fun i => min_le_left _ _

theorem meet_le_right (I J : IntervalIndex α β) : meet α β I J≤J :=
  fun i => min_le_right _ _

theorem left_le_join (I J : IntervalIndex α β) : I≤join α β I J :=
  fun i => le_max_left _ _

theorem right_le_join (I J : IntervalIndex α β) : J≤join α β I J :=
  fun i => le_max_right _ _

theorem le_meet (A I J : IntervalIndex α β) (hI : A≤I) (hJ : A≤J) : A≤meet α β I J :=
  fun i => le_min (hI i) (hJ i)

theorem meet_eq_left (I J : IntervalIndex α β) (h : I≤J) : meet α β I J=I := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact min_eq_left (h i)

theorem meet_eq_right (I J : IntervalIndex α β) (h : J≤I) : meet α β I J=J := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact min_eq_right (h i)

theorem join_eq_right (I J : IntervalIndex α β) (h : I≤J) : join α β I J=J := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact max_eq_right (h i)

theorem join_eq_left (I J : IntervalIndex α β) (h : J≤I) : join α β I J=I := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact max_eq_left (h i)

def insert (I : IntervalIndex α β) : List (IntervalIndex α β) → List (IntervalIndex α β)
  | [] => [I]
  | J::L => meet α β I J :: insert (join α β I J) L

@[simp] theorem length_insert (I : IntervalIndex α β) (L : List (IntervalIndex α β)) :
    (insert α β I L).length=L.length+1 := by
  induction L generalizing I with
  | nil => rfl
  | cons J L ih => simp only [insert,List.length_cons,ih]

theorem insert_lower_bound (A I : IntervalIndex α β) (L : List (IntervalIndex α β))
    (hI : A≤I) (hL : ∀ J∈L,A≤J) : ∀ J∈insert α β I L,A≤J := by
  induction L generalizing I with
  | nil =>
      intro J hJ
      have he : J=I := List.mem_singleton.mp hJ
      exact he.symm ▸ hI
  | cons J L ih =>
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact le_meet α β A I J hI (hL J List.mem_cons_self)
      · exact ih (join α β I J) (hI.trans (left_le_join α β I J))
          (fun T hT => hL T (List.mem_cons_of_mem _ hT)) Z hZ

theorem insert_sorted (I : IntervalIndex α β) (L : List (IntervalIndex α β))
    (hL : L.Pairwise (·≤·)) : (insert α β I L).Pairwise (·≤·) := by
  induction L generalizing I with
  | nil => simp only [insert,List.pairwise_singleton]
  | cons J L ih =>
      have h := List.pairwise_cons.mp hL
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih (join α β I J) h.2⟩
      exact insert_lower_bound α β (meet α β I J) (join α β I J) L
        ((meet_le_left α β I J).trans (left_le_join α β I J))
        (fun T hT => (meet_le_right α β I J).trans (h.1 T hT))

def sort (L : List (IntervalIndex α β)) : List (IntervalIndex α β) :=
  L.foldr (insert α β) []

@[simp] theorem length_sort (L : List (IntervalIndex α β)) :
    (sort α β L).length=L.length := by
  induction L with
  | nil => rfl
  | cons I L ih =>
      change (insert α β I (sort α β L)).length=(I::L).length
      rw [length_insert,ih,List.length_cons]

theorem sort_sorted (L : List (IntervalIndex α β)) :
    (sort α β L).Pairwise (·≤·) := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons I L ih => exact insert_sorted α β I (sort α β L) ih

def chainOfList (L : List (IntervalIndex α β)) (hL : L.Pairwise (·≤·)) :
    BandChain α β L.length :=
  ⟨fun j => (L.get j).val.val,fun j => (L.get j).val.property,
    (fun j i => (L.get j).property i),fun a b hab => hL.rel_get_of_le hab⟩

def intervalIndexOfChain {r : ℕ} (C : BandChain α β r) (j : Fin r) :
    IntervalIndex α β := ⟨⟨C.val j,C.property.1 j⟩,C.property.2.1 j⟩

theorem intervalIndexOfChain_injective {r : ℕ} :
    Function.Injective (fun C : BandChain α β r => intervalIndexOfChain α β C) := by
  intro C D h
  apply Subtype.ext
  funext j i
  exact congrArg (fun I : IntervalIndex α β => I.val.val i) (congrFun h j)

end PaperVerification.AlternatingForms.Hibi
end
end
end TAF_LiteralSource_0230

section TAF_LiteralSource_0231
/- Original module: PaperVerification.AlternatingFormsHibiPresentation -/


/-!
# The literal Hibi presentation and its complete chain basis

The defining binomials replace incomparable tuples by their coordinatewise
meet and join. Finite lattice insertion sorts every actual product modulo
these relations. Diagonal exponent vectors distinguish all chains, proving
both independence and equality with the actual diagonal-monomial kernel.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] {s n : ℕ} (α β : Fin s → Fin n)

@[expose]
def incomparable (I J : IntervalIndex α β) : Prop := ¬I≤J ∧ ¬J≤I

@[expose]
def relation (I J : IntervalIndex α β) : MvPolynomial (IntervalIndex α β) K :=
  X I*X J-X (meet α β I J)*X (join α β I J)

@[expose]
def relationIdeal : Ideal (MvPolynomial (IntervalIndex α β) K) :=
  Ideal.span {p | ∃ I J,incomparable α β I J ∧ p=relation α β I J}

theorem relation_mem (I J : IntervalIndex α β) : relation (K := K) α β I J∈relationIdeal α β := by
  classical
  by_cases hIJ : I≤J
  · simp only [relation,meet_eq_left α β I J hIJ,join_eq_right α β I J hIJ,sub_self,
      Ideal.zero_mem]
  · by_cases hJI : J≤I
    · simp only [relation,meet_eq_right α β I J hJI,join_eq_left α β I J hJI,
        mul_comm (X I) (X J),sub_self,Ideal.zero_mem]
    · exact Ideal.subset_span ⟨I,J,⟨hIJ,hJI⟩,rfl⟩

def diagonalMonomial (I : IntervalIndex α β) : MvPolynomial (Fin s × Fin n) K :=
  monomial (minorTermExponent I.val.val 1) 1

def diagonalMap : MvPolynomial (IntervalIndex α β) K →ₐ[K]
    MvPolynomial (Fin s × Fin n) K := aeval (diagonalMonomial α β)

theorem pair_exponents (I J : IntervalIndex α β) :
    minorTermExponent (meet α β I J).val.val 1+
        minorTermExponent (join α β I J).val.val 1=
      minorTermExponent I.val.val 1+minorTermExponent J.val.val 1 := by
  simp only [minorTermExponent,Equiv.Perm.one_apply]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : I.val.val i≤J.val.val i
  · simp only [meet,join,min_eq_left h,max_eq_right h]
  · have h' : J.val.val i≤I.val.val i := (le_of_not_ge h)
    simp only [meet,join,min_eq_right h',max_eq_left h',add_comm]

theorem diagonalMap_relation (I J : IntervalIndex α β) :
    diagonalMap (K := K) α β (relation α β I J)=0 := by
  simp only [relation,diagonalMap,map_sub,map_mul,aeval_X,diagonalMonomial,
    monomial_mul,one_mul,pair_exponents,sub_self]

theorem relationIdeal_le_kernel :
    relationIdeal (K := K) α β≤RingHom.ker (diagonalMap α β).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨I,J,h,rfl⟩
  exact diagonalMap_relation α β I J

def diagonalQuotientMap :
    (MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β) →ₐ[K]
      MvPolynomial (Fin s × Fin n) K :=
  Ideal.Quotient.liftₐ _ (diagonalMap α β) (fun p hp => relationIdeal_le_kernel α β hp)

def word (L : List (IntervalIndex α β)) : MvPolynomial (IntervalIndex α β) K :=
  (L.map X).prod

@[simp] theorem word_nil : word (K := K) α β []=1 := rfl

@[simp] theorem word_cons (I : IntervalIndex α β) (L : List (IntervalIndex α β)) :
    word (K := K) α β (I::L)=X I*word α β L := rfl

theorem quotient_pair (I J : IntervalIndex α β) :
    Ideal.Quotient.mk (relationIdeal (K := K) α β) (X I*X J)=
      Ideal.Quotient.mk _ (X (meet α β I J)*X (join α β I J)) :=
  (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (relation_mem α β I J)

theorem quotient_word_insert (I : IntervalIndex α β) (L : List (IntervalIndex α β)) :
    Ideal.Quotient.mk (relationIdeal (K := K) α β) (word α β (insert α β I L))=
      Ideal.Quotient.mk _ (X I*word α β L) := by
  induction L generalizing I with
  | nil => simp only [insert,word_cons,word_nil,mul_one]
  | cons J L ih =>
      simp only [insert,word_cons,map_mul]
      rw [ih,map_mul,←mul_assoc,←map_mul,←quotient_pair,map_mul,mul_assoc]

theorem quotient_word_sort (L : List (IntervalIndex α β)) :
    Ideal.Quotient.mk (relationIdeal (K := K) α β) (word α β (sort α β L))=
      Ideal.Quotient.mk _ (word α β L) := by
  induction L with
  | nil => rfl
  | cons I L ih =>
      change Ideal.Quotient.mk _ (word α β (insert α β I (sort α β L)))=_
      rw [quotient_word_insert,word_cons,map_mul,map_mul,ih]

def standardPolynomial {r : ℕ} (C : BandChain α β r) :
    MvPolynomial (IntervalIndex α β) K := ∏ j,X (intervalIndexOfChain α β C j)

def standardClass (C : Σ r,BandChain α β r) :
    MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β :=
  Ideal.Quotient.mk _ (standardPolynomial α β C.2)

theorem standardPolynomial_word {r : ℕ} (C : BandChain α β r) :
    standardPolynomial (K := K) α β C=
      word α β (List.ofFn (intervalIndexOfChain α β C)) := by
  simp only [word,List.map_ofFn,List.prod_ofFn,standardPolynomial,Function.comp_def]

theorem standardPolynomial_chainOfList (L : List (IntervalIndex α β))
    (hL : L.Pairwise (·≤·)) :
    standardPolynomial (K := K) α β (chainOfList α β L hL)=word α β L := by
  rw [standardPolynomial_word]
  congr 1
  have he : intervalIndexOfChain α β (chainOfList α β L hL)=L.get := rfl
  rw [he,List.ofFn_get]

def standardSpan : Submodule K (MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β) :=
  Submodule.span K (Set.range (standardClass α β))

theorem word_class_mem_standardSpan (L : List (IntervalIndex α β)) :
    Ideal.Quotient.mk (relationIdeal (K := K) α β) (word α β L)∈standardSpan α β := by
  rw [←quotient_word_sort]
  apply Submodule.subset_span
  refine ⟨⟨(sort α β L).length,chainOfList α β _ (sort_sorted α β L)⟩,?_⟩
  rw [standardClass,standardPolynomial_chainOfList]

theorem standardSpan_mul_variable
    {z : MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β}
    (hz : z∈standardSpan α β) (I : IntervalIndex α β) :
    z*Ideal.Quotient.mk _ (X I)∈standardSpan α β := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨C,rfl⟩ := hz
      have h := word_class_mem_standardSpan (K := K) α β
        (I::List.ofFn (intervalIndexOfChain α β C.2))
      simpa only [word_cons,map_mul,←standardPolynomial_word,standardClass,mul_comm] using h
  | zero => simpa only [zero_mul] using (standardSpan (K := K) α β).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [add_mul] using (standardSpan α β).add_mem ihx ihy
  | smul a x hx ih =>
      simpa only [smul_mul_assoc] using (standardSpan α β).smul_mem a ih

theorem standardSpan_eq_top : standardSpan (K := K) α β=⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h1 := word_class_mem_standardSpan (K := K) α β []
      simp only [word_nil,map_one] at h1
      have ha := (standardSpan α β).smul_mem a h1
      change (algebraMap K (MvPolynomial (IntervalIndex α β) K ⧸ relationIdeal α β)) a ∈
        standardSpan α β
      rw [Algebra.algebraMap_eq_smul_one]
      exact ha
  | add p q hp hq => simpa only [map_add] using (standardSpan α β).add_mem hp hq
  | mul_X p I hp => simpa only [map_mul] using standardSpan_mul_variable α β hp I

theorem diagonalMap_standardPolynomial {r : ℕ} (C : BandChain α β r) :
    diagonalMap (K := K) α β (standardPolynomial α β C)=
      monomial (chainDiagonalExponent C.val) 1 := by
  unfold standardPolynomial
  rw [map_prod]
  trans ∏ i : Fin r,diagonalMonomial (K := K) α β (intervalIndexOfChain α β C i)
  · apply Finset.prod_congr rfl
    intro i hi
    exact MvPolynomial.aeval_X (diagonalMonomial (K := K) α β)
      (intervalIndexOfChain α β C i)
  · simp only [diagonalMonomial,intervalIndexOfChain,
      prod_monomial_eq_monomial_sum,Finset.prod_const_one,
      chainDiagonalExponent,chainTermExponent]

theorem diagonalStandardProducts_linearIndependent (hs : 0<s) :
    LinearIndependent K (fun C : Σ r,BandChain α β r =>
      (monomial (chainDiagonalExponent C.2.val) 1 : MvPolynomial (Fin s × Fin n) K)) := by
  simpa only [MvPolynomial.coe_basisMonomials,Function.comp_def] using
    (MvPolynomial.basisMonomials (Fin s × Fin n) K).linearIndependent.comp
      (fun C : Σ r,BandChain α β r => chainDiagonalExponent C.2.val)
      (allChainDiagonalExponent_injective α β hs)

theorem diagonalQuotientMap_injective (hs : 0<s) :
    Function.Injective (diagonalQuotientMap (K := K) α β) := by
  change Function.Injective (diagonalQuotientMap (K := K) α β).toLinearMap
  apply LinearMap.injective_of_linearIndependent
    (f := (diagonalQuotientMap (K := K) α β).toLinearMap)
    (show Submodule.span K (Set.range (standardClass (K := K) α β))=⊤ from
      standardSpan_eq_top α β)
  have he : (diagonalQuotientMap (K := K) α β).toLinearMap ∘ standardClass α β=
      fun C : Σ r,BandChain α β r => monomial (chainDiagonalExponent C.2.val) 1 := by
    funext C
    exact diagonalMap_standardPolynomial α β C.2
  rw [he]
  exact diagonalStandardProducts_linearIndependent α β hs

theorem relationIdeal_eq_kernel (hs : 0<s) :
    relationIdeal (K := K) α β=RingHom.ker (diagonalMap α β).toRingHom := by
  apply le_antisymm (relationIdeal_le_kernel α β)
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply diagonalQuotientMap_injective α β hs
  change diagonalMap α β p=diagonalQuotientMap α β 0
  rw [map_zero]
  exact hp

theorem relationIdeal_isPrime (hs : 0<s) : (relationIdeal (K := K) α β).IsPrime := by
  rw [relationIdeal_eq_kernel α β hs]
  exact RingHom.ker_isPrime _

theorem standardClass_linearIndependent (hs : 0<s) :
    LinearIndependent K (standardClass (K := K) α β) := by
  apply LinearIndependent.of_comp (diagonalQuotientMap α β).toLinearMap
  have he : (diagonalQuotientMap (K := K) α β).toLinearMap ∘ standardClass α β=
      fun C : Σ r,BandChain α β r => monomial (chainDiagonalExponent C.2.val) 1 := by
    funext C
    exact diagonalMap_standardPolynomial α β C.2
  rw [he]
  exact diagonalStandardProducts_linearIndependent α β hs

/-- The full Hibi chain basis, in the literal binomial quotient. -/
def standardBasis (hs : 0<s) : Module.Basis (Σ r,BandChain α β r) K
    (MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β) :=
  Module.Basis.mk (standardClass_linearIndependent α β hs)
    (by rw [←standardSpan_eq_top (K := K) α β]; exact le_rfl)

end PaperVerification.AlternatingForms.Hibi
end
end
end TAF_LiteralSource_0231

section TAF_LiteralSource_0232
/- Original module: PaperVerification.AlternatingFormsGoodPresentation -/


/-!
# Removing the forbidden variables from the actual Richardson presentation

The source ring has exactly the interval variables. Its map to the full
Richardson quotient is proved surjective by setting the forbidden variables
to zero. Its kernel is the kernel of the literal band-minor substitution,
using the previously proved injectivity of the actual band chart map.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] {s n : ℕ}
  (α β : Fin s → Fin n)

@[expose]
def goodBandMap : MvPolynomial (IntervalIndex α β) K →ₐ[K]
    MvPolynomial (Fin s × Fin n) K :=
  aeval (fun I => bandMinor α β I.val.val)

@[expose]
def goodBandIdeal : Ideal (MvPolynomial (IntervalIndex α β) K) :=
  RingHom.ker (goodBandMap α β).toRingHom

def goodToInterval : MvPolynomial (IntervalIndex α β) K →ₐ[K]
    (MvPolynomial (PluckerIndex s n) K⧸intervalPluckerIdeal α β) :=
  (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)).comp
    (rename (fun I : IntervalIndex α β => I.val))

def eraseForbidden : MvPolynomial (PluckerIndex s n) K →ₐ[K]
    MvPolynomial (IntervalIndex α β) K :=
  aeval (fun I => if h : ∀ i,α i≤I.val i ∧ I.val i≤β i then X ⟨I,h⟩ else 0)

theorem goodToInterval_eraseForbidden (p : MvPolynomial (PluckerIndex s n) K) :
    goodToInterval α β (eraseForbidden α β p)=Ideal.Quotient.mkₐ K _ p := by
  have he : (goodToInterval (K := K) α β).comp (eraseForbidden α β)=
      Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) := by
    apply MvPolynomial.algHom_ext
    intro I
    simp only [AlgHom.comp_apply,eraseForbidden,aeval_X]
    split_ifs with h
    · unfold goodToInterval
      simp only [AlgHom.comp_apply]
      erw [MvPolynomial.rename_X]
    · rw [map_zero]
      symm
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right (Ideal.subset_span ⟨I,h,rfl⟩))
  exact congrArg (fun f : MvPolynomial (PluckerIndex s n) K →ₐ[K]
    (MvPolynomial (PluckerIndex s n) K⧸intervalPluckerIdeal α β) => f p) he

theorem goodToInterval_surjective : Function.Surjective (goodToInterval (K := K) α β) := by
  intro z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective K (intervalPluckerIdeal α β) z
  exact ⟨eraseForbidden α β p,goodToInterval_eraseForbidden α β p⟩

theorem intervalBandMap_goodToInterval (hα : Monotone α) (hβ : Monotone β)
    (p : MvPolynomial (IntervalIndex α β) K) :
    intervalBandMap α β hα hβ (goodToInterval α β p)=goodBandMap α β p := by
  have he : (intervalBandMap (K := K) α β hα hβ).comp (goodToInterval α β)=
      goodBandMap α β := by
    apply MvPolynomial.algHom_ext
    intro I
    unfold goodToInterval intervalBandMap goodBandMap bandPluckerMap
    simp only [AlgHom.comp_apply,rename_X,Ideal.Quotient.mkₐ_eq_mk]
    erw [Ideal.Quotient.liftₐ_apply,Ideal.Quotient.lift_mk,MvPolynomial.aeval_X]
    exact (MvPolynomial.aeval_X
      (fun J : IntervalIndex α β => bandMinor (K := K) α β J.val.val) I).symm
  exact congrArg (fun f : MvPolynomial (IntervalIndex α β) K →ₐ[K]
    MvPolynomial (Fin s × Fin n) K => f p) he

theorem goodToInterval_kernel (hα : Monotone α) (hβ : Monotone β) (hs : 0<s) :
    RingHom.ker (goodToInterval (K := K) α β).toRingHom=goodBandIdeal α β := by
  ext p
  change goodToInterval α β p=0 ↔ goodBandMap α β p=0
  rw [←intervalBandMap_goodToInterval α β hα hβ p,
    ←map_zero (intervalBandMap (K := K) α β hα hβ)]
  exact (intervalBandMap_injective α β hα hβ hs).eq_iff.symm

def goodBandQuotientEquiv (hα : Monotone α) (hβ : Monotone β) (hs : 0<s) :
    (MvPolynomial (IntervalIndex α β) K⧸goodBandIdeal α β) ≃ₐ[K]
      (MvPolynomial (PluckerIndex s n) K⧸intervalPluckerIdeal α β) :=
  (Ideal.quotientEquivAlgOfEq K (goodToInterval_kernel α β hα hβ hs).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (goodToInterval_surjective α β))

@[simp] theorem goodBandQuotientEquiv_mk (hα : Monotone α) (hβ : Monotone β)
    (hs : 0<s) (p : MvPolynomial (IntervalIndex α β) K) :
    goodBandQuotientEquiv α β hα hβ hs (Ideal.Quotient.mk _ p)=goodToInterval α β p := by
  rfl

theorem goodBandMap_standardPolynomial {r : ℕ} (C : BandChain α β r) :
    goodBandMap (K := K) α β (standardPolynomial α β C)=bandStandardProduct α β C := by
  unfold standardPolynomial bandStandardProduct
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact MvPolynomial.aeval_X (f := fun I : IntervalIndex α β =>
    bandMinor (K := K) α β I.val.val) (intervalIndexOfChain α β C i)

theorem goodToInterval_standardPolynomial {r : ℕ} (C : BandChain α β r) :
    goodToInterval (K := K) α β (standardPolynomial α β C)=intervalStandardProduct α β C := by
  unfold goodToInterval standardPolynomial
  simp only [AlgHom.comp_apply,map_prod,intervalIndexOfChain,
    intervalStandardProduct,chainPluckerProduct,Ideal.Quotient.mkₐ_eq_mk,map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  erw [MvPolynomial.rename_X]

theorem goodBandMap_mem_standardSpan (hα : Monotone α) (hβ : Monotone β)
    (p : MvPolynomial (IntervalIndex α β) K) :
    goodBandMap α β p∈Submodule.span K
      (Set.range (fun C : Σ r,BandChain α β r =>
        goodBandMap α β (standardPolynomial α β C.2))) := by
  have h : goodToInterval α β p∈intervalStandardSpan (K := K) α β := by
    rw [intervalStandardSpan_eq_top]
    trivial
  rw [←intervalBandMap_goodToInterval α β hα hβ]
  generalize hz : goodToInterval α β p = z at h ⊢
  clear hz
  induction h using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨C,rfl⟩ := hz
      apply Submodule.subset_span
      exact ⟨C,by
        change goodBandMap α β (standardPolynomial α β C.2)=_
        rw [goodBandMap_standardPolynomial]
        exact (intervalBandMap_standardProduct α β hα hβ C.2).symm⟩
  | zero => simpa only [map_zero] using (Submodule.zero_mem _)
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

end PaperVerification.AlternatingForms.Hibi
end
end
end TAF_LiteralSource_0232

section TAF_LiteralSource_0233
/- Original module: PaperVerification.WeightedSagbiCore -/


/-!
# An exact initial-kernel criterion from actual leading monomials

The criterion uses a spanning family in the literal polynomial image. Its
distinct greatest monomials force every finite normal form to respect the
filtration. The resulting equality is an equality of the full conventional
initial ideal and the actual monomial-evaluation kernel; no flatness, Hilbert
function, or equality of dimensions is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedSagbi

open MvPolynomial
open scoped BigOperators
open AlternatingForms WeightedInitialFiber

variable {K σ τ C : Type*} [Field K]

theorem natCast_weight (w : τ → ℕ) (a : τ →₀ ℕ) :
    (Finsupp.weight w a : ℤ)=Finsupp.weight (fun i => (w i : ℤ)) a := by
  simp only [Finsupp.weight_apply,Finsupp.sum,nsmul_eq_mul,Nat.cast_sum,Nat.cast_mul,Nat.cast_id]

theorem weightBound_of_weightMonic (w : τ → ℕ) (p : MvPolynomial τ K)
    (a : τ →₀ ℕ) (hp : IsWeightMonic (fun i => (w i : ℤ)) p a) :
    WeightBound w (Finsupp.weight w a) p := by
  intro b hb
  have h := hp.weight_le hb
  rw [←natCast_weight,←natCast_weight] at h
  exact_mod_cast h

theorem component_of_weightMonic (w : τ → ℕ) (p : MvPolynomial τ K)
    (a : τ →₀ ℕ) (hp : IsWeightMonic (fun i => (w i : ℤ)) p a) :
    weightedHomogeneousComponent w (Finsupp.weight w a) p=monomial a 1 := by
  classical
  ext b
  rw [coeff_weightedHomogeneousComponent,coeff_monomial]
  by_cases hba : b=a
  · subst b
    simp only [hp.1,ite_true]
  · rw [if_neg (Ne.symm hba)]
    by_cases hw : Finsupp.weight w b=Finsupp.weight w a
    · rw [if_pos hw]
      apply hp.2 b hba
      rw [←natCast_weight,←natCast_weight,hw]
    · rw [if_neg hw]

theorem weightBound_smul (w : σ → ℕ) (d : ℕ) (a : K) (p : MvPolynomial σ K)
    (hp : WeightBound w d p) : WeightBound w d (a • p) := by
  intro b hb
  apply hp b
  intro h
  exact hb (by simp only [coeff_smul,h,smul_zero])

theorem weightBound_sub (w : σ → ℕ) (d : ℕ) (p q : MvPolynomial σ K)
    (hp : WeightBound w d p) (hq : WeightBound w d q) : WeightBound w d (p-q) := by
  simpa only [neg_one_smul,sub_eq_add_neg] using
    weightBound_add w d hp (weightBound_smul w d (-1 : K) q hq)

/-- In a finite expansion by distinct leading monomials, vanishing of the
top component forces every nonzero coefficient strictly below that degree. -/
theorem expansion_degree_lt (u : τ → ℕ) (v : C → MvPolynomial τ K)
    (a : C → τ →₀ ℕ) (degree : C → ℕ)
    (ha : Function.Injective a)
    (hv : ∀ c,IsWeightMonic (fun i => (u i : ℤ)) (v c) (a c))
    (hw : ∀ c,Finsupp.weight u (a c)=degree c)
    (coeff : C →₀ K) (d : ℕ)
    (hbound : WeightBound u d (coeff.sum fun c z => z • v c))
    (htop : weightedHomogeneousComponent u d (coeff.sum fun c z => z • v c)=0) :
    ∀ c,coeff c≠0 → degree c<d := by
  classical
  intro c hc
  have hS : coeff.support.Nonempty := ⟨c,Finsupp.mem_support_iff.mpr hc⟩
  obtain ⟨j,hj,hmax⟩ := coeff.support.exists_max_image degree hS
  have hcj : coeff j≠0 := Finsupp.mem_support_iff.mp hj
  have hlead : (coeff.sum fun c z => z • v c).coeff (a j)=coeff j := by
    simp only [Finsupp.sum,coeff_sum]
    rw [Finset.sum_eq_single j]
    · rw [coeff_smul,(hv j).1,smul_eq_mul,mul_one]
    · intro i hi hij
      rw [coeff_smul,(hv i).2 (a j) (fun he => hij (ha he.symm)),smul_zero]
      rw [←natCast_weight,←natCast_weight,hw,hw]
      exact_mod_cast hmax i hi
    · intro h
      exact (h hj).elim
  have hle : degree j≤d := by
    rw [←hw j]
    exact hbound (a j) (by rwa [hlead])
  have hne : degree j≠d := by
    intro he
    have h := congrArg (fun p : MvPolynomial τ K => p.coeff (a j)) htop
    rw [coeff_weightedHomogeneousComponent,hw,he,if_pos rfl,hlead] at h
    exact hcj (by simpa using h)
  exact (hmax c (Finsupp.mem_support_iff.mpr hc)).trans_lt (lt_of_le_of_ne hle hne)

section ExactKernel

variable (w : σ → ℕ) (u : τ → ℕ)
  (f f₀ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
  (v : C → MvPolynomial σ K) (degree : C → ℕ) (a : C → τ →₀ ℕ)
  (ha : Function.Injective a)
  (hv : ∀ c,(v c).IsWeightedHomogeneous w (degree c))
  (hlead : ∀ c,IsWeightMonic (fun i => (u i : ℤ)) (f (v c)) (a c))
  (hw : ∀ c,Finsupp.weight u (a c)=degree c)
  (hspan : ∀ p,f p∈Submodule.span K (Set.range (fun c => f (v c))))
  (hbound : ∀ p d,WeightBound w d p → WeightBound u d (f p))
  (htop : ∀ p d,WeightBound w d p →
    weightedHomogeneousComponent u d (f p)=f₀ (weightedHomogeneousComponent w d p))
  (hgraded : ∀ p d,weightedHomogeneousComponent u d (f₀ p)=
    f₀ (weightedHomogeneousComponent w d p))

include ha hv hlead hw hspan hbound htop hgraded

theorem homogeneous_kernel_mem_initial (p : MvPolynomial σ K) (d : ℕ)
    (hp : p.IsWeightedHomogeneous w d) (hp₀ : f₀ p=0) :
    p∈initialIdeal (RingHom.ker f.toRingHom) w := by
  classical
  have hbp : WeightBound w d p := fun b hb => (hp hb).le
  have hfp : weightedHomogeneousComponent u d (f p)=0 := by
    rw [htop p d hbp,weightedHomogeneousComponent_eq_self hp,hp₀]
  obtain ⟨coeff,hcoeff⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan p)
  have hsum : (coeff.sum fun c z => z • f (v c))=f p := by
    simpa only [Finsupp.linearCombination_apply] using hcoeff
  have hdeg : ∀ c,coeff c≠0 → degree c<d :=
    expansion_degree_lt u (fun c => f (v c)) a degree ha hlead hw coeff d
      (by rw [hsum]; exact hbound p d hbp) (by rw [hsum]; exact hfp)
  let q : MvPolynomial σ K := coeff.sum fun c z => z • v c
  have hfq : f q=f p := by
    simpa only [q,Finsupp.sum,map_sum,map_smul] using hsum
  have hbq : WeightBound w d q := by
    apply weightBound_sum
    intro c hc
    apply weightBound_smul
    intro b hb
    exact (hv c hb).le.trans (hdeg c (Finsupp.mem_support_iff.mp hc)).le
  have htq : weightedHomogeneousComponent w d q=0 := by
    simp only [q,Finsupp.sum,map_sum,map_smul]
    apply Finset.sum_eq_zero
    intro c hc
    rw [weightedHomogeneousComponent_of_mem (hv c),if_neg,smul_zero]
    exact (hdeg c (Finsupp.mem_support_iff.mp hc)).ne'
  have hr : p-q∈RingHom.ker f.toRingHom := by
    change f (p-q)=0
    rw [map_sub,hfq,sub_self]
  have h := component_mem_initialIdeal (RingHom.ker f.toRingHom) w (p-q) hr d
    (weightBound_sub w d p q hbp hbq)
  rwa [map_sub,weightedHomogeneousComponent_eq_self hp,htq,sub_zero] at h

/-- The entire initial ideal, with no restriction on polynomial degree or
standard-family cardinality, is the literal monomial-map kernel. -/
theorem initial_kernel_eq :
    initialIdeal (RingHom.ker f.toRingHom) w=RingHom.ker f₀.toRingHom := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    change f₀ (weightedHomogeneousComponent w (weightedTotalDegree w p) p)=0
    rw [←htop p _ (weightBound_total w p)]
    change weightedHomogeneousComponent u _ (f p)=0
    rw [show f p=0 from hp,map_zero]
  · intro p hp
    rw [←sum_components_of_bound w p (weightedTotalDegree w p) (weightBound_total w p)]
    apply Ideal.sum_mem
    intro d hd
    apply homogeneous_kernel_mem_initial w u f f₀ v degree a ha hv hlead hw hspan
      hbound htop hgraded _ d (weightedHomogeneousComponent_isWeightedHomogeneous d p)
    rw [←hgraded p d,show f₀ p=0 from hp,map_zero]

end ExactKernel
end PaperVerification.WeightedSagbi
end
end
end TAF_LiteralSource_0233

section TAF_LiteralSource_0234
/- Original module: PaperVerification.WeightedSagbiSubstitution -/


/-!
# Weighted top parts of the actual polynomial substitution

Products of the specified greatest monomials give the greatest monomial of
each substituted source monomial. Finite coefficient expansion then proves
the bounded top-component and graded monomial-substitution identities used
by the exact initial-kernel criterion.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedSagbi

open MvPolynomial
open scoped BigOperators
open AlternatingForms WeightedInitialFiber

variable {K σ τ : Type*} [Field K]

def exponentMap (a : σ → τ →₀ ℕ) : (σ →₀ ℕ) →ₗ[ℕ] (τ →₀ ℕ) :=
  Finsupp.linearCombination ℕ a

@[expose]
def inducedWeight (u : τ → ℕ) (a : σ → τ →₀ ℕ) : σ → ℕ :=
  fun i => Finsupp.weight u (a i)

theorem exponentMap_weight (u : τ → ℕ) (a : σ → τ →₀ ℕ) (m : σ →₀ ℕ) :
    Finsupp.weight u (exponentMap a m)=Finsupp.weight (inducedWeight u a) m := by
  change Finsupp.linearCombination ℕ u (Finsupp.linearCombination ℕ a m)=
    Finsupp.linearCombination ℕ (fun i => Finsupp.linearCombination ℕ u (a i)) m
  exact Finsupp.linearCombination_linearCombination ℕ u a m

def monomialSubstitution (a : σ → τ →₀ ℕ) :
    MvPolynomial σ K →ₐ[K] MvPolynomial τ K :=
  aeval (fun i => monomial (a i) 1)

theorem monomialSubstitution_monomial (a : σ → τ →₀ ℕ) (m : σ →₀ ℕ) (c : K) :
    monomialSubstitution a (monomial m c)=monomial (exponentMap a m) c := by
  classical
  simp only [monomialSubstitution,aeval_monomial,exponentMap,Finsupp.linearCombination_apply,
    Finsupp.prod,Finsupp.sum,monomial_pow,one_pow]
  rw [show (∏ i ∈ m.support,monomial (m i • a i) (1 : K))=
      monomial (∑ i ∈ m.support,m i • a i) 1 from by
    induction m.support using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        rw [Finset.prod_insert hi,Finset.sum_insert hi,ih,monomial_mul,one_mul]]
  simp only [algebraMap_eq,C_mul_monomial,mul_one]

theorem substitution_monomial_weightMonic (u : τ → ℕ)
    (p : σ → MvPolynomial τ K) (a : σ → τ →₀ ℕ)
    (hp : ∀ i,IsWeightMonic (fun j => (u j : ℤ)) (p i) (a i)) (m : σ →₀ ℕ) :
    IsWeightMonic (fun j => (u j : ℤ)) (aeval (R := K) p (monomial m 1)) (exponentMap a m) := by
  classical
  rw [aeval_monomial,map_one,one_mul]
  exact isWeightMonic_prod m.support (fun i => p i ^ m i) (fun i => m i • a i)
    (fun i hi => (hp i).pow (m i))

theorem map_eq_coefficient_sum
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (q : MvPolynomial σ K) :
    f q=∑ m ∈ q.support,q.coeff m • f (monomial m 1) := by
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have he : monomial m (q.coeff m)=q.coeff m • (monomial m 1 : MvPolynomial σ K) := by
    simp only [smul_monomial,smul_eq_mul,mul_one]
  rw [he,map_smul]

theorem substitution_bound (u : τ → ℕ) (p : σ → MvPolynomial τ K)
    (a : σ → τ →₀ ℕ)
    (hp : ∀ i,IsWeightMonic (fun j => (u j : ℤ)) (p i) (a i))
    (q : MvPolynomial σ K) (d : ℕ) (hq : WeightBound (inducedWeight u a) d q) :
    WeightBound u d (aeval (R := K) p q) := by
  classical
  rw [map_eq_coefficient_sum]
  apply weightBound_sum
  intro m hm
  apply weightBound_smul
  have h := weightBound_of_weightMonic u _ _ (substitution_monomial_weightMonic u p a hp m)
  intro b hb
  exact (h b hb).trans (by
    rw [exponentMap_weight]
    exact hq m (mem_support_iff.mp hm))

theorem substitution_top (u : τ → ℕ) (p : σ → MvPolynomial τ K)
    (a : σ → τ →₀ ℕ)
    (hp : ∀ i,IsWeightMonic (fun j => (u j : ℤ)) (p i) (a i))
    (q : MvPolynomial σ K) (d : ℕ) (hq : WeightBound (inducedWeight u a) d q) :
    weightedHomogeneousComponent u d (aeval (R := K) p q)=
      monomialSubstitution a (weightedHomogeneousComponent (inducedWeight u a) d q) := by
  classical
  rw [map_eq_coefficient_sum (aeval (R := K) p) q]
  conv_rhs => rw [q.as_sum]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro m hm
  have hmono := substitution_monomial_weightMonic u p a hp m
  have hw := hq m (mem_support_iff.mp hm)
  have hsource := isWeightedHomogeneous_monomial (inducedWeight u a) m (q.coeff m) rfl
  rw [weightedHomogeneousComponent_of_mem hsource]
  by_cases hd : d=Finsupp.weight (inducedWeight u a) m
  · rw [if_pos hd,monomialSubstitution_monomial,hd,←exponentMap_weight,
      component_of_weightMonic u _ _ hmono,smul_monomial,smul_eq_mul,mul_one]
  · rw [if_neg hd,map_zero]
    have hlt : weightedTotalDegree u (aeval (R := K) p (monomial m 1))<d := by
      exact (total_le_of_weightBound u _ _ (weightBound_of_weightMonic u _ _ hmono)).trans_lt
        (by rw [exponentMap_weight]; omega)
    rw [weightedHomogeneousComponent_eq_zero d _ hlt,smul_zero]

theorem monomialSubstitution_graded (u : τ → ℕ) (a : σ → τ →₀ ℕ)
    (q : MvPolynomial σ K) (d : ℕ) :
    weightedHomogeneousComponent u d (monomialSubstitution a q)=
      monomialSubstitution a (weightedHomogeneousComponent (inducedWeight u a) d q) := by
  classical
  induction q using MvPolynomial.induction_on' with
  | add q r hq hr => simp only [map_add,hq,hr]
  | monomial m c =>
      rw [monomialSubstitution_monomial,
        weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial u _ c rfl),
        weightedHomogeneousComponent_of_mem
          (isWeightedHomogeneous_monomial (inducedWeight u a) m c rfl),exponentMap_weight]
      split_ifs <;> simp only [monomialSubstitution_monomial,map_zero]

end PaperVerification.WeightedSagbi
end
end
end TAF_LiteralSource_0234

section TAF_LiteralSource_0235
/- Original module: PaperVerification.AlternatingFormsHibiDegeneration -/


/-!
# The actual Richardson-to-Hibi weighted degeneration

The source has exactly the good Plücker variables, and its ideal is the
literal band-minor kernel. Distinct diagonal leading monomials in the full
standard basis establish the entire initial-kernel equality. The special
fiber is consequently the actual Hibi binomial quotient, and every nonzero
fiber is the actual Richardson ring. This uses the concrete Rees image and
its proved flatness, rather than an abstract degeneration assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators
open WeightedInitialFiber WeightedSagbi

variable {K : Type*} [Field K] [CharZero K] {s n : ℕ}
  (α β : Fin s → Fin n)

@[expose]
def diagonalEntryWeight (i : Fin s × Fin n) : ℕ := i.1.val*i.2.val

@[expose]
def diagonalExponent (I : IntervalIndex α β) : (Fin s × Fin n) →₀ ℕ :=
  minorTermExponent I.val.val 1

@[expose]
def diagonalWeight : IntervalIndex α β → ℕ :=
  inducedWeight (diagonalEntryWeight (s := s) (n := n)) (diagonalExponent α β)

def standardDiagonalWeight (C : Σ r,BandChain α β r) : ℕ :=
  ∑ j,diagonalWeight α β (intervalIndexOfChain α β C.2 j)

theorem diagonalEntryWeight_cast :
    (fun i : Fin s × Fin n => (diagonalEntryWeight i : ℤ))=bandEntryWeight s n := by
  funext i
  simp only [diagonalEntryWeight,bandEntryWeight,Nat.cast_mul]

theorem standardPolynomial_diagonal_homogeneous (C : Σ r,BandChain α β r) :
    (standardPolynomial (K := K) α β C.2).IsWeightedHomogeneous
      (diagonalWeight α β) (standardDiagonalWeight α β C) := by
  apply IsWeightedHomogeneous.prod Finset.univ
  intro j hj
  exact isWeightedHomogeneous_X _ _ _

theorem chainDiagonalExponent_weight (C : Σ r,BandChain α β r) :
    Finsupp.weight (diagonalEntryWeight (s := s) (n := n)) (chainDiagonalExponent C.2.val)=
      standardDiagonalWeight α β C := by
  simp only [chainDiagonalExponent,chainTermExponent,map_sum,standardDiagonalWeight,
    diagonalWeight,inducedWeight,diagonalExponent,intervalIndexOfChain]

theorem bandMinor_diagonal_weightMonic (I : IntervalIndex α β) :
    IsWeightMonic (fun i => (diagonalEntryWeight i : ℤ))
      (bandMinor (K := K) α β I.val.val) (diagonalExponent α β I) := by
  rw [diagonalEntryWeight_cast]
  exact bandMinor_weightMonic α β I.val.val I.val.property I.property

set_option maxHeartbeats 800000 in
theorem goodBandInitial_eq_hibi (hα : Monotone α) (hβ : Monotone β) (hs : 0<s) :
    initialIdeal (goodBandIdeal (K := K) α β) (diagonalWeight α β)=relationIdeal α β := by
  rw [relationIdeal_eq_kernel α β hs]
  apply initial_kernel_eq (K := K) (diagonalWeight α β) diagonalEntryWeight
    (goodBandMap α β) (diagonalMap α β)
    (fun C : Σ r,BandChain α β r => standardPolynomial α β C.2)
    (standardDiagonalWeight α β) (fun C => chainDiagonalExponent C.2.val)
    (allChainDiagonalExponent_injective α β hs)
    (standardPolynomial_diagonal_homogeneous α β)
  · intro C
    rw [goodBandMap_standardPolynomial,diagonalEntryWeight_cast]
    exact bandStandardProduct_weightMonic α β C.2
  · exact chainDiagonalExponent_weight α β
  · exact goodBandMap_mem_standardSpan (K := K) α β hα hβ
  · intro p d hp
    exact substitution_bound (K := K) (diagonalEntryWeight (s := s) (n := n))
      (fun I : IntervalIndex α β => bandMinor (K := K) α β I.val.val)
      (diagonalExponent α β) (bandMinor_diagonal_weightMonic (K := K) α β) p d hp
  · intro p d hp
    exact substitution_top (K := K) (diagonalEntryWeight (s := s) (n := n))
      (fun I : IntervalIndex α β => bandMinor (K := K) α β I.val.val)
      (diagonalExponent α β) (bandMinor_diagonal_weightMonic (K := K) α β) p d hp
  · intro p d
    exact monomialSubstitution_graded (K := K)
      (diagonalEntryWeight (s := s) (n := n)) (diagonalExponent α β) p d

/-- The special fiber is the literal binomial Hibi quotient. -/
def hibiSpecialFiberEquiv (hα : Monotone α) (hβ : Monotone β) (hs : 0<s) :
    ZeroFiber (goodBandIdeal (K := K) α β) (diagonalWeight α β) ≃ₐ[K]
      (MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β) :=
  (initialQuotientEquiv (goodBandIdeal α β) (diagonalWeight α β)).symm.trans
    (Ideal.quotientEquivAlgOfEq K (goodBandInitial_eq_hibi α β hα hβ hs))

def hibiNonzeroFiberEquiv (hα : Monotone α) (hβ : Monotone β) (hs : 0<s)
    (c : K) (hc : c≠0) :
    ParameterFiber (goodBandIdeal (K := K) α β) (diagonalWeight α β) c ≃ₐ[K]
      (MvPolynomial (PluckerIndex s n) K⧸intervalPluckerIdeal α β) :=
  (nonzeroFiberEquiv (goodBandIdeal α β) (diagonalWeight α β) c hc).trans
    (goodBandQuotientEquiv α β hα hβ hs)

/-- The actual flat family, with every fiber identified in the original
presentations. Positive row count is the only size condition. -/
theorem richardson_hibi_flat_family (hα : Monotone α) (hβ : Monotone β) (hs : 0<s) :
    Module.Flat (Polynomial K)
      (reesAlgebra (goodBandIdeal (K := K) α β) (diagonalWeight α β)) ∧
    Nonempty (ZeroFiber (goodBandIdeal (K := K) α β) (diagonalWeight α β) ≃ₐ[K]
      (MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β)) ∧
    ∀ c : K,c≠0 → Nonempty
      (ParameterFiber (goodBandIdeal (K := K) α β) (diagonalWeight α β) c ≃ₐ[K]
        (MvPolynomial (PluckerIndex s n) K⧸intervalPluckerIdeal α β)) :=
  ⟨inferInstance,⟨hibiSpecialFiberEquiv α β hα hβ hs⟩,
    fun c hc => ⟨hibiNonzeroFiberEquiv α β hα hβ hs c hc⟩⟩

end PaperVerification.AlternatingForms.Hibi
end
end
end TAF_LiteralSource_0235

section TAF_LiteralSource_0236
/- Original module: PaperVerification.AlternatingFormsHibiWeights -/


/-!
# The positive rank-square weight for the literal Hibi relations

The interval rank is the sum of the coordinate increments above its lower
endpoint. Meet and join preserve the sum of the two ranks, and an incomparable
pair strictly increases their separation. Complementing their squares by a
uniform positive constant gives the paper's strictly decreasing sorting
weight, with no order or termination hypothesis supplied.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open scoped BigOperators

variable {s n : ℕ} (α β : Fin s → Fin n)

def intervalRank (I : IntervalIndex α β) : ℕ := ∑ i, ((I.val.val i).val-(α i).val)
def rankBound : ℕ := ∑ i, ((β i).val-(α i).val)

theorem intervalRank_le_bound (I : IntervalIndex α β) : intervalRank α β I ≤ rankBound α β := by
  unfold intervalRank rankBound
  apply Finset.sum_le_sum
  intro i hi
  have h := (I.property i).2
  exact Nat.sub_le_sub_right h _

theorem intervalRank_strict (I J : IntervalIndex α β) (hle : I ≤ J) (hne : I≠J) :
    intervalRank α β I < intervalRank α β J := by
  have hex : ∃ i,I.val.val i≠J.val.val i := by
    by_contra h
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Classical.not_not.mp (fun hi => h ⟨i,hi⟩)
  obtain ⟨j,hj⟩ := hex
  unfold intervalRank
  apply Finset.sum_lt_sum
  · intro i hi
    exact Nat.sub_le_sub_right (hle i) _
  · refine ⟨j,Finset.mem_univ _,?_⟩
    have h1 : (I.val.val j).val ≤ (J.val.val j).val := hle j
    have h2 : (α j).val ≤ (I.val.val j).val := (I.property j).1
    have h3 : (I.val.val j).val≠(J.val.val j).val := fun h => hj (Fin.ext h)
    omega

theorem intervalRank_meet_join (I J : IntervalIndex α β) :
    intervalRank α β (meet α β I J)+intervalRank α β (join α β I J)=
      intervalRank α β I+intervalRank α β J := by
  unfold intervalRank
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : I.val.val i ≤ J.val.val i
  · simp only [meet,join,min_eq_left h,max_eq_right h]
  · have h' : J.val.val i ≤ I.val.val i := le_of_not_ge h
    simp only [meet,join,min_eq_right h',max_eq_left h',add_comm]

theorem intervalRank_meet_lt_left (I J : IntervalIndex α β)
    (h : incomparable α β I J) :
    intervalRank α β (meet α β I J) < intervalRank α β I := by
  apply intervalRank_strict α β _ _ (meet_le_left α β I J)
  intro he
  exact h.1 (he ▸ meet_le_right α β I J)

theorem intervalRank_meet_lt_right (I J : IntervalIndex α β)
    (h : incomparable α β I J) :
    intervalRank α β (meet α β I J) < intervalRank α β J := by
  apply intervalRank_strict α β _ _ (meet_le_right α β I J)
  intro he
  exact h.2 (he ▸ meet_le_left α β I J)

def sortingWeight (I : IntervalIndex α β) : ℕ :=
  (rankBound α β)^2+1-(intervalRank α β I)^2

theorem sortingWeight_positive (I : IntervalIndex α β) : 0 < sortingWeight α β I := by
  have h := intervalRank_le_bound α β I
  have hsq : (intervalRank α β I)^2 ≤ (rankBound α β)^2 := pow_le_pow_left' h 2
  unfold sortingWeight
  omega

theorem sortingWeight_decreases (I J : IntervalIndex α β)
    (h : incomparable α β I J) :
    sortingWeight α β (meet α β I J)+sortingWeight α β (join α β I J) < 
      sortingWeight α β I+sortingWeight α β J := by
  let a := intervalRank α β (meet α β I J)
  let b := intervalRank α β I
  let c := intervalRank α β J
  let d := intervalRank α β (join α β I J)
  have hab : a < b := intervalRank_meet_lt_left α β I J h
  have hac : a < c := intervalRank_meet_lt_right α β I J h
  have hsum : a+d=b+c := intervalRank_meet_join α β I J
  have habZ : (a : ℤ) < b := by exact_mod_cast hab
  have hacZ : (a : ℤ) < c := by exact_mod_cast hac
  have hp : (0 : ℤ) < ((b : ℤ)-a)*((c : ℤ)-a) :=
    mul_pos (sub_pos.mpr habZ) (sub_pos.mpr hacZ)
  have hsumZ : (a : ℤ)+d=b+c := by exact_mod_cast hsum
  have hsquareZ : (b : ℤ)^2+c^2 < a^2+d^2 := by nlinarith
  have hsquare : b^2+c^2 < a^2+d^2 := by exact_mod_cast hsquareZ
  have ha := pow_le_pow_left' (intervalRank_le_bound α β (meet α β I J)) 2
  have hb := pow_le_pow_left' (intervalRank_le_bound α β I) 2
  have hc := pow_le_pow_left' (intervalRank_le_bound α β J) 2
  have hd := pow_le_pow_left' (intervalRank_le_bound α β (join α β I J)) 2
  change (rankBound α β)^2+1-a^2+((rankBound α β)^2+1-d^2) < 
    (rankBound α β)^2+1-b^2+((rankBound α β)^2+1-c^2)
  dsimp only [a,b,c,d] at hsquare ⊢
  omega

variable {K : Type*} [Field K]

/-- The proposed quadratic monomial initial ideal, with exactly the
incomparable pairs as generators. -/
def incomparableIdeal : Ideal (MvPolynomial (IntervalIndex α β) K) :=
  Ideal.span {p | ∃ I J,incomparable α β I J ∧ p=MvPolynomial.X I*MvPolynomial.X J}

theorem relation_top (I J : IntervalIndex α β) (h : incomparable α β I J) :
    MvPolynomial.weightedHomogeneousComponent (sortingWeight α β)
      (sortingWeight α β I+sortingWeight α β J) (relation (K := K) α β I J)=
        MvPolynomial.X I*MvPolynomial.X J := by
  have hleft := (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) I).mul
    (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) J)
  have hright :=
    (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) (meet α β I J)).mul
      (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) (join α β I J))
  have hne := (sortingWeight_decreases α β I J h).ne'
  rw [relation,map_sub,MvPolynomial.weightedHomogeneousComponent_of_mem hleft,
    MvPolynomial.weightedHomogeneousComponent_of_mem hright]
  simp only [ite_true,if_neg hne,sub_zero]

theorem relation_weightBound (I J : IntervalIndex α β) (h : incomparable α β I J) :
    WeightedInitialFiber.WeightBound (sortingWeight α β)
      (sortingWeight α β I+sortingWeight α β J) (relation (K := K) α β I J) := by
  have hleft := (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) I).mul
    (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) J)
  have hright :=
    (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) (meet α β I J)).mul
      (MvPolynomial.isWeightedHomogeneous_X K (sortingWeight α β) (join α β I J))
  intro a ha
  by_cases hl : (MvPolynomial.X I*MvPolynomial.X J :
      MvPolynomial (IntervalIndex α β) K).coeff a=0
  · have hr : (MvPolynomial.X (meet α β I J)*MvPolynomial.X (join α β I J) :
        MvPolynomial (IntervalIndex α β) K).coeff a≠0 := by
      intro hr
      exact ha (by simp only [relation,MvPolynomial.coeff_sub,hl,hr,sub_zero])
    exact (hright hr).le.trans (sortingWeight_decreases α β I J h).le
  · exact (hleft hl).le

theorem incomparableIdeal_le_initial :
    incomparableIdeal (K := K) α β ≤ 
      WeightedInitialFiber.initialIdeal (relationIdeal α β) (sortingWeight α β) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨I,J,h,rfl⟩
  rw [←relation_top α β I J h]
  exact WeightedInitialFiber.component_mem_initialIdeal _ _ _
    (relation_mem α β I J) _ (relation_weightBound α β I J h)

end PaperVerification.AlternatingForms.Hibi
end
end
end TAF_LiteralSource_0236

section TAF_LiteralSource_0237
/- Original module: PaperVerification.WeightedMonicNormalForm -/


/-!
# Coefficient control in an actual distinct-leading-term expansion

Every nonzero basis coefficient lies below the input's weight bound. At
that bound its coefficient is the corresponding leading-monomial
coefficient of the input. In particular a monic input can have only its
unique matching standard leading exponent at the greatest weight.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedSagbi

open MvPolynomial
open scoped BigOperators
open AlternatingForms WeightedInitialFiber

variable {K τ C : Type*} [Field K]

variable (u : τ → ℕ) (v : C → MvPolynomial τ K)
  (a : C → τ →₀ ℕ) (degree : C → ℕ)
  (ha : Function.Injective a)
  (hv : ∀ c,IsWeightMonic (fun i => (u i : ℤ)) (v c) (a c))
  (hw : ∀ c,Finsupp.weight u (a c)=degree c)

include ha hv hw

/-- Distinct leading terms prohibit cancellation at the maximal active
weight, including when several basis terms have the same weight. -/
theorem expansion_degree_le (coeff : C →₀ K) (d : ℕ)
    (hbound : WeightBound u d (coeff.sum fun c z => z • v c)) :
    ∀ c,coeff c≠0 → degree c≤d := by
  classical
  intro c hc
  have hS : coeff.support.Nonempty := ⟨c,Finsupp.mem_support_iff.mpr hc⟩
  obtain ⟨j,hj,hmax⟩ := coeff.support.exists_max_image degree hS
  have hcj : coeff j≠0 := Finsupp.mem_support_iff.mp hj
  have hlead : (coeff.sum fun c z => z • v c).coeff (a j)=coeff j := by
    simp only [Finsupp.sum,coeff_sum]
    rw [Finset.sum_eq_single j]
    · rw [coeff_smul,(hv j).1,smul_eq_mul,mul_one]
    · intro i hi hij
      rw [coeff_smul,(hv i).2 (a j) (fun he => hij (ha he.symm)),smul_zero]
      rw [←natCast_weight,←natCast_weight,hw,hw]
      exact_mod_cast hmax i hi
    · intro h
      exact (h hj).elim
  have hle : degree j≤d := by
    rw [←hw j]
    exact hbound (a j) (by rwa [hlead])
  exact (hmax c (Finsupp.mem_support_iff.mpr hc)).trans hle

/-- At the bound, the leading coefficient of a basis vector is not mixed
with any other vector in the full finite expansion. -/
theorem expansion_coefficient_at_bound (coeff : C →₀ K) (d : ℕ)
    (hbound : WeightBound u d (coeff.sum fun c z => z • v c))
    (c : C) (hc : degree c=d) :
    (coeff.sum fun c z => z • v c).coeff (a c)=coeff c := by
  classical
  have hdeg := expansion_degree_le u v a degree ha hv hw coeff d hbound
  simp only [Finsupp.sum,coeff_sum]
  rw [Finset.sum_eq_single c]
  · rw [coeff_smul,(hv c).1,smul_eq_mul,mul_one]
  · intro i hi hic
    rw [coeff_smul,(hv i).2 (a c) (fun he => hic (ha he.symm)),smul_zero]
    rw [←natCast_weight,←natCast_weight,hw,hw,hc]
    exact_mod_cast hdeg i (Finsupp.mem_support_iff.mp hi)
  · intro hc'
    have hz : coeff c=0 := Finsupp.notMem_support_iff.mp hc'
    rw [hz,zero_smul]
    rfl

theorem expansion_monic_top_exponent (coeff : C →₀ K)
    (p : MvPolynomial τ K) (ap : τ →₀ ℕ)
    (hp : IsWeightMonic (fun i => (u i : ℤ)) p ap)
    (hexp : coeff.sum (fun c z => z • v c)=p)
    (c : C) (hc : coeff c≠0) (hd : degree c=Finsupp.weight u ap) : a c=ap := by
  have hb : WeightBound u (Finsupp.weight u ap) (coeff.sum fun c z => z • v c) := by
    rw [hexp]
    exact weightBound_of_weightMonic u p ap hp
  have hcoeff := expansion_coefficient_at_bound u v a degree ha hv hw coeff _ hb c hd
  rw [hexp] at hcoeff
  by_contra hne
  have hz := hp.2 (a c) hne
    (by rw [←natCast_weight,←natCast_weight,hw,hd])
  exact hc (hcoeff.symm.trans hz)

theorem expansion_monic_top_coefficient (coeff : C →₀ K)
    (p : MvPolynomial τ K) (ap : τ →₀ ℕ)
    (hp : IsWeightMonic (fun i => (u i : ℤ)) p ap)
    (hexp : coeff.sum (fun c z => z • v c)=p)
    (c : C) (hc : a c=ap) : coeff c=1 := by
  have hb : WeightBound u (Finsupp.weight u ap) (coeff.sum fun c z => z • v c) := by
    rw [hexp]
    exact weightBound_of_weightMonic u p ap hp
  have hd : degree c=Finsupp.weight u ap := by rw [←hw,hc]
  have hcoeff := expansion_coefficient_at_bound u v a degree ha hv hw coeff _ hb c hd
  rw [hexp,hc,hp.1] at hcoeff
  exact hcoeff.symm

end PaperVerification.WeightedSagbi
end
end
end TAF_LiteralSource_0237

section TAF_LiteralSource_0238
/- Original module: PaperVerification.AlternatingFormsRichardsonNormalForm -/


/-!
# Diagonal control of the actual Richardson normal form

Coefficients are defined by the proved basis of the actual interval
Plücker quotient. Mapping its full finite expansion into the band matrix
ring proves the diagonal bound. At the greatest diagonal weight the
product of two minors has precisely its meet/join chain, with coefficient
one. No straightening coefficient or triangularity condition is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators
open WeightedSagbi WeightedInitialFiber

variable {K : Type*} [Field K] [CharZero K] {s n : ℕ}
  (α β : Fin s → Fin n)

/-- The actual sorted two-column chain. -/
def pairChain (I J : IntervalIndex α β) : Σ r,BandChain α β r :=
  ⟨2,chainOfList α β [meet α β I J,join α β I J] (by
    refine List.pairwise_cons.mpr ⟨?_, by simp⟩
    intro x hx
    have hx' : x = join α β I J := by simpa only [List.mem_singleton] using hx
    subst x
    exact (meet_le_left α β I J).trans (left_le_join α β I J))⟩

theorem standardPolynomial_pairChain (I J : IntervalIndex α β) :
    standardPolynomial (K := K) α β (pairChain α β I J).2=
      X (meet α β I J)*X (join α β I J) := by
  rw [pairChain,standardPolynomial_chainOfList]
  simp only [word_cons,word_nil,mul_one]

theorem pairChain_diagonal (I J : IntervalIndex α β) :
    chainDiagonalExponent (pairChain α β I J).2.val=
      diagonalExponent α β I+diagonalExponent α β J := by
  change (∑ j : Fin 2,
    minorTermExponent (([meet α β I J,join α β I J].get j).val.val) 1)=_
  rw [Fin.sum_univ_two]
  exact pair_exponents α β I J

theorem pairChain_diagonalWeight (I J : IntervalIndex α β) :
    standardDiagonalWeight α β (pairChain α β I J)=
      diagonalWeight α β I+diagonalWeight α β J := by
  rw [←chainDiagonalExponent_weight,pairChain_diagonal,map_add]
  rfl

theorem pairChain_sum_weight (w : IntervalIndex α β → ℕ)
    (I J : IntervalIndex α β) :
    (∑ j,w (intervalIndexOfChain α β (pairChain α β I J).2 j))=
      w (meet α β I J)+w (join α β I J) := by
  simp only [pairChain,Fin.sum_univ_two,intervalIndexOfChain,chainOfList]
  rfl

variable (hα : Monotone α) (hβ : Monotone β) (hs : 0<s)

def intervalCoefficients (p : MvPolynomial (PluckerIndex s n) K) :
    (Σ r,BandChain α β r) →₀ K :=
  (intervalStandardBasis (K := K) α β hα hβ hs).repr (Ideal.Quotient.mk _ p)

theorem intervalCoefficients_band_expansion (p : MvPolynomial (PluckerIndex s n) K) :
    (intervalCoefficients (K := K) α β hα hβ hs p).sum
      (fun C c => c • bandStandardProduct (K := K) α β C.2)=bandPluckerMap (K := K) α β p := by
  have h := congrArg (intervalBandMap (K := K) α β hα hβ)
    ((intervalStandardBasis (K := K) α β hα hβ hs).linearCombination_repr
      (Ideal.Quotient.mk _ p))
  have hm : intervalBandMap (K := K) α β hα hβ (Ideal.Quotient.mk _ p) =
      bandPluckerMap (K := K) α β p := rfl
  rw [hm] at h
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    intervalStandardBasis,Module.Basis.mk_apply,intervalAllStandardProduct,
    intervalBandMap_standardProduct,intervalCoefficients] using h

theorem intervalCoefficients_diagonal_le
    (p : MvPolynomial (PluckerIndex s n) K) (d : ℕ)
    (hp : WeightBound diagonalEntryWeight d (bandPluckerMap (K := K) α β p))
    (C : Σ r,BandChain α β r) (hc : intervalCoefficients (K := K) α β hα hβ hs p C≠0) :
    standardDiagonalWeight α β C≤d := by
  apply expansion_degree_le diagonalEntryWeight
    (fun C : Σ r,BandChain α β r => bandStandardProduct (K := K) α β C.2)
    (fun C => chainDiagonalExponent C.2.val) (standardDiagonalWeight α β)
    (allChainDiagonalExponent_injective α β hs)
    (fun C => by rw [diagonalEntryWeight_cast]; exact bandStandardProduct_weightMonic α β C.2)
    (chainDiagonalExponent_weight α β)
    (intervalCoefficients (K := K) α β hα hβ hs p) d ?_ C hc
  rwa [intervalCoefficients_band_expansion]

theorem band_pair_weightMonic (I J : IntervalIndex α β) :
    IsWeightMonic (fun i => (diagonalEntryWeight i : ℤ))
      (bandPluckerMap (K := K) α β (X I.val*X J.val : MvPolynomial (PluckerIndex s n) K))
      (diagonalExponent α β I+diagonalExponent α β J) := by
  simp only [bandPluckerMap,map_mul,aeval_X]
  exact (bandMinor_diagonal_weightMonic α β I).mul
    (bandMinor_diagonal_weightMonic α β J)

theorem interval_pair_diagonal_le (I J : IntervalIndex α β)
    (C : Σ r,BandChain α β r)
    (hc : intervalCoefficients (K := K) α β hα hβ hs (X I.val*X J.val) C≠0) :
    standardDiagonalWeight α β C≤diagonalWeight α β I+diagonalWeight α β J := by
  apply intervalCoefficients_diagonal_le (K := K) α β hα hβ hs _ _ ?_ C hc
  simpa only [map_add,diagonalWeight,inducedWeight] using
    weightBound_of_weightMonic diagonalEntryWeight _ _ (band_pair_weightMonic (K := K) α β I J)

/-- The unique possible greatest-diagonal-weight term is the actual
meet/join chain, in the full basis over all chain lengths. -/
theorem interval_pair_top_chain (I J : IntervalIndex α β)
    (C : Σ r,BandChain α β r)
    (hc : intervalCoefficients (K := K) α β hα hβ hs (X I.val*X J.val) C≠0)
    (hd : standardDiagonalWeight α β C=diagonalWeight α β I+diagonalWeight α β J) :
    C=pairChain α β I J := by
  apply allChainDiagonalExponent_injective α β hs
  change chainDiagonalExponent C.2.val = chainDiagonalExponent (pairChain α β I J).2.val
  rw [pairChain_diagonal]
  apply expansion_monic_top_exponent diagonalEntryWeight
    (fun C : Σ r,BandChain α β r => bandStandardProduct (K := K) α β C.2)
    (fun C => chainDiagonalExponent C.2.val) (standardDiagonalWeight α β)
    (allChainDiagonalExponent_injective α β hs)
    (fun C => by rw [diagonalEntryWeight_cast]; exact bandStandardProduct_weightMonic α β C.2)
    (chainDiagonalExponent_weight α β)
    (intervalCoefficients (K := K) α β hα hβ hs (X I.val*X J.val)) _ _
    (band_pair_weightMonic (K := K) α β I J)
    (intervalCoefficients_band_expansion (K := K) α β hα hβ hs _) C hc
  simpa only [map_add,diagonalWeight,inducedWeight] using hd

theorem interval_pair_top_coefficient (I J : IntervalIndex α β) :
    intervalCoefficients (K := K) α β hα hβ hs (X I.val*X J.val) (pairChain α β I J)=1 := by
  apply expansion_monic_top_coefficient diagonalEntryWeight
    (fun C : Σ r,BandChain α β r => bandStandardProduct (K := K) α β C.2)
    (fun C => chainDiagonalExponent C.2.val) (standardDiagonalWeight α β)
    (allChainDiagonalExponent_injective α β hs)
    (fun C => by rw [diagonalEntryWeight_cast]; exact bandStandardProduct_weightMonic α β C.2)
    (chainDiagonalExponent_weight α β)
    (intervalCoefficients (K := K) α β hα hβ hs (X I.val*X J.val)) _ _
    (band_pair_weightMonic (K := K) α β I J)
    (intervalCoefficients_band_expansion (K := K) α β hα hβ hs _) (pairChain α β I J)
  exact pairChain_diagonal α β I J

end PaperVerification.AlternatingForms.Hibi
end
end
end TAF_LiteralSource_0238

section TAF_LiteralSource_0239
/- Original module: PaperVerification.FilteredBasisNormalForm -/


/-!
# Filtration bounds and top coefficients of the actual lifted normal form

The normal form is defined using the already established basis of the
actual quotient. Bounded relation lifts prove that it respects the weight
filtration. At the greatest weight its coefficients agree with the actual
initial-quotient basis coefficients. These are conclusions about the
literal quotient maps, not triangular-normal-form assumptions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.FilteredBasisTransfer

open PaperVerification.Fermion.BasisFiltered
open scoped BigOperators

variable {K M I E Q Q₀ : Type*} [Field K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup Q] [Module K Q] [AddCommGroup Q₀] [Module K Q₀]
  (b : Module.Basis I K M) (w : I → ℕ)

/-- Bounded relation lifting yields a representative with the same bound
in the span of the actual homogeneous standard representatives. -/
theorem bounded_spanning (N N₀ : Submodule K M)
    (hlift : ∀ x∈N₀,∀ d,∃ y∈N,Bound b w d y ∧
      component b w d y=component b w d x)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (hspan : Submodule.span K (Set.range v)⊔N₀=⊤)
    (d : ℕ) (x : M) (hx : Bound b w d x) :
    ∃ z∈Submodule.span K (Set.range v),Bound b w d z ∧ x-z∈N := by
  have step (e : ℕ) (y : M) (hy : Bound b w e y) :
      ∃ u∈Submodule.span K (Set.range v),∃ a∈N,
        Bound b w e u ∧ Bound b w e a ∧ component b w e (y-u-a)=0 := by
    have hm : y∈Submodule.span K (Set.range v)⊔N₀ := by rw [hspan]; trivial
    obtain ⟨u,hu,j,hj,huj⟩ := Submodule.mem_sup.mp hm
    obtain ⟨a,ha,hab,hac⟩ := hlift j hj e
    refine ⟨component b w e u,component_mem_span b w v degree hv u hu e,
      a,ha,bound_component b w e u,hab,?_⟩
    have huu : component b w e (component b w e u)=component b w e u := by
      rw [component_of_homogeneous b w (homogeneous_component b w e u),if_pos rfl]
    rw [map_sub,map_sub,huu,hac,←huj,map_add]
    abel
  induction d generalizing x with
  | zero =>
      obtain ⟨u,hu,a,ha,hub,hab,hc⟩ := step 0 x hx
      have hz := eq_zero_of_bound_zero_component_zero b w
        (bound_sub b w (bound_sub b w hx hub) hab) hc
      exact ⟨u,hu,hub,by rw [sub_eq_zero.mp hz]; exact ha⟩
  | succ d ih =>
      obtain ⟨u,hu,a,ha,hub,hab,hc⟩ := step (d+1) x hx
      have hb : Bound b w d (x-u-a) := bound_pred_of_component_zero b w
        (bound_sub b w (bound_sub b w hx hub) hab) hc
      obtain ⟨z,hz,hzb,hr⟩ := ih (x-u-a) hb
      have he : x-(u+z)=a+((x-u-a)-z) := by abel
      refine ⟨u+z,Submodule.add_mem _ hu hz,
        bound_add b w hub (bound_mono b w (Nat.le_succ d) hzb),?_⟩
      rw [he]
      exact N.add_mem ha hr

variable (q : M →ₗ[K] Q) (v : E → M) (B : Module.Basis E K Q)

def normalRepresentative : M →ₗ[K] M :=
  (Finsupp.linearCombination K v).comp (B.repr.toLinearMap.comp q)

@[simp] theorem normalRepresentative_apply (x : M) :
    normalRepresentative q v B x=(B.repr (q x)).sum (fun e c => c • v e) := rfl

theorem normalRepresentative_generator (hB : ∀ e,B e=q (v e)) (e : E) :
    normalRepresentative q v B (v e)=v e := by
  rw [normalRepresentative_apply,←hB e,B.repr_self,Finsupp.sum_single_index,one_smul]
  exact zero_smul _ _

theorem normalRepresentative_eq_self (hB : ∀ e,B e=q (v e))
    (x : M) (hx : x∈Submodule.span K (Set.range v)) : normalRepresentative q v B x=x := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨e,rfl⟩ := hx; exact normalRepresentative_generator q v B hB e
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy]
  | smul c x hx ih => rw [map_smul,ih]

theorem quotient_normalRepresentative (hB : ∀ e,B e=q (v e)) (x : M) :
    q (normalRepresentative q v B x)=q x := by
  rw [normalRepresentative_apply]
  simp only [Finsupp.sum,map_sum,map_smul,←hB]
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using
    B.linearCombination_repr (q x)

theorem normalRepresentative_bound
    (q₀ : M →ₗ[K] Q₀) (hq₀ : Function.Surjective q₀)
    (hlift : ∀ x,q₀ x=0 → ∀ d,∃ y,q y=0 ∧ Bound b w d y ∧
      component b w d y=component b w d x)
    (degree : E → ℕ) (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e))
    (hB : ∀ e,B e=q (v e)) (x : M) (d : ℕ) (hx : Bound b w d x) :
    Bound b w d (normalRepresentative q v B x) := by
  have hspan : Submodule.span K (Set.range v)⊔q₀.ker=⊤ := by
    apply (LinearMap.map_eq_top_iff (LinearMap.range_eq_top.mpr hq₀)).mp
    rw [Submodule.map_span,←Set.range_comp']
    simpa only [←hB₀] using B₀.span_eq
  obtain ⟨z,hz,hzb,hxz⟩ := bounded_spanning b w q.ker q₀.ker
    (fun y hy e => by
      obtain ⟨a,ha,hb,ht⟩ := hlift y (LinearMap.mem_ker.mp hy) e
      exact ⟨a,LinearMap.mem_ker.mpr ha,hb,ht⟩)
    v degree hv hspan d x hx
  have hq : q x=q z := by
    have h := LinearMap.mem_ker.mp hxz
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have hn : normalRepresentative q v B x=normalRepresentative q v B z := by
    simp only [normalRepresentative_apply,hq]
  rw [hn,normalRepresentative_eq_self q v B hB z hz]
  exact hzb

theorem initial_coordinate_normalRepresentative
    (q₀ : M →ₗ[K] Q₀) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e))
    (x : M) (d : ℕ) (e : E) :
    B₀.repr (q₀ (component b w d (normalRepresentative q v B x))) e=
      if degree e=d then B.repr (q x) e else 0 := by
  classical
  rw [normalRepresentative_apply]
  simp only [Finsupp.sum,map_sum,map_smul]
  simp_rw [component_of_homogeneous b w (hv _)]
  simp only [apply_ite,map_zero,←hB₀,B₀.repr_self]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single e]
  · by_cases he : d=degree e <;> simp [he,eq_comm]
  · intro j hj hje
    by_cases hd : d=degree j <;> simp [hd,hje,Ne.symm hje]
  · intro he
    simp [Finsupp.notMem_support_iff.mp he]

/-- The top coefficient of the actual quotient normal form equals the
coefficient in the initial quotient, once the input bound is established. -/
theorem top_coefficient_eq
    (q₀ : M →ₗ[K] Q₀)
    (hinitial : ∀ x,q x=0 → ∀ d,Bound b w d x → q₀ (component b w d x)=0)
    (degree : E → ℕ) (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e))
    (hB : ∀ e,B e=q (v e)) (x : M) (d : ℕ)
    (hx : Bound b w d x) (hn : Bound b w d (normalRepresentative q v B x))
    (e : E) (he : degree e=d) :
    B.repr (q x) e=B₀.repr (q₀ (component b w d x)) e := by
  have hq : q (x-normalRepresentative q v B x)=0 := by
    rw [map_sub,quotient_normalRepresentative q v B hB,sub_self]
  have h := hinitial _ hq d (bound_sub b w hx hn)
  rw [map_sub,map_sub,sub_eq_zero] at h
  rw [h,initial_coordinate_normalRepresentative b w q v B q₀ degree hv B₀ hB₀ x d e,
    if_pos he]

/-- No coefficient of weight greater than the bound can occur. -/
theorem coefficient_eq_zero_of_bound
    (q₀ : M →ₗ[K] Q₀) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e))
    (x : M) (d : ℕ) (hn : Bound b w d (normalRepresentative q v B x))
    (e : E) (he : d<degree e) : B.repr (q x) e=0 := by
  have hz := component_eq_zero_of_bound_lt b w he hn
  have h := congrArg (fun z : M => B₀.repr (q₀ z) e) hz
  rw [initial_coordinate_normalRepresentative b w q v B q₀ degree hv B₀ hB₀,
    if_pos rfl,map_zero,map_zero,Finsupp.zero_apply] at h
  exact h

end PaperVerification.FilteredBasisTransfer
end
end
end TAF_LiteralSource_0239

section TAF_LiteralSource_0240
/- Original module: PaperVerification.WeightedInitialNormalForm -/


/-!
# The actual normal form of a lifted initial-quotient basis

The polynomial normal form is the finite expansion in the already proved
basis, using the same homogeneous representatives. Its weight bound and
its top coefficients follow from bounded lifts of every initial relation.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace PaperVerification.WeightedInitialFiber

open MvPolynomial
open PaperVerification.FilteredBasisTransfer

-- Use the proved basis through its public type and application theorem.
-- Unfolding its bounded-lifting construction during unrelated coercion
-- inference expands a large proof term without changing the mathematics.
attribute [local irreducible] liftedInitialBasis

variable {K σ E : Type*} [Field K]
local notation "P" => MvPolynomial σ K

variable (Q : Ideal P) (w : σ → ℕ)
  (v : E → P) (degree : E → ℕ)
  (hv : ∀ e,(v e).IsWeightedHomogeneous w (degree e))
  (B₀ : Module.Basis E K (P⧸initialIdeal Q w))
  (hB₀ : ∀ e,B₀ e=Ideal.Quotient.mk _ (v e))

def liftedNormalForm
    (Q : Ideal P) (w : σ → ℕ) (v : E → P) (degree : E → ℕ)
    (hv : ∀ e,(v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P⧸initialIdeal Q w))
    (hB₀ : ∀ e,B₀ e=Ideal.Quotient.mk _ (v e)) : P →ₗ[K] P := by
  exact normalRepresentative (K := K) (M := P) (Q := P⧸Q) (E := E)
    (Ideal.Quotient.mkₐ K Q).toLinearMap v
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀)

@[simp] theorem liftedNormalForm_apply
    (Q : Ideal P) (w : σ → ℕ) (v : E → P) (degree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P ⧸ initialIdeal Q w))
    (hB₀ : ∀ e, B₀ e = Ideal.Quotient.mk _ (v e))
    (p : P) :
    liftedNormalForm (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀ p=
      ((liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀).repr
        ((Ideal.Quotient.mkₐ K Q).toLinearMap p)).sum (fun e c => c • v e) := by
  unfold liftedNormalForm
  exact normalRepresentative_apply
    (Ideal.Quotient.mkₐ K Q).toLinearMap v
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀) p

theorem liftedNormalForm_bound
    (Q : Ideal P) (w : σ → ℕ) (v : E → P) (degree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P ⧸ initialIdeal Q w))
    (hB₀ : ∀ e, B₀ e = Ideal.Quotient.mk _ (v e))
    (p : P) (d : ℕ) (hp : WeightBound (K := K) w d p) :
    WeightBound (K := K) w d (liftedNormalForm (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀ p) := by
  apply (monomialBasis_bound_iff w d _).mp
  unfold liftedNormalForm
  apply normalRepresentative_bound (K := K) (M := P) (Q := P⧸Q)
    (Q₀ := P⧸initialIdeal Q w) (I := σ →₀ ℕ) (E := E) (basisMonomials σ K) (Finsupp.weight w)
    (Ideal.Quotient.mkₐ K Q).toLinearMap v
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀)
    (Ideal.Quotient.mkₐ K (initialIdeal Q w)).toLinearMap
    (Ideal.Quotient.mkₐ_surjective K (initialIdeal Q w)) ?_ degree
    (fun e => (monomialBasis_homogeneous_iff w (degree e) (v e)).mpr (hv e))
    B₀ hB₀ (liftedInitialBasis_apply (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀) p d
    ((monomialBasis_bound_iff w d p).mpr hp)
  intro x hx e
  obtain ⟨a,ha,hb,ht⟩ := initial_component_lift Q w x
    (Ideal.Quotient.eq_zero_iff_mem.mp hx) e
  exact ⟨a,Ideal.Quotient.eq_zero_iff_mem.mpr ha,
    (monomialBasis_bound_iff w e a).mpr hb,
    by simpa only [monomialBasis_component] using ht⟩

theorem lifted_coefficient_eq_zero_of_weight_lt
    (Q : Ideal P) (w : σ → ℕ) (v : E → P) (degree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P ⧸ initialIdeal Q w))
    (hB₀ : ∀ e, B₀ e = Ideal.Quotient.mk _ (v e))
    (p : P) (d : ℕ)
    (hp : WeightBound (K := K) w d p) (e : E) (he : d<degree e) :
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀).repr
      ((Ideal.Quotient.mkₐ K Q).toLinearMap p) e=0 := by
  apply coefficient_eq_zero_of_bound (K := K) (M := P) (Q := P⧸Q)
    (Q₀ := P⧸initialIdeal Q w) (I := σ →₀ ℕ) (E := E) (basisMonomials σ K) (Finsupp.weight w)
    (Ideal.Quotient.mkₐ K Q).toLinearMap v
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀)
    (Ideal.Quotient.mkₐ K (initialIdeal Q w)).toLinearMap degree
    (fun i => (monomialBasis_homogeneous_iff w (degree i) (v i)).mpr (hv i))
    B₀ hB₀ p d
  · exact (monomialBasis_bound_iff w d _).mpr
      (liftedNormalForm_bound (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀ p d hp)
  · exact he

theorem lifted_top_coefficient
    (Q : Ideal P) (w : σ → ℕ) (v : E → P) (degree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P ⧸ initialIdeal Q w))
    (hB₀ : ∀ e, B₀ e = Ideal.Quotient.mk _ (v e))
    (p : P) (d : ℕ) (hp : WeightBound (K := K) w d p)
    (e : E) (he : degree e=d) :
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀).repr
      ((Ideal.Quotient.mkₐ K Q).toLinearMap p) e=
        B₀.repr ((Ideal.Quotient.mkₐ K (initialIdeal Q w)).toLinearMap
          (weightedHomogeneousComponent w d p)) e := by
  simpa only [monomialBasis_component] using
    top_coefficient_eq (K := K) (M := P) (Q := P⧸Q)
    (Q₀ := P⧸initialIdeal Q w) (I := σ →₀ ℕ) (E := E) (basisMonomials σ K) (Finsupp.weight w)
    (Ideal.Quotient.mkₐ K Q).toLinearMap v
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀)
    (Ideal.Quotient.mkₐ K (initialIdeal Q w)).toLinearMap
    (by
      intro x hx r hb
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [monomialBasis_component]
      exact component_mem_initialIdeal Q w x
        (Ideal.Quotient.eq_zero_iff_mem.mp hx) r
        ((monomialBasis_bound_iff w r x).mp hb))
    degree (fun i => (monomialBasis_homogeneous_iff w (degree i) (v i)).mpr (hv i))
    B₀ hB₀ (liftedInitialBasis_apply (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀) p d
    ((monomialBasis_bound_iff w d p).mpr hp)
    ((monomialBasis_bound_iff w d _).mpr
      (liftedNormalForm_bound (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀ p d hp)) e he

end PaperVerification.WeightedInitialFiber
end
end
end TAF_LiteralSource_0240

section TAF_LiteralSource_0241
/- Original module: PaperVerification.HomogeneousBasisCoefficients -/


/-!
# Coefficients of an actual homogeneous basis

Projection to a graded piece keeps exactly the basis coordinates with
that degree. The grading is the supplied genuine direct-sum decomposition;
the result does not assign a grading retrospectively to a desired basis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.GradedComponentBasis

variable {K V I : Type*} {D : Type} [Field K] [AddCommGroup V] [Module K V]
  [DecidableEq D]
  (G : TauCeti.InternalGrading K V D) (B : Module.Basis I K V)
  (degree : I → D) (hhom : ∀ i,B i∈G.piece (degree i))

include hhom in
theorem repr_projection (p : D) (x : V) (i : I) :
    B.repr (projection G p x) i=if degree i=p then B.repr x i else 0 := by
  classical
  have hx := B.mem_span x
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j,rfl⟩ := hx
      by_cases hji : j=i
      · subst j
        by_cases hi : degree i=p
        · rw [projection_of_mem G p _ (hi ▸ hhom i),if_pos hi]
        · rw [projection_of_mem_ne G p (degree i) _ (hhom i) hi,if_neg hi]
          simp only [map_zero,Finsupp.zero_apply]
      · by_cases hj : degree j=p
        · rw [projection_of_mem G p _ (hj ▸ hhom j),B.repr_self,
            Finsupp.single_eq_of_ne (Ne.symm hji)]
          split_ifs <;> rfl
        · rw [projection_of_mem_ne G p (degree j) _ (hhom j) hj,
            map_zero,Finsupp.zero_apply,B.repr_self,Finsupp.single_eq_of_ne (Ne.symm hji)]
          split_ifs <;> rfl
  | zero => simp only [map_zero,Finsupp.zero_apply,ite_self]
  | add x y hx hy ihx ihy =>
      rw [map_add,map_add,Finsupp.add_apply,ihx,ihy,map_add,Finsupp.add_apply]
      split_ifs <;> simp only [add_zero]
  | smul c x hx ih =>
      rw [map_smul,map_smul,Finsupp.smul_apply,ih,map_smul,Finsupp.smul_apply]
      split_ifs <;> simp only [smul_zero]

include hhom in
theorem repr_eq_zero_of_degree_ne (p : D) (x : V) (hx : x∈G.piece p)
    (i : I) (hi : degree i≠p) : B.repr x i=0 := by
  have h := repr_projection G B degree hhom p x i
  rwa [projection_of_mem G p x hx,if_neg hi] at h

end PaperVerification.GradedComponentBasis
end
end
end TAF_LiteralSource_0241

section TAF_LiteralSource_0242
/- Original module: PaperVerification.AlternatingFormsOddNormalForm -/


/-!
# The three genuine bounds on the odd-pencil normal form

The coefficients below are the coordinates in the actual quotient basis.
Their ordinary degree is forced by the inherited quotient grading. Their
first weight is bounded by actual initial-relation lifts; at equality they
are the Richardson coefficients, whose diagonal leading terms supply the
second bound and identify the unique possible meet/join term.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators
open WeightedInitialFiber Hibi

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "w" => pluckerVertexWeight (oddNatVertexWeight k)
local notation "B" => oddPluckerStandardBasis (K := K) k t hs
local notation "B₀" => oddInitialStandardBasis (K := K) k t hs

def oddCoefficients (p : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) :
    OddStandardIndex k t hs →₀ K := (B).repr (Ideal.Quotient.mk Q p)

theorem oddInitialCoefficient_eq_interval
    (p : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K)
    (C : OddStandardIndex k t hs) :
    (B₀).repr (Ideal.Quotient.mk _ p) C=
      intervalCoefficients (K := K) α β (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega) p C := by
  change (intervalStandardBasis α β
      (oddIntervalLower_strictMono k (t+2) hs).monotone
      (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)).repr
    ((Ideal.quotientEquivAlgOfEq K (odd_isotropic_initial_eq_interval k t hs).symm).symm
      (Ideal.Quotient.mk _ p)) C=_
  rw [Ideal.quotientEquivAlgOfEq_symm,Ideal.quotientEquivAlgOfEq_mk]
  rfl

theorem oddCoefficients_weight_le
    (p : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) (d : ℕ)
    (hp : WeightBound w d p) (C : OddStandardIndex k t hs)
    (hc : oddCoefficients (K := K) k t hs p C≠0) : oddStandardWeight k t hs C≤d := by
  by_contra h
  exact hc (lifted_coefficient_eq_zero_of_weight_lt Q w
    (oddStandardRepresentative (K := K) k t hs) (oddStandardWeight k t hs)
    (oddStandardRepresentative_weighted (K := K) k t hs) B₀ (oddInitialStandardBasis_apply (K := K) k t hs)
    p d hp C (lt_of_not_ge h))

theorem oddCoefficients_top_eq
    (p : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) (d : ℕ)
    (hp : WeightBound w d p) (C : OddStandardIndex k t hs)
    (hc : oddStandardWeight k t hs C=d) :
    oddCoefficients (K := K) k t hs p C=
      intervalCoefficients (K := K) α β (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)
        (weightedHomogeneousComponent w d p) C := by
  exact (lifted_top_coefficient Q w (oddStandardRepresentative (K := K) k t hs)
    (oddStandardWeight k t hs) (oddStandardRepresentative_weighted (K := K) k t hs)
    B₀ (oddInitialStandardBasis_apply (K := K) k t hs) p d hp C hc).trans
      (oddInitialCoefficient_eq_interval (K := K) k t hs _ C)

theorem oddCoefficients_degree_eq
    (p : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) (d : ℕ)
    (hp : p.IsHomogeneous d) (C : OddStandardIndex k t hs)
    (hc : oddCoefficients (K := K) k t hs p C≠0) : C.1=d := by
  by_contra hne
  apply hc
  apply GradedComponentBasis.repr_eq_zero_of_degree_ne
    (HomogeneousIdealPieces.grading Q (isotropicPluckerIdeal_isHomogeneous _)) B
    (fun C => C.1)
    (fun C => by
      rw [HomogeneousIdealPieces.grading_piece]
      exact oddPluckerStandardBasis_mem_degree (K := K) k t hs C)
    d (Ideal.Quotient.mk Q p) ?_ C hne
  rw [HomogeneousIdealPieces.grading_piece]
  exact ⟨p,hp,rfl⟩

def oddGoodWeight (I : IntervalIndex α β) : ℕ := w I.val

theorem odd_pair_homogeneous (I J : IntervalIndex α β) :
    (X I.val*X J.val : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K).IsWeightedHomogeneous w (oddGoodWeight k t hs I+oddGoodWeight k t hs J) :=
  (isWeightedHomogeneous_X K w I.val).mul (isWeightedHomogeneous_X K w J.val)

theorem odd_pair_coefficients_degree (I J : IntervalIndex α β)
    (C : OddStandardIndex k t hs)
    (hc : oddCoefficients (K := K) k t hs (X I.val*X J.val) C≠0) : C.1=2 :=
  oddCoefficients_degree_eq (K := K) k t hs _ 2
    ((isHomogeneous_X K I.val).mul (isHomogeneous_X K J.val)) C hc

theorem odd_pair_coefficients_interval (I J : IntervalIndex α β)
    (C : OddStandardIndex k t hs)
    (hw : oddStandardWeight k t hs C=oddGoodWeight k t hs I+oddGoodWeight k t hs J) :
    oddCoefficients (K := K) k t hs (X I.val*X J.val) C=
      intervalCoefficients (K := K) α β (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)
        (X I.val*X J.val) C := by
  have hp := odd_pair_homogeneous (K := K) k t hs I J
  rw [oddCoefficients_top_eq (K := K) k t hs _ _ (fun a ha => (hp ha).le) C hw,
    weightedHomogeneousComponent_eq_self hp]

/-- Every actual straightening coefficient obeys the two filtration
bounds. In the common top of both, its chain is exactly meet/join. -/
theorem odd_pair_coefficients_triangular (I J : IntervalIndex α β)
    (C : OddStandardIndex k t hs)
    (hc : oddCoefficients (K := K) k t hs (X I.val*X J.val) C≠0) :
    oddStandardWeight k t hs C<oddGoodWeight k t hs I+oddGoodWeight k t hs J ∨
      (oddStandardWeight k t hs C=oddGoodWeight k t hs I+oddGoodWeight k t hs J ∧
        (standardDiagonalWeight α β C<diagonalWeight α β I+diagonalWeight α β J ∨
          (standardDiagonalWeight α β C=diagonalWeight α β I+diagonalWeight α β J ∧
            C=pairChain α β I J))) := by
  have hp := odd_pair_homogeneous (K := K) k t hs I J
  have hw := oddCoefficients_weight_le (K := K) k t hs _ _ (fun a ha => (hp ha).le) C hc
  rcases hw.lt_or_eq with hw | hw
  · exact Or.inl hw
  · refine Or.inr ⟨hw,?_⟩
    have hc' : intervalCoefficients (K := K) α β
        (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)
        (X I.val*X J.val) C≠0 := by
      rwa [←odd_pair_coefficients_interval (K := K) k t hs I J C hw]
    have hd := interval_pair_diagonal_le (K := K) α β
      (oddIntervalLower_strictMono k (t+2) hs).monotone
      (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega) I J C hc'
    rcases hd.lt_or_eq with hd | hd
    · exact Or.inl hd
    · exact Or.inr ⟨hd,interval_pair_top_chain (K := K) α β
        (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega) I J C hc' hd⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0242

section TAF_LiteralSource_0243
/- Original module: PaperVerification.AlternatingFormsHibiMonomials -/


/-!
# The actual monomials avoiding incomparable pairs

A monomial avoids the incomparable quadratic divisors exactly when its
support is a chain. Meet/join insertion of such a multiset only permutes
its entries, so its product is literally a standard chain product before
taking any quotient. Distinct such monomials have distinct diagonal images.
These statements identify the genuine division remainders needed for the
Hibi Gröbner proof.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] {s n : ℕ} (α β : Fin s → Fin n)

def ComparableSet (A : Set (IntervalIndex α β)) : Prop :=
  ∀ I∈A,∀ J∈A,I≤J ∨ J≤I

theorem meet_mem_comparable {A : Set (IntervalIndex α β)} (hA : ComparableSet α β A)
    (I J : IntervalIndex α β) (hI : I∈A) (hJ : J∈A) : meet α β I J∈A := by
  rcases hA I hI J hJ with h | h
  · rwa [meet_eq_left α β I J h]
  · rwa [meet_eq_right α β I J h]

theorem join_mem_comparable {A : Set (IntervalIndex α β)} (hA : ComparableSet α β A)
    (I J : IntervalIndex α β) (hI : I∈A) (hJ : J∈A) : join α β I J∈A := by
  rcases hA I hI J hJ with h | h
  · rwa [join_eq_right α β I J h]
  · rwa [join_eq_left α β I J h]

theorem insert_mem_comparable {A : Set (IntervalIndex α β)} (hA : ComparableSet α β A)
    (I : IntervalIndex α β) (L : List (IntervalIndex α β))
    (hI : I∈A) (hL : ∀ J∈L,J∈A) : ∀ J∈insert α β I L,J∈A := by
  induction L generalizing I with
  | nil => simpa only [insert,List.mem_singleton,forall_eq] using hI
  | cons J L ih =>
      intro Z hZ
      have hJ := hL J (List.mem_cons_self)
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact meet_mem_comparable α β hA I J hI hJ
      · exact ih (join α β I J) (join_mem_comparable α β hA I J hI hJ)
          (fun T hT => hL T (List.mem_cons_of_mem _ hT)) Z hZ

theorem sort_mem_comparable {A : Set (IntervalIndex α β)} (hA : ComparableSet α β A)
    (L : List (IntervalIndex α β)) (hL : ∀ J∈L,J∈A) : ∀ J∈sort α β L,J∈A := by
  induction L with
  | nil => simp only [sort,List.foldr_nil,List.not_mem_nil,false_implies,implies_true]
  | cons I L ih =>
      exact insert_mem_comparable α β hA I (sort α β L)
        (hL I (List.mem_cons_self))
        (ih (fun J hJ => hL J (List.mem_cons_of_mem _ hJ)))

theorem pair_eq_of_comparable (I J : IntervalIndex α β) (h : I≤J ∨ J≤I) :
    X (meet α β I J)*X (join α β I J)=(X I*X J : MvPolynomial (IntervalIndex α β) K) := by
  rcases h with h | h
  · rw [meet_eq_left α β I J h,join_eq_right α β I J h]
  · rw [meet_eq_right α β I J h,join_eq_left α β I J h,mul_comm]

theorem word_insert_eq_of_comparable {A : Set (IntervalIndex α β)}
    (hA : ComparableSet α β A) (I : IntervalIndex α β) (L : List (IntervalIndex α β))
    (hI : I∈A) (hL : ∀ J∈L,J∈A) :
    word (K := K) α β (insert α β I L)=X I*word α β L := by
  induction L generalizing I with
  | nil => simp only [insert,word_cons,word_nil,mul_one]
  | cons J L ih =>
      have hJ := hL J (List.mem_cons_self)
      rw [insert,word_cons,ih (join α β I J)
        (join_mem_comparable α β hA I J hI hJ)
        (fun T hT => hL T (List.mem_cons_of_mem _ hT)),word_cons,←mul_assoc,
        pair_eq_of_comparable α β I J (hA I hI J hJ),mul_assoc]

theorem word_sort_eq_of_comparable {A : Set (IntervalIndex α β)}
    (hA : ComparableSet α β A) (L : List (IntervalIndex α β)) (hL : ∀ J∈L,J∈A) :
    word (K := K) α β (sort α β L)=word α β L := by
  induction L with
  | nil => rfl
  | cons I L ih =>
      change word α β (insert α β I (sort α β L))=word α β (I::L)
      rw [word_insert_eq_of_comparable α β hA I _ (hL I (List.mem_cons_self))
        (sort_mem_comparable α β hA L (fun J hJ => hL J (List.mem_cons_of_mem _ hJ))),
        ih (fun J hJ => hL J (List.mem_cons_of_mem _ hJ)),word_cons]

def multisetWord (M : Multiset (IntervalIndex α β)) : MvPolynomial (IntervalIndex α β) K :=
  (M.map X).prod

theorem multisetWord_toMultiset (m : IntervalIndex α β →₀ ℕ) :
    multisetWord (K := K) α β m.toMultiset=monomial m 1 := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp only [Finsupp.toMultiset_zero,multisetWord,Multiset.map_zero,
      Multiset.prod_zero,monomial_zero',map_one]
  | add m m' hm hm' =>
      simp only [Finsupp.toMultiset_add,multisetWord,Multiset.map_add,Multiset.prod_add] at *
      rw [hm,hm',monomial_mul,one_mul]
  | single I r =>
      have hmap : (r • ({I} : Multiset (IntervalIndex α β))).map
          (X : IntervalIndex α β → MvPolynomial (IntervalIndex α β) K)=r • {X I} := by
        simpa only [Multiset.coe_mapAddMonoidHom,Multiset.map_singleton] using
          (Multiset.mapAddMonoidHom (X : IntervalIndex α β →
            MvPolynomial (IntervalIndex α β) K)).map_nsmul r ({I} : Multiset (IntervalIndex α β))
      simp only [Finsupp.toMultiset_single,multisetWord,hmap,
        Multiset.prod_nsmul,Multiset.prod_singleton,X_pow_eq_monomial]

theorem word_toMultiset (m : IntervalIndex α β →₀ ℕ) :
    word (K := K) α β m.toMultiset.toList=monomial m 1 := by
  have h : word (K := K) α β m.toMultiset.toList=multisetWord α β m.toMultiset := by
    unfold word multisetWord
    rw [←Multiset.prod_coe,←Multiset.map_coe,Multiset.coe_toList]
  exact h.trans (multisetWord_toMultiset α β m)

def NormalMonomial (m : IntervalIndex α β →₀ ℕ) : Prop :=
  ComparableSet α β (m.support : Set (IntervalIndex α β))

def normalChain (m : IntervalIndex α β →₀ ℕ) : Σ r,BandChain α β r :=
  ⟨(sort α β m.toMultiset.toList).length,
    chainOfList α β _ (sort_sorted α β m.toMultiset.toList)⟩

theorem normalChain_polynomial (m : IntervalIndex α β →₀ ℕ) (hm : NormalMonomial α β m) :
    standardPolynomial (K := K) α β (normalChain α β m).2=monomial m 1 := by
  rw [normalChain,standardPolynomial_chainOfList,
    word_sort_eq_of_comparable α β hm,word_toMultiset]
  intro I hI
  exact (Finsupp.mem_toMultiset m I).mp (Multiset.mem_toList.mp hI)

def hibiExponentMap : (IntervalIndex α β →₀ ℕ) →ₗ[ℕ] ((Fin s × Fin n) →₀ ℕ) :=
  WeightedSagbi.exponentMap (fun I : IntervalIndex α β => minorTermExponent I.val.val 1)

theorem diagonalMap_monomial (m : IntervalIndex α β →₀ ℕ) (c : K) :
    diagonalMap α β (monomial m c)=monomial (hibiExponentMap α β m) c :=
  WeightedSagbi.monomialSubstitution_monomial _ m c

include K in
theorem normalChain_diagonal (m : IntervalIndex α β →₀ ℕ) (hm : NormalMonomial α β m) :
    chainDiagonalExponent (normalChain α β m).2.val=hibiExponentMap α β m := by
  apply MvPolynomial.monomial_left_injective (one_ne_zero : (1 : K)≠0)
  change (monomial (chainDiagonalExponent (normalChain α β m).2.val) 1 :
      MvPolynomial (Fin s × Fin n) K)=monomial (hibiExponentMap α β m) 1
  calc
    _ = diagonalMap α β (standardPolynomial α β (normalChain α β m).2) :=
      (diagonalMap_standardPolynomial α β (normalChain α β m).2).symm
    _ = diagonalMap α β (monomial m 1) :=
      congrArg (diagonalMap α β) (normalChain_polynomial α β m hm)
    _ = _ := diagonalMap_monomial α β m 1

include K in
theorem hibiExponentMap_normal_injective (hs : 0<s) :
    Function.Injective (fun m : {m : IntervalIndex α β →₀ ℕ // NormalMonomial α β m} =>
      hibiExponentMap α β m.val) := by
  intro m m' h
  have hc : normalChain α β m.val=normalChain α β m'.val := by
    apply allChainDiagonalExponent_injective α β hs
    change chainDiagonalExponent (normalChain α β m.val).2.val=
      chainDiagonalExponent (normalChain α β m'.val).2.val
    exact (normalChain_diagonal (K := K) α β m.val m.property).trans
      (h.trans (normalChain_diagonal (K := K) α β m'.val m'.property).symm)
  apply Subtype.ext
  apply MvPolynomial.monomial_left_injective (one_ne_zero : (1 : K)≠0)
  change (monomial m.val 1 : MvPolynomial (IntervalIndex α β) K)=monomial m'.val 1
  have hp := congrArg (fun C : Σ r,BandChain α β r =>
    standardPolynomial (K := K) α β C.2) hc
  exact (normalChain_polynomial α β m.val m.property).symm.trans
    (hp.trans (normalChain_polynomial α β m'.val m'.property))

/-- A polynomial supported on chain monomials has no diagonal-image
cancellation. This is the independence needed for actual remainders. -/
theorem normal_polynomial_eq_zero (hs : 0<s) (p : MvPolynomial (IntervalIndex α β) K)
    (hp : ∀ m∈p.support,NormalMonomial α β m) (hz : diagonalMap α β p=0) : p=0 := by
  classical
  have hli : LinearIndependent K (fun m : p.support =>
      diagonalMap α β (monomial m.val 1 : MvPolynomial (IntervalIndex α β) K)) := by
    simp only [diagonalMap_monomial]
    apply (MvPolynomial.basisMonomials (Fin s × Fin n) K).linearIndependent.comp
    intro m m' h
    have he := hibiExponentMap_normal_injective (K := K) α β hs
      (show hibiExponentMap α β (⟨m.val,hp m.val m.property⟩ :
        {m : IntervalIndex α β →₀ ℕ // NormalMonomial α β m})=
        hibiExponentMap α β (⟨m'.val,hp m'.val m'.property⟩ :
        {m : IntervalIndex α β →₀ ℕ // NormalMonomial α β m}) from h)
    apply Subtype.ext
    exact congrArg (fun a : {m : IntervalIndex α β →₀ ℕ // NormalMonomial α β m} => a.val) he
  have hsum : (∑ m : p.support,p.coeff m.val •
      diagonalMap α β (monomial m.val 1 : MvPolynomial (IntervalIndex α β) K))=0 := by
    rw [Finset.sum_coe_sort (s := p.support)
      (f := fun m : IntervalIndex α β →₀ ℕ => p.coeff m •
        diagonalMap α β (monomial m 1 : MvPolynomial (IntervalIndex α β) K))]
    rw [←WeightedSagbi.map_eq_coefficient_sum]
    exact hz
  have hc := Fintype.linearIndependent_iff.mp hli (fun m => p.coeff m.val) hsum
  ext m
  by_cases hm : m∈p.support
  · simpa only [MvPolynomial.coeff_zero,Finsupp.zero_apply] using hc ⟨m,hm⟩
  · simp only [notMem_support_iff.mp hm,MvPolynomial.coeff_zero,Finsupp.zero_apply]

end PaperVerification.AlternatingForms.Hibi
end
end
end TAF_LiteralSource_0243

section TAF_LiteralSource_0244
/- Original module: PaperVerification.WeightedMonomialOrder -/


/-!
# A monomial order refining an actual natural weight

The synonym is the additive graph of `(weight, oldOrder)` inside the
lexicographic product. This constructs the order and its well-foundedness;
no compatibility or termination condition is assumed of the weight.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedMonomialOrder

variable {σ : Type*}

/-- A base monomial order on any finite variable set. The temporary
linear order is scoped inside this definition, so it does not replace any
existing partial order used to express the mathematical chain condition. -/
def finiteBaseOrder (σ : Type*) [Fintype σ] : MonomialOrder σ := by
  classical
  let e := Fintype.equivFin σ
  letI : LinearOrder σ := LinearOrder.lift' e e.injective
  letI : WellFoundedGT σ := InvImage.wf e (wellFounded_gt (α := Fin (Fintype.card σ)))
  exact MonomialOrder.lex

def graph (m : MonomialOrder σ) (w : σ → ℕ) :
    (σ →₀ ℕ) →+ Lex (ℕ × m.syn) where
  toFun a := toLex (Finsupp.weight w a,m.toSyn a)
  map_zero' := by simp only [map_zero]; rfl
  map_add' a b := by simp only [map_add]; rfl

theorem graph_injective (m : MonomialOrder σ) (w : σ → ℕ) :
    Function.Injective (graph m w) := by
  intro a b h
  exact m.toSyn.injective (congrArg (fun z : Lex (ℕ × m.syn) => (ofLex z).2) h)

def weightedRefinement (m : MonomialOrder σ) (w : σ → ℕ) : MonomialOrder σ where
  syn := AddMonoidHom.mrange (graph m w)
  toSyn :=
    { Equiv.ofBijective (AddMonoidHom.mrangeRestrict (graph m w))
        ⟨fun a b h => graph_injective m w (congrArg Subtype.val h),
          AddMonoidHom.mrangeRestrict_surjective (graph m w)⟩ with
      map_add' a b := by
        apply Subtype.ext
        exact (graph m w).map_add' a b }
  toSyn_monotone := by
    intro a b hab
    change toLex (Finsupp.weight w a,m.toSyn a)≤toLex (Finsupp.weight w b,m.toSyn b)
    apply Prod.Lex.le_iff.mpr
    have hw : Finsupp.weight w a≤Finsupp.weight w b := by
      obtain ⟨c,rfl⟩ := exists_add_of_le hab
      rw [map_add]
      exact Nat.le_add_right _ _
    rcases hw.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,m.toSyn_monotone hab⟩

theorem lt_of_weight_lt (m : MonomialOrder σ) (w : σ → ℕ) (a b : σ →₀ ℕ)
    (h : Finsupp.weight w a<Finsupp.weight w b) :
    (weightedRefinement m w).toSyn a<(weightedRefinement m w).toSyn b := by
  change toLex (Finsupp.weight w a,m.toSyn a)<toLex (Finsupp.weight w b,m.toSyn b)
  exact Prod.Lex.lt_iff.mpr (Or.inl h)

theorem weight_le_of_le (m : MonomialOrder σ) (w : σ → ℕ) (a b : σ →₀ ℕ)
    (h : (weightedRefinement m w).toSyn a≤(weightedRefinement m w).toSyn b) :
    Finsupp.weight w a≤Finsupp.weight w b := by
  change toLex (Finsupp.weight w a,m.toSyn a)≤toLex (Finsupp.weight w b,m.toSyn b) at h
  rcases Prod.Lex.le_iff.mp h with h | ⟨h,_⟩
  · exact h.le
  · exact h.le

theorem lt_of_weight_eq_of_lt (m : MonomialOrder σ) (w : σ → ℕ)
    (a b : σ →₀ ℕ) (he : Finsupp.weight w a=Finsupp.weight w b)
    (hlt : m.toSyn a<m.toSyn b) :
    (weightedRefinement m w).toSyn a<(weightedRefinement m w).toSyn b := by
  change toLex (Finsupp.weight w a,m.toSyn a)<toLex (Finsupp.weight w b,m.toSyn b)
  exact Prod.Lex.lt_iff.mpr (Or.inr ⟨he,hlt⟩)

end PaperVerification.WeightedMonomialOrder
end
end
end TAF_LiteralSource_0244

section TAF_LiteralSource_0245
/- Original module: TauCeti.RingTheory.MvPolynomial.MonomialOrder -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Leading monomials for a monomial order

This file collects facts about leading monomials of multivariate polynomials for a monomial order
`m` on `σ →₀ ℕ`: comparisons of degrees with their `WithBot` forms, the degree of a monomial
multiple, the cancellation of leading terms by an S-polynomial, the behaviour of leading data
under a change of coefficients, leading data of the weighted homogeneous component containing
the leading monomial, leading data of renamed polynomials, elimination orders and the
lexicographic ones among them, and algebraic independence from leading monomials.

The product `X^a * b`, normalized to leading coefficient one when `b` has a unit leading
coefficient, differs from another such product of the same degree by a monomial multiple of
their S-polynomial. This is the cancellation of leading terms behind Buchberger's criterion.

Let `yᵢ`, `i ∈ σ`, be polynomials in the variables `Xᵢ` over a ring without zero divisors. If the
leading monomial of each `yᵢ` is the variable `Xᵢ`, then the `yᵢ` are algebraically independent:
the image of a monomial `c X^d` under `Xᵢ ↦ yᵢ` has leading monomial `X^d`, so the images of the
distinct monomials of a nonzero polynomial have distinct leading monomials and cannot cancel.

This is the triangularity argument for a family such as `yₙ = cₙ Xₙ + qₙ(X₁, …, Xₙ₋₁)` with
`cₙ ≠ 0`, ordered lexicographically with the variables of larger index more significant, as for
the images of the generators of the Lazard ring in a polynomial ring.

## Main results

* `MonomialOrder.toWithBotSyn_withBotDegree_le_toSyn_degree`: the `WithBot` degree of a polynomial
  is at most its degree.
* `MonomialOrder.withBotDegree_sub_lt`: if `q` has degree at most that of `f ≠ 0` and the same
  coefficient of `X^(deg f)`, then `f - q` has smaller degree than `f`.
* `MonomialOrder.toSyn_degree_monomial_mul_le`: `c X^a * b` has degree at most `a + deg b`.
* `MonomialOrder.monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial`: if `b₀` has a unit
  leading coefficient, then `X^a * b` minus `lc b` times the product of `b₀` of the same degree
  normalized to leading coefficient one is a monomial multiple of the S-polynomial
  `m.sPolynomial b b₀`.
* `MonomialOrder.degree_map_of_injective`, `MonomialOrder.leadingCoeff_map_of_injective`,
  `MonomialOrder.leadingTerm_map_of_injective`, `MonomialOrder.sPolynomial_map_of_injective`: an
  injective coefficient map `φ` preserves leading monomials and commutes with leading
  coefficients, leading terms and S-polynomials.
* `MonomialOrder.leadingTerm_weightedHomogeneousComponent_weight_degree`: the weighted
  homogeneous component of `f` containing its leading monomial has the leading term of `f`.
* `MonomialOrder.degree_rename`, `MonomialOrder.leadingCoeff_rename` and
  `MonomialOrder.leadingTerm_rename`: renaming the variables along a relabeling which carries one
  monomial order to another commutes with leading monomials, coefficients and terms; such a
  relabeling is injective by `MonomialOrder.injective_of_forall_toSyn_le_iff`.
* `MonomialOrder.exists_rename_eq_of_coe_support_degree_subset`: for an elimination order, a
  polynomial whose leading monomial only involves the variables `e τ` is a renamed polynomial.
* `MonomialOrder.coe_support_subset_of_lex_le`: monomials supported in an upper set of variables
  form a lower set for the lexicographic order.
* `MonomialOrder.algebraicIndependent_of_degree_eq_single`: polynomials `yᵢ` whose leading
  monomial is `Xᵢ` are algebraically independent.
-/

public section

open MvPolynomial

namespace MonomialOrder

variable {σ R : Type*} (m : MonomialOrder σ)

/-- The `WithBot` degree of a polynomial is at most its degree. -/
theorem toWithBotSyn_withBotDegree_le_toSyn_degree [CommSemiring R] (p : MvPolynomial σ R) :
    m.toWithBotSyn (m.withBotDegree p) ≤ m.toSyn (m.degree p) := by
  classical
  rw [withBotDegree_eq]
  split_ifs <;> simp [toWithBotSyn_apply_coe]

/-- If `q` has degree at most that of `f ≠ 0` and the same coefficient of `X^(deg f)`, then
`f - q` has smaller degree than `f`. -/
theorem withBotDegree_sub_lt [CommRing R] {f q : MvPolynomial σ R} (hf : f ≠ 0)
    (hq : m.toWithBotSyn (m.withBotDegree q) ≤ m.toWithBotSyn (m.withBotDegree f))
    (hqf : q.coeff (m.degree f) = m.leadingCoeff f) :
    m.toWithBotSyn (m.withBotDegree (f - q)) < m.toWithBotSyn (m.withBotDegree f) := by
  refine lt_of_le_of_ne ?_ fun heq ↦ ?_
  · simpa [sub_eq_add_neg] using
      (m.withBotDegree_add_le f (-q)).trans (max_le le_rfl (by rwa [withBotDegree_neg]))
  rw [EmbeddingLike.apply_eq_iff_eq, withBotDegree_eq_withBotDegree_iff] at heq
  have := m.degree_mem_support fun h0 ↦ hf (heq.2.1 h0)
  rw [heq.1, mem_support_iff, coeff_sub, hqf, leadingCoeff, sub_self] at this
  exact this rfl

/-- A monomial multiple `c X^a * b` has degree at most `a + deg b`. -/
theorem toSyn_degree_monomial_mul_le [CommSemiring R] (a : σ →₀ ℕ) (c : R)
    (b : MvPolynomial σ R) : m.toSyn (m.degree (monomial a c * b)) ≤ m.toSyn (a + m.degree b) := by
  rw [map_add]
  exact m.toSyn_degree_mul_le.trans (by gcongr; exact m.degree_monomial_le c)

/-- **Cancellation of leading terms by an S-polynomial.** If `b₀` has unit leading coefficient
`u₀` and `deg b₀ ≤ a + deg b`, the difference between `X^a * b` and `lc b` times the normalized
product `X^(a + deg b - deg b₀) * b₀ / lc b₀` is `X^(a + deg b - L) / lc b₀ * S(b, b₀)`, where
`L = deg b ⊔ deg b₀`. -/
theorem monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial [CommRing R] {a : σ →₀ ℕ}
    {b b₀ : MvPolynomial σ R} (hb₀ : m.degree b₀ ≤ a + m.degree b) (u₀ : Rˣ)
    (hu₀ : (u₀ : R) = m.leadingCoeff b₀) :
    monomial a 1 * b -
        m.leadingCoeff b • (monomial (a + m.degree b - m.degree b₀) ((u₀⁻¹ : Rˣ) : R) * b₀) =
      monomial (a + m.degree b - m.degree b ⊔ m.degree b₀) ((u₀⁻¹ : Rˣ) : R) *
        m.sPolynomial b b₀ := by
  have hL : m.degree b ⊔ m.degree b₀ ≤ a + m.degree b := sup_le le_add_self hb₀
  -- The exponents of the two summands of the right-hand side.
  have e₁ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b) =
      a := by
    rw [tsub_add_tsub_cancel hL le_sup_left, add_tsub_cancel_right]
  have e₂ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b₀) =
      a + m.degree b - m.degree b₀ :=
    tsub_add_tsub_cancel hL le_sup_right
  -- The coefficient of the first summand.
  have hc : ((u₀⁻¹ : Rˣ) : R) * m.leadingCoeff b₀ = 1 := by rw [← hu₀, Units.inv_mul]
  simp only [sPolynomial_def, mul_sub, ← mul_assoc, monomial_mul_monomial, smul_eq_C_mul,
    C_mul_monomial, e₁, e₂, hc, mul_comm (m.leadingCoeff b)]

section Map

variable {S : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring S] (φ : R →+* S) {f : MvPolynomial σ R}

/-- A coefficient map that does not kill the leading coefficient preserves the leading monomial. -/
theorem degree_map_of_leadingCoeff_ne_zero (h : φ (m.leadingCoeff f) ≠ 0) :
    m.degree (map φ f) = m.degree f := by
  have hmem : m.degree f ∈ (map φ f).support := by
    rwa [mem_support_iff, coeff_map]
  exact m.toSyn.injective <| le_antisymm
    (m.degree_le_iff.2 fun _ hc ↦ m.le_degree (support_map_subset φ f hc)) (m.le_degree hmem)

/-- A coefficient map that does not kill the leading coefficient maps it to the leading
coefficient of the image. -/
theorem leadingCoeff_map_of_leadingCoeff_ne_zero (h : φ (m.leadingCoeff f) ≠ 0) :
    m.leadingCoeff (map φ f) = φ (m.leadingCoeff f) := by
  rw [leadingCoeff, degree_map_of_leadingCoeff_ne_zero m φ h, coeff_map, leadingCoeff]

variable {φ}

/-- An injective coefficient map preserves the leading monomial. -/
theorem degree_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.degree (map φ f) = m.degree f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  exact m.degree_map_of_leadingCoeff_ne_zero φ
    ((map_ne_zero_iff φ hφ).2 (m.leadingCoeff_ne_zero_iff.2 hf))

/-- An injective coefficient map preserves the `WithBot` degree. -/
theorem withBotDegree_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.withBotDegree (map φ f) = m.withBotDegree f := by
  classical
  simp [withBotDegree_eq, m.degree_map_of_injective hφ, map_eq_zero_iff _ (map_injective φ hφ)]

/-- An injective coefficient map sends the leading coefficient to the leading coefficient of the
image. -/
theorem leadingCoeff_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.leadingCoeff (map φ f) = φ (m.leadingCoeff f) := by
  rw [leadingCoeff, m.degree_map_of_injective hφ, coeff_map, leadingCoeff]

/-- An injective coefficient map sends the leading term to the leading term of the image. -/
theorem leadingTerm_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.leadingTerm (map φ f) = map φ (m.leadingTerm f) := by
  rw [leadingTerm, leadingTerm, map_monomial, m.degree_map_of_injective hφ,
    m.leadingCoeff_map_of_injective hφ]

end CommSemiring

/-- An injective coefficient map sends the S-polynomial of `f` and `g` to the S-polynomial of
their images. -/
theorem sPolynomial_map_of_injective [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) (f g : MvPolynomial σ R) :
    m.sPolynomial (map φ f) (map φ g) = map φ (m.sPolynomial f g) := by
  simp only [sPolynomial, map_sub, map_mul, map_monomial, m.degree_map_of_injective hφ,
    m.leadingCoeff_map_of_injective hφ]

end Map

section WeightedHomogeneous

open Finsupp

variable {M : Type*} [AddCommMonoid M] [CommSemiring R] (w : σ → M)

/-- The weighted homogeneous component of `f` whose weight is that of the leading monomial of `f`
has the same leading monomial as `f`. -/
@[simp]
theorem degree_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.degree (weightedHomogeneousComponent w (weight w (m.degree f)) f) = m.degree f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hsupp := support_weightedHomogeneousComponent (w := w) (weight w (m.degree f)) f
  refine m.toSyn.injective (le_antisymm (m.degree_le_iff.2 fun c hc ↦ ?_) (m.le_degree ?_))
  · rw [hsupp] at hc
    exact m.le_degree (Finset.mem_filter.1 hc).1
  · rw [hsupp]
    exact Finset.mem_filter.2 ⟨m.degree_mem_support hf, rfl⟩

/-- The weighted homogeneous component of `f` containing its leading monomial has the same leading
coefficient as `f`. -/
@[simp]
theorem leadingCoeff_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.leadingCoeff (weightedHomogeneousComponent w (weight w (m.degree f)) f) =
      m.leadingCoeff f := by
  classical
  simp [leadingCoeff, coeff_weightedHomogeneousComponent]

/-- The weighted homogeneous component of `f` containing its leading monomial has the same leading
term as `f`. -/
@[simp]
theorem leadingTerm_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.leadingTerm (weightedHomogeneousComponent w (weight w (m.degree f)) f) =
      m.leadingTerm f := by
  simp [leadingTerm]

/-- The weighted homogeneous component of `f` containing its leading monomial is weighted
homogeneous of the weight of its own leading monomial. -/
theorem isWeightedHomogeneous_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    IsWeightedHomogeneous w (weightedHomogeneousComponent w (weight w (m.degree f)) f)
      (weight w (m.degree (weightedHomogeneousComponent w (weight w (m.degree f)) f))) := by
  rw [degree_weightedHomogeneousComponent_weight_degree]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

end WeightedHomogeneous

section Rename

variable {τ : Type*} [CommSemiring R] {m} {m' : MonomialOrder τ} {e : τ → σ}

/-- A relabeling of variables which carries the monomial order `m'` to `m` is injective. -/
theorem injective_of_forall_toSyn_le_iff
    (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e) :
    Function.Injective e := by
  intro i j hij
  -- The two variables `X i`, `X j` are renamed to the same variable, so neither exceeds the other.
  have hsingle : m.toSyn ((Finsupp.single i 1).mapDomain e) =
      m.toSyn ((Finsupp.single j 1).mapDomain e) := by
    simp [hij]
  have h := m'.toSyn.injective <| le_antisymm ((hm _ _).2 hsingle.le) ((hm _ _).2 hsingle.ge)
  simpa [Finsupp.single_left_inj] using h

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m` renames
the leading monomial. -/
theorem degree_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.degree (rename e p) = (m'.degree p).mapDomain e := by
  classical
  have he := injective_of_forall_toSyn_le_iff hm
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine m.toSyn.injective (le_antisymm (m.degree_le_iff.2 fun c hc ↦ ?_) (m.le_degree ?_))
  · rw [support_rename_of_injective he, Finset.mem_image] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    exact (hm _ _).1 (m'.le_degree ha)
  · rw [support_rename_of_injective he]
    exact Finset.mem_image_of_mem _ (m'.degree_mem_support hp)

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m`
preserves the leading coefficient. -/
theorem leadingCoeff_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.leadingCoeff (rename e p) = m'.leadingCoeff p := by
  rw [leadingCoeff, degree_rename hm,
    coeff_rename_mapDomain _ (injective_of_forall_toSyn_le_iff hm), leadingCoeff]

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m`
renames the leading term. -/
theorem leadingTerm_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.leadingTerm (rename e p) = rename e (m'.leadingTerm p) := by
  rw [leadingTerm, leadingTerm, degree_rename hm, leadingCoeff_rename hm, rename_monomial]

/-- For an elimination order `m` for the variables `e τ`, that is, one in which every monomial
below a monomial in these variables is again a monomial in these variables, a polynomial whose
leading monomial only involves the variables `e τ` is the renaming of a polynomial in the
variables `τ`. -/
theorem exists_rename_eq_of_coe_support_degree_subset
    (helim : ∀ a b : σ →₀ ℕ, a ≼[m] b → ↑b.support ⊆ Set.range e → ↑a.support ⊆ Set.range e)
    (he : Function.Injective e) {g : MvPolynomial σ R}
    (hg : ↑(m.degree g).support ⊆ Set.range e) : ∃ g' : MvPolynomial τ R, rename e g' = g := by
  classical
  refine exists_rename_eq_of_vars_subset_range g e he fun i hi ↦ ?_
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).1 hi
  exact helim d _ (m.le_degree hd) hg hid

end Rename

section Lex

/-- For the lexicographic order, the monomials supported in an upper set of variables form a
lower set: with the antitone variable convention these are the smallest variables. -/
theorem coe_support_subset_of_lex_le [LinearOrder σ] [WellFoundedGT σ] {s : Set σ}
    (hs : IsUpperSet s) {a b : σ →₀ ℕ} (hab : a ≼[lex] b) (hb : ↑b.support ⊆ s) :
    ↑a.support ⊆ s := by
  intro j hj
  by_contra hjs
  rcases eq_or_ne a b with rfl | hne
  · exact hjs (hb hj)
  -- `a < b` first differs from `b` at some `i` with `0 ≤ a i < b i`, so `i ∈ s`; since `j ∉ s`,
  -- `j < i`, and then `a j = b j = 0`.
  obtain ⟨i, hi, hlt⟩ := Finsupp.Lex.lt_iff.1 <| lex_lt_iff.1 <|
    lt_of_le_of_ne hab (lex.toSyn.injective.ne hne)
  have hbi : i ∈ s := hb (Finsupp.mem_support_iff.2 (Nat.zero_lt_of_lt hlt).ne')
  have hji : j < i := lt_of_not_ge fun hij ↦ hjs (hs hij hbi)
  have hbj : b j = 0 := Finsupp.notMem_support_iff.1 fun h ↦ hjs (hb h)
  exact (Finsupp.mem_support_iff.1 hj) ((hi j hji).trans hbj)

end Lex

variable [CommRing R] [NoZeroDivisors R]

/-- **Algebraic independence from leading monomials.** Over a ring without zero divisors, a family
`yᵢ` of polynomials in the variables `Xᵢ` whose leading monomial for a monomial order is `Xᵢ` is
algebraically independent. -/
theorem algebraicIndependent_of_degree_eq_single {y : σ → MvPolynomial σ R}
    (hy : ∀ i, m.degree (y i) = Finsupp.single i 1) : AlgebraicIndependent R y := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact algebraicIndependent_iff_injective_aeval.2 fun _ _ _ ↦ Subsingleton.elim _ _
  have hy0 (i : σ) : y i ≠ 0 := fun h ↦ by
    simpa [h] using congrArg (fun d ↦ d i) (hy i)
  have hne (d : σ →₀ ℕ) : (d.prod fun i k ↦ y i ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hy0 i)
  -- The image `c ∏ yᵢ ^ dᵢ` of a monomial `c X^d` with `c ≠ 0` has leading monomial `X^d`.
  have hterm {c : R} (hc : c ≠ 0) (d : σ →₀ ℕ) : m.degree (aeval y (monomial d c)) = d := by
    rw [aeval_monomial, algebraMap_eq, m.degree_mul (C_ne_zero.2 hc) (hne d), m.degree_C,
      zero_add, Finsupp.prod, m.degree_prod fun i _ ↦ pow_ne_zero _ (hy0 i)]
    simp_rw [m.degree_pow, hy, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact d.sum_single
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  rw [p.as_sum, map_sum] at hp
  -- The images of the monomials of `p` have pairwise distinct leading monomials, so their sum is
  -- nonzero.
  refine AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree (D := m.toSyn)
    (support_nonempty.2 hp0) (fun d hd ↦ ?_) (fun d hd e he hde ↦ ?_) hp
  · rw [aeval_monomial, algebraMap_eq]
    exact mul_ne_zero (C_ne_zero.2 (mem_support_iff.1 hd)) (hne d)
  · have key (d : σ →₀ ℕ) (hd : d ∈ p.support) :
        AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) = m.toSyn d := by
      -- `m.degree` is defined as the supremum `AddMonoidAlgebra.supDegree m.toSyn`, read back
      -- through `m.toSyn`.
      have h : m.toSyn (m.degree (aeval y (monomial d (p.coeff d)))) =
          AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) := by
        rw [degree, AddEquiv.apply_symm_apply]
        rfl
      rw [← h, hterm (mem_support_iff.1 hd)]
    change AddMonoidAlgebra.supDegree m.toSyn (aeval (R := R) y (monomial d (p.coeff d))) =
      AddMonoidAlgebra.supDegree m.toSyn (aeval (R := R) y (monomial e (p.coeff e))) at hde
    rw [key d hd,key e he] at hde
    exact m.toSyn.injective hde

end MonomialOrder
end
end TAF_LiteralSource_0245

section TAF_LiteralSource_0246
/- Original module: TauCeti.RingTheory.MvPolynomial.Groebner.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Remainders and Gröbner bases

Let `m` be a monomial order on `σ →₀ ℕ`. This file defines remainders on division by a set of
multivariate polynomials, and Gröbner bases of an ideal, and proves that remainders on division by
a Gröbner basis decide ideal membership.

* `MonomialOrder.IsRemainder m f B r`: `r` is a remainder of `f` on division by `B`, i.e.
  `f = ∑ g_b * b + r` where each product `g_b * b` has degree at most that of `f`, and no monomial
  of `r` is divisible by the leading monomial of a nonzero `b ∈ B`. The degree condition is
  stated with `MonomialOrder.withBotDegree`, so that the zero polynomial has degree `⊥`, and as
  the inequality `deg b + deg g_b ≤ deg f`; the remainder condition only concerns divisibility,
  not a comparison of degrees.
* `MonomialOrder.IsGroebnerBasis m G I`: `G` is a subset of the ideal `I` whose leading terms
  span the same ideal as the leading terms of all elements of `I`.

## Main results

* `MonomialOrder.exists_isRemainder`: remainders exist when every nonzero divisor has a unit
  leading coefficient; this is `MonomialOrder.div_set`.
* `MonomialOrder.IsGroebnerBasis.exists_degree_le_degree`: the leading monomial of every nonzero
  element of `I` is divisible by the leading monomial of a nonzero element of a Gröbner basis.
* `MonomialOrder.isGroebnerBasis_iff_forall_exists_degree_le_degree`: the converse, for a family
  whose nonzero members have unit leading coefficients.
* `MonomialOrder.IsGroebnerBasis.image_leadingTerm`: the leading terms of such a Gröbner basis of
  `I` form a Gröbner basis of the ideal of leading terms of `I`.
* `MonomialOrder.IsGroebnerBasis.sub_mem_iff`: for remainders `r₁`, `r₂` of `f₁`, `f₂` on division
  by a Gröbner basis of `I`, `f₁ - f₂ ∈ I` if and only if `r₁ = r₂`. In particular remainders on
  division by a Gröbner basis are unique (`MonomialOrder.IsGroebnerBasis.eq_of_isRemainder`) and
  a remainder vanishes exactly on `I` (`MonomialOrder.IsGroebnerBasis.remainder_eq_zero_iff_mem`).
* `MonomialOrder.IsGroebnerBasis.isRemainder_zero_iff_mem`: `0` is a remainder of `f` on division
  by a Gröbner basis of `I` if and only if `f ∈ I`, whatever the leading coefficients of the basis:
  every element of `I` has a standard representation (Adams–Loustaunau, Theorem 4.1.12).
* `MonomialOrder.IsGroebnerBasis.ideal_eq_span`: a Gröbner basis generates its ideal.
* `MonomialOrder.isGroebnerBasis_iff_isRemainder_zero`: `G ⊆ I` is a Gröbner basis of `I` if and
  only if every element of `I` has remainder `0` on division by `G`.

None of these results assume that the coefficients form a field: the statements needing division
assume that the nonzero members of the divisor set have unit leading coefficients, which over a
field is discharged by `MonomialOrder.isUnit_leadingCoeff`.

## References

The definitions `IsRemainder` and `IsGroebnerBasis` are those of Junyu Guo and Hao Shen in
Mathlib pull request 29203, upstreamed from the WuProver Gröbner basis project.

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §§5–6.
* W. W. Adams, P. Loustaunau, *An Introduction to Gröbner Bases*, Graduate Studies in
  Mathematics 3, American Mathematical Society, 1994, §4.1: Gröbner bases over rings and standard
  representations.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} (m : MonomialOrder σ)

section CommSemiring

variable [CommSemiring R]

/-- `r` is a remainder of `f` on division by the set `B` for the monomial order `m`: there is a
finitely supported family `g : B →₀ MvPolynomial σ R` such that

1. `f = ∑ g_b * b + r`;
2. for each `b ∈ B`, `deg b + deg g_b ≤ deg f`, degrees being taken in `WithBot` so that the zero
   polynomial has degree `⊥`;
3. no monomial of `r` is divisible by the leading monomial of a nonzero `b ∈ B`. -/
def IsRemainder (f : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    Prop :=
  (∃ g : B →₀ MvPolynomial σ R,
    f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
    ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
      m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f)) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c

/-- A subset `G` of an ideal `I` is a Gröbner basis of `I` for the monomial order `m` if the
leading terms of the elements of `G` span the same ideal as the leading terms of all elements
of `I`. -/
@[expose]
def IsGroebnerBasis (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)

variable {m} {f r : MvPolynomial σ R} {B G G' : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- Unfolding lemma for `MonomialOrder.IsRemainder`. -/
theorem isRemainder_iff : m.IsRemainder f B r ↔
    (∃ g : B →₀ MvPolynomial σ R,
      f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
      ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
        m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f)) ∧
    ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c :=
  Iff.rfl

/-- The division representation of a remainder: `f = ∑ g_b * b + r` with
`deg b + deg g_b ≤ deg f` for each `b ∈ B`. -/
theorem IsRemainder.exists_linearCombination (h : m.IsRemainder f B r) :
    ∃ g : B →₀ MvPolynomial σ R,
      f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
      ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
        m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f) :=
  h.1

/-- No monomial of a remainder is divisible by the leading monomial of a nonzero divisor. -/
theorem IsRemainder.not_degree_le (h : m.IsRemainder f B r) {c : σ →₀ ℕ} (hc : c ∈ r.support)
    {b : MvPolynomial σ R} (hb : b ∈ B) (hb0 : b ≠ 0) : ¬ m.degree b ≤ c :=
  h.2 c hc b hb hb0

/-- Unfolding lemma for `MonomialOrder.IsGroebnerBasis`. -/
theorem isGroebnerBasis_iff : m.IsGroebnerBasis G I ↔
    G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G) :=
  Iff.rfl

/-- A subset of `I` whose leading terms span the ideal of leading terms of `I` is a Gröbner basis
of `I`. -/
theorem IsGroebnerBasis.mk (hGI : G ⊆ I)
    (hspan : Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)) :
    m.IsGroebnerBasis G I :=
  ⟨hGI, hspan⟩

/-- For nonzero `p`, `q` and `f`, the `WithBot` degree bound `deg p + deg q ≤ deg f` used in
`MonomialOrder.IsRemainder` is the corresponding bound on `MonomialOrder.degree`. -/
theorem toWithBotSyn_withBotDegree_add_le_iff {p q : MvPolynomial σ R} (hp : p ≠ 0) (hq : q ≠ 0)
    (hf : f ≠ 0) :
    m.toWithBotSyn (m.withBotDegree p) + m.toWithBotSyn (m.withBotDegree q) ≤
        m.toWithBotSyn (m.withBotDegree f) ↔
      m.toSyn (m.degree p) + m.toSyn (m.degree q) ≤ m.toSyn (m.degree f) := by
  simp [(m.withBotDegree_eq_coe_degree_iff _).2, toWithBotSyn_apply_coe, ← WithBot.coe_add, *]

/-- The remainders of `0` are exactly `0`. -/
@[simp]
theorem isRemainder_zero_left_iff : m.IsRemainder 0 B r ↔ r = 0 := by
  refine ⟨fun ⟨⟨g, hg, hdeg⟩, _⟩ ↦ ?_, fun hr ↦ ⟨⟨0, by simp [hr], by simp⟩, by simp [hr]⟩⟩
  -- Each product `g b * b` vanishes, since its degree is bounded by the degree `⊥` of `0`.
  have hgb (b : B) : g b • (b : MvPolynomial σ R) = 0 := by
    have := hdeg b
    simp only [withBotDegree_zero, toWithBotSyn_apply_bot, le_bot_iff, WithBot.add_eq_bot,
      toWithBotSyn_apply_eq_bot_iff, withBotDegree_eq_bot_iff] at this
    rcases this with h | h <;> simp [h]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_eq_zero fun b _ ↦ hgb b,
    zero_add] at hg
  exact hg.symm

/-- A polynomial is a remainder of itself on division by `B` exactly when none of its monomials is
divisible by the leading monomial of a nonzero element of `B`. -/
theorem isRemainder_self_iff :
    m.IsRemainder r B r ↔ ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c :=
  ⟨And.right, fun h ↦ ⟨⟨0, by simp, by simp⟩, h⟩⟩

/-- If `0` is a remainder of `f` on division by `B`, then the leading term of `f` lies in the ideal
spanned by the leading terms of `B`. -/
theorem leadingTerm_mem_span_leadingTerm_of_isRemainder_zero (h : m.IsRemainder f B 0) :
    m.leadingTerm f ∈ Ideal.span (m.leadingTerm '' B) := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  rw [add_zero, Finsupp.linearCombination_apply, Finsupp.sum] at hfg
  -- `lt f` is the sum of the `deg f` terms of the products `g_b * b`.
  have hlt : m.leadingTerm f = ∑ b ∈ g.support,
      monomial (m.degree f) ((g b * (b : MvPolynomial σ R)).coeff (m.degree f)) := by
    simp_rw [← map_sum, ← coeff_sum, ← smul_eq_mul, ← hfg, leadingTerm, leadingCoeff]
  refine hlt ▸ sum_mem fun b _ ↦ ?_
  by_cases hb : m.degree f ∈ (g b * (b : MvPolynomial σ R)).support
  · have hgb0 : g b ≠ 0 := fun h ↦ by simp [h] at hb
    have hb0 : (b : MvPolynomial σ R) ≠ 0 := fun h ↦ by simp [h] at hb
    -- The degree condition gives `deg b + deg g_b ≤ deg f`, and `deg f` is a monomial of
    -- `g_b * b`, so the two sides are equal and the `deg f` term is `lt g_b * lt b`.
    have hle := (toWithBotSyn_withBotDegree_add_le_iff hb0 hgb0 hf).1 (hdeg b)
    have heq : m.degree f = m.degree (g b) + m.degree (b : MvPolynomial σ R) :=
      m.toSyn.injective <| by
        rw [map_add]
        exact le_antisymm ((m.le_degree hb).trans m.toSyn_degree_mul_le)
          ((add_comm _ _).trans_le hle)
    rw [heq, coeff_mul_of_degree_add, ← monomial_mul_monomial]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, b.2, rfl⟩)
  · rw [notMem_support_iff.1 hb, map_zero]
    exact zero_mem _

/-- Every monomial of an element of the ideal spanned by the leading terms of `G` is divisible by
the leading monomial of a nonzero element of `G`. -/
theorem exists_degree_le_of_mem_span_leadingTerm {p : MvPolynomial σ R}
    (hp : p ∈ Ideal.span (m.leadingTerm '' G)) {c : σ →₀ ℕ} (hc : c ∈ p.support) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ c := by
  have hle : Ideal.span (m.leadingTerm '' G) ≤
      Ideal.span ((fun d ↦ monomial d (1 : R)) '' (m.degree '' (G \ {0}))) := by
    rw [← m.span_leadingTerm_sdiff_singleton_zero, Ideal.span_le, Set.image_subset_iff]
    intro g hg
    rw [Set.mem_preimage, SetLike.mem_coe, ← C_mul_leadingCoeff_monomial_degree]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m.degree g, ⟨g, hg, rfl⟩, rfl⟩)
  obtain ⟨_, ⟨g, ⟨hgG, hg0⟩, rfl⟩, hgc⟩ := mem_ideal_span_monomial_image.1 (hle hp) c hc
  exact ⟨g, hgG, by simpa using hg0, hgc⟩

/-- If `0` is a remainder of a nonzero `f` on division by `B`, then the leading monomial of `f` is
divisible by the leading monomial of a nonzero element of `B`. -/
theorem exists_degree_le_degree_of_isRemainder_zero (h : m.IsRemainder f B 0) (hf : f ≠ 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree f :=
  exists_degree_le_of_mem_span_leadingTerm (leadingTerm_mem_span_leadingTerm_of_isRemainder_zero h)
    (by rw [m.support_leadingTerm' hf]; exact Finset.mem_singleton_self _)

/-- The coefficient of `X^D` in an element of the ideal spanned by the leading terms of `G` lies in
the ideal of `R` spanned by the leading coefficients of those `g ∈ G` with `deg g ≤ D`. -/
theorem coeff_mem_span_leadingCoeff {p : MvPolynomial σ R}
    (hp : p ∈ Ideal.span (m.leadingTerm '' G)) (D : σ →₀ ℕ) :
    p.coeff D ∈ Ideal.span (m.leadingCoeff '' {g ∈ G | m.degree g ≤ D}) := by
  classical
  induction hp using Submodule.span_induction generalizing D with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [leadingTerm, coeff_monomial]
    split_ifs with h
    · exact Ideal.subset_span ⟨g, ⟨hg, h.le⟩, rfl⟩
    · exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem (hx D) (hy D)
  | smul a x _ hx =>
    -- Each term `a_e * x_{e'}` of the `D` coefficient of `a * x` has `e' ≤ D`.
    rw [smul_eq_mul, coeff_mul]
    refine sum_mem fun e he ↦ Ideal.mul_mem_left _ _ <|
      Ideal.span_mono (Set.image_mono ?_) (hx e.2)
    rw [Finset.mem_antidiagonal] at he
    exact fun g hg ↦ ⟨hg.1, hg.2.trans (he ▸ le_add_self)⟩

/-- A Gröbner basis of `I` is contained in `I`. -/
theorem IsGroebnerBasis.subset (h : m.IsGroebnerBasis G I) : G ⊆ I :=
  h.1

/-- The leading terms of a Gröbner basis of `I` span the ideal of leading terms of `I`. -/
theorem IsGroebnerBasis.span_leadingTerm_image (h : m.IsGroebnerBasis G I) :
    Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G) :=
  h.2

/-- An ideal is a Gröbner basis of itself. -/
theorem isGroebnerBasis_self (I : Ideal (MvPolynomial σ R)) : m.IsGroebnerBasis (I : Set _) I :=
  .mk subset_rfl rfl

/-- Adjoining further elements of `I` to a Gröbner basis of `I` gives a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.mono (h : m.IsGroebnerBasis G I) (hGG' : G ⊆ G') (hG'I : G' ⊆ I) :
    m.IsGroebnerBasis G' I :=
  .mk hG'I <| le_antisymm
    (h.span_leadingTerm_image.le.trans (Ideal.span_mono (Set.image_mono hGG')))
    (Ideal.span_mono (Set.image_mono hG'I))

/-- Removing `0` does not change whether a set is a Gröbner basis. -/
@[simp]
theorem isGroebnerBasis_sdiff_singleton_zero :
    m.IsGroebnerBasis (G \ {0}) I ↔ m.IsGroebnerBasis G I := by
  simp only [isGroebnerBasis_iff, m.span_leadingTerm_sdiff_singleton_zero,
    Set.sdiff_singleton_subset_iff, Set.insert_eq_of_mem (show (0 : MvPolynomial σ R) ∈ (I : Set _)
      from I.zero_mem)]

/-- The leading monomial of every nonzero element of `I` is divisible by the leading monomial of a
nonzero element of a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.exists_degree_le_degree (h : m.IsGroebnerBasis G I)
    {p : MvPolynomial σ R} (hp : p ∈ I) (hp0 : p ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree p := by
  refine exists_degree_le_of_mem_span_leadingTerm
    (h.span_leadingTerm_image ▸ Ideal.subset_span ⟨p, hp, rfl⟩ : m.leadingTerm p ∈ _) ?_
  rw [m.support_leadingTerm' hp0]
  exact Finset.mem_singleton_self _

/-- No monomial of a remainder on division by a Gröbner basis of `I` is divisible by the leading
monomial of a nonzero element of `I`. -/
theorem IsGroebnerBasis.not_degree_le_of_isRemainder (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder f G r) {c : σ →₀ ℕ} (hc : c ∈ r.support) {p : MvPolynomial σ R}
    (hp : p ∈ I) (hp0 : p ≠ 0) : ¬ m.degree p ≤ c := fun hle ↦
  let ⟨_, hg, hg0, hgp⟩ := h.exists_degree_le_degree hp hp0
  hr.not_degree_le hc hg hg0 (hgp.trans hle)

/-- A subset `G` of `I` whose nonzero members have unit leading coefficients is a Gröbner basis of
`I` if and only if the leading monomial of every nonzero element of `I` is divisible by the
leading monomial of a nonzero element of `G`. -/
theorem isGroebnerBasis_iff_forall_exists_degree_le_degree
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔
      G ⊆ I ∧ ∀ p ∈ I, p ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree p := by
  refine ⟨fun h ↦ ⟨h.subset, fun p hp hp0 ↦ h.exists_degree_le_degree hp hp0⟩,
    fun ⟨hGI, hdeg⟩ ↦ .mk hGI (le_antisymm ?_ (Ideal.span_mono (Set.image_mono hGI)))⟩
  rw [Ideal.span_le, Set.image_subset_iff]
  intro p hp
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  obtain ⟨g, hgG, hg0, hgp⟩ := hdeg p hp hp0
  -- `lt p = (lc p / lc g) X^(deg p - deg g) * lt g`.
  have hu := hG g hgG hg0
  have hlt : m.leadingTerm p = monomial (m.degree p - m.degree g)
      (m.leadingCoeff p * ↑hu.unit⁻¹) * m.leadingTerm g := by
    simp [leadingTerm, monomial_mul_monomial, tsub_add_cancel_of_le hgp, mul_assoc]
  rw [Set.mem_preimage, SetLike.mem_coe, hlt]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, hgG, rfl⟩)

/-- If the nonzero members of `G` have unit leading coefficients, then so do the nonzero leading
terms of members of `G`. -/
theorem isUnit_leadingCoeff_of_mem_image_leadingTerm
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    ∀ p ∈ m.leadingTerm '' G, p ≠ 0 → IsUnit (m.leadingCoeff p) := by
  rintro _ ⟨g, hg, rfl⟩ hg0
  rw [leadingCoeff_leadingTerm]
  exact hG g hg (by rintro rfl; simp at hg0)

/-- The leading terms of a Gröbner basis `G` of `I` whose nonzero members have unit leading
coefficients form a Gröbner basis of the ideal of leading terms of `I`. -/
theorem IsGroebnerBasis.image_leadingTerm (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (m.leadingTerm '' G) (Ideal.span (m.leadingTerm '' I)) := by
  refine (isGroebnerBasis_iff_forall_exists_degree_le_degree
    (isUnit_leadingCoeff_of_mem_image_leadingTerm hG)).2 ⟨?_, fun p hp hp0 ↦ ?_⟩
  · rw [h.span_leadingTerm_image]
    exact Ideal.subset_span
  · rw [h.span_leadingTerm_image] at hp
    obtain ⟨g, hg, hg0, hgp⟩ :=
      exists_degree_le_of_mem_span_leadingTerm hp (m.degree_mem_support hp0)
    exact ⟨m.leadingTerm g, ⟨g, hg, rfl⟩, (m.leadingTerm_eq_zero_iff g).not.2 hg0,
      (m.degree_leadingTerm g).symm ▸ hgp⟩

end CommSemiring

section CommRing

variable [CommRing R] {m} {f f₁ f₂ r r₁ r₂ : MvPolynomial σ R} {B G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- A polynomial differs from its remainders by an element of the ideal spanned by the divisors. -/
theorem IsRemainder.sub_mem_span (h : m.IsRemainder f B r) : f - r ∈ Ideal.span B := by
  obtain ⟨g, hf, -⟩ := h.exists_linearCombination
  rw [hf, add_sub_cancel_right, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun b _ ↦ Submodule.smul_mem _ _ (Ideal.subset_span b.2)

/-- **Existence of remainders.** If every nonzero element of `B` has a unit leading coefficient,
then every polynomial has a remainder on division by `B`. -/
theorem exists_isRemainder (hB : ∀ b ∈ B, b ≠ 0 → IsUnit (m.leadingCoeff b))
    (f : MvPolynomial σ R) : ∃ r, m.IsRemainder f B r := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, isRemainder_zero_left_iff.2 rfl⟩
  -- Divide by the nonzero elements of `B`, then extend the quotients by `0` to all of `B`.
  obtain ⟨g, r, hfgr, hdeg, hr⟩ := m.div_set (B := B \ {0}) (fun b hb ↦ hB b hb.1 hb.2) f
  refine ⟨r, ⟨g.mapDomain (Set.inclusion Set.sdiff_subset), ?_, fun b ↦ ?_⟩,
    fun c hc b hb hb0 ↦ hr c hc b ⟨hb, hb0⟩⟩
  · rwa [Finsupp.linearCombination_mapDomain]
  by_cases hb0 : (b : MvPolynomial σ R) = 0
  · simp [hb0]
  have hgb : g.mapDomain (Set.inclusion Set.sdiff_subset) b = g ⟨b, b.2, hb0⟩ :=
    Finsupp.mapDomain_apply_of_injective (Set.inclusion_injective _) g ⟨b, b.2, hb0⟩
  rw [hgb, ← map_add, ← withBotDegree_mul_of_left_mem_nonZeroDivisors
    (hB b b.2 hb0).mem_nonZeroDivisors, withBotDegree_le_withBotDegree_iff]
  exact ⟨hdeg ⟨b, b.2, hb0⟩, fun h ↦ absurd h hf⟩

/-- **Remainders modulo a Gröbner basis.** If `r₁` and `r₂` are remainders of `f₁` and `f₂` on
division by a Gröbner basis of `I`, then `f₁ - f₂ ∈ I` if and only if `r₁ = r₂`. -/
theorem IsGroebnerBasis.sub_mem_iff (h : m.IsGroebnerBasis G I) (h₁ : m.IsRemainder f₁ G r₁)
    (h₂ : m.IsRemainder f₂ G r₂) : f₁ - f₂ ∈ I ↔ r₁ = r₂ := by
  classical
  have hdiff : f₁ - f₂ - (r₁ - r₂) ∈ I := by
    have := Ideal.span_le.2 h.subset (Ideal.sub_mem _ h₁.sub_mem_span h₂.sub_mem_span)
    rwa [sub_sub_sub_comm] at this
  rw [← sub_add_cancel (f₁ - f₂) (r₁ - r₂), I.add_mem_iff_right hdiff]
  refine ⟨fun hr ↦ by_contra fun hne ↦ ?_, fun hr ↦ by simp [hr]⟩
  -- The leading monomial of the nonzero `r₁ - r₂ ∈ I` would be a reducible monomial of `r₁`
  -- or `r₂`.
  have hne' : r₁ - r₂ ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨g, hgG, hg0, hgd⟩ := h.exists_degree_le_degree hr hne'
  rcases Finset.mem_union.1 (support_sub σ r₁ r₂ (m.degree_mem_support hne')) with hc | hc
  · exact h₁.not_degree_le hc hgG hg0 hgd
  · exact h₂.not_degree_le hc hgG hg0 hgd

/-- **Uniqueness of remainders.** Remainders on division by a Gröbner basis are unique. -/
theorem IsGroebnerBasis.eq_of_isRemainder (h : m.IsGroebnerBasis G I) (h₁ : m.IsRemainder f G r₁)
    (h₂ : m.IsRemainder f G r₂) : r₁ = r₂ :=
  (h.sub_mem_iff h₁ h₂).1 (by simp)

/-- **Ideal membership.** A remainder on division by a Gröbner basis of `I` vanishes if and only
if the divided polynomial lies in `I`. -/
theorem IsGroebnerBasis.remainder_eq_zero_iff_mem (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder f G r) : r = 0 ↔ f ∈ I := by
  simpa using (h.sub_mem_iff hr (isRemainder_zero_left_iff.2 rfl)).symm

/-- If `r` is a remainder of `X^a` on division by a Gröbner basis of `I`, and `a` is the leading
exponent of a nonzero element of `I`, then `X^a - r` is a nonzero monic element of `I` with
leading exponent `a`. -/
theorem IsGroebnerBasis.monic_monomial_sub_of_isRemainder (h : m.IsGroebnerBasis G I)
    {a : σ →₀ ℕ} (hr : m.IsRemainder (monomial a 1) G r)
    {p : MvPolynomial σ R} (hp : p ∈ I) (hp0 : p ≠ 0) (hpa : m.degree p = a) :
    monomial a 1 - r ∈ I ∧ monomial a 1 - r ≠ 0 ∧ m.degree (monomial a 1 - r) = a ∧
      m.Monic (monomial a 1 - r) := by
  classical
  have hmem : monomial a 1 - r ∈ I := Ideal.span_le.2 h.subset hr.sub_mem_span
  have hcoeff : (monomial a 1 - r).coeff a = 1 := by
    have : a ∉ r.support := fun hc ↦ h.not_degree_le_of_isRemainder hr hc hp hp0 hpa.le
    simp [notMem_support_iff.1 this]
  have hne : monomial a 1 - r ≠ 0 := by
    have : Nontrivial R := nontrivial_of_ne _ _ (m.leadingCoeff_ne_zero_iff.2 hp0)
    exact fun h0 ↦ by simp [h0] at hcoeff
  -- The leading monomial is not a monomial of `r`, so it is `a`.
  have hdeg : m.degree (monomial a 1 - r) = a := by
    rcases Finset.mem_union.1 (support_sub σ _ _ (m.degree_mem_support hne)) with hc | hc
    · exact Finset.mem_singleton.1 (support_monomial_subset hc)
    · exact absurd le_rfl (h.not_degree_le_of_isRemainder hr hc hmem hne)
  exact ⟨hmem, hne, hdeg, by rw [Monic, leadingCoeff, hdeg, hcoeff]⟩

variable (m) in
/-- The polynomials `∑ g_b * b` over `b ∈ B` with `deg b + deg g_b ≤ d` for every `b`: the
`R`-span of the monomial multiples of elements of `B` of degree at most `d`. -/
private def boundedSpan (B : Set (MvPolynomial σ R)) (d : WithBot m.syn) :
    Submodule R (MvPolynomial σ R) where
  carrier := {p | ∃ g : B →₀ MvPolynomial σ R,
    p = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g ∧
    ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
      m.toWithBotSyn (m.withBotDegree (g b)) ≤ d}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro _ _ ⟨g, rfl, hg⟩ ⟨g', rfl, hg'⟩
    refine ⟨g + g', by rw [map_add], fun b ↦ ?_⟩
    refine (add_le_add_right (m.withBotDegree_add_le _ _) _).trans ?_
    rw [← max_add_add_left]
    exact max_le (hg b) (hg' b)
  smul_mem' := by
    rintro r _ ⟨g, rfl, hg⟩
    refine ⟨r • g, by rw [LinearMap.map_smul_of_tower], fun b ↦ le_trans ?_ (hg b)⟩
    exact add_le_add_right (m.withBotDegree_le_withBotDegree_of_support_subset support_smul) _

/-- `boundedSpan m B d` is monotone in the bound `d`. -/
private theorem boundedSpan_mono {d d' : WithBot m.syn} (hdd' : d ≤ d') :
    boundedSpan m B d ≤ boundedSpan m B d' := by
  rintro _ ⟨g, rfl, hg⟩
  exact ⟨g, rfl, fun b ↦ (hg b).trans hdd'⟩

/-- An element of `boundedSpan m B d` lies in the ideal spanned by `B`. -/
private theorem mem_span_of_mem_boundedSpan {d : WithBot m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ boundedSpan m B d) : p ∈ Ideal.span B := by
  obtain ⟨g, rfl, -⟩ := hp
  exact (Finsupp.mem_span_iff_linearCombination _ _ _).2 ⟨g, rfl⟩

/-- An element of `boundedSpan m B d` has degree at most `d`. -/
private theorem withBotDegree_le_of_mem_boundedSpan {d : WithBot m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ boundedSpan m B d) : m.toWithBotSyn (m.withBotDegree p) ≤ d := by
  obtain ⟨g, rfl, hg⟩ := hp
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine m.withBotDegree_sum_le.trans (Finset.sup_le fun b _ ↦ ?_)
  exact (m.toWithBotSyn_withBotDegree_mul_le _ _).trans ((add_comm _ _).trans_le (hg b))

/-- An element of the ideal of `R` spanned by the leading coefficients of those `g ∈ G` with
`deg g ≤ D` is the coefficient of `X^D` in an element of `boundedSpan m G D`. -/
private theorem span_leadingCoeff_le_map_boundedSpan (D : σ →₀ ℕ) :
    Ideal.span (m.leadingCoeff '' {g ∈ G | m.degree g ≤ D}) ≤
      (boundedSpan m G (m.toSyn D)).map (lcoeff R D) := by
  classical
  rw [Ideal.span_le]
  rintro _ ⟨g, ⟨hgG, hgD⟩, rfl⟩
  -- `lc g` is the `D` coefficient of `X^(D - deg g) * g`.
  refine ⟨monomial (D - m.degree g) 1 * g,
    ⟨Finsupp.single ⟨g, hgG⟩ (monomial (D - m.degree g) 1), by simp, fun b ↦ ?_⟩, ?_⟩
  · rw [Finsupp.single_apply]
    split_ifs with h
    · subst h
      refine (add_le_add (m.toWithBotSyn_withBotDegree_le_toSyn_degree _)
        ((m.toWithBotSyn_withBotDegree_le_toSyn_degree _).trans
          (WithBot.coe_le_coe.2 (m.degree_monomial_le _)))).trans_eq ?_
      rw [← WithBot.coe_add, ← map_add, add_tsub_cancel_of_le hgD]
    · simp
  · simp [coeff_monomial_mul', tsub_tsub_cancel_of_le hgD, leadingCoeff]

/-- **Standard representations** (Adams–Loustaunau, Theorem 4.1.12): every element `f` of `I` is
`∑ g_b * b` over a Gröbner basis `G` of `I` with `deg b + deg g_b ≤ deg f` for every `b`.
No condition on leading coefficients is needed. -/
private theorem IsGroebnerBasis.mem_boundedSpan (h : m.IsGroebnerBasis G I) (hf : f ∈ I) :
    f ∈ boundedSpan m G (m.toWithBotSyn (m.withBotDegree f)) := by
  classical
  -- Induct on the degree of `f` in the well-founded synonym order.
  induction hd : m.toWithBotSyn (m.withBotDegree f) using WellFoundedLT.induction
    generalizing f with
  | ind d ih =>
  subst hd
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  have hW : m.toWithBotSyn (m.withBotDegree f) = m.toSyn (m.degree f) := by
    rw [(m.withBotDegree_eq_coe_degree_iff f).2 hf0, toWithBotSyn_apply_coe]
  -- Some `q ∈ boundedSpan m G (deg f)` has the same leading coefficient as `f`, and then
  -- `f - q ∈ I` has smaller degree than `f`.
  have hlt : m.leadingTerm f ∈ Ideal.span (m.leadingTerm '' G) :=
    h.span_leadingTerm_image ▸ Ideal.subset_span ⟨f, hf, rfl⟩
  have hc := coeff_mem_span_leadingCoeff hlt (m.degree f)
  rw [leadingTerm, coeff_monomial, ite_eq_left rfl] at hc
  obtain ⟨q, hq, hqf⟩ := span_leadingCoeff_le_map_boundedSpan (m.degree f) hc
  rw [← hW] at hq
  have hdeg := m.withBotDegree_sub_lt hf0 (withBotDegree_le_of_mem_boundedSpan hq) hqf
  have hqI : q ∈ I := Ideal.span_le.2 h.subset (mem_span_of_mem_boundedSpan hq)
  have := add_mem (boundedSpan_mono hdeg.le (ih _ hdeg (sub_mem hf hqI) rfl)) hq
  rwa [sub_add_cancel] at this

/-- For a Gröbner basis `G` of `I`, `0` is a remainder of `f` on division by `G` exactly when
`f ∈ I`. No condition on the leading coefficients of `G` is needed. -/
theorem IsGroebnerBasis.isRemainder_zero_iff_mem (h : m.IsGroebnerBasis G I) :
    m.IsRemainder f G 0 ↔ f ∈ I := by
  refine ⟨fun hr ↦ (h.remainder_eq_zero_iff_mem hr).1 rfl, fun hf ↦ ?_⟩
  obtain ⟨g, hg, hdeg⟩ := h.mem_boundedSpan hf
  exact ⟨⟨g, by rwa [add_zero], hdeg⟩, by simp⟩

/-- A Gröbner basis of `I` generates `I`. -/
theorem IsGroebnerBasis.ideal_eq_span (h : m.IsGroebnerBasis G I) : I = Ideal.span G := by
  refine le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.2 h.subset)
  simpa using (h.isRemainder_zero_iff_mem.2 hf).sub_mem_span

/-- Remainders on division by a Gröbner basis whose nonzero members have unit leading
coefficients exist and are unique. -/
theorem IsGroebnerBasis.existsUnique_isRemainder (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (f : MvPolynomial σ R) :
    ∃! r, m.IsRemainder f G r :=
  (exists_isRemainder hG f).elim fun r hr ↦ ⟨r, hr, fun _ hr' ↦ h.eq_of_isRemainder hr' hr⟩

/-- A subset `G` of `I` is a Gröbner basis of `I` if and only if every element of `I` has remainder
`0` on division by `G`. -/
theorem isGroebnerBasis_iff_isRemainder_zero :
    m.IsGroebnerBasis G I ↔ G ⊆ I ∧ ∀ f ∈ I, m.IsRemainder f G 0 := by
  refine ⟨fun h ↦ ⟨h.subset, fun f ↦ h.isRemainder_zero_iff_mem.2⟩, fun ⟨hGI, h0⟩ ↦ .mk hGI ?_⟩
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (Set.image_mono hGI))
  rintro _ ⟨f, hf, rfl⟩
  exact leadingTerm_mem_span_leadingTerm_of_isRemainder_zero (h0 f hf)

end CommRing

end MonomialOrder
end
end TAF_LiteralSource_0246

section TAF_LiteralSource_0247
/- Original module: PaperVerification.AlternatingFormsHibiGroebner -/


/-!
# The actual quadratic Gröbner basis of the Hibi ideal

The order refines the positive rank-square weight. Its division remainder
has only chain-support monomials. Their actual diagonal images are linearly
independent, so a remainder of an element of the Hibi ideal is zero. This
proves the full Gröbner property, not only termination of the displayed
quadratic substitutions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators MonomialOrder

variable {K : Type*} [Field K] {s n : ℕ} (α β : Fin s → Fin n)

def quadraticSet : Set (MvPolynomial (IntervalIndex α β) K) :=
  {p | ∃ I J,incomparable α β I J ∧ p=relation α β I J}

def pairExponent (I J : IntervalIndex α β) : IntervalIndex α β →₀ ℕ :=
  Finsupp.single I 1+Finsupp.single J 1

theorem pair_monomial (I J : IntervalIndex α β) :
    (X I*X J : MvPolynomial (IntervalIndex α β) K)=monomial (pairExponent α β I J) 1 := by
  simp only [X,monomial_mul,one_mul,pairExponent]

def sortingOrder (m : MonomialOrder (IntervalIndex α β)) :
    MonomialOrder (IntervalIndex α β) :=
  WeightedMonomialOrder.weightedRefinement m (sortingWeight α β)

theorem pair_sorting_lt (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (h : incomparable α β I J) :
    pairExponent α β (meet α β I J) (join α β I J) ≺[sortingOrder α β m]
      pairExponent α β I J := by
  apply WeightedMonomialOrder.lt_of_weight_lt
  simpa only [pairExponent,map_add,Finsupp.weight_single,one_smul] using
    sortingWeight_decreases α β I J h

theorem relation_degree (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (h : incomparable α β I J) :
    (sortingOrder α β m).degree (relation (K := K) α β I J)=pairExponent α β I J := by
  classical
  have hlt : (sortingOrder α β m).degree
      (monomial (pairExponent α β (meet α β I J) (join α β I J)) (1 : K))
        ≺[sortingOrder α β m]
      (sortingOrder α β m).degree (monomial (pairExponent α β I J) (1 : K)) := by
    simpa only [MonomialOrder.degree_monomial,ite_eq_right one_ne_zero] using
      pair_sorting_lt α β m I J h
  rw [relation,pair_monomial,pair_monomial,
    (sortingOrder α β m).degree_sub_of_lt hlt,MonomialOrder.degree_monomial,
    ite_eq_right one_ne_zero]

theorem relation_leadingCoeff (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (h : incomparable α β I J) :
    (sortingOrder α β m).leadingCoeff (relation (K := K) α β I J)=1 := by
  classical
  have hlt : (sortingOrder α β m).degree
      (monomial (pairExponent α β (meet α β I J) (join α β I J)) (1 : K))
        ≺[sortingOrder α β m]
      (sortingOrder α β m).degree (monomial (pairExponent α β I J) (1 : K)) := by
    simpa only [MonomialOrder.degree_monomial,ite_eq_right one_ne_zero] using
      pair_sorting_lt α β m I J h
  rw [relation,pair_monomial,pair_monomial,
    (sortingOrder α β m).leadingCoeff_sub_of_lt hlt,MonomialOrder.leadingCoeff_monomial]

theorem relation_ne_zero (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (h : incomparable α β I J) : relation (K := K) α β I J≠0 := by
  intro hz
  have he := relation_leadingCoeff (K := K) α β m I J h
  rw [hz,MonomialOrder.leadingCoeff_zero] at he
  exact zero_ne_one he

theorem pairExponent_le_of_support (a : IntervalIndex α β →₀ ℕ)
    (I J : IntervalIndex α β) (hI : I∈a.support) (hJ : J∈a.support) (hne : I≠J) :
    pairExponent α β I J≤a := by
  classical
  intro T
  by_cases hTI : T=I
  · subst T
    simpa only [pairExponent,Finsupp.add_apply,Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hne,add_zero] using
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hI)
  · by_cases hTJ : T=J
    · subst T
      simpa only [pairExponent,Finsupp.add_apply,Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hne.symm,zero_add] using
          Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hJ)
    · simp only [pairExponent,Finsupp.add_apply,Finsupp.single_eq_of_ne hTI,
        Finsupp.single_eq_of_ne hTJ,add_zero,Nat.zero_le]

theorem remainder_normal_support (m : MonomialOrder (IntervalIndex α β))
    (f r : MvPolynomial (IntervalIndex α β) K)
    (hr : (sortingOrder α β m).IsRemainder f (quadraticSet α β) r) :
    ∀ a∈r.support,NormalMonomial α β a := by
  intro a ha I hI J hJ
  by_contra h
  have hinc : incomparable α β I J := not_or.mp h
  have hne : I≠J := fun he => hinc.1 (he ▸ le_rfl)
  have hnot := hr.not_degree_le ha (show relation (K := K) α β I J∈quadraticSet α β from
    ⟨I,J,hinc,rfl⟩) (relation_ne_zero α β m I J hinc)
  rw [relation_degree α β m I J hinc] at hnot
  exact hnot (pairExponent_le_of_support α β a I J hI hJ hne)

/-- The displayed literal binomials are a genuine quadratic Gröbner basis
of their full ideal for the explicitly constructed sorting order. -/
theorem quadratic_isGroebnerBasis (m : MonomialOrder (IntervalIndex α β)) (hs : 0<s) :
    (sortingOrder α β m).IsGroebnerBasis (quadraticSet (K := K) α β) (relationIdeal α β) := by
  apply MonomialOrder.isGroebnerBasis_iff_isRemainder_zero.mpr
  refine ⟨fun p hp => Ideal.subset_span hp,?_⟩
  intro p hp
  obtain ⟨r,hr⟩ := (sortingOrder α β m).exists_isRemainder (B := quadraticSet (K := K) α β)
    (fun b hb hb0 => by
      obtain ⟨I,J,h,rfl⟩ := hb
      rw [relation_leadingCoeff α β m I J h]
      exact isUnit_one) p
  have hrI : r∈relationIdeal (K := K) α β := by
    have hsub : p-r∈relationIdeal α β := hr.sub_mem_span
    simpa only [sub_sub_cancel] using (relationIdeal (K := K) α β).sub_mem hp hsub
  have hr0 : r=0 := normal_polynomial_eq_zero α β hs r
    (remainder_normal_support α β m p r hr)
    (by rw [relationIdeal_eq_kernel α β hs] at hrI; exact hrI)
  simpa only [hr0] using hr

theorem quadratic_leadingIdeal (m : MonomialOrder (IntervalIndex α β)) (hs : 0<s) :
    Ideal.span ((sortingOrder α β m).leadingTerm ''
      (relationIdeal (K := K) α β : Set (MvPolynomial (IntervalIndex α β) K)))=
        incomparableIdeal α β := by
  rw [(quadratic_isGroebnerBasis (K := K) α β m hs).span_leadingTerm_image]
  congr 1
  ext p
  constructor
  · rintro ⟨q,⟨I,J,h,rfl⟩,rfl⟩
    refine ⟨I,J,h,?_⟩
    rw [MonomialOrder.leadingTerm,relation_degree α β m I J h,
      relation_leadingCoeff α β m I J h,pair_monomial]
  · rintro ⟨I,J,h,rfl⟩
    refine ⟨relation α β I J,⟨I,J,h,rfl⟩,?_⟩
    rw [MonomialOrder.leadingTerm,relation_degree α β m I J h,
      relation_leadingCoeff α β m I J h,pair_monomial]

end PaperVerification.AlternatingForms.Hibi
end
end
end TAF_LiteralSource_0247

section TAF_LiteralSource_0248
/- Original module: PaperVerification.AlternatingFormsOddGoodCoordinates -/




@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators
open Hibi

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "B" => oddPluckerStandardBasis (K := K) k t hs
local notation "P" => MvPolynomial (IntervalIndex α β) K

@[expose]
def oddGoodMap : P →ₐ[K]
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) :=
  (Ideal.Quotient.mkₐ K Q).comp (rename Subtype.val)

@[expose]
def oddGoodIdeal : Ideal P := RingHom.ker (oddGoodMap (K := K) k t hs).toRingHom

@[simp] theorem oddGoodMap_X (I : IntervalIndex α β) :
    oddGoodMap (K := K) k t hs (X I)=Ideal.Quotient.mk Q (X I.val) := by
  change Ideal.Quotient.mkₐ K Q (rename Subtype.val (X I)) = _
  exact congrArg (Ideal.Quotient.mkₐ K Q) (MvPolynomial.rename_X Subtype.val I)

theorem oddGoodMap_standardPolynomial (C : OddStandardIndex k t hs) :
    oddGoodMap (K := K) k t hs (standardPolynomial α β C.2)=B C := by
  rw [oddPluckerStandardBasis_apply]
  simp only [standardPolynomial,map_prod,oddStandardRepresentative,chainPluckerProduct]
  apply Finset.prod_congr rfl
  intro j hj
  exact oddGoodMap_X (K := K) k t hs (intervalIndexOfChain α β C.2 j)

def oddGoodRepresentative
    (q : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) : P :=
  ((B).repr q).sum (fun C c => c • standardPolynomial α β C.2)

theorem oddGoodMap_representative
    (q : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) :
    oddGoodMap k t hs (oddGoodRepresentative k t hs q)=q := by
  simp only [oddGoodRepresentative,Finsupp.sum,map_sum,map_smul,
    oddGoodMap_standardPolynomial]
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using (B).linearCombination_repr q

theorem oddGoodMap_surjective : Function.Surjective (oddGoodMap (K := K) k t hs) :=
  fun q => ⟨oddGoodRepresentative k t hs q,oddGoodMap_representative k t hs q⟩

def oddGoodQuotientEquiv : (P⧸oddGoodIdeal k t hs) ≃ₐ[K]
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) :=
  Ideal.quotientKerAlgEquivOfSurjective (oddGoodMap_surjective k t hs)

def oddGoodNormalForm (p : P) : P :=
  oddGoodRepresentative k t hs (oddGoodMap k t hs p)

@[simp] theorem oddGoodMap_normalForm (p : P) :
    oddGoodMap k t hs (oddGoodNormalForm k t hs p)=oddGoodMap k t hs p :=
  oddGoodMap_representative k t hs _

theorem oddGoodNormalForm_pair (I J : IntervalIndex α β) :
    oddGoodNormalForm (K := K) k t hs (X I*X J)=
      (oddCoefficients (K := K) k t hs (X I.val*X J.val)).sum
        (fun C c => c • standardPolynomial α β C.2) := by
  simp only [oddGoodNormalForm,oddGoodRepresentative,oddCoefficients,map_mul,oddGoodMap_X]
  all_goals rfl


def oddQuadraticRelation (I J : IntervalIndex α β) : P :=
  X I*X J-oddGoodNormalForm k t hs (X I*X J)

def oddQuadraticSet : Set P :=
  {p | ∃ I J,incomparable α β I J ∧ p=oddQuadraticRelation k t hs I J}

theorem oddQuadraticRelation_mem (I J : IntervalIndex α β) :
    oddQuadraticRelation (K := K) k t hs I J∈oddGoodIdeal k t hs := by
  change oddGoodMap k t hs (X I*X J-oddGoodNormalForm k t hs (X I*X J))=0
  rw [map_sub,oddGoodMap_normalForm,sub_self]

theorem standardPolynomial_isHomogeneous (C : OddStandardIndex k t hs) :
    (standardPolynomial (K := K) α β C.2).IsHomogeneous C.1 := by
  simpa only [standardPolynomial,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_id] using
    IsHomogeneous.prod Finset.univ
      (fun j => (X (intervalIndexOfChain α β C.2 j) : P)) (fun _ => 1)
      (fun j hj => isHomogeneous_X K _)

theorem oddQuadraticRelation_homogeneous (I J : IntervalIndex α β) :
    (oddQuadraticRelation (K := K) k t hs I J).IsHomogeneous 2 := by
  apply ((isHomogeneous_X K I).mul (isHomogeneous_X K J)).sub
  rw [oddGoodNormalForm_pair]
  apply IsHomogeneous.sum
  intro C hC
  have hd := odd_pair_coefficients_degree k t hs I J C (Finsupp.mem_support_iff.mp hC)
  intro a ha
  refine (standardPolynomial_isHomogeneous (K := K) k t hs C ?_).trans hd
  intro hz
  apply ha
  simp only [coeff_smul,hz,smul_zero]

def goodChainExponent (C : OddStandardIndex k t hs) : IntervalIndex α β →₀ ℕ :=
  ∑ j,Finsupp.single (intervalIndexOfChain α β C.2 j) 1

theorem standardPolynomial_eq_monomial (C : OddStandardIndex k t hs) :
    standardPolynomial (K := K) α β C.2=monomial (goodChainExponent k t hs C) 1 := by
  simp only [standardPolynomial,X,prod_monomial_eq_monomial_sum,
    Finset.prod_const_one,goodChainExponent]

theorem goodChainExponent_weight (u : IntervalIndex α β → ℕ)
    (C : OddStandardIndex k t hs) :
    Finsupp.weight u (goodChainExponent k t hs C)=
      ∑ j,u (intervalIndexOfChain α β C.2 j) := by
  simp only [goodChainExponent,map_sum,Finsupp.weight_single,one_smul]

theorem goodChainExponent_vertexWeight (C : OddStandardIndex k t hs) :
    Finsupp.weight (oddGoodWeight k t hs) (goodChainExponent k t hs C)=
      oddStandardWeight k t hs C := by
  rw [goodChainExponent_weight]
  rfl

theorem goodChainExponent_diagonalWeight (C : OddStandardIndex k t hs) :
    Finsupp.weight (diagonalWeight α β) (goodChainExponent k t hs C)=
      standardDiagonalWeight α β C := goodChainExponent_weight k t hs _ C

theorem normalChain_injective_on_normal :
    Function.Injective (fun a : {a : IntervalIndex α β →₀ ℕ // NormalMonomial α β a} =>
      normalChain α β a.val) := by
  intro a b h
  apply Subtype.ext
  apply MvPolynomial.monomial_left_injective (one_ne_zero : (1 : ℚ)≠0)
  change (monomial a.val 1 : MvPolynomial (IntervalIndex α β) ℚ) = monomial b.val 1
  rw [←normalChain_polynomial α β a.val a.property,
    ←normalChain_polynomial α β b.val b.property]
  exact congrArg (fun C : Σ r, BandChain α β r =>
    standardPolynomial (K := ℚ) α β C.2) h


theorem oddGood_normal_polynomial_eq_zero (p : P)
    (hp : ∀ a∈p.support,NormalMonomial α β a) (hz : oddGoodMap k t hs p=0) : p=0 := by
  classical
  have hli : LinearIndependent K (fun a : p.support =>
      oddGoodMap k t hs (monomial a.val 1 : P)) := by
    have h := (B).linearIndependent.comp
      (fun a : p.support => normalChain α β a.val) (by
        intro a b hab
        have hne := normalChain_injective_on_normal k t hs
          (show normalChain α β (⟨a.val,hp a.val a.property⟩ :
            {a : IntervalIndex α β →₀ ℕ // NormalMonomial α β a}).val=
            normalChain α β (⟨b.val,hp b.val b.property⟩ :
            {a : IntervalIndex α β →₀ ℕ // NormalMonomial α β a}).val from hab)
        exact Subtype.ext (congrArg
          (fun z : {a : IntervalIndex α β →₀ ℕ // NormalMonomial α β a} => z.val) hne))
    convert h using 1
    funext a
    rw [←normalChain_polynomial α β a.val (hp a.val a.property)]
    exact oddGoodMap_standardPolynomial (K := K) k t hs (normalChain α β a.val)
  have hsum : (∑ a : p.support,p.coeff a.val •
      oddGoodMap k t hs (monomial a.val 1 : P))=0 := by
    rw [Finset.sum_coe_sort p.support (fun a => p.coeff a •
      oddGoodMap k t hs (monomial a 1 : P))]
    have he : oddGoodMap k t hs p = ∑ a ∈ p.support,
        p.coeff a • oddGoodMap k t hs (monomial a 1 : P) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [show monomial a (p.coeff a) = p.coeff a • (monomial a 1 : P) from by
        simp only [smul_monomial,smul_eq_mul,mul_one],map_smul]
    exact he.symm.trans hz
  have hc := Fintype.linearIndependent_iff.mp hli (fun a => p.coeff a.val) hsum
  ext a
  change p.coeff a = 0
  by_cases ha : a∈p.support
  · exact hc ⟨a,ha⟩
  · exact notMem_support_iff.mp ha

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0248

section TAF_LiteralSource_0249
/- Original module: PaperVerification.AlternatingFormsOddGroebner -/


/-!
# A genuine quadratic Gröbner basis in the original good coordinates

The explicit order compares the odd-pencil vertex weight, then the band
diagonal weight, then the positive Hibi sorting weight. Actual quotient
normal-form coefficients satisfy these comparisons. Division therefore
leaves only chain monomials, whose independence in the original quotient
proves the full Gröbner property of the literal kernel.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators MonomialOrder
open Hibi WeightedMonomialOrder

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "P" => MvPolynomial (IntervalIndex α β) K

/-- The three weights are compared in the same order as the two actual
degenerations followed by meet/join sorting. -/
def oddGoodOrder (m : MonomialOrder (IntervalIndex α β)) :
    MonomialOrder (IntervalIndex α β) :=
  weightedRefinement
    (weightedRefinement (sortingOrder α β m) (diagonalWeight α β))
    (oddGoodWeight k t hs)

theorem goodChainExponent_pairChain (I J : IntervalIndex α β) :
    goodChainExponent k t hs (pairChain α β I J)=
      pairExponent α β (meet α β I J) (join α β I J) := by
  apply MvPolynomial.monomial_left_injective (one_ne_zero : (1 : ℚ)≠0)
  change (monomial (goodChainExponent k t hs (pairChain α β I J)) 1 :
    MvPolynomial (IntervalIndex α β) ℚ) =
      monomial (pairExponent α β (meet α β I J) (join α β I J)) 1
  erw [←standardPolynomial_eq_monomial,standardPolynomial_pairChain,pair_monomial]

theorem odd_normal_term_lt (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (hinc : incomparable α β I J)
    (C : OddStandardIndex k t hs)
    (hc : oddCoefficients (K := K) k t hs (X I.val*X J.val) C≠0) :
    goodChainExponent k t hs C ≺[oddGoodOrder k t hs m] pairExponent α β I J := by
  rcases odd_pair_coefficients_triangular k t hs I J C hc with hw | ⟨hw,hd⟩
  · apply lt_of_weight_lt
    simpa only [goodChainExponent_vertexWeight,pairExponent,map_add,
      Finsupp.weight_single,one_smul] using hw
  · apply lt_of_weight_eq_of_lt
    · simpa only [goodChainExponent_vertexWeight,pairExponent,map_add,
        Finsupp.weight_single,one_smul] using hw
    · rcases hd with hd | ⟨hd,hC⟩
      · apply lt_of_weight_lt
        simpa only [goodChainExponent_diagonalWeight,pairExponent,map_add,
          Finsupp.weight_single,one_smul] using hd
      · apply lt_of_weight_eq_of_lt
        · simpa only [goodChainExponent_diagonalWeight,pairExponent,map_add,
            Finsupp.weight_single,one_smul] using hd
        · rw [hC,goodChainExponent_pairChain]
          exact pair_sorting_lt α β m I J hinc

theorem oddGoodNormalForm_support (I J : IntervalIndex α β)
    (a : IntervalIndex α β →₀ ℕ)
    (ha : a∈(oddGoodNormalForm (K := K) k t hs (X I*X J)).support) :
    ∃ C : OddStandardIndex k t hs,
      oddCoefficients (K := K) k t hs (X I.val*X J.val) C≠0 ∧ a=goodChainExponent k t hs C := by
  classical
  have h := mem_support_iff.mp ha
  rw [oddGoodNormalForm_pair] at h
  simp only [Finsupp.sum,coeff_sum] at h
  obtain ⟨C,hC,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨C,Finsupp.mem_support_iff.mp hC,?_⟩
  by_contra hne
  apply hterm
  simp only [coeff_smul,standardPolynomial_eq_monomial,coeff_monomial,
    if_neg (Ne.symm hne),smul_zero]

theorem pairExponent_ne_zero (I J : IntervalIndex α β) : pairExponent α β I J≠0 := by
  intro h
  have he := congrArg (fun a : IntervalIndex α β →₀ ℕ => a I) h
  simp only [pairExponent,Finsupp.add_apply,Finsupp.single_eq_same,
    Finsupp.zero_apply] at he
  omega

theorem oddGoodNormalForm_degree_lt (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (hinc : incomparable α β I J) :
    (oddGoodOrder k t hs m).degree (oddGoodNormalForm (K := K) k t hs (X I*X J))
      ≺[oddGoodOrder k t hs m] pairExponent α β I J := by
  have hpos : 0 ≺[oddGoodOrder k t hs m] pairExponent α β I J := by
    rw [map_zero,MonomialOrder.toSyn_lt_iff_ne_zero]
    intro h
    exact pairExponent_ne_zero k t hs I J
      ((oddGoodOrder k t hs m).toSyn.injective (by simpa only [map_zero] using h))
  apply ((oddGoodOrder k t hs m).degree_lt_iff hpos).mpr
  intro a ha
  obtain ⟨C,hC,rfl⟩ := oddGoodNormalForm_support k t hs I J a ha
  exact odd_normal_term_lt k t hs m I J hinc C hC

theorem oddQuadraticRelation_degree (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (hinc : incomparable α β I J) :
    (oddGoodOrder k t hs m).degree (oddQuadraticRelation (K := K) k t hs I J)=
      pairExponent α β I J := by
  classical
  have h := oddGoodNormalForm_degree_lt (K := K) k t hs m I J hinc
  have h' : (oddGoodOrder k t hs m).degree (oddGoodNormalForm (K := K) k t hs (X I*X J))
      ≺[oddGoodOrder k t hs m]
        (oddGoodOrder k t hs m).degree (X I*X J : P) := by
    simpa only [pair_monomial,MonomialOrder.degree_monomial,if_neg (one_ne_zero : (1 : K) ≠ 0)] using h
  rw [oddQuadraticRelation,(oddGoodOrder k t hs m).degree_sub_of_lt h',
    pair_monomial,MonomialOrder.degree_monomial,if_neg (one_ne_zero : (1 : K) ≠ 0)]

theorem oddQuadraticRelation_leadingCoeff (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (hinc : incomparable α β I J) :
    (oddGoodOrder k t hs m).leadingCoeff (oddQuadraticRelation (K := K) k t hs I J)=1 := by
  classical
  have h := oddGoodNormalForm_degree_lt (K := K) k t hs m I J hinc
  have h' : (oddGoodOrder k t hs m).degree (oddGoodNormalForm (K := K) k t hs (X I*X J))
      ≺[oddGoodOrder k t hs m]
        (oddGoodOrder k t hs m).degree (X I*X J : P) := by
    simpa only [pair_monomial,MonomialOrder.degree_monomial,if_neg (one_ne_zero : (1 : K) ≠ 0)] using h
  rw [oddQuadraticRelation,(oddGoodOrder k t hs m).leadingCoeff_sub_of_lt h',
    pair_monomial,MonomialOrder.leadingCoeff_monomial]

theorem oddQuadraticRelation_ne_zero (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (hinc : incomparable α β I J) :
    oddQuadraticRelation (K := K) k t hs I J≠0 := by
  intro h
  have hlead := oddQuadraticRelation_leadingCoeff (K := K) k t hs m I J hinc
  rw [h,MonomialOrder.leadingCoeff_zero] at hlead
  exact zero_ne_one hlead

theorem odd_remainder_normal_support (m : MonomialOrder (IntervalIndex α β))
    (p r : P) (hr : (oddGoodOrder k t hs m).IsRemainder p (oddQuadraticSet k t hs) r) :
    ∀ a∈r.support,NormalMonomial α β a := by
  intro a ha I hI J hJ
  by_contra h
  have hinc : incomparable α β I J := not_or.mp h
  have hne : I≠J := fun he => hinc.1 (he ▸ le_rfl)
  have hnot := hr.not_degree_le ha
    (show oddQuadraticRelation (K := K) k t hs I J∈oddQuadraticSet k t hs from
      ⟨I,J,hinc,rfl⟩) (oddQuadraticRelation_ne_zero k t hs m I J hinc)
  rw [oddQuadraticRelation_degree k t hs m I J hinc] at hnot
  exact hnot (pairExponent_le_of_support α β a I J hI hJ hne)

/-- The actual good-coordinate kernel of the canonical odd-pencil ring
has the asserted quadratic Gröbner basis. -/
theorem odd_good_quadratic_isGroebnerBasis (m : MonomialOrder (IntervalIndex α β)) :
    (oddGoodOrder k t hs m).IsGroebnerBasis
      (oddQuadraticSet (K := K) k t hs) (oddGoodIdeal k t hs) := by
  have hsub : oddQuadraticSet (K := K) k t hs ⊆ (oddGoodIdeal (K := K) k t hs : Set P) := by
    rintro p ⟨I,J,h,rfl⟩
    exact oddQuadraticRelation_mem k t hs I J
  apply MonomialOrder.isGroebnerBasis_iff_isRemainder_zero.mpr
  refine ⟨hsub,?_⟩
  intro p hp
  obtain ⟨r,hr⟩ := (oddGoodOrder k t hs m).exists_isRemainder (B := oddQuadraticSet (K := K) k t hs)
    (fun b hb hb0 => by
      obtain ⟨I,J,h,rfl⟩ := hb
      rw [oddQuadraticRelation_leadingCoeff k t hs m I J h]
      exact isUnit_one) p
  have hpr : p-r∈oddGoodIdeal (K := K) k t hs :=
    Ideal.span_le.mpr hsub hr.sub_mem_span
  have hrI : r∈oddGoodIdeal (K := K) k t hs := by
    simpa only [sub_sub_cancel] using (oddGoodIdeal (K := K) k t hs).sub_mem hp hpr
  have hr0 : r=0 := oddGood_normal_polynomial_eq_zero k t hs r
    (odd_remainder_normal_support k t hs m p r hr) hrI
  simpa only [hr0] using hr

theorem oddQuadraticSet_finite : (oddQuadraticSet (K := K) k t hs).Finite := by
  apply (Set.finite_range (fun a : IntervalIndex α β × IntervalIndex α β =>
    oddQuadraticRelation (K := K) k t hs a.1 a.2)).subset
  rintro p ⟨I,J,h,rfl⟩
  exact ⟨(I,J),rfl⟩

/-- Every member of the displayed finite Gröbner basis is an actual
homogeneous quadratic polynomial in the good coordinates. -/
theorem odd_good_quadratic_groebner_data (m : MonomialOrder (IntervalIndex α β)) :
    (oddQuadraticSet (K := K) k t hs).Finite ∧
    (∀ p∈oddQuadraticSet (K := K) k t hs,p.IsHomogeneous 2) ∧
    (oddGoodOrder k t hs m).IsGroebnerBasis
      (oddQuadraticSet (K := K) k t hs) (oddGoodIdeal k t hs) := by
  refine ⟨oddQuadraticSet_finite k t hs,?_,odd_good_quadratic_isGroebnerBasis k t hs m⟩
  rintro p ⟨I,J,h,rfl⟩
  exact oddQuadraticRelation_homogeneous k t hs I J

/-- The Gröbner assertion is existential in an actual monomial order;
there is no term-order or triangularity hypothesis on the original ring. -/
theorem odd_good_exists_quadratic_groebner :
    ∃ m : MonomialOrder.{0,0} (IntervalIndex α β),
      (oddQuadraticSet (K := K) k t hs).Finite ∧
      (∀ p∈oddQuadraticSet (K := K) k t hs,p.IsHomogeneous 2) ∧
      m.IsGroebnerBasis (oddQuadraticSet (K := K) k t hs) (oddGoodIdeal k t hs) :=
  ⟨oddGoodOrder k t hs (finiteBaseOrder (IntervalIndex α β)),
    odd_good_quadratic_groebner_data k t hs (finiteBaseOrder (IntervalIndex α β))⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0249

section TAF_LiteralSource_0250
/- Original module: PaperVerification.AugmentedAlgebraBasis -/


/-!
# An actual unit-plus-augmentation basis

These are coefficient identities for a genuine augmented algebra and a
basis whose distinguished vector is the unit. They are the algebraic
inputs for the normalized free bar resolution: positive multiplication,
its associativity, and the splitting used by the contracting homotopy.
No bar exactness or homological claim is assumed in these data.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AugmentedAlgebraBasis

open scoped BigOperators

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

@[expose]
def positiveVector (i : I) : A := B (some i)

@[expose]
def positiveCoordinates : A →ₗ[K] (I →₀ K) :=
  (Finsupp.lcomapDomain (R := K) (M := K) Option.some (Option.some_injective I)).comp
    B.repr.toLinearMap

@[simp] theorem positiveCoordinates_apply (x : A) (i : I) :
    positiveCoordinates B x i=B.repr x (some i) := rfl

def positiveCombination : (I →₀ K) →ₗ[K] A :=
  Finsupp.linearCombination K (positiveVector B)

@[simp] theorem positiveCombination_apply (c : I →₀ K) :
    positiveCombination B c=c.sum (fun i z => z • positiveVector B i) := rfl

include hunit hε in
theorem augmentation_eq_coordinate (x : A) : ε x=B.repr x none := by
  have he : ε.toLinearMap=B.coord none := by
    apply B.ext
    intro i
    cases i with
    | none =>
        change ε (B none)=B.repr (B none) none
        rw [Module.Basis.repr_self,Finsupp.single_eq_same,hunit,map_one]
    | some i =>
        change ε (B (some i))=B.repr (B (some i)) none
        rw [hε,Module.Basis.repr_self,Finsupp.single_eq_of_ne (by simp)]
  exact LinearMap.congr_fun he x

@[simp] theorem positiveCoordinates_vector (i : I) :
    positiveCoordinates B (positiveVector B i)=Finsupp.single i 1 := by
  classical
  ext j
  simp [positiveCoordinates_apply,positiveVector,Module.Basis.repr_self,
    Finsupp.single_apply]

include hunit in
@[simp] theorem positiveCoordinates_one : positiveCoordinates B (1 : A)=0 := by
  rw [←hunit]
  ext i
  simp only [positiveCoordinates_apply,Module.Basis.repr_self,Finsupp.single_apply,
    reduceCtorEq,ite_false,Finsupp.zero_apply]

include hunit hε in
/-- The literal splitting of every algebra element into its scalar and
augmentation parts. -/
theorem scalar_add_positive (x : A) :
    ε x • (1 : A)+positiveCombination B (positiveCoordinates B x)=x := by
  have h := B.linearCombination_repr x
  rw [Finsupp.linearCombination_apply,Finsupp.sum_option_index_smul,hunit,
    ←augmentation_eq_coordinate ε B hunit hε x] at h
  exact h

include hunit hε in
theorem positiveCombination_coordinates (x : A) (hx : ε x=0) :
    positiveCombination B (positiveCoordinates B x)=x := by
  have h := scalar_add_positive ε B hunit hε x
  simpa only [hx,zero_smul,zero_add] using h

@[simp] theorem positiveCoordinates_combination (c : I →₀ K) :
    positiveCoordinates B (positiveCombination B c)=c := by
  rw [positiveCombination_apply]
  simp only [Finsupp.sum,map_sum,map_smul,positiveCoordinates_vector,
    Finsupp.smul_single,smul_eq_mul,mul_one]
  exact Finsupp.sum_single c

theorem positiveCombination_injective : Function.Injective (positiveCombination B) :=
  Function.LeftInverse.injective (positiveCoordinates_combination B)

@[expose]
def productCoefficients (i j : I) : I →₀ K :=
  positiveCoordinates B (positiveVector B i*positiveVector B j)

include hunit hε in
theorem product_expansion (i j : I) :
    positiveCombination B (productCoefficients B i j)=positiveVector B i*positiveVector B j := by
  apply positiveCombination_coordinates ε B hunit hε
  simp only [positiveVector,map_mul,hε,mul_zero]

include hunit hε in
theorem productCoefficients_associative (i j k : I) :
    (productCoefficients B i j).sum (fun a c => c • productCoefficients B a k)=
      (productCoefficients B j k).sum (fun a c => c • productCoefficients B i a) := by
  apply positiveCombination_injective B
  simp only [Finsupp.sum,map_sum,map_smul,product_expansion ε B hunit hε]
  have hl := congrArg (fun z : A => z*positiveVector B k)
    (product_expansion ε B hunit hε i j)
  have hr := congrArg (fun z : A => positiveVector B i*z)
    (product_expansion ε B hunit hε j k)
  simp only [positiveCombination_apply,Finsupp.sum,Finset.sum_mul,smul_mul_assoc] at hl
  simp only [positiveCombination_apply,Finsupp.sum,Finset.mul_sum,mul_smul_comm] at hr
  exact hl.trans ((mul_assoc _ _ _).trans hr.symm)

include hunit hε in
/-- This is the identity that cancels the first multiplication term
against the positive-prefix part of the normalized bar homotopy. -/
theorem positiveCoordinates_mul_vector (x : A) (j : I) :
    positiveCoordinates B (x*positiveVector B j)=
      ε x • Finsupp.single j 1+
        (positiveCoordinates B x).sum (fun i c => c • productCoefficients B i j) := by
  have h := congrArg (fun z : A => positiveCoordinates B (z*positiveVector B j))
    (scalar_add_positive ε B hunit hε x)
  rw [add_mul,smul_mul_assoc,one_mul,map_add,map_smul,positiveCoordinates_vector] at h
  rw [positiveCombination_apply] at h
  simp only [Finsupp.sum,Finset.sum_mul,smul_mul_assoc,map_sum,map_smul] at h
  exact h.symm

end PaperVerification.AugmentedAlgebraBasis
end
end
end TAF_LiteralSource_0250

section TAF_LiteralSource_0251
/- Original module: PaperVerification.ReducedBarBasis -/


/-!
# The actual normalized bar differential in a positive algebra basis

A basis word denotes a tensor of augmentation-ideal basis vectors. The
map merges adjacent tensor factors using their actual multiplication
coefficients and alternating signs. Associativity of the original algebra
proves that its square is zero. These are genuine coefficient formulas;
no differential or complex identity is supplied as an assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.ReducedBarBasis

open scoped BigOperators
open AugmentedAlgebraBasis

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

local notation "W" => List I →₀ K

@[expose]
def prepend (i : I) : W →ₗ[K] W :=
  Finsupp.linearCombination K (fun L => Finsupp.single (i::L) 1)

@[expose]
def appendTail (L : List I) : (I →₀ K) →ₗ[K] W :=
  Finsupp.linearCombination K (fun i => Finsupp.single (i::L) 1)

@[simp] theorem prefix_single (i : I) (L : List I) (c : K) :
    prepend i (Finsupp.single L c : W)=Finsupp.single (i::L) c := by
  simp only [prepend,Finsupp.linearCombination_single,Finsupp.smul_single,smul_eq_mul,mul_one]

@[simp] theorem appendTail_single (L : List I) (i : I) (c : K) :
    appendTail L (Finsupp.single i c : I →₀ K)=Finsupp.single (i::L) c := by
  simp only [appendTail,Finsupp.linearCombination_single,Finsupp.smul_single,smul_eq_mul,mul_one]

@[expose]
def mergeBasis (i : I) : List I → W
  | [] => 0
  | j::L => appendTail L (productCoefficients B i j)

@[expose]
def merge (i : I) : W →ₗ[K] W := Finsupp.linearCombination K (mergeBasis B i)

@[simp] theorem merge_single (i : I) (L : List I) (c : K) :
    merge B i (Finsupp.single L c)=c • mergeBasis B i L :=
  Finsupp.linearCombination_single _ _ _

/-- Multiplication of the first tensor factor by a fixed augmentation
basis vector, written as an actual finite sum of prepend maps. -/
theorem merge_prefix (i j : I) (z : W) :
    merge B i (prepend j z)=
      (productCoefficients B i j).sum (fun a c => c • prepend a z) := by
  have he : (merge B i).comp (prepend j)=
      Finsupp.linearCombination K (fun a => prepend (K := K) a) (productCoefficients B i j) := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply,prefix_single,merge_single,mergeBasis,
      Finsupp.linearCombination_apply,Finsupp.sum,LinearMap.sum_apply,
      LinearMap.smul_apply,prefix_single,appendTail,Finsupp.linearCombination_apply]
    simp only [Finset.smul_sum,Finsupp.smul_single,smul_eq_mul,mul_one]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [mul_comm]
  have h := LinearMap.congr_fun he z
  simpa only [LinearMap.comp_apply,Finsupp.linearCombination_apply,Finsupp.sum,LinearMap.sum_apply,
    LinearMap.smul_apply] using h

include hunit hε in
/-- Successive first-factor multiplications retain the original algebra's
associativity, including all actual structure coefficients. -/
theorem merge_merge (i j : I) (z : W) :
    merge B i (merge B j z)=
      (productCoefficients B i j).sum (fun a c => c • merge B a z) := by
  have he : (merge B i).comp (merge B j)=
      Finsupp.linearCombination K (merge B) (productCoefficients B i j) := by
    apply Finsupp.lhom_ext
    intro L c
    cases L with
    | nil => simp only [LinearMap.comp_apply,merge_single,mergeBasis,smul_zero,map_zero,
        Finsupp.linearCombination_apply,Finsupp.sum,LinearMap.sum_apply,
        LinearMap.smul_apply,Finset.sum_const_zero]
    | cons k L =>
        have h := congrArg (appendTail (K := K) L)
          (productCoefficients_associative ε B hunit hε i j k)
        simp only [Finsupp.sum,map_sum,map_smul] at h
        simp only [LinearMap.comp_apply,merge_single,mergeBasis,map_smul,
          appendTail,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,
          Finsupp.linearCombination_apply,LinearMap.sum_apply,LinearMap.smul_apply,
          Finset.smul_sum,smul_smul] at h ⊢
        simpa only [Finset.smul_sum,smul_smul,mul_comm,mul_left_comm,mul_assoc,one_mul,mul_one] using
          congrArg (c • ·) h.symm
  have h := LinearMap.congr_fun he z
  simpa only [LinearMap.comp_apply,Finsupp.linearCombination_apply,Finsupp.sum,LinearMap.sum_apply,
    LinearMap.smul_apply] using h

/-- The alternating sum of adjacent multiplication operations, defined
recursively on the actual positive-basis tensor word. -/
@[expose]
def differentialBasis : List I → W
  | [] => 0
  | i::L => merge B i (Finsupp.single L 1)-prepend i (differentialBasis L)

@[expose]
def differential : W →ₗ[K] W := Finsupp.linearCombination K (differentialBasis B)

@[simp] theorem differential_single (L : List I) (c : K) :
    differential B (Finsupp.single L c)=c • differentialBasis B L :=
  Finsupp.linearCombination_single _ _ _

theorem differential_prefix (i : I) (z : W) :
    differential B (prepend i z)=merge B i z-prepend i (differential B z) := by
  have he : (differential B).comp (prepend i)=
      merge B i-(prepend i).comp (differential B) := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply,LinearMap.sub_apply,prefix_single,differential_single,
      differentialBasis,merge_single,map_smul,smul_sub,one_smul]
  exact LinearMap.congr_fun he z

include hunit hε in
/-- Associativity is exactly the commutation needed for the square-zero
bar differential. -/
theorem differential_merge (i : I) (z : W) :
    differential B (merge B i z)=merge B i (differential B z) := by
  have hprefix (j : I) (z : W) :
      differential B (merge B i (prepend j z))=merge B i (differential B (prepend j z)) := by
    rw [merge_prefix,differential_prefix,map_sub]
    simp only [Finsupp.sum,map_sum,map_smul,differential_prefix,smul_sub,
      Finset.sum_sub_distrib]
    have h₁ := merge_merge ε B hunit hε i j z
    have h₂ := merge_prefix B i j (differential B z)
    simpa only [Finsupp.sum] using congrArg₂ (fun x y : W ↦ x-y) h₁.symm h₂.symm
  have he : (differential B).comp (merge B i)=(merge B i).comp (differential B) := by
    apply Finsupp.lhom_ext
    intro L c
    cases L with
    | nil => simp only [LinearMap.comp_apply,merge_single,mergeBasis,smul_zero,map_zero,
        differential_single,differentialBasis]
    | cons j L =>
        have h := hprefix j (Finsupp.single L c)
        simpa only [prefix_single,LinearMap.comp_apply] using h
  exact LinearMap.congr_fun he z

include hunit hε in
theorem differentialBasis_squared (L : List I) :
    differential B (differentialBasis B L)=0 := by
  induction L with
  | nil => exact map_zero _
  | cons i L ih =>
      rw [differentialBasis,map_sub,differential_merge ε B hunit hε,
        differential_prefix,differential_single,one_smul,ih,map_zero,sub_zero,sub_self]

include hunit hε in
/-- The literal adjacent-product differential squares to zero. -/
theorem differential_squared (z : W) : differential B (differential B z)=0 := by
  have he : (differential B).comp (differential B)=0 := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply,differential_single,map_smul,
      differentialBasis_squared ε B hunit hε,smul_zero,LinearMap.zero_apply]
  exact LinearMap.congr_fun he z

/-- A two-tensor is sent to its actual product in the augmentation ideal. -/
theorem differential_pair (i j : I) :
    differential B (Finsupp.single [i,j] (1 : K))=
      (productCoefficients B i j).sum (fun a c => Finsupp.single [a] c) := by
  simp only [differential_single,one_smul,differentialBasis,merge_single,mergeBasis,
    smul_zero,map_zero,sub_zero,appendTail,Finsupp.linearCombination_apply,
    Finsupp.smul_single,smul_eq_mul,mul_one]

end PaperVerification.ReducedBarBasis
end
end
end TAF_LiteralSource_0251

section TAF_LiteralSource_0252
/- Original module: PaperVerification.AlternatingFormsBarFree -/


/-!
# The normalized free bar differential of an augmented algebra

The free module is indexed by words in the positive basis. Its differential
has the actual left multiplication term and the actual adjacent-product terms.
All coefficients come from the supplied algebra and its unit-plus-augmentation
basis; no differential identity or homological exactness is assumed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms.BarFree

open PaperVerification.AugmentedAlgebraBasis

variable {K A I : Type*} [CommRing K] [CommRing A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

abbrev Words (I A : Type*) [Zero A] := List I →₀ A

/-- Extension of word coefficients along the actual algebra map. -/
def lift : Words I K →ₗ[K] Words I A :=
  Finsupp.linearCombination K (fun L ↦ Finsupp.single L 1)

@[simp] theorem lift_single (L : List I) (c : K) :
    lift (A := A) (Finsupp.single L c)=c • Finsupp.single L 1 :=
  Finsupp.linearCombination_single _ _ _

def prepend (i : I) : Words I A →ₗ[A] Words I A :=
  Finsupp.lmapDomain A A (List.cons i)

@[simp] theorem prefix_single (i : I) (L : List I) (a : A) :
    prepend i (Finsupp.single L a)=Finsupp.single (i::L) a := by
  simp [prepend]

def frontBasis : List I → Words I A
  | [] => 0
  | i::L => Finsupp.single L (positiveVector B i)

/-- The term that multiplies the free coefficient by the first bar factor. -/
def front : Words I A →ₗ[A] Words I A :=
  Finsupp.linearCombination A (frontBasis B)

@[simp] theorem front_single (L : List I) (a : A) :
    front B (Finsupp.single L a)=a • frontBasis B L :=
  Finsupp.linearCombination_single _ _ _

/-- The scalar extension of the actual positive-basis adjacent-product differential. -/
def internal : Words I A →ₗ[A] Words I A :=
  Finsupp.linearCombination A (fun L ↦
    lift (PaperVerification.ReducedBarBasis.differentialBasis B L))

@[simp] theorem internal_single (L : List I) (a : A) :
    internal B (Finsupp.single L a)=
      a • lift (PaperVerification.ReducedBarBasis.differentialBasis B L) :=
  Finsupp.linearCombination_single _ _ _

theorem lift_prefix (i : I) (z : Words I K) :
    lift (PaperVerification.ReducedBarBasis.prepend i z)=
      prepend i (lift (A := A) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw]
  | single L c =>
    simp only [PaperVerification.ReducedBarBasis.prefix_single,lift_single,
      LinearMap.map_smul_of_tower,prefix_single]

theorem internal_lift (z : Words I K) :
    internal B (lift z)=lift (PaperVerification.ReducedBarBasis.differential B z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw]
  | single L c =>
    simp only [lift_single,LinearMap.map_smul_of_tower,internal_single,one_smul,
      PaperVerification.ReducedBarBasis.differential_single,map_smul]

theorem front_lift_prefix (i : I) (z : Words I K) :
    front B (lift (PaperVerification.ReducedBarBasis.prepend i z))=
      positiveVector B i • lift z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L c =>
    simp only [PaperVerification.ReducedBarBasis.prefix_single,lift_single,
      LinearMap.map_smul_of_tower,front_single,frontBasis,one_smul]
    rw [smul_comm]
    congr 1
    simp only [Finsupp.smul_single,smul_eq_mul,mul_one]

theorem front_lift_appendTail (L : List I) (c : I →₀ K) :
    front B (lift (PaperVerification.ReducedBarBasis.appendTail L c))=
      Finsupp.single L (positiveCombination B c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.single_zero]
  | add c d hc hd => simp only [map_add,Finsupp.single_add,hc,hd]
  | single i c =>
    simp only [PaperVerification.ReducedBarBasis.appendTail_single,lift_single,
      LinearMap.map_smul_of_tower,front_single,frontBasis,one_smul,
      positiveCombination,Finsupp.linearCombination_single,Finsupp.smul_single,
      smul_assoc,one_smul]

include hunit hε in
theorem front_lift_merge (i : I) (z : Words I K) :
    front B (lift (PaperVerification.ReducedBarBasis.merge B i z))=
      positiveVector B i • front B (lift z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L c =>
    cases L with
    | nil =>
      simp only [PaperVerification.ReducedBarBasis.merge_single,
        PaperVerification.ReducedBarBasis.mergeBasis,smul_zero,map_zero,
        lift_single,LinearMap.map_smul_of_tower,front_single,frontBasis]
    | cons j L =>
      simp only [PaperVerification.ReducedBarBasis.merge_single,
        PaperVerification.ReducedBarBasis.mergeBasis,map_smul,
        LinearMap.map_smul_of_tower,front_lift_appendTail,
        product_expansion ε B hunit hε,lift_single,front_single,frontBasis,one_smul]
      rw [smul_comm]
      congr 1
      simp only [Finsupp.smul_single,smul_eq_mul]

include hunit hε in
theorem internal_squared (z : Words I A) : internal B (internal B z)=0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw,add_zero]
  | single L a =>
    rw [internal_single,map_smul,internal_lift,
      PaperVerification.ReducedBarBasis.differentialBasis_squared ε B hunit hε,
      map_zero,smul_zero]

include hunit hε in
/-- The first multiplication term and the internal terms satisfy the identity
that leaves exactly the square of the first multiplication term. -/
theorem front_internal (z : Words I A) :
    front B (internal B z)+internal B (front B z)=front B (front B z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,add_zero]
  | add z w hz hw =>
    simp only [map_add]
    rw [show front B (internal B z)+front B (internal B w)+
      (internal B (front B z)+internal B (front B w))=
      (front B (internal B z)+internal B (front B z))+
      (front B (internal B w)+internal B (front B w)) by abel,hz,hw]
  | single L a =>
    have h : front B (internal B (Finsupp.single L 1))+
        internal B (front B (Finsupp.single L 1))=
        front B (front B (Finsupp.single L 1)) := by
      cases L with
      | nil =>
        simp only [internal_single,PaperVerification.ReducedBarBasis.differentialBasis,
          front_single,frontBasis,map_zero,smul_zero,add_zero]
      | cons i L =>
        simp only [internal_single,one_smul,
          PaperVerification.ReducedBarBasis.differentialBasis,map_sub,
          front_lift_merge ε B hunit hε,front_lift_prefix,
          front_single,frontBasis,map_smul,internal_single,one_smul,lift_single,
          LinearMap.map_smul_of_tower]
        abel
    have ha : Finsupp.single L a=a • (Finsupp.single L 1 : Words I A) := by
      simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
    rw [ha]
    simp only [map_smul,←smul_add,h]

/-- The genuine normalized free bar differential, with the standard signs. -/
def differential : Words I A →ₗ[A] Words I A := front B-internal B

include hunit hε in
theorem differential_squared (z : Words I A) :
    differential B (differential B z)=0 := by
  change front B (front B z-internal B z)-
    internal B (front B z-internal B z)=0
  rw [map_sub,map_sub,internal_squared ε B hunit hε,sub_zero]
  have h := front_internal ε B hunit hε z
  rw [←h]
  abel

/-- The positive-part prepend used in the actual contracting homotopy. -/
def positivePrefix (L : List I) : A →ₗ[K] Words I A :=
  (Finsupp.linearCombination K (fun i ↦ Finsupp.single (i::L) 1)).comp
    (positiveCoordinates B)

/-- This map increases bar length by one and is K-linear, as a contraction
of a free A-resolution should be. It is not asserted to be A-linear. -/
def homotopy : Words I A →ₗ[K] Words I A :=
  Finsupp.lsum K (positivePrefix B)

@[simp] theorem homotopy_single (L : List I) (a : A) :
    homotopy B (Finsupp.single L a)=
      Finsupp.linearCombination K (fun i ↦ Finsupp.single (i::L) 1)
        (positiveCoordinates B a) := by
  simp only [homotopy,Finsupp.lsum_single,positivePrefix,LinearMap.comp_apply]

include hunit in
@[simp] theorem homotopy_single_one (L : List I) :
    homotopy B (Finsupp.single L (1 : A))=0 := by
  rw [homotopy_single,positiveCoordinates_one B hunit,map_zero]

@[simp] theorem homotopy_single_positive (L : List I) (i : I) :
    homotopy B (Finsupp.single L (positiveVector B i))=Finsupp.single (i::L) 1 := by
  rw [homotopy_single,positiveCoordinates_vector,
    Finsupp.linearCombination_single,one_smul]

/-- Scalar extension of multiplication of the first positive tensor factor. -/
def merge (i : I) : Words I A →ₗ[A] Words I A :=
  Finsupp.linearCombination A (fun L ↦
    lift (PaperVerification.ReducedBarBasis.mergeBasis B i L))

@[simp] theorem merge_single (i : I) (L : List I) (a : A) :
    merge B i (Finsupp.single L a)=
      a • lift (PaperVerification.ReducedBarBasis.mergeBasis B i L) :=
  Finsupp.linearCombination_single _ _ _

theorem front_prefix (i : I) (z : Words I A) :
    front B (prepend i z)=positiveVector B i • z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L a =>
    simp only [prefix_single,front_single,frontBasis,Finsupp.smul_single,smul_eq_mul,mul_comm]

theorem internal_prefix (i : I) (z : Words I A) :
    internal B (prepend i z)=merge B i z-prepend i (internal B z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,sub_zero]
  | add z w hz hw => simp only [map_add,hz,hw]; abel
  | single L a =>
    simp only [prefix_single,internal_single,
      PaperVerification.ReducedBarBasis.differentialBasis,map_sub,
      PaperVerification.ReducedBarBasis.merge_single,one_smul,
      lift_prefix,smul_sub,merge_single,map_smul]

def positivePrefixMap (a : A) : Words I A →ₗ[K] Words I A :=
  Finsupp.linearCombination K (fun i ↦ (prepend (A := A) i).restrictScalars K)
    (positiveCoordinates B a)

def positiveMergeMap (a : A) : Words I A →ₗ[K] Words I A :=
  Finsupp.linearCombination K (fun i ↦ (merge B i).restrictScalars K)
    (positiveCoordinates B a)

theorem homotopy_single_eq_prefix (L : List I) (a : A) :
    homotopy B (Finsupp.single L a)=
      positivePrefixMap B a (Finsupp.single L 1) := by
  simp only [homotopy_single,positivePrefixMap,Finsupp.linearCombination_apply,
    Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.restrictScalars_apply,prefix_single]

theorem homotopy_smul_lift (a : A) (z : Words I K) :
    homotopy B (a • lift z)=positivePrefixMap B a (lift z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L c =>
    calc
      homotopy B (a • lift (Finsupp.single L c)) =
          homotopy B (c • (a • (Finsupp.single L 1 : Words I A))) := by
        rw [lift_single,smul_comm a c]
      _ = c • homotopy B (Finsupp.single L a) := by
        rw [map_smul]
        congr 1
        simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
      _ = c • positivePrefixMap B a (Finsupp.single L 1) := by
        rw [homotopy_single_eq_prefix]
      _ = positivePrefixMap B a (lift (Finsupp.single L c)) := by
        rw [lift_single,map_smul]

theorem front_positivePrefixMap (a : A) (z : Words I A) :
    front B (positivePrefixMap B a z)=
      positiveCombination B (positiveCoordinates B a) • z := by
  simp only [positivePrefixMap,Finsupp.linearCombination_apply,Finsupp.sum,
    LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.restrictScalars_apply,
    map_sum,LinearMap.map_smul_of_tower,front_prefix,positiveCombination_apply,
    Finset.sum_smul,smul_assoc]

theorem internal_positivePrefixMap (a : A) (z : Words I A) :
    internal B (positivePrefixMap B a z)=
      positiveMergeMap B a z-positivePrefixMap B a (internal B z) := by
  simp only [positivePrefixMap,positiveMergeMap,Finsupp.linearCombination_apply,
    Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.restrictScalars_apply,
    map_sum,LinearMap.map_smul_of_tower,internal_prefix,smul_sub,Finset.sum_sub_distrib]

include hunit hε in
theorem front_positivePrefixMap_add_scalar (a : A) (z : Words I A) :
    front B (positivePrefixMap B a z)+ε a • z=a • z := by
  rw [front_positivePrefixMap]
  have h := congrArg (fun x : A ↦ x • z) (scalar_add_positive ε B hunit hε a)
  simp only [add_smul,smul_assoc,one_smul] at h
  simpa only [add_comm] using h

theorem lift_appendTail (L : List I) (c : I →₀ K) :
    lift (A := A) (PaperVerification.ReducedBarBasis.appendTail L c)=
      Finsupp.linearCombination K (fun i ↦ Finsupp.single (i::L) (1 : A)) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single i c =>
    simp only [PaperVerification.ReducedBarBasis.appendTail_single,lift_single,
      Finsupp.linearCombination_single]

include hunit hε in
/-- The coefficient splitting of a product gives exactly the two terms that
cancel the first adjacent multiplication in the homotopy identity. -/
theorem homotopy_front_cons (a : A) (i : I) (L : List I) :
    homotopy B (front B (Finsupp.single (i::L) a))=
      ε a • Finsupp.single (i::L) 1+
        positiveMergeMap B a (Finsupp.single (i::L) 1) := by
  rw [front_single]
  change homotopy B (a • Finsupp.single L (positiveVector B i))=_
  rw [Finsupp.smul_single]
  change homotopy B (Finsupp.single L (a*positiveVector B i))=_
  rw [homotopy_single,positiveCoordinates_mul_vector ε B hunit hε,
    map_add,map_smul,Finsupp.linearCombination_single]
  simp only [Finsupp.sum,map_sum,map_smul,positiveMergeMap,
    Finsupp.linearCombination_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.restrictScalars_apply,merge_single,one_smul,
    PaperVerification.ReducedBarBasis.mergeBasis,lift_appendTail]

theorem positiveMergeMap_nil (a : A) :
    positiveMergeMap B a (Finsupp.single [] (1 : A))=0 := by
  simp only [positiveMergeMap,Finsupp.linearCombination_apply,Finsupp.sum,
    LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.restrictScalars_apply,
    merge_single,PaperVerification.ReducedBarBasis.mergeBasis,map_zero,smul_zero,
    Finset.sum_const_zero]

/-- Augmentation followed by the degree-zero unit inclusion. -/
def augmentationProjection : Words I A →ₗ[K] Words I A :=
  (ε.toLinearMap.smulRight (Finsupp.single [] (1 : A))).comp
    (Finsupp.lapply [])

@[simp] theorem augmentationProjection_nil (a : A) :
    augmentationProjection (I := I) ε (Finsupp.single [] a)=
      ε a • Finsupp.single [] 1 := by
  simp [augmentationProjection]

@[simp] theorem augmentationProjection_cons (i : I) (L : List I) (a : A) :
    augmentationProjection ε (Finsupp.single (i::L) a)=0 := by
  simp [augmentationProjection]

include hunit hε in
/-- The explicit K-linear contraction of the augmented normalized free bar
complex. Together with the length restriction, this proves actual exactness. -/
theorem contracting_identity (z : Words I A) :
    differential B (homotopy B z)+homotopy B (differential B z)+
      augmentationProjection ε z=z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,add_zero]
  | add z w hz hw =>
    simp only [map_add]
    calc
      _ = (differential B (homotopy B z)+homotopy B (differential B z)+
          augmentationProjection ε z)+
        (differential B (homotopy B w)+homotopy B (differential B w)+
          augmentationProjection ε w) := by abel
      _ = _ := by rw [hz,hw]
  | single L a =>
    cases L with
    | nil =>
      rw [homotopy_single_eq_prefix,augmentationProjection_nil]
      have hd : differential B (Finsupp.single [] a)=0 := by
        simp only [differential,LinearMap.sub_apply,front_single,frontBasis,
          internal_single,PaperVerification.ReducedBarBasis.differentialBasis,
          map_zero,smul_zero,sub_zero]
      rw [hd,map_zero,add_zero]
      change front B (positivePrefixMap B a (Finsupp.single [] 1))-
        internal B (positivePrefixMap B a (Finsupp.single [] 1))+
          ε a • Finsupp.single [] 1=Finsupp.single [] a
      rw [internal_positivePrefixMap,positiveMergeMap_nil,internal_single,
        PaperVerification.ReducedBarBasis.differentialBasis,map_zero,smul_zero,
        map_zero,sub_zero,sub_zero,front_positivePrefixMap_add_scalar ε B hunit hε]
      simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
    | cons i L =>
      rw [homotopy_single_eq_prefix,augmentationProjection_cons,add_zero]
      have hd : homotopy B (differential B (Finsupp.single (i::L) a))=
          ε a • Finsupp.single (i::L) 1+
            positiveMergeMap B a (Finsupp.single (i::L) 1)-
            positivePrefixMap B a
              (lift (PaperVerification.ReducedBarBasis.differentialBasis B (i::L))) := by
        change homotopy B (front B (Finsupp.single (i::L) a)-
          internal B (Finsupp.single (i::L) a))=_
        rw [map_sub,homotopy_front_cons ε B hunit hε,internal_single,homotopy_smul_lift]
      rw [hd]
      change (front B (positivePrefixMap B a (Finsupp.single (i::L) 1))-
        internal B (positivePrefixMap B a (Finsupp.single (i::L) 1)))+_=_
      rw [internal_positivePrefixMap,internal_single,one_smul]
      have h := front_positivePrefixMap_add_scalar ε B hunit hε a
        (Finsupp.single (i::L) (1 : A))
      have ha : a • (Finsupp.single (i::L) 1 : Words I A)=Finsupp.single (i::L) a := by
        simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
      rw [ha] at h
      calc
        _ = front B (positivePrefixMap B a (Finsupp.single (i::L) 1))+
            ε a • Finsupp.single (i::L) 1 := by abel
        _ = _ := h

end PaperVerification.AlternatingForms.BarFree
end
end
end TAF_LiteralSource_0252

section TAF_LiteralSource_0253
/- Original module: PaperVerification.AlternatingFormsBarLength -/


/-!
# Length grading and exactness of the normalized free bar construction

The length pieces are actual supported submodules of the word module. The
differential decreases length and the explicit contraction increases it.
This supplies cycle-to-boundary witnesses in every positive bar degree.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms.BarFree

open PaperVerification.AugmentedAlgebraBasis

variable {K A I : Type*} [CommRing K] [CommRing A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

def lengthPiece (I A : Type*) [CommRing A] (r : ℕ) :
    Submodule A (Words I A) :=
  Finsupp.supported A A {L | L.length=r}

theorem single_mem_lengthPiece (L : List I) (a : A) {r : ℕ} (hL : L.length=r) :
    Finsupp.single L a ∈ lengthPiece I A r :=
  Finsupp.single_mem_supported A a hL

theorem mem_lengthPiece_iff (z : Words I A) (r : ℕ) :
    z ∈ lengthPiece I A r ↔ ∀ L : List I,L.length≠r → z L=0 :=
  Finsupp.mem_supported' A z

theorem lengthPiece_eq_span (r : ℕ) :
    lengthPiece I A r=Submodule.span A
      ((fun L : List I ↦ Finsupp.single L (1 : A)) '' {L | L.length=r}) :=
  Finsupp.supported_eq_span_single A {L : List I | L.length=r}

instance lengthPiece_free (r : ℕ) : Module.Free A (lengthPiece I A r) :=
  Module.Free.of_basis ((Module.Basis.ofRepr (LinearEquiv.refl A _) :
      Module.Basis {L : List I | L.length=r} A ({L : List I | L.length=r} →₀ A)).map
    (Finsupp.supportedEquivFinsupp (M := A) (R := A) {L : List I | L.length=r}).symm)

theorem lift_apply (z : Words I K) (L : List I) :
    lift (A := A) z L=algebraMap K A (z L) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add z w hz hw => simp only [map_add,Finsupp.add_apply,hz,hw]
  | single T c =>
    by_cases h : T=L <;>
      simp [lift_single,Finsupp.single_apply,h,Algebra.smul_def]

theorem lift_mem_lengthPiece {r : ℕ} (z : Words I K) (hz : z∈lengthPiece I K r) :
    lift (A := A) z ∈ lengthPiece I A r := by
  rw [mem_lengthPiece_iff] at hz ⊢
  intro L hL
  rw [lift_apply,hz L hL,map_zero]

theorem prefix_mem_lengthPiece (i : I) {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A r) : prepend i z∈lengthPiece I A (r+1) := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r at hL
    rw [prefix_single]
    exact single_mem_lengthPiece _ _ (by simpa only [List.length_cons,hL])
  | zero => simpa only [map_zero] using (lengthPiece I A (r+1)).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I A (r+1)).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I A (r+1)).smul_mem a ih

theorem reduced_prefix_eq (i : I) :
    PaperVerification.ReducedBarBasis.prepend (K := K) i=prepend (A := K) i := by
  apply Finsupp.lhom_ext
  intro L c
  simp only [PaperVerification.ReducedBarBasis.prefix_single,prefix_single]

theorem appendTail_mem_lengthPiece (L : List I) (c : I →₀ K) :
    PaperVerification.ReducedBarBasis.appendTail L c∈lengthPiece I K (L.length+1) := by
  rw [PaperVerification.ReducedBarBasis.appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  exact (lengthPiece I K (L.length+1)).smul_mem _
    (single_mem_lengthPiece _ _ rfl)

theorem reducedDifferentialBasis_mem_lengthPiece (L : List I) :
    PaperVerification.ReducedBarBasis.differentialBasis B L∈
      lengthPiece I K (L.length-1) := by
  induction L with
  | nil =>
    simp only [PaperVerification.ReducedBarBasis.differentialBasis]
    exact Submodule.zero_mem _
  | cons i L ih =>
    cases L with
    | nil =>
      simp only [PaperVerification.ReducedBarBasis.differentialBasis,
        PaperVerification.ReducedBarBasis.merge_single,
        PaperVerification.ReducedBarBasis.mergeBasis,smul_zero,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons j L =>
      change PaperVerification.ReducedBarBasis.differentialBasis B (i::j::L)∈
        lengthPiece I K (L.length+1)
      rw [PaperVerification.ReducedBarBasis.differentialBasis]
      apply Submodule.sub_mem
      · rw [PaperVerification.ReducedBarBasis.merge_single,one_smul,
          PaperVerification.ReducedBarBasis.mergeBasis]
        exact appendTail_mem_lengthPiece L _
      · rw [reduced_prefix_eq]
        exact prefix_mem_lengthPiece i _
          (by simpa only [List.length_cons,Nat.add_sub_cancel] using ih)

theorem front_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : front B z∈lengthPiece I A r := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r+1 at hL
    cases L with
    | nil => simp only [List.length_nil] at hL; omega
    | cons i L =>
      rw [front_single,one_smul]
      exact single_mem_lengthPiece _ _ (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hL)
  | zero => simpa only [map_zero] using (lengthPiece I A r).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I A r).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I A r).smul_mem a ih

theorem internal_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : internal B z∈lengthPiece I A r := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r+1 at hL
    rw [internal_single,one_smul]
    have h := lift_mem_lengthPiece (A := A) _ (reducedDifferentialBasis_mem_lengthPiece B L)
    simpa only [hL,Nat.add_sub_cancel] using h
  | zero => simpa only [map_zero] using (lengthPiece I A r).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I A r).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I A r).smul_mem a ih

theorem differential_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : differential B z∈lengthPiece I A r :=
  (lengthPiece I A r).sub_mem (front_mem_lengthPiece B z hz)
    (internal_mem_lengthPiece B z hz)

theorem homotopy_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A r) : homotopy B z∈lengthPiece I A (r+1) := by
  classical
  rw [←Finsupp.sum_single z,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro L hL
  have hlen : L.length=r := hz hL
  rw [homotopy_single,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  exact (lengthPiece I A (r+1)).smul_of_tower_mem _
    (single_mem_lengthPiece _ _ (by simp only [List.length_cons,hlen]))

theorem augmentationProjection_eq_zero_of_positive {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : augmentationProjection ε z=0 := by
  have hzero : z []=0 := (mem_lengthPiece_iff z (r+1)).mp hz [] (by simp)
  simp only [augmentationProjection,LinearMap.comp_apply,LinearMap.smulRight_apply,
    Finsupp.lapply_apply,hzero,AlgHom.toLinearMap_apply,map_zero,zero_smul]

include hunit hε in
/-- Every positive-length cycle is a boundary of the explicitly constructed
next-length element. This is exactness of the actual differential. -/
theorem positive_cycle_is_boundary {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) (hd : differential B z=0) :
    ∃ y∈lengthPiece I A (r+2),differential B y=z := by
  refine ⟨homotopy B z,homotopy_mem_lengthPiece B z hz,?_⟩
  have h := contracting_identity ε B hunit hε z
  simpa only [hd,map_zero,augmentationProjection_eq_zero_of_positive ε z hz,add_zero] using h

end PaperVerification.AlternatingForms.BarFree
end
end
end TAF_LiteralSource_0253

section TAF_LiteralSource_0254
/- Original module: PaperVerification.AlternatingFormsBarResolution -/


/-!
# An actual projective normalized bar resolution

The terms are the free length pieces and the differential is the literal
normalized bar differential. Exactness is proved using the explicit contraction.
The augmentation module is the actual quotient by the augmentation ideal,
proved algebra-isomorphic to the coefficient ring.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.AlternatingForms.BarFree

open CategoryTheory CategoryTheory.Limits
open PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [CommRing K] [CommRing A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

def residueIdeal : Ideal A := RingHom.ker ε.toRingHom
abbrev Residue := A ⧸ residueIdeal ε

theorem augmentation_surjective : Function.Surjective ε := by
  intro c
  exact ⟨algebraMap K A c, ε.commutes c⟩

def residueEquivCoefficients : Residue ε ≃ₐ[K] K :=
  Ideal.quotientKerAlgEquivOfSurjective (augmentation_surjective ε)

def degreeDifferential (r : ℕ) :
    lengthPiece I A (r+1) →ₗ[A] lengthPiece I A r :=
  LinearMap.codRestrict _
    ((differential B).comp (lengthPiece I A (r+1)).subtype)
    (fun z ↦ differential_mem_lengthPiece B z.val z.property)

@[simp] theorem degreeDifferential_coe (r : ℕ) (z : lengthPiece I A (r+1)) :
    (degreeDifferential B r z : Words I A)=differential B z.val := rfl

include hunit hε in
theorem degreeDifferential_comp (r : ℕ) :
    (degreeDifferential B r).comp (degreeDifferential B (r+1))=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact differential_squared ε B hunit hε z.val

def complex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun r ↦ ModuleCat.of A (lengthPiece I A r))
    (fun r ↦ ModuleCat.ofHom (degreeDifferential B r))
    (fun r ↦ ModuleCat.hom_ext (degreeDifferential_comp ε B hunit hε r))

include hunit hε in
@[simp] theorem complex_X (r : ℕ) :
    (complex ε B hunit hε).X r=ModuleCat.of A (lengthPiece I A r) := rfl

include hunit hε in
@[simp] theorem complex_d (r : ℕ) :
    (complex ε B hunit hε).d (r+1) r=ModuleCat.ofHom (degreeDifferential B r) := by
  simp [complex]

/-- The degree-zero map is evaluation of the free coefficient modulo the
actual augmentation ideal. -/
def augmentationMap : lengthPiece I A 0 →ₗ[A] Residue ε :=
  (residueIdeal ε).mkQ.comp
    ((Finsupp.lapply []).comp (lengthPiece I A 0).subtype)

theorem length_zero_eq_single (z : Words I A) (hz : z∈lengthPiece I A 0) :
    z=Finsupp.single [] (z []) := by
  classical
  ext L
  by_cases hL : L=[]
  · subst L
    simp
  · have hlen : L.length≠0 := fun h => hL (List.length_eq_zero_iff.mp h)
    rw [(mem_lengthPiece_iff z 0).mp hz L hlen,Finsupp.single_eq_of_ne hL]

theorem differential_length_zero (z : Words I A) (hz : z∈lengthPiece I A 0) :
    differential B z=0 := by
  rw [length_zero_eq_single z hz]
  simp only [differential,LinearMap.sub_apply,front_single,frontBasis,internal_single,
    PaperVerification.ReducedBarBasis.differentialBasis,map_zero,smul_zero,sub_zero]

theorem augmentationMap_surjective : Function.Surjective (augmentationMap (I := I) ε) := by
  intro q
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨⟨Finsupp.single [] a,single_mem_lengthPiece _ _ rfl⟩,by
    simp [augmentationMap]⟩

include hunit hε in
/-- The augmentation kills the literal differential on every length-one word. -/
theorem augmentation_differential_zero (z : Words I A)
    (hz : z∈lengthPiece I A 1) :
    (residueIdeal ε).mkQ ((differential B z) [])=0 := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    obtain ⟨i,rfl⟩ := List.length_eq_one_iff.mp hL
    simp only [differential,LinearMap.sub_apply,front_single,frontBasis,internal_single,
      PaperVerification.ReducedBarBasis.differentialBasis,
      PaperVerification.ReducedBarBasis.merge_single,
      PaperVerification.ReducedBarBasis.mergeBasis,smul_zero,map_zero,sub_zero,one_smul,
      Finsupp.single_eq_same]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hε i
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add z w hz hw ihz ihw => simp only [map_add,Finsupp.add_apply,ihz,ihw,add_zero]
  | smul a z hz ih =>
    simp only [map_smul,Finsupp.smul_apply,ih,smul_zero]

include hunit hε in
theorem augmentationMap_differential :
    (augmentationMap (I := I) ε).comp (degreeDifferential B 0)=0 := by
  apply LinearMap.ext
  intro z
  exact augmentation_differential_zero ε B hunit hε z.val z.property

include hunit hε in
theorem degreeDifferential_exact (r : ℕ) :
    Function.Exact (degreeDifferential B (r+1)) (degreeDifferential B r) := by
  intro z
  constructor
  · intro hz
    have hd : differential B z.val=0 := congrArg Subtype.val hz
    obtain ⟨y,hy,hd⟩ := positive_cycle_is_boundary ε B hunit hε z.val z.property hd
    exact ⟨⟨y,hy⟩,Subtype.ext hd⟩
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    exact differential_squared ε B hunit hε y.val

include hunit hε in
theorem augmentationMap_exact :
    Function.Exact (degreeDifferential B 0) (augmentationMap (I := I) ε) := by
  intro z
  constructor
  · intro hz
    have he : ε (z.val [])=0 := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hp : augmentationProjection ε z.val=0 := by
      simp only [augmentationProjection,LinearMap.comp_apply,LinearMap.smulRight_apply,
        Finsupp.lapply_apply,AlgHom.toLinearMap_apply,he,zero_smul]
    refine ⟨⟨homotopy B z.val,homotopy_mem_lengthPiece B z.val z.property⟩,?_⟩
    apply Subtype.ext
    change differential B (homotopy B z.val)=z.val
    have h := contracting_identity ε B hunit hε z.val
    simpa only [differential_length_zero B z.val z.property,map_zero,hp,add_zero] using h
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun (augmentationMap_differential ε B hunit hε) y

include hunit hε in
theorem complex_exactAt_succ (r : ℕ) :
    (complex ε B hunit hε).ExactAt (r+1) := by
  rw [HomologicalComplex.exactAt_iff' _ ((r+1)+1) (r+1) r (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',
    complex,ChainComplex.of_d,ModuleCat.hom_ofHom]
  exact (LinearMap.exact_iff.mp (degreeDifferential_exact ε B hunit hε r)).symm

def augmentation :
    (complex ε B hunit hε).X 0 ⟶ ModuleCat.of A (Residue ε) :=
  ModuleCat.ofHom (augmentationMap ε)

include hunit hε in
theorem complex_d_augmentation :
    (complex ε B hunit hε).d 1 0 ≫ augmentation ε B hunit hε=0 := by
  apply ModuleCat.hom_ext
  exact augmentationMap_differential ε B hunit hε

include hunit hε in
theorem augmentation_exact :
    (ShortComplex.mk _ _ (complex_d_augmentation ε B hunit hε)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (degreeDifferential B 0)=LinearMap.ker (augmentationMap ε)
  exact (LinearMap.exact_iff.mp (augmentationMap_exact ε B hunit hε)).symm

instance augmentation_epi : Epi (augmentation ε B hunit hε) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentationMap_surjective ε)

/-- The actual normalized free bar resolution, with no exactness premise. -/
def resolution : ProjectiveResolution (ModuleCat.of A (Residue ε)) where
  complex := complex ε B hunit hε
  projective r := by
    change Projective (ModuleCat.of A (lengthPiece I A r))
    infer_instance
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨augmentation ε B hunit hε,complex_d_augmentation ε B hunit hε⟩
  quasiIso := ⟨fun r ↦ by
    cases r with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk _ _ (complex_d_augmentation ε B hunit hε)).Exact ∧
          Epi (augmentation ε B hunit hε)
        exact ⟨augmentation_exact ε B hunit hε,inferInstance⟩
      all_goals rfl
    | succ r =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt_succ ε B hunit hε r
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- Mathlib's actual derived tensor is computed by this free bar resolution. -/
def torIso (E : ModuleCat A) (r : ℕ) :
    (((Tor (ModuleCat A) r).obj E).obj (ModuleCat.of A (Residue ε))) ≅
      ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat A)).obj E).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (resolution ε B hunit hε).complex).homology r :=
  (resolution ε B hunit hε).isoLeftDerivedObj _ r

end PaperVerification.AlternatingForms.BarFree
end
end
end TAF_LiteralSource_0254

section TAF_LiteralSource_0255
/- Original module: PaperVerification.AlternatingFormsBarTensor -/


/-!
# The actual Tor complex and the normalized reduced bar complex

Tensoring the explicit free resolution with the augmentation residue kills
the first multiplication term. The surviving differential is exactly the
negative adjacent-product differential in the original positive basis.
The comparison is an isomorphism of actual chain complexes.
-/

@[expose] public section
noncomputable section
open scoped BigOperators TensorProduct

namespace PaperVerification.AlternatingForms.BarFree

open CategoryTheory CategoryTheory.Limits
open PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [CommRing K] [CommRing A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

def specialize : Words I A →ₗ[K] Words I K :=
  Finsupp.mapRange.linearMap ε.toLinearMap

@[simp] theorem specialize_apply (z : Words I A) (L : List I) :
    specialize ε z L=ε (z L) := rfl

@[simp] theorem specialize_single (L : List I) (a : A) :
    specialize ε (Finsupp.single L a)=Finsupp.single L (ε a) := by
  classical
  ext T
  by_cases h : L=T <;> simp [specialize_apply,Finsupp.single_apply,h]

theorem specialize_smul (a : A) (z : Words I A) :
    specialize ε (a • z)=ε a • specialize ε z := by
  ext L
  simp only [specialize_apply,Finsupp.smul_apply,smul_eq_mul,map_mul]

theorem specialize_lift (z : Words I K) : specialize ε (lift z)=z := by
  ext L
  rw [specialize_apply,lift_apply,ε.commutes]
  rfl

include hε in
theorem specialize_front (z : Words I A) : specialize ε (front B z)=0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw,add_zero]
  | single L a =>
    cases L with
    | nil => simp only [front_single,frontBasis,smul_zero,map_zero]
    | cons i L =>
      rw [front_single,specialize_smul]
      change ε a • specialize ε (Finsupp.single L (B (some i)))=0
      rw [specialize_single,hε,Finsupp.single_zero,smul_zero]

theorem specialize_internal (z : Words I A) :
    specialize ε (internal B z)=
      PaperVerification.ReducedBarBasis.differential B (specialize ε z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw]
  | single L a =>
    rw [internal_single,specialize_smul,specialize_lift,specialize_single,
      PaperVerification.ReducedBarBasis.differential_single]

include hε in
theorem specialize_differential (z : Words I A) :
    specialize ε (differential B z)=
      -PaperVerification.ReducedBarBasis.differential B (specialize ε z) := by
  change specialize ε (front B z-internal B z)=_
  rw [map_sub,specialize_front ε B hε,specialize_internal,zero_sub]

theorem specialize_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A r) : specialize ε z∈lengthPiece I K r := by
  rw [mem_lengthPiece_iff] at hz ⊢
  intro L hL
  rw [specialize_apply,hz L hL,map_zero]

def specializePiece (r : ℕ) : lengthPiece I A r →ₗ[K] lengthPiece I K r :=
  LinearMap.codRestrict _
    ((specialize ε).comp ((lengthPiece I A r).subtype.restrictScalars K))
    (fun z ↦ specialize_mem_lengthPiece ε z.val z.property)

theorem reducedDifferential_mem_lengthPiece {r : ℕ} (z : Words I K)
    (hz : z∈lengthPiece I K (r+1)) :
    PaperVerification.ReducedBarBasis.differential B z∈lengthPiece I K r := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r+1 at hL
    rw [PaperVerification.ReducedBarBasis.differential_single,one_smul]
    simpa only [hL,Nat.add_sub_cancel] using reducedDifferentialBasis_mem_lengthPiece B L
  | zero => simpa only [map_zero] using (lengthPiece I K r).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I K r).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I K r).smul_mem a ih

def reducedDegreeDifferential (r : ℕ) :
    lengthPiece I K (r+1) →ₗ[K] lengthPiece I K r :=
  LinearMap.codRestrict _
    ((PaperVerification.ReducedBarBasis.differential B).comp
      (lengthPiece I K (r+1)).subtype)
    (fun z ↦ reducedDifferential_mem_lengthPiece B z.val z.property)

/-- The literal pointwise negative of the actual adjacent-product map.
Its formula is stated explicitly, so the construction does not depend
on inferring a second additive-group dictionary for a space of maps. -/
def negativeReducedDegreeDifferential (r : ℕ) :
    lengthPiece I K (r+1) →ₗ[K] lengthPiece I K r where
  toFun z := ⟨-(PaperVerification.ReducedBarBasis.differential B z.val),
    (lengthPiece I K r).neg_mem
      (reducedDifferential_mem_lengthPiece B z.val z.property)⟩
  map_add' x y := by
    apply Subtype.ext
    change -(PaperVerification.ReducedBarBasis.differential B (x.val+y.val))=
      -(PaperVerification.ReducedBarBasis.differential B x.val)+
        -(PaperVerification.ReducedBarBasis.differential B y.val)
    rw [map_add,neg_add]
  map_smul' c z := by
    apply Subtype.ext
    change -(PaperVerification.ReducedBarBasis.differential B (c • z.val))=
      c • -(PaperVerification.ReducedBarBasis.differential B z.val)
    rw [map_smul,smul_neg]

@[simp] theorem negativeReducedDegreeDifferential_apply (r : ℕ)
    (z : lengthPiece I K (r+1)) :
    negativeReducedDegreeDifferential B r z=-(reducedDegreeDifferential B r z) := rfl

include hunit hε in
theorem negativeReducedDifferential_comp (r : ℕ) :
    (negativeReducedDegreeDifferential B r).comp (negativeReducedDegreeDifferential B (r+1))=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change -PaperVerification.ReducedBarBasis.differential B
    (-PaperVerification.ReducedBarBasis.differential B z.val)=0
  rw [map_neg,neg_neg,PaperVerification.ReducedBarBasis.differential_squared ε B hunit hε]

def reducedComplex : ChainComplex (ModuleCat K) ℕ :=
  ChainComplex.of (fun r ↦ ModuleCat.of K (lengthPiece I K r))
    (fun r ↦ ModuleCat.ofHom (negativeReducedDegreeDifferential B r))
    (fun r ↦ ModuleCat.hom_ext (negativeReducedDifferential_comp ε B hunit hε r))

include hunit hε in
@[simp] theorem reducedComplex_d (r : ℕ) :
    (reducedComplex ε B hunit hε).d (r+1) r=
      ModuleCat.ofHom (negativeReducedDegreeDifferential B r) := by
  simp [reducedComplex]

def tensorComplex : ChainComplex (ModuleCat A) ℕ :=
  (((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat A)).obj
    (ModuleCat.of A (Residue ε))).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (resolution ε B hunit hε).complex

def tensorComplexOverK : ChainComplex (ModuleCat K) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap K A)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (tensorComplex ε B hunit hε)

include hunit hε in
/-- The tensor differential on a pure tensor, reduced through the actual
functorial complex before any comparison of coefficient bases. -/
@[simp] theorem tensorComplexOverK_d_tmul (r : ℕ) (q : Residue ε)
    (z : lengthPiece I A (r+1)) :
    (tensorComplexOverK ε B hunit hε).d (r+1) r (q ⊗ₜ[A] z)=
      q ⊗ₜ[A] degreeDifferential B r z := by
  simp only [tensorComplexOverK,tensorComplex,Functor.mapHomologicalComplex_obj_d,
    resolution,complex_d,ModuleCat.restrictScalars.map_apply,
    CategoryTheory.MonoidalCategory.curriedTensor_obj_map,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,ModuleCat.ofHom_apply]
  rfl

def tensorTermAlgebraEquiv (r : ℕ) :
    (Residue ε ⊗[A] lengthPiece I A r) ≃ₗ[A]
      ({L : List I // L.length=r} →₀ Residue ε) := by
  classical
  exact (TensorProduct.congr (LinearEquiv.refl A (Residue ε))
    (Finsupp.supportedEquivFinsupp (M := A) (R := A) {L : List I | L.length=r})).trans
      (TensorProduct.finsuppScalarRight A A (Residue ε) {L : List I // L.length=r})

set_option backward.isDefEq.respectTransparency false in
def restrictTensorDomainEquiv {X Y : Type u} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] [Module K Y] [IsScalarTower K A Y]
    (e : X ≃ₗ[A] Y) :
    ((ModuleCat.restrictScalars (algebraMap K A)).obj (ModuleCat.of A X)) ≃ₗ[K] Y where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' c x := by
    exact (e.map_smul (algebraMap K A c) (show X from x)).trans
      (algebraMap_smul A c (e (show X from x)))

def tensorTermEquiv (r : ℕ) :
    (tensorComplexOverK ε B hunit hε).X r ≃ₗ[K] lengthPiece I K r :=
  (restrictTensorDomainEquiv (tensorTermAlgebraEquiv (I := I) ε r)).trans
    ((Finsupp.mapRange.linearEquiv (residueEquivCoefficients ε).toLinearEquiv).trans
      (Finsupp.supportedEquivFinsupp (M := K) (R := K) {L : List I | L.length=r}).symm)

@[simp] theorem residueEquivCoefficients_mk (a : A) :
    residueEquivCoefficients ε (Ideal.Quotient.mk (residueIdeal ε) a)=ε a :=
  Ideal.quotientKerAlgEquivOfSurjective_mk (augmentation_surjective ε) a

theorem residueEquivCoefficients_smul (a : A) (q : Residue ε) :
    residueEquivCoefficients ε (a • q)=ε a * residueEquivCoefficients ε q := by
  change residueEquivCoefficients ε
    (Ideal.Quotient.mk (residueIdeal ε) a*q)=_
  rw [map_mul,residueEquivCoefficients_mk]

set_option backward.isDefEq.respectTransparency false in
include hunit hε in
theorem tensorTermEquiv_coordinate (r : ℕ) (q : Residue ε)
    (z : lengthPiece I A r) (L : {L : List I // L.length=r}) :
    (Finsupp.supportedEquivFinsupp (M := K) (R := K) {L : List I | L.length=r})
      (tensorTermEquiv ε B hunit hε r (q ⊗ₜ[A] z)) L=
        ε (z.val L.val) * residueEquivCoefficients ε q := by
  classical
  simp only [tensorTermEquiv,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
    Finsupp.mapRange.linearEquiv_apply,Finsupp.mapRange_apply]
  erw [LinearEquiv.apply_symm_apply]
  simp only [Finsupp.mapRange_apply]
  change residueEquivCoefficients ε (tensorTermAlgebraEquiv ε r (q ⊗ₜ[A] z) L)=_
  have h : tensorTermAlgebraEquiv ε r (q ⊗ₜ[A] z) L=z.val L.val • q := by
    exact TensorProduct.finsuppScalarRight_apply_tmul_apply (R := A) (S := A) q
      ((Finsupp.supportedEquivFinsupp (M := A) (R := A)
        {L : List I | L.length=r})
          (show Finsupp.supported A A {L : List I | L.length=r} from z)) L
  rw [h,residueEquivCoefficients_smul]

set_option backward.isDefEq.respectTransparency false in
include hunit hε in
theorem tensorTermEquiv_tmul (r : ℕ) (q : Residue ε) (z : lengthPiece I A r) :
    tensorTermEquiv ε B hunit hε r (q ⊗ₜ[A] z)=
      residueEquivCoefficients ε q • specializePiece ε r z := by
  apply (Finsupp.supportedEquivFinsupp (M := K) (R := K)
    {L : List I | L.length=r}).injective
  ext L
  rw [tensorTermEquiv_coordinate]
  change ε (z.val L.val)*residueEquivCoefficients ε q=
    residueEquivCoefficients ε q*ε (z.val L.val)
  exact mul_comm _ _

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
include hunit hε in
theorem tensorTermEquiv_comm (r : ℕ) :
    (tensorTermEquiv ε B hunit hε (r+1)).toModuleIso.hom ≫
        (reducedComplex ε B hunit hε).d (r+1) r =
      (tensorComplexOverK ε B hunit hε).d (r+1) r ≫
        (tensorTermEquiv ε B hunit hε r).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro q x
    simp only [ModuleCat.hom_comp,LinearMap.comp_apply,ModuleCat.comp_apply]
    rw [tensorComplexOverK_d_tmul,reducedComplex_d]
    change -(reducedDegreeDifferential B r
        (tensorTermEquiv ε B hunit hε (r+1) (q ⊗ₜ[A] x)))=
      tensorTermEquiv ε B hunit hε r (q ⊗ₜ[A] degreeDifferential B r x)
    rw [tensorTermEquiv_tmul,tensorTermEquiv_tmul,map_smul]
    apply Subtype.ext
    change -(residueEquivCoefficients ε q •
      PaperVerification.ReducedBarBasis.differential B (specialize ε x.val))=
      residueEquivCoefficients ε q • specialize ε (differential B x.val)
    rw [specialize_differential ε B hε,smul_neg]
  · intro x y hx hy
    simp only [ModuleCat.comp_apply,ModuleCat.hom_comp,LinearMap.comp_apply,map_add] at hx hy ⊢
    exact congrArg₂ (· + ·) hx hy

def tensorComplexIso : tensorComplexOverK ε B hunit hε ≅ reducedComplex ε B hunit hε :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦ (tensorTermEquiv ε B hunit hε r).toModuleIso) (by
      intro i j hij
      change j+1=i at hij
      subst i
      exact tensorTermEquiv_comm ε B hunit hε j)

def tensorHomologyRestrictionIso (r : ℕ) :
    (tensorComplexOverK ε B hunit hε).homology r ≅
      (ModuleCat.restrictScalars (algebraMap K A)).obj
        ((tensorComplex ε B hunit hε).homology r) := by
  change (((tensorComplex ε B hunit hε).sc r).map
      (ModuleCat.restrictScalars (algebraMap K A))).homology ≅
    (ModuleCat.restrictScalars (algebraMap K A)).obj
      ((tensorComplex ε B hunit hε).sc r).homology
  exact ((tensorComplex ε B hunit hε).sc r).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap K A))

def TorOverCoefficients (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K A)).obj
    (((Tor (ModuleCat A) r).obj (ModuleCat.of A (Residue ε))).obj
      (ModuleCat.of A (Residue ε)))

/-- The normalized reduced bar homology is identified with actual Tor. -/
def reducedBarTorIso (r : ℕ) :
    TorOverCoefficients ε r ≅ (reducedComplex ε B hunit hε).homology r :=
  (ModuleCat.restrictScalars (algebraMap K A)).mapIso
      (torIso ε B hunit hε (ModuleCat.of A (Residue ε)) r) ≪≫
    (tensorHomologyRestrictionIso ε B hunit hε r).symm ≪≫
    HomologicalComplex.homologyMapIso (tensorComplexIso ε B hunit hε) r

end PaperVerification.AlternatingForms.BarFree
end
end
end TAF_LiteralSource_0255

section TAF_LiteralSource_0256
/- Original module: PaperVerification.AlternatingFormsOddBar -/


/-!
# The actual augmentation and normalized bar complex of the odd Plücker ring

The augmentation sends every positive-degree Plücker coordinate to zero.
Its kernel is the actual augmentation ideal. The unit-plus-positive basis
is a reindexing of the previously constructed standard-product basis;
neither the multiplication nor its coefficients are replaced by a model.
The final comparison computes ordinary Mathlib Tor for this actual ring.
Off-diagonal vanishing still requires the PBW filtration argument.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial CategoryTheory
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K]

def isotropicAugmentation (t n : ℕ) (forms : Fin 2 → StrictPairs n → K) :
    (MvPolynomial (PluckerIndex (t+2) n) K⧸isotropicPluckerIdeal forms) →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (matrixMinorEvaluation (0 : Matrix (Fin (t+2)) (Fin n) K))
    (by
      change isotropicPluckerIdeal (t := t) forms ≤
        RingHom.ker (matrixMinorEvaluation (0 : Matrix (Fin (t+2)) (Fin n) K)).toRingHom
      apply sup_le
      · exact matrixPluckerIdeal_le_matrixMinorKernel _
      · apply Ideal.span_le.mpr
        rintro _ ⟨⟨l,J⟩,rfl⟩
        exact matrixMinorEvaluation_isotropy_eq_zero (forms l) _
          (by intro i j; simp [alternatingRowPair]) J)

@[simp] theorem isotropicAugmentation_mk (t n : ℕ)
    (forms : Fin 2 → StrictPairs n → K)
    (p : MvPolynomial (PluckerIndex (t+2) n) K) :
    isotropicAugmentation t n forms (Ideal.Quotient.mk _ p)=
      matrixMinorEvaluation (0 : Matrix (Fin (t+2)) (Fin n) K) p := rfl

@[simp] theorem isotropicAugmentation_X (t n : ℕ)
    (forms : Fin 2 → StrictPairs n → K) (I : PluckerIndex (t+2) n) :
    isotropicAugmentation t n forms (Ideal.Quotient.mk _ (X I))=0 := by
  rw [isotropicAugmentation_mk]
  simp only [matrixMinorEvaluation,aeval_X]
  change (0 : Matrix (Fin (t+2)) (Fin (t+2)) K).det = 0
  exact Matrix.det_zero

variable (k t : ℕ) (hs : t+2≤k+1)

def oddEmptyStandardIndex : OddStandardIndex k t hs :=
  ⟨0,⟨Fin.elim0,by
    refine ⟨?_,?_,?_⟩
    · intro j; exact Fin.elim0 j
    · intro j; exact Fin.elim0 j
    · intro i; exact Fin.elim0 i⟩⟩

theorem oddStandardIndex_eq_empty_of_degree_zero (C : OddStandardIndex k t hs)
    (hC : C.1=0) : C=oddEmptyStandardIndex k t hs := by
  rcases C with ⟨r,C⟩
  dsimp only at hC
  subst r
  congr 1
  apply Subtype.ext
  exact funext (fun i => Fin.elim0 i)

theorem oddStandardIndex_degree_positive (C : OddStandardIndex k t hs)
    (hC : C≠oddEmptyStandardIndex k t hs) : 0<C.1 := by
  by_contra h
  exact hC (oddStandardIndex_eq_empty_of_degree_zero k t hs C (by omega))

def OddPositiveStandardIndex (K : Type u) :=
  ULift.{u} {C : OddStandardIndex k t hs // C≠oddEmptyStandardIndex k t hs}

def oddOptionStandardEquiv :
    Option (OddPositiveStandardIndex (K := K) k t hs) ≃ OddStandardIndex k t hs := by
  classical
  exact (Equiv.optionCongr Equiv.ulift).trans
    (Equiv.optionSubtypeNe (oddEmptyStandardIndex k t hs))

def oddAugmentedBasis :
    Module.Basis (Option (OddPositiveStandardIndex (K := K) k t hs)) K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) :=
  (oddPluckerStandardBasis k t hs).reindex (oddOptionStandardEquiv (K := K) k t hs).symm

@[simp] theorem oddAugmentedBasis_none :
    oddAugmentedBasis (K := K) k t hs none=1 := by
  rw [oddAugmentedBasis,Module.Basis.reindex_apply,Equiv.symm_symm]
  change oddPluckerStandardBasis (K := K) k t hs (oddEmptyStandardIndex k t hs)=1
  rw [oddPluckerStandardBasis_apply]
  simp [oddStandardRepresentative,chainPluckerProduct,oddEmptyStandardIndex]
  exact Finset.prod_eq_one (fun i _ => Fin.elim0 i)

@[simp] theorem oddAugmentedBasis_some (C : OddPositiveStandardIndex (K := K) k t hs) :
    oddAugmentedBasis (K := K) k t hs (some C)=
      oddPluckerStandardBasis k t hs C.down.val := by
  rw [oddAugmentedBasis,Module.Basis.reindex_apply,Equiv.symm_symm]
  rfl

@[expose]
def oddAugmentation :=
  isotropicAugmentation (K := K) t (2*k+1) (oddPluckerForms k)

theorem oddAugmentation_positive (C : OddPositiveStandardIndex (K := K) k t hs) :
    oddAugmentation (K := K) k t (oddAugmentedBasis k t hs (some C))=0 := by
  classical
  rw [oddAugmentedBasis_some,oddPluckerStandardBasis_apply]
  change isotropicAugmentation t (2*k+1) (oddPluckerForms k)
    (Ideal.Quotient.mk _ (chainPluckerProduct _ _ C.down.val.2))=0
  simp only [chainPluckerProduct,map_prod]
  have hpos := oddStandardIndex_degree_positive k t hs C.down.val C.down.property
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0,hpos⟩ : Fin C.down.val.1))
    (isotropicAugmentation_X t (2*k+1) (oddPluckerForms k) _)

/-- This is the internal degree of the actual positive standard product. -/
def oddPositiveDegree (C : OddPositiveStandardIndex (K := K) k t hs) : ℕ :=
  C.down.val.1

theorem oddPositiveDegree_pos (C : OddPositiveStandardIndex (K := K) k t hs) :
    0<oddPositiveDegree (K := K) k t hs C :=
  oddStandardIndex_degree_positive k t hs C.down.val C.down.property

theorem oddAugmentedBasis_homogeneous (C : OddPositiveStandardIndex (K := K) k t hs) :
    oddAugmentedBasis (K := K) k t hs (some C)∈
      oddPluckerDegree k t (oddPositiveDegree (K := K) k t hs C) := by
  rw [oddAugmentedBasis_some]
  exact oddPluckerStandardBasis_mem_degree k t hs C.down.val

/-- The residue, tensor functor, and homology here are the genuine ones
for the original isotropic Plücker quotient. This comparison alone does
not assert Koszulness. -/
def oddNormalizedBarTorIso (r : ℕ) :
    BarFree.TorOverCoefficients (oddAugmentation (K := K) k t) r ≅
      (BarFree.reducedComplex (oddAugmentation (K := K) k t)
        (oddAugmentedBasis k t hs) (oddAugmentedBasis_none k t hs)
        (oddAugmentation_positive k t hs)).homology r :=
  BarFree.reducedBarTorIso (oddAugmentation k t) (oddAugmentedBasis k t hs)
    (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs) r

end PaperVerification.AlternatingForms

end
end
end TAF_LiteralSource_0256

section TAF_LiteralSource_0257
/- Original module: PaperVerification.AlternatingFormsPBWNormalForm -/


/-!
# Bounds for every actual PBW product

The previously proved quadratic Groebner basis controls arbitrary products,
not only pairs of generators. The normal form used here is the actual
coordinate expansion in the original odd Plucker quotient. Its support
and degree bounds therefore apply to the actual reduced bar differential.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators MonomialOrder
open Hibi

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "P" => MvPolynomial (IntervalIndex α β) K
local notation "𝔅" => oddPluckerStandardBasis (K := K) k t hs

theorem goodChainExponent_support (C : OddStandardIndex k t hs)
    (I : IntervalIndex α β) (hI : I∈(goodChainExponent k t hs C).support) :
    ∃ j : Fin C.1,intervalIndexOfChain α β C.2 j=I := by
  classical
  by_contra h
  apply Finsupp.mem_support_iff.mp hI
  change (Finsupp.applyAddHom I)
    (∑ j : Fin C.1,Finsupp.single (intervalIndexOfChain α β C.2 j) 1)=0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finsupp.single_eq_of_ne
  intro he
  exact h ⟨j,he.symm⟩

theorem goodChainExponent_normal (C : OddStandardIndex k t hs) :
    NormalMonomial α β (goodChainExponent k t hs C) := by
  intro I hI J hJ
  obtain ⟨i,rfl⟩ := goodChainExponent_support k t hs C I hI
  obtain ⟨j,rfl⟩ := goodChainExponent_support k t hs C J hJ
  rcases le_total i j with hij | hji
  · exact Or.inl (C.2.property.2.2 hij)
  · exact Or.inr (C.2.property.2.2 hji)

theorem goodChainExponent_injective :
    Function.Injective (goodChainExponent k t hs) := by
  intro C D h
  apply (oddPluckerStandardBasis (K := ℚ) k t hs).injective
  rw [←oddGoodMap_standardPolynomial k t hs C,
    ←oddGoodMap_standardPolynomial k t hs D,
    standardPolynomial_eq_monomial,standardPolynomial_eq_monomial,h]

theorem oddGoodRepresentative_support
    (q : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
    (a : IntervalIndex α β →₀ ℕ)
    (ha : a∈(oddGoodRepresentative k t hs q).support) :
    ∃ C : OddStandardIndex k t hs,((𝔅).repr q) C≠0 ∧ a=goodChainExponent k t hs C := by
  classical
  have h := mem_support_iff.mp ha
  rw [oddGoodRepresentative] at h
  simp only [Finsupp.sum,coeff_sum] at h
  obtain ⟨C,hC,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨C,Finsupp.mem_support_iff.mp hC,?_⟩
  by_contra hne
  apply hterm
  simp only [coeff_smul,standardPolynomial_eq_monomial,coeff_monomial,
    if_neg (Ne.symm hne),smul_zero]

theorem oddGoodNormalForm_normal (p : P) :
    ∀ a∈(oddGoodNormalForm k t hs p).support,NormalMonomial α β a := by
  intro a ha
  obtain ⟨C,hC,rfl⟩ := oddGoodRepresentative_support k t hs _ a ha
  exact goodChainExponent_normal k t hs C

theorem oddGoodRepresentative_coeff
    (q : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
    (C : OddStandardIndex k t hs) :
    (oddGoodRepresentative k t hs q).coeff (goodChainExponent k t hs C)=((𝔅).repr q) C := by
  classical
  simp only [oddGoodRepresentative,Finsupp.sum,coeff_sum,coeff_smul,
    standardPolynomial_eq_monomial,coeff_monomial,smul_eq_mul]
  rw [Finset.sum_eq_single C]
  · simp
  · intro D hD hDC
    have hne : goodChainExponent k t hs D≠goodChainExponent k t hs C :=
      fun h ↦ hDC (goodChainExponent_injective k t hs h)
    simp [hne]
  · intro hC
    simp [Finsupp.notMem_support_iff.mp hC]

theorem oddGoodNormalForm_eq_of_normal (p r : P)
    (hr : ∀ a∈r.support,NormalMonomial α β a)
    (he : oddGoodMap k t hs p=oddGoodMap k t hs r) :
    oddGoodNormalForm k t hs p=r := by
  classical
  apply sub_eq_zero.mp
  apply oddGood_normal_polynomial_eq_zero k t hs
    (oddGoodNormalForm k t hs p-r)
  · intro a ha
    rcases Finset.mem_union.mp (support_sub _ _ _ ha) with ha | ha
    · exact oddGoodNormalForm_normal k t hs p a ha
    · exact hr a ha
  · rw [map_sub,oddGoodMap_normalForm,he,sub_self]

theorem oddGoodNormalForm_isRemainder (m : MonomialOrder (IntervalIndex α β)) (p : P) :
    (oddGoodOrder k t hs m).IsRemainder p (oddQuadraticSet k t hs)
      (oddGoodNormalForm k t hs p) := by
  obtain ⟨r,hr⟩ := (oddGoodOrder k t hs m).exists_isRemainder (B := oddQuadraticSet (K := K) k t hs)
    (fun b hb hb0 ↦ by
      obtain ⟨I,J,h,rfl⟩ := hb
      rw [oddQuadraticRelation_leadingCoeff k t hs m I J h]
      exact isUnit_one) p
  have hpr : p-r∈oddGoodIdeal (K := K) k t hs :=
    Ideal.span_le.mpr (odd_good_quadratic_isGroebnerBasis (K := K) k t hs m).subset
      hr.sub_mem_span
  have he : oddGoodMap k t hs p=oddGoodMap k t hs r := by
    change oddGoodMap k t hs (p-r)=0 at hpr
    rw [map_sub,sub_eq_zero] at hpr
    exact hpr
  rw [oddGoodNormalForm_eq_of_normal k t hs p r
    (odd_remainder_normal_support k t hs m p r hr) he]
  exact hr

/-- The degree bound follows from the actual ideal and the leading-term
criterion; no abstract multiplicative filtration hypothesis is assumed. -/
theorem oddGoodNormalForm_degree_le (m : MonomialOrder (IntervalIndex α β)) (p : P) :
    (oddGoodOrder k t hs m).degree (oddGoodNormalForm k t hs p)
      ≼[oddGoodOrder k t hs m] (oddGoodOrder k t hs m).degree p := by
  let M := oddGoodOrder k t hs m
  let r := oddGoodNormalForm (K := K) k t hs p
  have hr := oddGoodNormalForm_isRemainder k t hs m p
  by_contra h
  have hlt : M.degree p ≺[M] M.degree r := lt_of_not_ge h
  have hr0 : r≠0 := by
    intro hz
    rw [hz,M.degree_zero,map_zero,←M.bot_eq_zero] at hlt
    exact not_lt_of_ge bot_le hlt
  have hrp0 : r-p≠0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    rw [he] at hlt
    exact lt_irrefl _ hlt
  have hrp : r-p∈oddGoodIdeal (K := K) k t hs := by
    change oddGoodMap k t hs (r-p)=0
    rw [map_sub,oddGoodMap_normalForm,sub_self]
  obtain ⟨q,hq,hq0,hqd⟩ :=
    (odd_good_quadratic_isGroebnerBasis (K := K) k t hs m).exists_degree_le_degree hrp hrp0
  rw [M.degree_sub_of_lt hlt] at hqd
  exact hr.not_degree_le (M.degree_mem_support hr0) hq hq0 hqd

theorem oddGoodNormalForm_monomial_term_le (m : MonomialOrder (IntervalIndex α β))
    (a b : IntervalIndex α β →₀ ℕ)
    (hb : b∈(oddGoodNormalForm (K := K) k t hs (monomial a 1)).support) :
    b ≼[oddGoodOrder k t hs m] a := by
  classical
  have h := (oddGoodOrder k t hs m).le_degree hb
  have h' := oddGoodNormalForm_degree_le k t hs m (monomial a (1 : K))
  rw [MonomialOrder.degree_monomial,if_neg (one_ne_zero : (1 : K) ≠ 0)] at h'
  exact h.trans h'

theorem oddGoodNormalForm_nonnormal_term_lt (m : MonomialOrder (IntervalIndex α β))
    (a b : IntervalIndex α β →₀ ℕ) (ha : ¬NormalMonomial α β a)
    (hb : b∈(oddGoodNormalForm (K := K) k t hs (monomial a 1)).support) :
    b ≺[oddGoodOrder k t hs m] a := by
  apply lt_of_le_of_ne (oddGoodNormalForm_monomial_term_le k t hs m a b hb)
  intro he
  apply ha
  have hab : b=a := (oddGoodOrder k t hs m).toSyn.injective he
  exact hab ▸ oddGoodNormalForm_normal k t hs (monomial a (1 : K)) b hb

theorem oddGoodNormalForm_normal_monomial (a : IntervalIndex α β →₀ ℕ)
    (ha : NormalMonomial α β a) :
    oddGoodNormalForm (K := K) k t hs (monomial a 1)=monomial a 1 := by
  apply oddGoodNormalForm_eq_of_normal k t hs _ _ ?_ rfl
  intro b hb
  have hab : b=a := Finset.mem_singleton.mp (support_monomial_subset hb)
  exact hab.symm ▸ ha

end PaperVerification.AlternatingForms

end
end
end TAF_LiteralSource_0257

section TAF_LiteralSource_0258
/- Original module: PaperVerification.AlternatingFormsBarCompositions -/


/-!
# Actual bar factorizations and their full boundary sets

A factorization is a list of nonempty lists whose literal concatenation is
the original word. The equivalence with compositions records the actual
block lengths and is inverse to splitting the original word. Endpoints
are retained as mandatory boundaries: r bar factors give r+1 boundaries.
This convention makes the exterior contraction sign agree with the
negative normalized bar differential after tensoring the free resolution.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

variable {α : Type*}

def Factorization (W : List α) :=
  {L : List (List α) // L.flatten=W ∧ ∀ T∈L,0<T.length}

def factorizationComposition (W : List α) (L : Factorization W) :
    Composition W.length where
  blocks := L.val.map List.length
  blocks_pos := by
    intro n hn
    obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hn
    exact L.property.2 T hT
  blocks_sum := by
    rw [←List.length_flatten,L.property.1]

def splitFactorization (W : List α) (c : Composition W.length) : Factorization W :=
  ⟨W.splitWrtComposition c,List.flatten_splitWrtComposition W c,
    fun T hT ↦ List.length_pos_of_mem_splitWrtComposition hT⟩

@[simp] theorem composition_splitFactorization (W : List α) (c : Composition W.length) :
    factorizationComposition W (splitFactorization W c)=c := by
  apply Composition.ext
  exact List.map_length_splitWrtComposition W c

@[simp] theorem split_compositionFactorization (W : List α) (L : Factorization W) :
    splitFactorization W (factorizationComposition W L)=L := by
  rcases L with ⟨L,hL,hpos⟩
  subst W
  apply Subtype.ext
  exact List.splitWrtComposition_flatten L
    (factorizationComposition L.flatten ⟨L,rfl,hpos⟩) rfl

def factorizationCompositionEquiv (W : List α) :
    Factorization W ≃ Composition W.length where
  toFun := factorizationComposition W
  invFun := splitFactorization W
  left_inv := split_compositionFactorization W
  right_inv := composition_splitFactorization W

def factorizationBoundaryEquiv (W : List α) :
    Factorization W ≃ CompositionAsSet W.length :=
  (factorizationCompositionEquiv W).trans (compositionEquiv W.length)

def boundaries (W : List α) (L : Factorization W) : Finset (Fin (W.length+1)) :=
  (factorizationComposition W L).boundaries

@[simp] theorem boundaries_card (W : List α) (L : Factorization W) :
    (boundaries W L).card=L.val.length+1 := by
  simpa only [boundaries,Composition.length,factorizationComposition,List.length_map] using
    (factorizationComposition W L).card_boundaries_eq_succ_length

theorem zero_mem_boundaries (W : List α) (L : Factorization W) :
    (0 : Fin (W.length+1))∈boundaries W L :=
  (factorizationComposition W L).toCompositionAsSet.zero_mem

theorem last_mem_boundaries (W : List α) (L : Factorization W) :
    Fin.last W.length∈boundaries W L :=
  (factorizationComposition W L).toCompositionAsSet.getLast_mem

theorem boundaries_injective (W : List α) :
    Function.Injective (boundaries W) := by
  intro L M h
  apply (factorizationBoundaryEquiv W).injective
  apply CompositionAsSet.ext
  exact h

/-- Every cut set with both endpoints is realized by a unique actual
factorization of the original word. -/
theorem exists_unique_factorization (W : List α) (S : Finset (Fin (W.length+1)))
    (h0 : (0 : Fin (W.length+1))∈S) (hN : Fin.last W.length∈S) :
    ∃! L : Factorization W,boundaries W L=S := by
  let c : CompositionAsSet W.length := ⟨S,h0,hN⟩
  refine ⟨(factorizationBoundaryEquiv W).symm c,?_,?_⟩
  · have h := (factorizationBoundaryEquiv W).apply_symm_apply c
    exact congrArg CompositionAsSet.boundaries h
  · intro L hL
    apply boundaries_injective W
    rw [hL]
    exact (congrArg CompositionAsSet.boundaries
      ((factorizationBoundaryEquiv W).apply_symm_apply c)).symm

/-- An interior position fails to be a boundary precisely when it lies
strictly inside one of the actual blocks. -/
theorem not_mem_boundaries_iff {n : ℕ} (c : Composition n) (j : Fin (n+1))
    (hj0 : 0<j.val) (hjn : j.val<n) :
    j∉c.boundaries ↔ ∃ i : Fin c.length,
      c.sizeUpTo i.val<j.val ∧ j.val<c.sizeUpTo (i.val+1) := by
  constructor
  · intro hj
    let k : Fin n := ⟨j.val,hjn⟩
    refine ⟨c.index k,?_,c.lt_sizeUpTo_index_succ k⟩
    have hle := c.sizeUpTo_index_le k
    apply lt_of_le_of_ne hle
    intro he
    apply hj
    apply Finset.mem_map.mpr
    refine ⟨(c.index k).castSucc,Finset.mem_univ _,?_⟩
    apply Fin.ext
    exact he
  · rintro ⟨i,hi₀,hi₁⟩ hj
    obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hj
    have hea : c.sizeUpTo a.val=j.val := congrArg Fin.val he
    by_cases hai : a.val ≤ i.val
    · have hm := c.monotone_sizeUpTo hai
      omega
    · have hai' : i.val+1≤a.val := by omega
      have hm := c.monotone_sizeUpTo hai'
      omega

/-- The internal degree is the actual sum of lengths of the tensor factors. -/
theorem total_length (W : List α) (L : Factorization W) :
    (L.val.map List.length).sum=W.length :=
  (factorizationComposition W L).blocks_sum

theorem number_of_blocks_le (W : List α) (L : Factorization W) :
    L.val.length≤W.length := by
  simpa only [Composition.length,factorizationComposition,List.length_map] using
    (factorizationComposition W L).length_le

/-- The diagonal bar degree consists exactly of the factorization into
single generators. -/
theorem diagonal_iff_singletons (W : List α) (L : Factorization W) :
    L.val.length=W.length ↔ ∀ T∈L.val,T.length=1 := by
  constructor
  · intro h T hT
    have hc : factorizationComposition W L=Composition.ones W.length :=
      Composition.eq_ones_iff_length.mpr (by
        simpa only [Composition.length,factorizationComposition,List.length_map] using h)
    exact (Composition.eq_ones_iff.mp hc) T.length (List.mem_map.mpr ⟨T,hT,rfl⟩)
  · intro h
    have hc : factorizationComposition W L=Composition.ones W.length :=
      Composition.eq_ones_iff.mpr (by
        intro n hn
        obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hn
        exact h T hT)
    simpa only [Composition.length,factorizationComposition,List.length_map] using
      Composition.eq_ones_iff_length.mp hc

end PaperVerification.AlternatingForms.BarCompositions

end
end
end TAF_LiteralSource_0258

section TAF_LiteralSource_0259
/- Original module: PaperVerification.AlternatingFormsBarAdmissibleCuts -/


/-!
# Admissible bar blocks and mandatory cuts

For any adjacency relation on letters, a nonempty block is normal exactly
when each adjacent pair inside it is allowed. This file identifies actual
factorizations into such blocks with boundary sets containing the two
endpoints and every forbidden adjacency. No algebraic or homological
condition is assumed in this combinatorial correspondence.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

variable {α : Type*} (R : α → α → Prop) (W : List α)

def block (c : Composition W.length) (i : Fin c.length) : List α :=
  (W.take (c.sizeUpTo (i.val+1))).drop (c.sizeUpTo i.val)

theorem block_length (c : Composition W.length) (i : Fin c.length) :
    (block W c i).length=c.sizeUpTo (i.val+1)-c.sizeUpTo i.val := by
  simp only [block,List.length_drop,List.length_take,
    Nat.min_eq_left (c.sizeUpTo_le _)]

theorem block_getElem (c : Composition W.length) (i : Fin c.length)
    (q : ℕ) (hq : q<(block W c i).length) :
    (block W c i)[q]=W[c.sizeUpTo i.val+q]'(by
      rw [block_length] at hq
      have hu := c.sizeUpTo_le (i.val+1)
      omega) := by
  simp only [block,List.getElem_drop,List.getElem_take]

def BadCut (j : Fin (W.length+1)) : Prop :=
  ∃ a : ℕ,∃ ha : a+1<W.length,
    j.val=a+1 ∧ ¬R (W[a]'(by omega)) (W[a+1]'ha)

def mandatoryCuts : Finset (Fin (W.length+1)) := by
  classical
  exact insert 0 (insert (Fin.last W.length) (Finset.univ.filter (BadCut R W)))

@[simp] theorem mem_mandatoryCuts (j : Fin (W.length+1)) :
    j∈mandatoryCuts R W ↔ j=0 ∨ j=Fin.last W.length ∨ BadCut R W j := by
  classical
  simp only [mandatoryCuts,Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and]

theorem block_admissible_iff (c : Composition W.length) :
    (∀ i : Fin c.length,(block W c i).IsChain R) ↔
      mandatoryCuts R W⊆c.boundaries := by
  constructor
  · intro hc j hj
    rcases (mem_mandatoryCuts R W j).mp hj with rfl | rfl | ⟨a,ha,hja,hbad⟩
    · exact c.toCompositionAsSet.zero_mem
    · exact c.toCompositionAsSet.getLast_mem
    · by_contra hjn
      have hj0 : 0<j.val := by omega
      have hjN : j.val<W.length := by omega
      obtain ⟨i,hlo,hup⟩ := (not_mem_boundaries_iff c j hj0 hjN).mp hjn
      let q := a-c.sizeUpTo i.val
      have hlow : c.sizeUpTo i.val≤a := by omega
      have hq : q+1<(block W c i).length := by
        rw [block_length]
        dsimp only [q]
        omega
      have hqa : c.sizeUpTo i.val+q=a := Nat.add_sub_of_le hlow
      have hqb : c.sizeUpTo i.val+(q+1)=a+1 := by omega
      have he := List.isChain_iff_getElem.mp (hc i) q hq
      rw [block_getElem,block_getElem] at he
      apply hbad
      simpa only [hqa,hqb] using he
  · intro hc i
    apply List.isChain_iff_getElem.mpr
    intro q hq
    rw [block_getElem,block_getElem]
    by_contra hbad
    have hq' := hq
    rw [block_length] at hq'
    have hu := c.sizeUpTo_le (i.val+1)
    let a := c.sizeUpTo i.val+q
    have ha : a+1<W.length := by dsimp only [a]; omega
    let j : Fin (W.length+1) := ⟨a+1,by omega⟩
    have hjbad : BadCut R W j := by
      refine ⟨a,ha,rfl,?_⟩
      simpa only [a,Nat.add_assoc] using hbad
    have hj : j∈c.boundaries := hc ((mem_mandatoryCuts R W j).mpr (Or.inr (Or.inr hjbad)))
    have hjn : j∉c.boundaries :=
      (not_mem_boundaries_iff c j (by dsimp only [j]; omega) ha).mpr
        ⟨i,by dsimp only [j,a]; omega,by dsimp only [j,a]; omega⟩
    exact hjn hj

theorem split_admissible_iff_blocks (c : Composition W.length) :
    (∀ T∈W.splitWrtComposition c,T.IsChain R) ↔
      ∀ i : Fin c.length,(block W c i).IsChain R := by
  constructor
  · intro h i
    have hi : i.val<(W.splitWrtComposition c).length := by
      rw [List.length_splitWrtComposition]
      exact i.isLt
    have he := h ((W.splitWrtComposition c)[i.val]) (List.getElem_mem hi)
    simpa only [List.getElem_splitWrtComposition,block] using he
  · intro h T hT
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hT
    have hj' : j<c.length := by rwa [List.length_splitWrtComposition] at hj
    have hh := h (⟨j,hj'⟩ : Fin c.length)
    rw [List.getElem_splitWrtComposition] at he
    simpa only [block,he] using hh

theorem split_admissible_iff (c : Composition W.length) :
    (∀ T∈W.splitWrtComposition c,T.IsChain R) ↔ mandatoryCuts R W⊆c.boundaries :=
  (split_admissible_iff_blocks R W c).trans (block_admissible_iff R W c)

def AdmissibleFactorization :=
  {L : Factorization W // ∀ T∈L.val,T.IsChain R}

def AdmissibleCutSet :=
  {S : Finset (Fin (W.length+1)) // mandatoryCuts R W⊆S}

theorem factorization_admissible_iff (L : Factorization W) :
    (∀ T∈L.val,T.IsChain R) ↔ mandatoryCuts R W⊆boundaries W L := by
  have h := split_admissible_iff R W (factorizationComposition W L)
  have he := congrArg Subtype.val (split_compositionFactorization W L)
  change W.splitWrtComposition (factorizationComposition W L)=L.val at he
  simpa only [he,boundaries] using h

def admissibleCutMap (L : AdmissibleFactorization R W) : AdmissibleCutSet R W :=
  ⟨boundaries W L.val,(factorization_admissible_iff R W L.val).mp L.property⟩

theorem admissibleCutMap_bijective : Function.Bijective (admissibleCutMap R W) := by
  constructor
  · intro L M h
    apply Subtype.ext
    apply boundaries_injective W
    exact congrArg Subtype.val h
  · intro S
    have h0 : (0 : Fin (W.length+1))∈S.val :=
      S.property ((mem_mandatoryCuts R W _).mpr (Or.inl rfl))
    have hN : Fin.last W.length∈S.val :=
      S.property ((mem_mandatoryCuts R W _).mpr (Or.inr (Or.inl rfl)))
    obtain ⟨L,hL,hunique⟩ := exists_unique_factorization W S.val h0 hN
    have hLa : ∀ T∈L.val,T.IsChain R :=
      (factorization_admissible_iff R W L).mpr (hL.symm ▸ S.property)
    refine ⟨⟨L,hLa⟩,?_⟩
    exact Subtype.ext hL

/-- The basis index correspondence for the literal monomial bar complex. -/
def admissibleCutEquiv : AdmissibleFactorization R W ≃ AdmissibleCutSet R W :=
  Equiv.ofBijective (admissibleCutMap R W) (admissibleCutMap_bijective R W)

theorem admissibleCutEquiv_card (L : AdmissibleFactorization R W) :
    (admissibleCutEquiv R W L).val.card=L.val.val.length+1 :=
  boundaries_card W L.val

end PaperVerification.AlternatingForms.BarCompositions

end
end
end TAF_LiteralSource_0259

section TAF_LiteralSource_0260
/- Original module: PaperVerification.MonomialBarCuts -/


/-!
# The actual Boolean cut complex of a quadratic monomial word

For a word with n internal positions, the mandatory cuts mark its forbidden
adjacent pairs. A valid bar cut set contains every mandatory cut. The
bar differential deletes the optional cuts with their exterior signs.
Creation at any optional position contracts this complex; if all positions
are mandatory, only the top cut degree occurs. The result is an equality
of actual cycles and boundaries, over every commutative coefficient ring.

The later normalized-bar comparison must identify these operators and
these basis vectors with the algebraic bar differential. This file does
not define Koszulness by the combinatorial result.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.MonomialBarCuts

open scoped BigOperators
open CliffordAlgebra

variable {K : Type*} [CommRing K] (n : ℕ)
local notation "V" => Fin n → K
local notation "E" => ExteriorAlgebra K V

noncomputable def coordinateBasis : Module.Basis (Fin n) K V := Pi.basisFun K (Fin n)

def cutPiece (mandatory : Finset (Fin n)) (r : ℕ) : Submodule K E :=
  Submodule.span K {x | ∃ S : Finset (Fin n),mandatory⊆S ∧ S.card=r ∧
    x=(coordinateBasis (K := K) n).ExteriorAlgebra S}

def optionalFunctional (mandatory : Finset (Fin n)) : Module.Dual K V :=
  ∑ i ∈ Finset.univ \ mandatory,(coordinateBasis (K := K) n).coord i

def differential (mandatory : Finset (Fin n)) : E →ₗ[K] E :=
  contractLeft (Q := (0 : QuadraticForm K V)) (optionalFunctional n mandatory)

def insertion (i : Fin n) : E →ₗ[K] E :=
  LinearMap.mulLeft K (ExteriorAlgebra.ι K ((coordinateBasis (K := K) n) i))

theorem optionalFunctional_basis (mandatory : Finset (Fin n)) (i : Fin n) :
    optionalFunctional (K := K) n mandatory ((coordinateBasis (K := K) n) i)=
      if i∈mandatory then 0 else 1 := by
  classical
  simp only [optionalFunctional,LinearMap.sum_apply,Module.Basis.coord_apply,
    Module.Basis.repr_self,Finsupp.single_apply]
  by_cases hi : i∈mandatory
  · rw [if_pos hi]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro hji
    subst j
    exact (Finset.mem_sdiff.mp hj).2 hi
  · rw [if_neg hi,Finset.sum_eq_single i]
    · simp only [if_pos rfl,ite_true]
    · intro j hj hji
      exact if_neg hji.symm
    · intro hnot
      exact (hnot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩)).elim

theorem differential_basis (mandatory S : Finset (Fin n)) :
    differential (K := K) n mandatory ((coordinateBasis (K := K) n).ExteriorAlgebra S)=
      ∑ i ∈ Finset.univ \ mandatory,
        if i∈S then TauCeti.ExteriorAlgebra.basisEraseSign i S •
          (coordinateBasis (K := K) n).ExteriorAlgebra (S.erase i) else 0 := by
  simp only [differential,optionalFunctional,map_sum,LinearMap.sum_apply,
    TauCeti.ExteriorAlgebra.contractLeft_coord_basis]

set_option maxHeartbeats 1000000 in
theorem differential_squared (mandatory : Finset (Fin n)) (x : E) :
    differential n mandatory (differential n mandatory x)=0 :=
  CliffordAlgebra.contractLeft_contractLeft
    (Q := (0 : QuadraticForm K (Fin n → K)))
    (optionalFunctional (K := K) n mandatory) x

private theorem sign_smul_mem (W : Submodule K E) (ε : ℤˣ) (x : E) (hx : x∈W) : ε • x∈W := by
  rcases Int.units_eq_one_or ε with h | h
  · simpa only [h,one_smul] using hx
  · simpa only [h,Units.smul_def,Units.val_neg,Units.val_one,neg_smul,one_smul]
      using W.neg_mem hx

theorem differential_mem_cutPiece (mandatory : Finset (Fin n)) (r : ℕ)
    (x : E) (hx : x∈cutPiece n mandatory (r+1)) :
    differential n mandatory x∈cutPiece n mandatory r := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨S,hMS,hS,rfl⟩ := hx
      rw [differential_basis]
      apply Submodule.sum_mem
      intro i hi
      by_cases hiS : i∈S
      · rw [if_pos hiS]
        apply sign_smul_mem
        apply Submodule.subset_span
        refine ⟨S.erase i,?_,?_,rfl⟩
        · intro j hj
          exact Finset.mem_erase.mpr
            ⟨fun he => (Finset.mem_sdiff.mp hi).2 (he ▸ hj),hMS hj⟩
        · have hc := Finset.card_erase_add_one hiS
          omega
      · rw [if_neg hiS]
        exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (cutPiece (K := K) n mandatory r).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (cutPiece (K := K) n mandatory r).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using (cutPiece (K := K) n mandatory r).smul_mem c ih

theorem insertion_mem_cutPiece (mandatory : Finset (Fin n)) (i : Fin n) (r : ℕ)
    (x : E) (hx : x∈cutPiece n mandatory r) :
    insertion n i x∈cutPiece n mandatory (r+1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨S,hMS,hS,rfl⟩ := hx
      change ExteriorAlgebra.ι K ((coordinateBasis (K := K) n) i)*
        (coordinateBasis (K := K) n).ExteriorAlgebra S∈_
      rw [TauCeti.ExteriorAlgebra.ι_mul_basis]
      by_cases hi : i∈S
      · rw [if_pos hi]
        exact Submodule.zero_mem _
      · rw [if_neg hi]
        apply sign_smul_mem
        apply Submodule.subset_span
        exact ⟨insert i S,fun j hj => Finset.mem_insert_of_mem (hMS hj),
          by rw [Finset.card_insert_of_notMem hi,hS],rfl⟩
  | zero => simpa only [map_zero] using (cutPiece (K := K) n mandatory (r+1)).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (cutPiece (K := K) n mandatory (r+1)).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using (cutPiece (K := K) n mandatory (r+1)).smul_mem c ih

/-- The actual contracting identity retains all required cuts, because
insertion only adjoins one optional position. -/
theorem differential_insertion (mandatory : Finset (Fin n)) (i : Fin n)
    (hi : i∉mandatory) (x : E) :
    differential n mandatory (insertion n i x)+
      insertion n i (differential n mandatory x)=x := by
  change contractLeft (Q := (0 : QuadraticForm K V)) (optionalFunctional n mandatory)
      (ExteriorAlgebra.ι K ((coordinateBasis (K := K) n) i)*x)+
      ExteriorAlgebra.ι K ((coordinateBasis (K := K) n) i)*
        contractLeft (Q := (0 : QuadraticForm K V)) (optionalFunctional n mandatory) x=x
  rw [CliffordAlgebra.contractLeft_ι_mul,optionalFunctional_basis,if_neg hi,
    one_smul,sub_add_cancel]

theorem cutPiece_univ_eq_bot (r : ℕ) (hr : r≠n) :
    cutPiece (K := K) n Finset.univ r=⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨S,hS,hcard,rfl⟩
  have he : S=Finset.univ := Finset.eq_univ_of_forall (fun i => hS (Finset.mem_univ i))
  have hn : n=r := by simpa only [he,Finset.card_univ,Fintype.card_fin] using hcard
  exact (hr hn.symm).elim

/-- Every off-top cycle is an actual boundary in the valid-cut subcomplex.
For a word of length n+1, the excluded top is exactly bar degree n+1. -/
theorem off_diagonal_cycle_is_boundary (mandatory : Finset (Fin n))
    (r : ℕ) (hr : r≠n) (x : E) (hx : x∈cutPiece n mandatory r)
    (hdx : differential n mandatory x=0) :
    ∃ y∈cutPiece n mandatory (r+1),differential n mandatory y=x := by
  classical
  by_cases hM : mandatory=Finset.univ
  · rw [hM,cutPiece_univ_eq_bot n r hr,Submodule.mem_bot] at hx
    subst x
    exact ⟨0,Submodule.zero_mem _,map_zero _⟩
  · have hex : ∃ i : Fin n,i∉mandatory := by
      by_contra h
      apply hM
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hi
      exact h ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hex
    refine ⟨insertion n i x,insertion_mem_cutPiece n mandatory i r x hx,?_⟩
    have h := differential_insertion n mandatory i hi x
    rwa [hdx,map_zero,add_zero] at h

end PaperVerification.MonomialBarCuts
end
end
end TAF_LiteralSource_0260

section TAF_LiteralSource_0261
/- Original module: PaperVerification.AlternatingFormsBarCutSigns -/


/-!
# The exact bar and exterior deletion signs

Both endpoints are retained in a factorization's boundary set. The
boundary at index j has exactly j earlier boundaries, so exterior
contraction deletes it with sign (-1)^j. The j=i+1 boundary is precisely
the cut merged by the i-th adjacent-product operation; its sign is the
negative normalized-bar sign. This agrees with the actual residue-tensor
differential in AlternatingFormsBarTensor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

theorem card_boundaries_before {n : ℕ} (c : Composition n)
    (j : Fin (c.length+1)) :
    (c.boundaries.filter (fun a ↦ a<c.boundary j)).card=j.val := by
  classical
  rw [Composition.boundaries,Finset.filter_map,Finset.card_map]
  have hf : Finset.univ.filter
      ((fun a : Fin (n+1) ↦ a<c.boundary j) ∘ c.boundary.toEmbedding)=Finset.Iio j := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Function.comp_apply,
      Finset.mem_Iio]
    change c.boundary i<c.boundary j ↔ i<j
    exact c.boundary.lt_iff_lt
  rw [hf,Fin.card_Iio]

theorem boundary_erase_sign {n : ℕ} (c : Composition n)
    (j : Fin (c.length+1)) :
    TauCeti.ExteriorAlgebra.basisEraseSign (c.boundary j) c.boundaries=
      (-1 : ℤˣ)^j.val := by
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt,
    card_boundaries_before]

/-- Keeping the left endpoint accounts for the exact minus sign in the
residue-tensor differential, with no unspecified sign convention. -/
theorem interior_boundary_erase_sign {n : ℕ} (c : Composition n)
    (i : ℕ) (hi : i+1<c.length+1) :
    TauCeti.ExteriorAlgebra.basisEraseSign
      (c.boundary ⟨i+1,hi⟩) c.boundaries=-((-1 : ℤˣ)^i) := by
  rw [boundary_erase_sign]
  simp only [pow_succ,mul_neg,mul_one]

end PaperVerification.AlternatingForms.BarCompositions

end
end
end TAF_LiteralSource_0261

section TAF_LiteralSource_0262
/- Original module: PaperVerification.AlternatingFormsBarMerging -/


/-!
# Merging adjacent bar factors deletes the corresponding literal cut

The list operation joins exactly factors i and i+1. Its concatenation and
positivity proofs make it an actual factorization of the original word.
The scan of block lengths proves that its boundary set is obtained by
erasing boundary i+1, including all endpoint and cardinality information.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BarCompositions

variable {α β : Type*}

def mergeAdjacent (op : α → α → α) : ℕ → List α → List α
  | 0,a::b::L => op a b::L
  | 0,L => L
  | i+1,a::L => a::mergeAdjacent op i L
  | _+1,[] => []

theorem map_mergeAdjacent (op : α → α → α) (op' : β → β → β)
    (f : α → β) (hf : ∀ a b,f (op a b)=op' (f a) (f b))
    (i : ℕ) (L : List α) :
    (mergeAdjacent op i L).map f=mergeAdjacent op' i (L.map f) := by
  induction i generalizing L with
  | zero => cases L with
    | nil => rfl
    | cons a L => cases L <;> simp only [mergeAdjacent,List.map_cons,List.map_nil,hf]
  | succ i ih => cases L with
    | nil => rfl
    | cons a L => simp only [mergeAdjacent,List.map_cons,ih]

theorem mergeAdjacent_length (op : α → α → α) (i : ℕ) (L : List α)
    (hi : i+1<L.length) : (mergeAdjacent op i L).length+1=L.length := by
  induction i generalizing L with
  | zero => cases L with
    | nil => simp at hi
    | cons a L => cases L with
      | nil => simp at hi
      | cons b L => simp only [mergeAdjacent,List.length_cons]
  | succ i ih => cases L with
    | nil => simp at hi
    | cons a L =>
      have hi' : i+1<L.length := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hi
      simpa only [mergeAdjacent,List.length_cons,Nat.add_assoc] using congrArg (·+1) (ih L hi')

theorem mergeAdjacent_positive (L : List (List α))
    (hL : ∀ T∈L,0<T.length) (i : ℕ) :
    ∀ T∈mergeAdjacent (·++·) i L,0<T.length := by
  induction i generalizing L with
  | zero =>
    cases L with
    | nil => simp [mergeAdjacent]
    | cons a L =>
      cases L with
      | nil => simpa only [mergeAdjacent] using hL
      | cons b L =>
        intro T hT
        rcases List.mem_cons.mp hT with rfl | hT
        · have ha := hL a (by simp)
          rw [List.length_append]
          omega
        · exact hL T (by simp only [List.mem_cons]; exact Or.inr (Or.inr hT))
  | succ i ih =>
    cases L with
    | nil => simp [mergeAdjacent]
    | cons a L =>
      intro T hT
      rcases List.mem_cons.mp hT with rfl | hT
      · exact hL _ List.mem_cons_self
      · exact ih L (fun S hS ↦ hL S (List.mem_cons_of_mem _ hS)) T hT

theorem flatten_mergeAdjacent (i : ℕ) (L : List (List α)) :
    (mergeAdjacent (·++·) i L).flatten=L.flatten := by
  induction i generalizing L with
  | zero =>
    cases L with
    | nil => rfl
    | cons a L => cases L <;> simp only [mergeAdjacent,List.flatten_cons,List.append_assoc]
  | succ i ih =>
    cases L with
    | nil => rfl
    | cons a L => simp only [mergeAdjacent,List.flatten_cons,ih]

def mergeFactorization (W : List α) (L : Factorization W)
    (i : ℕ) : Factorization W :=
  ⟨mergeAdjacent (·++·) i L.val,
    (flatten_mergeAdjacent i L.val).trans L.property.1,
    mergeAdjacent_positive L.val L.property.2 i⟩

/-- Scanning actual block lengths makes the deleted cut completely explicit. -/
theorem scanl_mergeAdjacent (i : ℕ) (L : List ℕ) (hi : i+1<L.length) (a : ℕ) :
    (mergeAdjacent (·+·) i L).scanl (·+·) a=
      (L.scanl (·+·) a).eraseIdx (i+1) := by
  induction i generalizing L a with
  | zero =>
    cases L with
    | nil => simp at hi
    | cons b L =>
      cases L with
      | nil => simp at hi
      | cons c L =>
        simp only [mergeAdjacent,List.scanl_cons,List.eraseIdx_cons_succ,
          List.eraseIdx_cons_zero,Nat.add_assoc]
  | succ i ih =>
    cases L with
    | nil => simp at hi
    | cons b L =>
      have hi' : i+1<L.length := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hi
      simp only [mergeAdjacent,List.scanl_cons,List.eraseIdx_cons_succ,ih L hi']

def boundaryList {n : ℕ} (c : Composition n) : List ℕ :=
  c.blocks.scanl (·+·) 0

theorem boundaryList_eq_ofFn {n : ℕ} (c : Composition n) :
    boundaryList c=List.ofFn (fun j : Fin (c.length+1) ↦ (c.boundary j).val) := by
  apply List.ext_getElem
  · simp only [boundaryList,List.length_scanl,List.length_ofFn,Composition.length]
  · intro i hi hj
    simp only [boundaryList,List.getElem_scanl,List.getElem_ofFn,←List.sum_eq_foldl]
    rfl

/-- Evaluate the boundary list before substituting any factorization-specific
length proof.  This avoids rewriting a list underneath a dependent index. -/
theorem boundaryList_getElem {n : ℕ} (c : Composition n)
    (j : Fin (c.length+1)) :
    (boundaryList c)[j.val]'(by
      simpa only [boundaryList,List.length_scanl,Composition.length] using j.isLt) =
        (c.boundary j).val := by
  simp only [boundaryList,List.getElem_scanl,←List.sum_eq_foldl]
  rfl

theorem boundaryList_nodup {n : ℕ} (c : Composition n) : (boundaryList c).Nodup := by
  rw [boundaryList_eq_ofFn,List.nodup_ofFn]
  exact Fin.val_injective.comp c.boundary.injective

theorem image_boundaries_eq_boundaryList {n : ℕ} (c : Composition n) :
    c.boundaries.image Fin.val=(boundaryList c).toFinset := by
  classical
  rw [boundaryList_eq_ofFn]
  ext x
  simp only [Composition.boundaries,Finset.mem_image,Finset.mem_map,
    Finset.mem_univ,true_and,List.mem_toFinset,List.mem_ofFn]
  constructor
  · rintro ⟨y,⟨j,rfl⟩,rfl⟩
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    exact ⟨c.boundary j,⟨j,rfl⟩,rfl⟩

theorem toFinset_eraseIdx [DecidableEq α] (L : List α) (hL : L.Nodup) (i : ℕ) (hi : i<L.length) :
    (L.eraseIdx i).toFinset=L.toFinset.erase L[i] := by
  ext x
  simp only [List.mem_toFinset,Finset.mem_erase,List.mem_eraseIdx_iff_getElem]
  constructor
  · rintro ⟨j,hj,hji,hx⟩
    refine ⟨?_,hx ▸ List.getElem_mem hj⟩
    intro he
    exact hji (hL.getElem_inj.mp (hx.trans he))
  · rintro ⟨hxi,hx⟩
    obtain ⟨j,hj,hjx⟩ := List.mem_iff_getElem.mp hx
    refine ⟨j,hj,?_,hjx⟩
    intro hji
    subst j
    exact hxi hjx.symm

/-- The actual merge deletes exactly the boundary between the two factors. -/
theorem boundaries_mergeFactorization (W : List α) (L : Factorization W)
    (i : ℕ) (hi : i+1<L.val.length) :
    boundaries W (mergeFactorization W L i)=
      (boundaries W L).erase
        ((factorizationComposition W L).boundary
          ⟨i+1,by simpa only [Composition.length,factorizationComposition,List.length_map] using
            Nat.lt_succ_of_lt hi⟩) := by
  classical
  let c := factorizationComposition W L
  let j : Fin (c.length+1) := ⟨i+1,by
    simpa only [c,Composition.length,factorizationComposition,List.length_map] using
      Nat.lt_succ_of_lt hi⟩
  apply Finset.image_injective (f := Fin.val) Fin.val_injective
  simp only [boundaries]
  rw [Finset.image_erase Fin.val_injective,
    image_boundaries_eq_boundaryList,image_boundaries_eq_boundaryList]
  have he : boundaryList (factorizationComposition W (mergeFactorization W L i))=
      (boundaryList c).eraseIdx (i+1) := by
    change ((mergeAdjacent (·++·) i L.val).map List.length).scanl (·+·) 0=
      ((L.val.map List.length).scanl (·+·) 0).eraseIdx (i+1)
    rw [map_mergeAdjacent (·++·) (·+·) List.length (fun a b => List.length_append),
      scanl_mergeAdjacent i _ (by simpa only [List.length_map] using hi)]
  rw [he,toFinset_eraseIdx _ (boundaryList_nodup c) (i+1) (by
    simpa only [boundaryList,List.length_scanl,c,Composition.length,
      factorizationComposition,List.length_map] using Nat.lt_succ_of_lt hi)]
  congr 1
  exact boundaryList_getElem c j

/-- For an admissible bar word, the merged tensor remains admissible
exactly when the deleted cut is optional. -/
theorem merge_admissible_iff_optional (R : α → α → Prop) (W : List α)
    (L : AdmissibleFactorization R W) (i : ℕ) (hi : i+1<L.val.val.length) :
    (∀ T∈(mergeFactorization W L.val i).val,T.IsChain R) ↔
      (factorizationComposition W L.val).boundary
        ⟨i+1,by simpa only [Composition.length,factorizationComposition,List.length_map] using
          Nat.lt_succ_of_lt hi⟩∉mandatoryCuts R W := by
  rw [factorization_admissible_iff,boundaries_mergeFactorization W L.val i hi,
    Finset.subset_erase]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨(factorization_admissible_iff R W L.val).mp L.property,h⟩

end PaperVerification.AlternatingForms.BarCompositions

end
end
end TAF_LiteralSource_0262

section TAF_LiteralSource_0263
/- Original module: PaperVerification.AlternatingFormsBarCutComplex -/


/-!
# The coefficient complex of admissible cuts

The coefficient modules have exactly the actual normal-block bar words
of fixed concatenation and length as basis. Their equivalence with the
exterior valid-cut submodules is explicit on every basis vector. This
transports the previously proved contraction to a cycle-boundary theorem.
The comparison with the algebra's leading adjacent-product differential
is a separate required step, not an assumption in this construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

open PaperVerification.MonomialBarCuts

variable {K α : Type*} [CommRing K]
  (R : α → α → Prop) (W : List α)

def BarIndex (r : ℕ) :=
  {L : AdmissibleFactorization R W // L.val.val.length=r}

def CutIndex (n : ℕ) (mandatory : Finset (Fin n)) (r : ℕ) :=
  {S : Finset (Fin n) // mandatory⊆S ∧ S.card=r}

def barCutDegreeEquiv (r : ℕ) :
    BarIndex R W r ≃ CutIndex (W.length+1) (mandatoryCuts R W) (r+1) where
  toFun L := ⟨(admissibleCutEquiv R W L.val).val,
    (admissibleCutEquiv R W L.val).property,by
      rw [admissibleCutEquiv_card,L.property]⟩
  invFun S := ⟨(admissibleCutEquiv R W).symm ⟨S.val,S.property.1⟩,by
    have h := admissibleCutEquiv_card R W
      ((admissibleCutEquiv R W).symm ⟨S.val,S.property.1⟩)
    have he : (admissibleCutEquiv R W
        ((admissibleCutEquiv R W).symm ⟨S.val,S.property.1⟩)).val.card=S.val.card :=
      congrArg (fun T : AdmissibleCutSet R W ↦ T.val.card)
        ((admissibleCutEquiv R W).apply_symm_apply ⟨S.val,S.property.1⟩)
    have hc := S.property.2
    omega⟩
  left_inv L := by
    apply Subtype.ext
    exact (admissibleCutEquiv R W).symm_apply_apply L.val
  right_inv S := by
    apply Subtype.ext
    change (admissibleCutEquiv R W
      ((admissibleCutEquiv R W).symm ⟨S.val,S.property.1⟩)).val=S.val
    exact congrArg (fun T : AdmissibleCutSet R W ↦ T.val)
      ((admissibleCutEquiv R W).apply_symm_apply ⟨S.val,S.property.1⟩)

def cutBasis (n : ℕ) (mandatory : Finset (Fin n)) (r : ℕ) :
    Module.Basis (CutIndex n mandatory r) K (cutPiece (K := K) n mandatory r) := by
  let b := (coordinateBasis (K := K) n).ExteriorAlgebra
  let v : CutIndex n mandatory r → ExteriorAlgebra K (Fin n → K) := fun S ↦ b S.val
  have hli : LinearIndependent K v :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  have hs : Submodule.span K (Set.range v)=cutPiece (K := K) n mandatory r := by
    congr 1
    ext x
    constructor
    · rintro ⟨S,rfl⟩
      exact ⟨S.val,S.property.1,S.property.2,rfl⟩
    · rintro ⟨S,hS,hcard,hx⟩
      exact ⟨⟨S,hS,hcard⟩,hx.symm⟩
  exact (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hs)

@[simp] theorem cutBasis_apply (n : ℕ) (mandatory : Finset (Fin n)) (r : ℕ)
    (S : CutIndex n mandatory r) :
    (cutBasis (K := K) n mandatory r S).val=
      (coordinateBasis (K := K) n).ExteriorAlgebra S.val := by
  simp only [cutBasis,Module.Basis.map_apply]
  exact (LinearEquiv.coe_ofEq_apply _ _).trans (Module.Basis.coe_span_apply _ S)

def barCutLinearEquiv (r : ℕ) :
    (BarIndex R W r →₀ K) ≃ₗ[K]
      cutPiece (K := K) (W.length+1) (mandatoryCuts R W) (r+1) :=
  (Finsupp.domLCongr (barCutDegreeEquiv R W r)).trans
    (cutBasis (K := K) (W.length+1) (mandatoryCuts R W) (r+1)).repr.symm

@[simp] theorem barCutLinearEquiv_single (r : ℕ) (L : BarIndex R W r) :
    (barCutLinearEquiv (K := K) R W r (Finsupp.single L 1)).val=
      (coordinateBasis (K := K) (W.length+1)).ExteriorAlgebra
        (boundaries W L.val.val) := by
  simp only [barCutLinearEquiv,LinearEquiv.trans_apply,
    Finsupp.domLCongr_single,Module.Basis.repr_symm_single_one,cutBasis_apply]
  change (coordinateBasis (K := K) (W.length+1)).ExteriorAlgebra
      (admissibleCutMap R W L.val).val=_
  rfl

def cutDegreeDifferential (n : ℕ) (mandatory : Finset (Fin n)) (r : ℕ) :
    cutPiece (K := K) n mandatory (r+1) →ₗ[K] cutPiece (K := K) n mandatory r :=
  LinearMap.codRestrict _
    ((differential n mandatory).comp (cutPiece n mandatory (r+1)).subtype)
    (fun x ↦ differential_mem_cutPiece n mandatory r x.val x.property)

def cutModelDifferential (r : ℕ) :
    (BarIndex R W (r+1) →₀ K) →ₗ[K] (BarIndex R W r →₀ K) :=
  (barCutLinearEquiv R W r).symm.toLinearMap.comp
    ((cutDegreeDifferential (W.length+1) (mandatoryCuts R W) (r+1)).comp
      (barCutLinearEquiv R W (r+1)).toLinearMap)

theorem cutModelDifferential_comm (r : ℕ) (z : BarIndex R W (r+1) →₀ K) :
    (barCutLinearEquiv R W r (cutModelDifferential (K := K) R W r z)).val=
      differential (W.length+1) (mandatoryCuts R W)
        (barCutLinearEquiv R W (r+1) z).val := by
  simp only [cutModelDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rfl

theorem cutModelDifferential_squared (r : ℕ) (z : BarIndex R W (r+2) →₀ K) :
    cutModelDifferential R W r (cutModelDifferential (K := K) R W (r+1) z)=0 := by
  apply (barCutLinearEquiv R W r).injective
  apply Subtype.ext
  rw [cutModelDifferential_comm,cutModelDifferential_comm,map_zero]
  exact differential_squared (W.length+1) (mandatoryCuts R W) _

/-- Every off-diagonal cycle in this explicit coefficient complex is an
actual boundary; the excluded degree is the literal word length. -/
theorem cutModel_cycle_is_boundary (r : ℕ) (hr : r≠W.length)
    (z : BarIndex R W r →₀ K)
    (hz : differential (W.length+1) (mandatoryCuts R W)
      (barCutLinearEquiv (K := K) R W r z).val=0) :
    ∃ y : BarIndex R W (r+1) →₀ K,cutModelDifferential R W r y=z := by
  obtain ⟨y,hy,hdy⟩ := off_diagonal_cycle_is_boundary (W.length+1)
    (mandatoryCuts R W) (r+1) (by omega)
      (barCutLinearEquiv (K := K) R W r z).val
      (barCutLinearEquiv (K := K) R W r z).property hz
  refine ⟨(barCutLinearEquiv R W (r+1)).symm ⟨y,hy⟩,?_⟩
  apply (barCutLinearEquiv R W r).injective
  apply Subtype.ext
  rw [cutModelDifferential_comm,LinearEquiv.apply_symm_apply]
  exact hdy

end PaperVerification.AlternatingForms.BarCompositions

end
end
end TAF_LiteralSource_0263

section TAF_LiteralSource_0264
/- Original module: PaperVerification.AlternatingFormsBarCutDifferential -/


/-!
# The cut differential is the literal adjacent-merge differential

The coordinate operator transported from exterior contraction is expanded
on every basis tensor. Each nonzero summand joins precisely the two
adjacent normal blocks separated by the chosen optional cut, with the
sign of the actual residue-tensor bar differential. The comparison is an
identity of operators on the full coefficient modules, without a rank or
dimension argument.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

open scoped BigOperators
open PaperVerification.MonomialBarCuts

variable {K α : Type*} [CommRing K]

theorem differential_basis_composition {n : ℕ} (c : Composition n)
    (mandatory : Finset (Fin (n+1))) :
    differential (n+1) mandatory
        ((coordinateBasis (K := K) (n+1)).ExteriorAlgebra c.boundaries)=
      ∑ j : Fin (c.length+1),
        if c.boundary j∈mandatory then 0 else
          (-1 : ℤˣ)^j.val •
            (coordinateBasis (K := K) (n+1)).ExteriorAlgebra
              (c.boundaries.erase (c.boundary j)) := by
  classical
  rw [differential_basis,←Finset.sum_filter]
  have hf : (Finset.univ \ mandatory).filter (fun x ↦ x∈c.boundaries)=
      c.boundaries.filter (fun x ↦ x∉mandatory) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    exact and_comm
  rw [hf,Finset.sum_filter]
  simp only [ite_not]
  calc
    (∑ x∈c.boundaries,if x∈mandatory then 0 else
      TauCeti.ExteriorAlgebra.basisEraseSign x c.boundaries •
        (coordinateBasis (K := K) (n+1)).ExteriorAlgebra (c.boundaries.erase x)) =
      ∑ j : Fin (c.length+1),if c.boundary j∈mandatory then 0 else
        TauCeti.ExteriorAlgebra.basisEraseSign (c.boundary j) c.boundaries •
          (coordinateBasis (K := K) (n+1)).ExteriorAlgebra
            (c.boundaries.erase (c.boundary j)) := by
        change (∑ x∈Finset.univ.map c.boundary.toEmbedding,_) = _
        rw [Finset.sum_map]
        rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [boundary_erase_sign]

variable (R : α → α → Prop) (W : List α)

theorem optional_boundary_index_bounds (L : AdmissibleFactorization R W)
    (j : Fin ((factorizationComposition W L.val).length+1))
    (hj : (factorizationComposition W L.val).boundary j∉mandatoryCuts R W) :
    0<j.val ∧ j.val<L.val.val.length := by
  let c := factorizationComposition W L.val
  have h0 : j≠0 := by
    intro he
    subst j
    apply hj
    rw [Composition.boundary_zero]
    exact (mem_mandatoryCuts R W _).mpr (Or.inl rfl)
  have hlast : j≠Fin.last c.length := by
    intro he
    subst j
    apply hj
    rw [Composition.boundary_last]
    exact (mem_mandatoryCuts R W _).mpr (Or.inr (Or.inl rfl))
  have hc : c.length=L.val.val.length := by
    simp only [c,Composition.length,factorizationComposition,List.length_map]
  have hjlt : j.val<c.length+1 := j.isLt
  have hj0 : j.val≠0 := fun h ↦ h0 (Fin.ext h)
  have hjlast : j.val≠c.length := fun h ↦ hlast (Fin.ext h)
  constructor <;> omega

def mergedBarIndex (r : ℕ) (L : BarIndex R W (r+1))
    (j : Fin ((factorizationComposition W L.val.val).length+1))
    (hj : (factorizationComposition W L.val.val).boundary j∉mandatoryCuts R W) :
    BarIndex R W r := by
  have hb := optional_boundary_index_bounds R W L.val j hj
  let i := j.val-1
  have hi : i+1<L.val.val.val.length := by dsimp only [i]; omega
  have he : i+1=j.val := by dsimp only [i]; omega
  have hmerge : ∀ T∈(mergeFactorization W L.val.val i).val,T.IsChain R := by
    apply (merge_admissible_iff_optional R W L.val i hi).mpr
    let jj : Fin ((factorizationComposition W L.val.val).length+1) :=
      ⟨i+1,by
        simpa only [Composition.length,factorizationComposition,List.length_map] using
          Nat.lt_succ_of_lt hi⟩
    have hindex : jj=j := Fin.ext he
    change (factorizationComposition W L.val.val).boundary jj∉mandatoryCuts R W
    rw [hindex]
    exact hj
  refine ⟨⟨mergeFactorization W L.val.val i,hmerge⟩,?_⟩
  have hl := mergeAdjacent_length (·++·) i L.val.val.val hi
  have hr := L.property
  dsimp only [mergeFactorization]
  omega

theorem mergedBarIndex_boundaries (r : ℕ) (L : BarIndex R W (r+1))
    (j : Fin ((factorizationComposition W L.val.val).length+1))
    (hj : (factorizationComposition W L.val.val).boundary j∉mandatoryCuts R W) :
    boundaries W (mergedBarIndex R W r L j hj).val.val=
      (boundaries W L.val.val).erase
        ((factorizationComposition W L.val.val).boundary j) := by
  have hb := optional_boundary_index_bounds R W L.val j hj
  have hi : j.val-1+1<L.val.val.val.length := by omega
  change boundaries W (mergeFactorization W L.val.val (j.val-1))=_
  rw [boundaries_mergeFactorization W L.val.val (j.val-1) hi]
  apply congrArg (fun a : Fin ((factorizationComposition W L.val.val).length+1) ↦
    (boundaries W L.val.val).erase ((factorizationComposition W L.val.val).boundary a))
  apply Fin.ext
  change j.val-1+1=j.val
  omega

def barExteriorMap (r : ℕ) :
    (BarIndex R W r →₀ K) →ₗ[K] ExteriorAlgebra K (Fin (W.length+1) → K) :=
  (cutPiece (W.length+1) (mandatoryCuts R W) (r+1)).subtype.comp
    (barCutLinearEquiv R W r).toLinearMap

theorem barExteriorMap_injective (r : ℕ) :
    Function.Injective (barExteriorMap (K := K) R W r) :=
  Subtype.val_injective.comp (barCutLinearEquiv R W r).injective

@[simp] theorem barExteriorMap_single (r : ℕ) (L : BarIndex R W r) :
    barExteriorMap (K := K) R W r (Finsupp.single L 1)=
      (coordinateBasis (K := K) (W.length+1)).ExteriorAlgebra
        (boundaries W L.val.val) :=
  barCutLinearEquiv_single R W r L

theorem barExteriorMap_differential (r : ℕ) (z : BarIndex R W (r+1) →₀ K) :
    barExteriorMap R W r (cutModelDifferential (K := K) R W r z)=
      differential (W.length+1) (mandatoryCuts R W) (barExteriorMap R W (r+1) z) :=
  cutModelDifferential_comm R W r z

/-- Exact formula on every actual factorization basis vector. -/
theorem cutModelDifferential_single_merges (r : ℕ) (L : BarIndex R W (r+1)) :
    cutModelDifferential (K := K) R W r (Finsupp.single L 1)=
      ∑ j : Fin ((factorizationComposition W L.val.val).length+1),
        if hj : (factorizationComposition W L.val.val).boundary j∉mandatoryCuts R W
        then (-1 : ℤˣ)^j.val • Finsupp.single (mergedBarIndex R W r L j hj) 1
        else 0 := by
  classical
  apply barExteriorMap_injective R W r
  rw [barExteriorMap_differential,barExteriorMap_single]
  change differential (W.length+1) (mandatoryCuts R W)
      ((coordinateBasis (K := K) (W.length+1)).ExteriorAlgebra
        (factorizationComposition W L.val.val).boundaries)=_
  rw [differential_basis_composition,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : (factorizationComposition W L.val.val).boundary j∉mandatoryCuts R W
  · rw [dif_pos h,if_neg h,map_zsmul_unit,barExteriorMap_single,
      mergedBarIndex_boundaries]
    rfl
  · rw [dif_neg h,if_pos (not_not.mp h),map_zero]

end PaperVerification.AlternatingForms.BarCompositions

end
end
end TAF_LiteralSource_0264

section TAF_LiteralSource_0265
/- Original module: PaperVerification.AlternatingFormsOddBarWords -/


/-!
# The original odd standard basis as normal words

The positive bar factors are put in bijection with nonempty increasing
words of actual good Plucker variables. The value of such a word is its
literal product in the original quotient. In particular, a concatenation
that is already increasing multiplies to the corresponding basis vector
with coefficient one, without lower terms.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial Hibi
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "I" => IntervalIndex α β

def oddChainTupleEquiv :
    OddStandardIndex k t hs ≃ {q : Σ r,Fin r → I // Monotone q.2} where
  toFun C := ⟨⟨C.1,intervalIndexOfChain α β C.2⟩,C.2.property.2.2⟩
  invFun q := ⟨q.val.1,⟨fun j ↦ (q.val.2 j).val.val,
    (fun j ↦ (q.val.2 j).val.property),
    (fun j a ↦ (q.val.2 j).property a),q.property⟩⟩
  left_inv C := by
    rcases C with ⟨r,C⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    apply Sigma.ext rfl
    apply heq_of_eq
    funext j
    apply Subtype.ext
    apply Subtype.ext
    rfl

def monotoneTupleWordEquiv (J : Type*) [Preorder J] :
    {q : Σ r,Fin r → J // Monotone q.2} ≃
      {L : List J // L.Pairwise (·≤·)} :=
  Equiv.subtypeEquiv List.equivSigmaTuple.symm (by
    intro q
    change Monotone q.2 ↔ (List.ofFn q.2).Pairwise (·≤·)
    rw [List.pairwise_ofFn]
    constructor
    · intro h i j hij
      exact h hij.le
    · intro h i j hij
      rcases hij.eq_or_lt with rfl | hij
      · exact le_rfl
      · exact h hij)

def oddStandardWordEquiv :
    OddStandardIndex k t hs ≃ {L : List I // L.Pairwise (·≤·)} :=
  (oddChainTupleEquiv k t hs).trans (monotoneTupleWordEquiv I)

@[simp] theorem oddStandardWordEquiv_val (C : OddStandardIndex k t hs) :
    (oddStandardWordEquiv k t hs C).val=
      List.ofFn (intervalIndexOfChain α β C.2) := rfl

@[simp] theorem oddStandardWordEquiv_length (C : OddStandardIndex k t hs) :
    (oddStandardWordEquiv k t hs C).val.length=C.1 := List.length_ofFn

def PositiveNormalWord (J : Type*) [Preorder J] :=
  {L : List J // 0<L.length ∧ L.IsChain (·≤·)}

def oddPositiveWord (C : OddPositiveStandardIndex (K := K) k t hs) :
    PositiveNormalWord I :=
  ⟨(oddStandardWordEquiv k t hs C.down.val).val,
    by rw [oddStandardWordEquiv_length]
       exact oddStandardIndex_degree_positive k t hs C.down.val C.down.property,
    List.isChain_iff_pairwise.mpr (oddStandardWordEquiv k t hs C.down.val).property⟩

theorem oddPositiveWord_bijective : Function.Bijective (oddPositiveWord (K := K) k t hs) := by
  constructor
  · intro C D h
    apply ULift.ext
    apply Subtype.ext
    apply (oddStandardWordEquiv k t hs).injective
    apply Subtype.ext
    exact congrArg (fun W : PositiveNormalWord I => W.val) h
  · intro L
    let C := (oddStandardWordEquiv k t hs).symm
      ⟨L.val,List.isChain_iff_pairwise.mp L.property.2⟩
    have hC : C≠oddEmptyStandardIndex k t hs := by
      intro he
      have hlen := oddStandardWordEquiv_length k t hs C
      have hword : (oddStandardWordEquiv k t hs C).val=L.val :=
        congrArg Subtype.val ((oddStandardWordEquiv k t hs).apply_symm_apply
          ⟨L.val,List.isChain_iff_pairwise.mp L.property.2⟩)
      rw [hword,he] at hlen
      have hpos := L.property.1
      change L.val.length=0 at hlen
      omega
    refine ⟨⟨⟨C,hC⟩⟩,?_⟩
    apply Subtype.ext
    change (oddStandardWordEquiv k t hs C).val = L.val
    exact congrArg (fun W : {L : List I // L.Pairwise (· ≤ ·)} => W.val)
      ((oddStandardWordEquiv k t hs).apply_symm_apply
        ⟨L.val,List.isChain_iff_pairwise.mp L.property.2⟩)

def oddPositiveWordEquiv :
    OddPositiveStandardIndex (K := K) k t hs ≃ PositiveNormalWord I :=
  Equiv.ofBijective (oddPositiveWord k t hs) (oddPositiveWord_bijective k t hs)

@[simp] theorem oddPositiveWord_degree (C : OddPositiveStandardIndex (K := K) k t hs) :
    (oddPositiveWordEquiv k t hs C).val.length=oddPositiveDegree (K := K) k t hs C :=
  oddStandardWordEquiv_length k t hs C.down.val

theorem oddGoodMap_standard_word (C : OddStandardIndex k t hs) :
    oddGoodMap (K := K) k t hs (word α β (oddStandardWordEquiv k t hs C).val)=
      oddPluckerStandardBasis k t hs C := by
  rw [←oddGoodMap_standardPolynomial k t hs C]
  congr 1
  simp only [oddStandardWordEquiv_val,word,List.map_ofFn,List.prod_ofFn,
    standardPolynomial,Function.comp_def]

theorem oddAugmentedBasis_word (C : OddPositiveStandardIndex (K := K) k t hs) :
    oddAugmentedBasis (K := K) k t hs (some C)=
      oddGoodMap k t hs (word α β (oddPositiveWordEquiv k t hs C).val) := by
  rw [oddAugmentedBasis_some]
  exact (oddGoodMap_standard_word k t hs C.down.val).symm

theorem word_append (L M : List I) :
    word (K := K) α β (L++M)=word α β L*word α β M := by
  simp only [word,List.map_append,List.prod_append]

def appendPositiveNormalWord (L M : PositiveNormalWord I)
    (h : (L.val++M.val).IsChain (·≤·)) : PositiveNormalWord I :=
  ⟨L.val++M.val,by rw [List.length_append]; exact Nat.add_pos_left L.property.1 _,h⟩

/-- Every already-normal product has its literal concatenation as its
unique output basis vector, with coefficient one. -/
theorem oddAugmentedBasis_mul_of_normal
    (C D : OddPositiveStandardIndex (K := K) k t hs)
    (h : ((oddPositiveWordEquiv k t hs C).val++
      (oddPositiveWordEquiv k t hs D).val).IsChain (·≤·)) :
    oddAugmentedBasis k t hs (some C)*oddAugmentedBasis k t hs (some D)=
      oddAugmentedBasis k t hs
        (some ((oddPositiveWordEquiv k t hs).symm
          (appendPositiveNormalWord k t hs
            (oddPositiveWordEquiv k t hs C) (oddPositiveWordEquiv k t hs D) h))) := by
  rw [oddAugmentedBasis_word,oddAugmentedBasis_word,oddAugmentedBasis_word,
    Equiv.apply_symm_apply]
  change oddGoodMap k t hs (word α β (oddPositiveWordEquiv k t hs C).val)*
    oddGoodMap k t hs (word α β (oddPositiveWordEquiv k t hs D).val)=
      oddGoodMap k t hs (word α β ((oddPositiveWordEquiv k t hs C).val++
        (oddPositiveWordEquiv k t hs D).val))
  rw [word_append,map_mul]

theorem odd_productCoefficients_of_normal
    (C D : OddPositiveStandardIndex (K := K) k t hs)
    (h : ((oddPositiveWordEquiv k t hs C).val++
      (oddPositiveWordEquiv k t hs D).val).IsChain (·≤·)) :
    PaperVerification.AugmentedAlgebraBasis.productCoefficients
        (oddAugmentedBasis (K := K) k t hs) C D=
      Finsupp.single ((oddPositiveWordEquiv k t hs).symm
        (appendPositiveNormalWord k t hs
          (oddPositiveWordEquiv k t hs C) (oddPositiveWordEquiv k t hs D) h)) 1 := by
  unfold PaperVerification.AugmentedAlgebraBasis.productCoefficients
  change PaperVerification.AugmentedAlgebraBasis.positiveCoordinates
    (oddAugmentedBasis k t hs)
      (oddAugmentedBasis k t hs (some C)*oddAugmentedBasis k t hs (some D))=_
  rw [oddAugmentedBasis_mul_of_normal k t hs C D h]
  exact PaperVerification.AugmentedAlgebraBasis.positiveCoordinates_vector _ _

end PaperVerification.AlternatingForms

end
end
end TAF_LiteralSource_0265

section TAF_LiteralSource_0266
/- Original module: PaperVerification.AlternatingFormsPBWInversions -/


/-!
# The finite secondary filtration for commutative PBW words

The number counted here is the literal number of out-of-order pairs of
letters. Replacing a subword by a permutation preserves every crossing
pair involving its context. Hence replacing a nonnormal subword by its
increasing rearrangement strictly lowers this number in every context.
This handles the commutative sorting steps that leave the monomial
exponent unchanged.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.PBWWords

variable {α : Type*} (R : α → α → Prop)

def badPairs : List α → ℕ
  | [] => 0
  | a::L => L.countP (fun b ↦ decide (¬R a b))+badPairs L

def crossing (L M : List α) : ℕ :=
  (L.map (fun a ↦ M.countP (fun b ↦ decide (¬R a b)))).sum

@[simp] theorem badPairs_nil : badPairs R ([] : List α)=0 := rfl
@[simp] theorem badPairs_cons (a : α) (L : List α) :
    badPairs R (a::L)=L.countP (fun b ↦ decide (¬R a b))+badPairs R L := rfl

@[simp] theorem crossing_nil (M : List α) : crossing R [] M=0 := rfl
@[simp] theorem crossing_cons (a : α) (L M : List α) :
    crossing R (a::L) M=M.countP (fun b ↦ decide (¬R a b))+crossing R L M := rfl

theorem crossing_append_left (L M N : List α) :
    crossing R (L++M) N=crossing R L N+crossing R M N := by
  simp only [crossing,List.map_append,List.sum_append]

theorem crossing_append_right (L M N : List α) :
    crossing R L (M++N)=crossing R L M+crossing R L N := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [crossing_cons,List.countP_append,ih]
    omega

theorem badPairs_append (L M : List α) :
    badPairs R (L++M)=badPairs R L+badPairs R M+crossing R L M := by
  induction L with
  | nil => simp only [List.nil_append,badPairs_nil,crossing_nil,Nat.zero_add,Nat.add_zero]
  | cons a L ih =>
    simp only [List.cons_append,badPairs_cons,List.countP_append,crossing_cons,ih]
    omega

theorem badPairs_eq_zero_iff (L : List α) :
    badPairs R L=0 ↔ L.Pairwise R := by
  classical
  induction L with
  | nil => exact ⟨fun _ ↦ List.Pairwise.nil,fun _ ↦ rfl⟩
  | cons a L ih =>
    rw [badPairs_cons,Nat.add_eq_zero,ih,List.pairwise_cons]
    constructor
    · rintro ⟨h,hL⟩
      refine ⟨?_,hL⟩
      intro b hb
      have he := List.countP_eq_zero.mp h b hb
      simpa only [Bool.not_eq_true,decide_eq_false_iff_not,not_not] using he
    · rintro ⟨h,hL⟩
      refine ⟨List.countP_eq_zero.mpr ?_,hL⟩
      intro b hb
      simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_not]
      exact h b hb

theorem crossing_perm_left {L M : List α} (h : L.Perm M) (N : List α) :
    crossing R L N=crossing R M N :=
  (h.map (fun a ↦ N.countP (fun b ↦ decide (¬R a b)))).sum_eq

theorem crossing_perm_right (L : List α) {M N : List α} (h : M.Perm N) :
    crossing R L M=crossing R L N := by
  unfold crossing
  congr 1
  apply List.map_congr_left
  intro a ha
  exact List.Perm.countP_eq _ h

theorem badPairs_context_balance (P Q L M : List α) (h : L.Perm M) :
    badPairs R (P++L++Q)+badPairs R M=
      badPairs R (P++M++Q)+badPairs R L := by
  simp only [badPairs_append,crossing_append_left,
    crossing_perm_left R h Q,crossing_perm_right R P h]
  omega

/-- Strict decrease is retained inside every surrounding bar word. -/
theorem badPairs_context_decrease (P Q L M : List α) (h : L.Perm M)
    (hL : ¬L.Pairwise R) (hM : M.Pairwise R) :
    badPairs R (P++M++Q)<badPairs R (P++L++Q) := by
  have hpos : 0<badPairs R L := Nat.pos_of_ne_zero
    (fun hz ↦ hL ((badPairs_eq_zero_iff R L).mp hz))
  have hz := (badPairs_eq_zero_iff R M).mpr hM
  have he := badPairs_context_balance R P Q L M h
  omega

end PaperVerification.AlternatingForms.PBWWords

end
end
end TAF_LiteralSource_0266

section TAF_LiteralSource_0267
/- Original module: PaperVerification.AlternatingFormsPBWWordOrder -/


/-!
# A finite natural-number filtration on words

The primary comparison is the actual commutative monomial order. A
secondary comparison counts out-of-order letter pairs. On words of each
fixed internal degree, the cardinality of the strict lower set converts
this comparison to a natural-number weight. Thus every replacement needed
by the PBW bar argument strictly decreases a literal finite filtration,
including commutative reorderings with unchanged monomial exponent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators MonomialOrder

namespace PaperVerification.AlternatingForms.PBWWords

variable {α : Type*}

def exponent : List α → α →₀ ℕ
  | [] => 0
  | a::L => Finsupp.single a 1+exponent L

@[simp] theorem exponent_append (L M : List α) :
    exponent (L++M)=exponent L+exponent M := by
  induction L with
  | nil => simp only [List.nil_append,exponent,zero_add]
  | cons a L ih => simp only [List.cons_append,exponent,ih,add_assoc]

@[simp] theorem exponent_apply (L : List α) (a : α) :
    exponent L a=L.count a := by
  induction L with
  | nil => simp only [exponent,Finsupp.zero_apply,List.count_nil]
  | cons b L ih =>
    by_cases h : b=a
    · subst b
      simp only [exponent,Finsupp.add_apply,Finsupp.single_eq_same,
        List.count_cons_self,ih,Nat.add_comm]
    · simp only [exponent,Finsupp.add_apply,Finsupp.single_eq_of_ne (Ne.symm h),
        List.count_cons_of_ne h,zero_add,ih]

theorem exponent_eq_iff_perm (L M : List α) :
    exponent L=exponent M ↔ L.Perm M := by
  rw [List.perm_iff_count]
  constructor
  · intro h a
    simpa only [exponent_apply] using congrArg (fun e : α →₀ ℕ ↦ e a) h
  · intro h
    ext a
    simpa only [exponent_apply] using h a

def Before (m : MonomialOrder α) (R : α → α → Prop) (L M : List α) : Prop :=
  exponent L ≺[m] exponent M ∨
    (exponent L=exponent M ∧ badPairs R L<badPairs R M)

theorem before_irrefl (m : MonomialOrder α) (R : α → α → Prop) (L : List α) :
    ¬Before m R L L := by
  rintro (h | ⟨_,h⟩) <;> exact lt_irrefl _ h

theorem before_trans (m : MonomialOrder α) (R : α → α → Prop)
    {L M N : List α} (hLM : Before m R L M) (hMN : Before m R M N) :
    Before m R L N := by
  rcases hLM with hLM | ⟨hLM,hLM'⟩
  · rcases hMN with hMN | ⟨hMN,hMN'⟩
    · exact Or.inl (hLM.trans hMN)
    · exact Or.inl (hMN ▸ hLM)
  · rcases hMN with hMN | ⟨hMN,hMN'⟩
    · exact Or.inl (hLM.symm ▸ hMN)
    · exact Or.inr ⟨hLM.trans hMN,hLM'.trans hMN'⟩

/-- The full strict word comparison is retained by an identical context.
Equal exponents imply equal multiplicities, so all inversions involving
the context cancel in the secondary comparison. -/
theorem before_context_of_before (m : MonomialOrder α) (R : α → α → Prop)
    (P Q L M : List α) (h : Before m R L M) :
    Before m R (P++L++Q) (P++M++Q) := by
  rcases h with h | ⟨he,h⟩
  · apply Or.inl
    simpa only [exponent_append,map_add,add_assoc,add_comm,add_left_comm] using
      add_lt_add_right (add_lt_add_left h (m.toSyn (exponent P))) (m.toSyn (exponent Q))
  · refine Or.inr ⟨by simp only [exponent_append,he],?_⟩
    have hp := (exponent_eq_iff_perm L M).mp he
    have hb := badPairs_context_balance R P Q L M hp
    omega

/-- A nonnormal product decreases in every context, either in its actual
monomial exponent or in the number of out-of-order pairs. -/
theorem before_context (m : MonomialOrder α) (R : α → α → Prop)
    (P Q L M : List α) (hmon : exponent M ≼[m] exponent L)
    (hL : ¬L.Pairwise R) (hM : M.Pairwise R) :
    Before m R (P++M++Q) (P++L++Q) := by
  rcases hmon.lt_or_eq with hlt | heq
  · apply Or.inl
    simpa only [exponent_append,map_add,add_assoc,add_comm,add_left_comm] using
      add_lt_add_right (add_lt_add_left hlt (m.toSyn (exponent P))) (m.toSyn (exponent Q))
  · have he : exponent M=exponent L := m.toSyn.injective heq
    refine Or.inr ⟨by simp only [exponent_append,he],?_⟩
    exact badPairs_context_decrease R P Q L M
      ((exponent_eq_iff_perm L M).mp he.symm) hL hM

def wordUniverse [Fintype α] (N : ℕ) : Finset (List α) :=
  (Finset.univ : Finset (Fin N → α)).image List.ofFn

theorem mem_wordUniverse [Fintype α] (N : ℕ) (L : List α) (hL : L.length=N) :
    L∈wordUniverse (α := α) N := by
  subst N
  apply Finset.mem_image.mpr
  exact ⟨L.get,Finset.mem_univ _,List.ofFn_get L⟩

def weight [Fintype α] (m : MonomialOrder α) (R : α → α → Prop) (N : ℕ)
    (L : List α) : ℕ :=
  ((wordUniverse (α := α) N).filter (fun M ↦ Before m R M L)).card

/-- Strict comparison is converted to strict natural-number decrease on
the finite set of words of the given internal degree. -/
theorem weight_lt [Fintype α] (m : MonomialOrder α) (R : α → α → Prop)
    (N : ℕ) (L M : List α) (hL : L.length=N) (h : Before m R L M) :
    weight m R N L<weight m R N M := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨hT.1,before_trans m R hT.2 h⟩
  · intro he
    have hmem : L∈(wordUniverse (α := α) N).filter (fun T ↦ Before m R T M) :=
      Finset.mem_filter.mpr ⟨mem_wordUniverse N L hL,h⟩
    rw [←he] at hmem
    exact before_irrefl m R L (Finset.mem_filter.mp hmem).2

theorem weight_context_lt [Fintype α] (m : MonomialOrder α) (R : α → α → Prop)
    (N : ℕ) (P Q L M : List α) (hlen : (P++M++Q).length=N)
    (hmon : exponent M ≼[m] exponent L)
    (hL : ¬L.Pairwise R) (hM : M.Pairwise R) :
    weight m R N (P++M++Q)<weight m R N (P++L++Q) :=
  weight_lt m R N _ _ hlen (before_context m R P Q L M hmon hL hM)

end PaperVerification.AlternatingForms.PBWWords

end
end
end TAF_LiteralSource_0267

section TAF_LiteralSource_0268
/- Original module: PaperVerification.AlternatingFormsOddPBWProducts -/


/-!
# Actual multiplication lowers the PBW word filtration

Every coefficient below is a coefficient of a genuine product in the
original odd isotropic Plucker quotient. Homogeneity gives the exact
internal degree, the established Groebner basis bounds the monomial
exponent, and literal inversion counts deal with equality of exponents.
Thus every nonnormal adjacent product lowers the finite word weight in
every surrounding tensor word.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators MonomialOrder

namespace PaperVerification.AlternatingForms

open MvPolynomial Hibi PaperVerification.AugmentedAlgebraBasis

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "I" => IntervalIndex α β
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "B₀" => oddPluckerStandardBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs

theorem oddAugmentedBasis_repr_some
    (x : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
    (C : OddPositiveStandardIndex (K := K) k t hs) :
    (B).repr x (some C)=(B₀).repr x C.down.val := by
  rw [oddAugmentedBasis,Module.Basis.repr_reindex_apply]
  rfl

theorem odd_productCoefficient_actual
    (C D E : OddPositiveStandardIndex (K := K) k t hs) :
    productCoefficients B C D E=
      (B₀).repr (B₀ C.down.val*B₀ D.down.val) E.down.val := by
  rw [productCoefficients,positiveCoordinates_apply]
  change (B).repr (B (some C)*B (some D)) (some E)=_
  rw [oddAugmentedBasis_repr_some,oddAugmentedBasis_some,oddAugmentedBasis_some]

theorem oddGoodMap_product_monomial
    (C D : OddPositiveStandardIndex (K := K) k t hs) :
    oddGoodMap k t hs
      (monomial (goodChainExponent k t hs C.down.val+
        goodChainExponent k t hs D.down.val) (1 : K))=
      B₀ C.down.val*B₀ D.down.val := by
  rw [←one_mul (1 : K),←monomial_mul,
    ←standardPolynomial_eq_monomial k t hs C.down.val,
    ←standardPolynomial_eq_monomial k t hs D.down.val,
    map_mul,oddGoodMap_standardPolynomial,oddGoodMap_standardPolynomial]

theorem odd_productCoefficient_normalForm
    (C D E : OddPositiveStandardIndex (K := K) k t hs) :
    productCoefficients B C D E=
      (oddGoodNormalForm k t hs
        (monomial (goodChainExponent k t hs C.down.val+
          goodChainExponent k t hs D.down.val) (1 : K))).coeff (goodChainExponent k t hs E.down.val) := by
  rw [oddGoodNormalForm,oddGoodRepresentative_coeff,oddGoodMap_product_monomial,
    odd_productCoefficient_actual]

theorem odd_productCoefficient_degree
    (C D E : OddPositiveStandardIndex (K := K) k t hs)
    (h : productCoefficients B C D E≠0) :
    oddPositiveDegree k t hs E=oddPositiveDegree k t hs C+oddPositiveDegree k t hs D := by
  have h' : oddCoefficients (K := K) k t hs
      (oddStandardRepresentative k t hs C.down.val*
        oddStandardRepresentative k t hs D.down.val) E.down.val≠0 := by
    simpa only [odd_productCoefficient_actual,oddCoefficients,
      oddPluckerStandardBasis_apply,map_mul] using h
  exact oddCoefficients_degree_eq k t hs _ _
    ((oddStandardRepresentative_homogeneous (K := K) k t hs C.down.val).mul
      (oddStandardRepresentative_homogeneous (K := K) k t hs D.down.val)) E.down.val h'

theorem odd_productCoefficient_exponent_le (m : MonomialOrder I)
    (C D E : OddPositiveStandardIndex (K := K) k t hs)
    (h : productCoefficients B C D E≠0) :
    goodChainExponent k t hs E.down.val ≼[oddGoodOrder k t hs m]
      goodChainExponent k t hs C.down.val+goodChainExponent k t hs D.down.val := by
  apply oddGoodNormalForm_monomial_term_le (K := K) k t hs m
  apply mem_support_iff.mpr
  rwa [←odd_productCoefficient_normalForm k t hs C D E]

theorem word_eq_monomial_exponent (L : List I) :
    word (K := K) α β L=monomial (PBWWords.exponent L) 1 := by
  induction L with
  | nil => simp only [word_nil,PBWWords.exponent,monomial_zero',map_one]
  | cons a L ih =>
    rw [word_cons,ih]
    simp only [X,monomial_mul,one_mul,PBWWords.exponent]

theorem oddPositiveWord_exponent (C : OddPositiveStandardIndex (K := K) k t hs) :
    PBWWords.exponent (e C).val=goodChainExponent k t hs C.down.val := by
  change PBWWords.exponent (List.ofFn (intervalIndexOfChain α β C.down.val.2)) = _
  apply MvPolynomial.monomial_left_injective (one_ne_zero : (1 : K)≠0)
  change (monomial (PBWWords.exponent (List.ofFn (intervalIndexOfChain α β C.down.val.2))) 1 :
    MvPolynomial I K) = monomial (goodChainExponent k t hs C.down.val) 1
  rw [←word_eq_monomial_exponent k t hs,←standardPolynomial_eq_monomial]
  simp only [word,List.map_ofFn,List.prod_ofFn,standardPolynomial,Function.comp_def]

/-- This is the strict filtration bound for every actual nonzero
coefficient of every nonnormal adjacent product, in every context. -/
theorem odd_productCoefficient_context_weight_lt (m : MonomialOrder I)
    (P Q : List I) (C D E : OddPositiveStandardIndex (K := K) k t hs)
    (h : productCoefficients B C D E≠0)
    (hnormal : ¬((e C).val++(e D).val).IsChain (·≤·)) :
    PBWWords.weight (oddGoodOrder k t hs m) (·≤·)
      (P++((e C).val++(e D).val)++Q).length (P++(e E).val++Q) <
    PBWWords.weight (oddGoodOrder k t hs m) (·≤·)
      (P++((e C).val++(e D).val)++Q).length (P++((e C).val++(e D).val)++Q) := by
  apply PBWWords.weight_context_lt
  · have hd := odd_productCoefficient_degree k t hs C D E h
    simp only [List.length_append,oddPositiveWord_degree]
    omega
  · simpa only [PBWWords.exponent_append,oddPositiveWord_exponent] using
      odd_productCoefficient_exponent_le k t hs m C D E h
  · exact fun hp ↦ hnormal (List.isChain_iff_pairwise.mpr hp)
  · exact List.isChain_iff_pairwise.mp (e E).property.2

end PaperVerification.AlternatingForms

end
end
end TAF_LiteralSource_0268

section TAF_LiteralSource_0269
/- Original module: PaperVerification.AlternatingFormsBarWordFibers -/


/-!
# Literal bar tensor indices and fixed-word fibers

A bar tensor is a list of actual positive basis indices. The equivalence
of each positive factor with its normal word identifies fixed-concatenation
tensor indices with the admissible factorizations used in the cut complex.
No tensor factors, internal degrees, or basis words are discarded.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

open PaperVerification.AlternatingForms

variable {C J : Type*} [Preorder J] (e : C ≃ PositiveNormalWord J)

@[expose]
def flattenBarWord (L : List C) : List J :=
  (L.map (fun c ↦ (e c).val)).flatten

def ActualBarIndex (W : List J) (r : ℕ) :=
  {L : List C // flattenBarWord e L=W ∧ L.length=r}

def actualFactorization (W : List J) (r : ℕ) (L : ActualBarIndex e W r) :
    BarIndex (·≤·) W r :=
  ⟨⟨⟨L.val.map (fun c ↦ (e c).val),L.property.1,by
    intro T hT
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hT
    exact (e c).property.1⟩,by
      intro T hT
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hT
      exact (e c).property.2⟩,by
        simpa only [List.length_map] using L.property.2⟩

def factorizationBarWord (W : List J) (L : AdmissibleFactorization (·≤·) W) : List C :=
  L.val.val.attach.map (fun T ↦ e.symm
    ⟨T.val,L.val.property.2 T.val T.property,L.property T.val T.property⟩)

theorem factorizationBarWord_map (W : List J)
    (L : AdmissibleFactorization (·≤·) W) :
    (factorizationBarWord e W L).map (fun c ↦ (e c).val)=L.val.val := by
  simp only [factorizationBarWord,List.map_map,Function.comp_def]
  calc
    _ = L.val.val.attach.map Subtype.val := by
      apply List.map_congr_left
      intro T hT
      exact congrArg (fun Z : PositiveNormalWord J => Z.val)
        (e.apply_symm_apply ⟨T.val,L.val.property.2 T.val T.property,
          L.property T.val T.property⟩)
    _ = _ := List.attach_map_subtype_val _

theorem factorizationBarWord_flatten (W : List J)
    (L : AdmissibleFactorization (·≤·) W) :
    flattenBarWord e (factorizationBarWord e W L)=W := by
  rw [flattenBarWord,factorizationBarWord_map,L.val.property.1]

theorem factorizationBarWord_length (W : List J)
    (L : AdmissibleFactorization (·≤·) W) :
    (factorizationBarWord e W L).length=L.val.val.length := by
  simp only [factorizationBarWord,List.length_map,List.length_attach]

def actualBarIndexEquiv (W : List J) (r : ℕ) :
    ActualBarIndex e W r ≃ BarIndex (·≤·) W r where
  toFun := actualFactorization e W r
  invFun L := ⟨factorizationBarWord e W L.val,
    factorizationBarWord_flatten e W L.val,
    (factorizationBarWord_length e W L.val).trans L.property⟩
  left_inv L := by
    apply Subtype.ext
    apply (List.map_injective_iff.mpr
      (show Function.Injective (fun c : C ↦ (e c).val) from
        fun c d h ↦ e.injective (Subtype.ext h)))
    rw [factorizationBarWord_map]
    rfl
  right_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact factorizationBarWord_map e W L.val

@[simp] theorem actualBarIndexEquiv_length (W : List J) (r : ℕ)
    (L : ActualBarIndex e W r) :
    (actualBarIndexEquiv e W r L).val.val.val.length=L.val.length :=
  List.length_map _

def InternalDegreeIndex (r N : ℕ) :=
  {L : List C // L.length=r ∧ (flattenBarWord e L).length=N}

def internalDegreeFiberEquiv (r N : ℕ) :
    InternalDegreeIndex e r N ≃
      Σ W : {W : List J // W.length=N},ActualBarIndex e W.val r where
  toFun L := ⟨⟨flattenBarWord e L.val,L.property.2⟩,⟨L.val,rfl,L.property.1⟩⟩
  invFun L := ⟨L.2.val,L.2.property.2,by
    rw [L.2.property.1]
    exact L.1.property⟩
  left_inv L := rfl
  right_inv L := by
    rcases L with ⟨⟨W,hW⟩,⟨L,hL,hlen⟩⟩
    dsimp only at hL
    subst W
    rfl

def internalDegreeCutFiberEquiv (r N : ℕ) :
    InternalDegreeIndex e r N ≃
      Σ W : {W : List J // W.length=N},BarIndex (·≤·) W.val r :=
  (internalDegreeFiberEquiv e r N).trans
    (Equiv.sigmaCongrRight (fun W ↦ actualBarIndexEquiv e W.val r))

variable {K : Type*} [CommRing K]

@[expose]
def internalDegreePiece (r N : ℕ) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | L.length=r ∧ (flattenBarWord e L).length=N}

def internalDegreeCoordinates (r N : ℕ) :
    internalDegreePiece (K := K) e r N ≃ₗ[K] (InternalDegreeIndex e r N →₀ K) :=
  Finsupp.supportedEquivFinsupp (R := K) _

def internalDegreeCutCoordinates (r N : ℕ) :
    internalDegreePiece (K := K) e r N ≃ₗ[K]
      ((Σ W : {W : List J // W.length=N},BarIndex (·≤·) W.val r) →₀ K) :=
  (internalDegreeCoordinates e r N).trans
    (Finsupp.domLCongr (internalDegreeCutFiberEquiv e r N))

end PaperVerification.AlternatingForms.BarCompositions

end
end
end TAF_LiteralSource_0269

section TAF_LiteralSource_0270
/- Original module: PaperVerification.AlternatingFormsBarLeadingExact -/


/-!
# Exactness of the leading bar complex in each internal degree

There are finitely many literal generator words of a fixed length. The
normal-block tensor module splits over these words, and the cut
differential acts separately on each fiber. The actual cut contraction
therefore proves exactness of this full leading complex away from the
diagonal, with no rank or acyclicity hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BarCompositions

variable {C J : Type*} [Preorder J] [Fintype J]
  (e : C ≃ PositiveNormalWord J)

instance fixedWordFintype (N : ℕ) : Fintype {W : List J // W.length=N} := by
  apply Fintype.ofSurjective
    (fun f : Fin N → J ↦ (⟨List.ofFn f,List.length_ofFn⟩ : {W : List J // W.length=N}))
  intro W
  rcases W with ⟨W,hW⟩
  subst N
  refine ⟨W.get,?_⟩
  apply Subtype.ext
  exact List.ofFn_get W

variable {K : Type*} [CommRing K]

def internalDegreeFiberCoordinates (r N : ℕ) :
    internalDegreePiece (K := K) e r N ≃ₗ[K]
      (W : {W : List J // W.length=N}) → (BarIndex (·≤·) W.val r →₀ K) :=
  (internalDegreeCutCoordinates e r N).trans (Finsupp.sigmaFinsuppLEquivPiFinsupp K)

def leadingFiberDifferential (r N : ℕ) :
    ((W : {W : List J // W.length=N}) → (BarIndex (·≤·) W.val (r+1) →₀ K)) →ₗ[K]
      ((W : {W : List J // W.length=N}) → (BarIndex (·≤·) W.val r →₀ K)) where
  toFun z W := cutModelDifferential (·≤·) W.val r (z W)
  map_add' z w := by
    funext W
    exact map_add (cutModelDifferential (K := K) (·≤·) W.val r) (z W) (w W)
  map_smul' a z := by
    funext W
    simpa only [Pi.smul_apply,RingHom.id_apply] using
      map_smul (cutModelDifferential (K := K) (·≤·) W.val r) a (z W)

theorem leadingFiberDifferential_apply (r N : ℕ)
    (z : (W : {W : List J // W.length=N}) → (BarIndex (·≤·) W.val (r+1) →₀ K))
    (W : {W : List J // W.length=N}) :
    leadingFiberDifferential (K := K) (J := J) r N z W=
      cutModelDifferential (K := K) (·≤·) W.val r (z W) := rfl

theorem leadingFiberDifferential_single (r N : ℕ)
    (W : {W : List J // W.length=N}) (z : BarIndex (·≤·) W.val (r+1) →₀ K) :
    leadingFiberDifferential r N (Pi.single W z)=
      Pi.single W (cutModelDifferential (·≤·) W.val r z) := by
  funext V
  rw [leadingFiberDifferential_apply (K := K) (J := J)]
  by_cases h : V=W
  · subst V
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h,map_zero]

def leadingDegreeDifferential (r N : ℕ) :
    internalDegreePiece (K := K) e (r+1) N →ₗ[K] internalDegreePiece (K := K) e r N :=
  (internalDegreeFiberCoordinates e r N).symm.toLinearMap.comp
    ((leadingFiberDifferential r N).comp
      (internalDegreeFiberCoordinates e (r+1) N).toLinearMap)

theorem leadingDegreeDifferential_comm (r N : ℕ)
    (z : internalDegreePiece (K := K) e (r+1) N) :
    internalDegreeFiberCoordinates e r N (leadingDegreeDifferential e r N z)=
      leadingFiberDifferential r N (internalDegreeFiberCoordinates e (r+1) N z) := by
  simp only [leadingDegreeDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem leadingFiberDifferential_squared (r N : ℕ)
    (z : (W : {W : List J // W.length=N}) → (BarIndex (·≤·) W.val (r+2) →₀ K)) :
    leadingFiberDifferential r N (leadingFiberDifferential (K := K) (r+1) N z)=0 := by
  funext W
  exact cutModelDifferential_squared (·≤·) W.val r (z W)

theorem leadingFiber_range_eq_ker (r N : ℕ) (hr : r+1≠N) :
    (leadingFiberDifferential (K := K) (J := J) (r+1) N).range=
      (leadingFiberDifferential (K := K) (J := J) r N).ker := by
  ext z
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.mem_ker.mpr (leadingFiberDifferential_squared r N y)
  · intro hz
    have hc : ∀ W : {W : List J // W.length=N},
        ∃ y : BarIndex (·≤·) W.val (r+2) →₀ K,
          cutModelDifferential (·≤·) W.val (r+1) y=z W := by
      intro W
      apply cutModel_cycle_is_boundary (·≤·) W.val (r+1)
        (by simpa only [W.property] using hr) (z W)
      have he := congrFun (LinearMap.mem_ker.mp hz) W
      change cutModelDifferential (·≤·) W.val r (z W)=0 at he
      have he' := congrArg (barExteriorMap (K := K) (·≤·) W.val r) he
      rw [barExteriorMap_differential,map_zero] at he'
      exact he'
    refine ⟨fun W ↦ Classical.choose (hc W),?_⟩
    funext W
    exact Classical.choose_spec (hc W)

theorem leadingDegree_range_eq_ker (r N : ℕ) (hr : r+1≠N) :
    (leadingDegreeDifferential (K := K) e (r+1) N).range=
      (leadingDegreeDifferential (K := K) e r N).ker := by
  ext z
  constructor
  · rintro ⟨y,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply (internalDegreeFiberCoordinates e r N).injective
    rw [leadingDegreeDifferential_comm,leadingDegreeDifferential_comm,map_zero]
    exact leadingFiberDifferential_squared r N _
  · intro hz
    have hc : internalDegreeFiberCoordinates e (r+1) N z∈
        (leadingFiberDifferential (K := K) (J := J) r N).ker := by
      apply LinearMap.mem_ker.mpr
      rw [←leadingDegreeDifferential_comm,LinearMap.mem_ker.mp hz,map_zero]
    rw [←leadingFiber_range_eq_ker r N hr] at hc
    obtain ⟨y,hy⟩ := hc
    refine ⟨(internalDegreeFiberCoordinates e (r+2) N).symm y,?_⟩
    apply (internalDegreeFiberCoordinates e (r+1) N).injective
    rw [leadingDegreeDifferential_comm,LinearEquiv.apply_symm_apply,hy]

end PaperVerification.AlternatingForms.BarCompositions

end
end
end TAF_LiteralSource_0270

section TAF_LiteralSource_0271
/- Original module: PaperVerification.FilteredComplexExactness -/



/-!
# Exactness and strictness for a filtered perturbation

The filtration is the actual finite support filtration of a weighted basis.
The leading differential is an explicit linear map, with equality of every
leading component required.  Exactness of the leading pair then proves
exactness of the perturbed pair by finite descent.  At the next degree it
also proves strictness of the first image, which rules out new leading
relations caused by cancellation among multipliers.

This is supporting mathematics for the differential normal-form theorem.
The leading exactness and differential identities must still be established
for its actual Lie--Rinehart and Koszul complexes; they are not conclusions
about those complexes merely from this abstract lemma.  This source has not
yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.FilteredComplex

open Fermion.BasisFiltered

variable {R M₀ M₁ M₂ I₀ I₁ I₂ : Type*} [CommRing R]
  [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]
  (b₀ : Module.Basis I₀ R M₀) (w₀ : I₀ → ℕ)
  (b₁ : Module.Basis I₁ R M₁) (w₁ : I₁ → ℕ)
  (b₂ : Module.Basis I₂ R M₂) (w₂ : I₂ → ℕ)

/-- The perturbed map preserves each actual filtration bound and has the
displayed map on leading components. -/
def HasLeadingMap (f g : M₁ →ₗ[R] M₀) : Prop :=
  ∀ d x, Bound b₁ w₁ d x →
    Bound b₀ w₀ d (f x) ∧
      component b₀ w₀ d (f x) = g (component b₁ w₁ d x)

/-- Homogeneity means commutation with the actual component projections. -/
def PreservesComponents (g : M₁ →ₗ[R] M₀) : Prop :=
  ∀ d x, g (component b₁ w₁ d x) = component b₀ w₀ d (g x)

variable (f : M₁ →ₗ[R] M₀) (d : M₂ →ₗ[R] M₁)
  (f₀ : M₁ →ₗ[R] M₀) (d₀ : M₂ →ₗ[R] M₁)

/-- A leading cycle has a homogeneous preimage in the leading complex.
Applying the perturbed differential gives a bounded lift of that cycle. -/
theorem leading_cycle_lift
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (m : ℕ) (x : M₁) (hx : f₀ (component b₁ w₁ m x) = 0) :
    ∃ y, Bound b₂ w₂ m y ∧ Bound b₁ w₁ m (d y) ∧
      component b₁ w₁ m (d y) = component b₁ w₁ m x := by
  have hmem : component b₁ w₁ m x ∈ d₀.range := by
    rw [hexact]
    exact LinearMap.mem_ker.mpr hx
  obtain ⟨z,hz⟩ := hmem
  let y := component b₂ w₂ m z
  have hy : Bound b₂ w₂ m y := bound_component b₂ w₂ m z
  have hyy : component b₂ w₂ m y = y := by
    rw [component_of_homogeneous b₂ w₂ (homogeneous_component b₂ w₂ m z),if_pos rfl]
  have hxx : component b₁ w₁ m (component b₁ w₁ m x) =
      component b₁ w₁ m x := by
    rw [component_of_homogeneous b₁ w₁ (homogeneous_component b₁ w₁ m x),if_pos rfl]
  refine ⟨y,hy,(hd m y hy).1,?_⟩
  rw [(hd m y hy).2,hyy]
  change d₀ (component b₂ w₂ m z) = component b₁ w₁ m x
  rw [hd₀ m z,hz,hxx]

/-- Every actual cycle with bound `m` is a boundary with that same bound.
No completion or infinite series enters the proof. -/
theorem bounded_cycle_is_boundary
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (m : ℕ) (x : M₁) (hbound : Bound b₁ w₁ m x) (hx : f x = 0) :
    ∃ y, Bound b₂ w₂ m y ∧ d y = x := by
  have hfd (y : M₂) : f (d y) = 0 := LinearMap.congr_fun hzero y
  induction m generalizing x with
  | zero =>
      have hc : f₀ (component b₁ w₁ 0 x) = 0 := by
        rw [←(hf 0 x hbound).2,hx,map_zero]
      obtain ⟨y,hy,hdy,he⟩ :=
        leading_cycle_lift b₁ w₁ b₂ w₂ d f₀ d₀ hd hd₀ hexact 0 x hc
      have hz : x-d y = 0 :=
        eq_zero_of_bound_zero_component_zero b₁ w₁
          (bound_sub b₁ w₁ hbound hdy) (by rw [map_sub,he,sub_self])
      exact ⟨y,hy,(sub_eq_zero.mp hz).symm⟩
  | succ m ih =>
      have hc : f₀ (component b₁ w₁ (m+1) x) = 0 := by
        rw [←(hf (m+1) x hbound).2,hx,map_zero]
      obtain ⟨y,hy,hdy,he⟩ :=
        leading_cycle_lift b₁ w₁ b₂ w₂ d f₀ d₀ hd hd₀ hexact (m+1) x hc
      have hr : Bound b₁ w₁ m (x-d y) :=
        bound_pred_of_component_zero b₁ w₁
          (bound_sub b₁ w₁ hbound hdy) (by rw [map_sub,he,sub_self])
      have hcycle : f (x-d y) = 0 := by rw [map_sub,hx,hfd,sub_self]
      obtain ⟨z,hz,hez⟩ := ih (x-d y) hr hcycle
      refine ⟨z+y,bound_add b₂ w₂
        (bound_mono b₂ w₂ (Nat.le_succ m) hz) hy,?_⟩
      rw [map_add,hez,sub_add_cancel]

/-- The entire perturbed pair is exact.  The conclusion is equality of
the actual range and actual kernel. -/
theorem range_eq_ker
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker) : d.range = f.ker := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.mem_ker.mpr (LinearMap.congr_fun hzero y)
  · intro hx
    obtain ⟨m,hm⟩ := exists_bound b₁ w₁ x
    obtain ⟨y,hy,he⟩ := bounded_cycle_is_boundary b₀ w₀ b₁ w₁ b₂ w₂
      f d f₀ d₀ hzero hf hd hd₀ hexact m x hm (LinearMap.mem_ker.mp hx)
    exact ⟨y,he⟩

/-- Cancellation among leading multipliers can be removed by subtracting
actual boundaries. Every bounded image has a preimage with the same bound. -/
theorem image_has_bounded_preimage
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (r : ℕ) (u : M₀) (hu : Bound b₀ w₀ r u) (him : u ∈ f.range) :
    ∃ x, Bound b₁ w₁ r x ∧ f x = u := by
  have hfd (y : M₂) : f (d y) = 0 := LinearMap.congr_fun hzero y
  have reduce : ∀ m x, Bound b₁ w₁ m x → f x = u →
      ∃ z, Bound b₁ w₁ r z ∧ f z = u := by
    intro m
    induction m with
    | zero =>
        intro x hx hxu
        exact ⟨x,bound_mono b₁ w₁ (Nat.zero_le r) hx,hxu⟩
    | succ m ih =>
        intro x hx hxu
        by_cases hmr : m+1 ≤ r
        · exact ⟨x,bound_mono b₁ w₁ hmr hx,hxu⟩
        · have hrm : r < m+1 := Nat.lt_of_not_ge hmr
          have hc : f₀ (component b₁ w₁ (m+1) x) = 0 := by
            rw [←(hf (m+1) x hx).2,hxu]
            exact component_eq_zero_of_bound_lt b₀ w₀ hrm hu
          obtain ⟨y,hy,hdy,he⟩ :=
            leading_cycle_lift b₁ w₁ b₂ w₂ d f₀ d₀ hd hd₀ hexact (m+1) x hc
          apply ih (x-d y)
          · exact bound_pred_of_component_zero b₁ w₁
              (bound_sub b₁ w₁ hx hdy) (by rw [map_sub,he,sub_self])
          · rw [map_sub,hxu,hfd,sub_zero]
  obtain ⟨x,hx⟩ := him
  obtain ⟨m,hm⟩ := exists_bound b₁ w₁ x
  exact reduce m x hm hx

/-- The leading part of every actual image belongs to the leading image.
This is a consequence of strictness, not a premise asserting the desired
associated-graded relation space. -/
theorem component_image_mem_leading_range
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (r : ℕ) (u : M₀) (hu : Bound b₀ w₀ r u) (him : u ∈ f.range) :
    component b₀ w₀ r u ∈ f₀.range := by
  obtain ⟨x,hx,hxu⟩ := image_has_bounded_preimage b₀ w₀ b₁ w₁ b₂ w₂
    f d f₀ d₀ hzero hf hd hd₀ hexact r u hu him
  exact ⟨component b₁ w₁ r x,((hf r x hx).2).symm.trans
    (congrArg (component b₀ w₀ r) hxu)⟩

/-- The initial submodule of the actual image is exactly the leading
image. Its definition uses leading components of actual image vectors. -/
theorem initial_image_eq
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker) :
    initialSubmodule b₀ w₀ f.range = f₀.range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨u,hu,r,hb,rfl⟩
    exact component_image_mem_leading_range b₀ w₀ b₁ w₁ b₂ w₂
      f d f₀ d₀ hzero hf hd hd₀ hexact r u hb hu
  · rintro y ⟨x,rfl⟩
    have hx : x ∈ Submodule.span R (Set.range b₁) := by
      rw [b₁.span_eq]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i,rfl⟩ := hx
        have hbi := homogeneous_bound b₁ w₁ (homogeneous_basis b₁ w₁ i)
        apply Submodule.subset_span
        refine ⟨f (b₁ i),⟨b₁ i,rfl⟩,w₁ i,(hf (w₁ i) (b₁ i) hbi).1,?_⟩
        rw [(hf (w₁ i) (b₁ i) hbi).2,
          component_of_homogeneous b₁ w₁ (homogeneous_basis b₁ w₁ i),if_pos rfl]
    | zero => simpa only [map_zero] using (initialSubmodule b₀ w₀ f.range).zero_mem
    | add x y hx hy ihx ihy =>
        simpa only [map_add] using (initialSubmodule b₀ w₀ f.range).add_mem ihx ihy
    | smul a x hx ih =>
        simpa only [map_smul] using (initialSubmodule b₀ w₀ f.range).smul_mem a ih

end PaperVerification.FilteredComplex
end
end
end TAF_LiteralSource_0271

section TAF_LiteralSource_0272
/- Original module: PaperVerification.AlternatingFormsFilteredComparison -/


/-!
# From actual basis comparisons to filtered exactness

These lemmas turn a strict coefficient bound on the difference between
two maps into the full filtered-complex hypotheses. They apply to every
finite-support vector, not only to individual basis tensors. The exactness
conclusion is for the original differential and uses its actual
square-zero identity.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.FilteredComparison

open scoped BigOperators
open PaperVerification.Fermion.BasisFiltered
open PaperVerification.FilteredComplex

variable {K M₀ M₁ M₂ I₀ I₁ I₂ : Type*} [CommRing K]
  [AddCommGroup M₀] [Module K M₀] [AddCommGroup M₁] [Module K M₁]
  [AddCommGroup M₂] [Module K M₂]
  (b₀ : Module.Basis I₀ K M₀) (w₀ : I₀ → ℕ)
  (b₁ : Module.Basis I₁ K M₁) (w₁ : I₁ → ℕ)
  (b₂ : Module.Basis I₂ K M₂) (w₂ : I₂ → ℕ)

theorem hasTop_of_strict_difference (d : ℕ) (x y : M₀)
    (hy : Homogeneous b₀ w₀ d y)
    (hxy : ∀ i,b₀.repr (x-y) i≠0 → w₀ i<d) :
    HasTop b₀ w₀ d x y := by
  have hcomponent : component b₀ w₀ d (x-y)=0 := by
    apply b₀.repr.injective
    ext i
    rw [repr_component,map_zero,Finsupp.zero_apply]
    by_cases hi : w₀ i=d
    · rw [if_pos hi]
      by_contra hne
      have hlt := hxy i hne
      omega
    · rw [if_neg hi]
  refine ⟨?_,?_⟩
  · intro i hi
    by_cases hyi : b₀.repr y i=0
    · apply le_of_lt
      apply hxy i
      simpa only [map_sub,Finsupp.sub_apply,hyi,sub_zero] using hi
    · exact (hy i hyi).le
  · rw [map_sub,component_of_homogeneous b₀ w₀ hy,if_pos rfl,sub_eq_zero] at hcomponent
    exact hcomponent

theorem leadingMap_of_basis (f g : M₁ →ₗ[K] M₀)
    (h : ∀ i,HasTop b₀ w₀ (w₁ i) (f (b₁ i)) (g (b₁ i))) :
    HasLeadingMap b₀ w₀ b₁ w₁ f g := by
  intro d x hx
  have hstep (i : I₁) (hi : i∈(b₁.repr x).support) :
      HasTop b₀ w₀ d (f (b₁ i)) (g (component b₁ w₁ d (b₁ i))) := by
    have hle := hx i (Finsupp.mem_support_iff.mp hi)
    by_cases he : d=w₁ i
    · subst d
      rw [component_of_homogeneous b₁ w₁ (homogeneous_basis b₁ w₁ i),if_pos rfl]
      exact h i
    · have hlt : w₁ i<d := by omega
      refine ⟨bound_mono b₀ w₀ hle (h i).1,?_⟩
      rw [component_eq_zero_of_bound_lt b₀ w₀ hlt (h i).1,
        component_of_homogeneous b₁ w₁ (homogeneous_basis b₁ w₁ i),if_neg he,map_zero]
  have hs := HasTop.sum b₀ w₀ (b₁.repr x).support
    (fun i ↦ b₁.repr x i • f (b₁ i))
    (fun i ↦ b₁.repr x i • g (component b₁ w₁ d (b₁ i))) d
    (fun i hi ↦ HasTop.smul b₀ w₀ (hstep i hi) (b₁.repr x i))
  have he : ∑ i∈(b₁.repr x).support,b₁.repr x i • b₁ i=x := by
    simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using b₁.linearCombination_repr x
  have hfx : ∑ i∈(b₁.repr x).support,b₁.repr x i • f (b₁ i)=f x := by
    simpa only [map_sum,map_smul] using congrArg f he
  have hgx : ∑ i∈(b₁.repr x).support,
      b₁.repr x i • g (component b₁ w₁ d (b₁ i))=g (component b₁ w₁ d x) := by
    simpa only [map_sum,map_smul] using congrArg (fun z ↦ g (component b₁ w₁ d z)) he
  simpa only [hfx,hgx,HasTop] using hs

theorem preservesComponents_of_basis (g : M₁ →ₗ[K] M₀)
    (h : ∀ i,Homogeneous b₀ w₀ (w₁ i) (g (b₁ i))) :
    PreservesComponents b₀ w₀ b₁ w₁ g := by
  intro d x
  have he : g.comp (component b₁ w₁ d)=(component b₀ w₀ d).comp g := by
    apply b₁.ext
    intro i
    simp only [LinearMap.comp_apply,
      component_of_homogeneous b₁ w₁ (homogeneous_basis b₁ w₁ i),
      component_of_homogeneous b₀ w₀ (h i)]
    split_ifs <;> simp only [map_zero]
  exact LinearMap.congr_fun he x

/-- Once the actual leading basis formulas and the cut exactness are
established, this proves exactness of the original coefficient maps. -/
theorem range_eq_ker_of_basis (f : M₁ →ₗ[K] M₀) (d : M₂ →ₗ[K] M₁)
    (f₀ : M₁ →ₗ[K] M₀) (d₀ : M₂ →ₗ[K] M₁)
    (hzero : f.comp d=0)
    (hf : ∀ i,HasTop b₀ w₀ (w₁ i) (f (b₁ i)) (f₀ (b₁ i)))
    (hd : ∀ i,HasTop b₁ w₁ (w₂ i) (d (b₂ i)) (d₀ (b₂ i)))
    (hexact : d₀.range=f₀.ker) :
    d.range=f.ker := by
  apply PaperVerification.FilteredComplex.range_eq_ker b₀ w₀ b₁ w₁ b₂ w₂
    f d f₀ d₀ hzero (leadingMap_of_basis b₀ w₀ b₁ w₁ f f₀ hf)
    (leadingMap_of_basis b₁ w₁ b₂ w₂ d d₀ hd)
  · apply preservesComponents_of_basis b₁ w₁ b₂ w₂
    intro i
    rw [←(hd i).2]
    exact homogeneous_component b₁ w₁ _ _
  · exact hexact

end PaperVerification.AlternatingForms.FilteredComparison

end
end
end TAF_LiteralSource_0272

