module

public import PaperVerification.AlternatingFormsEvenWalkDeterminants
public import PaperVerification.AlternatingFormsBooleanGoodSubsets
import Lean.Elab.Tactic.Omega

/-!
# The independent universal kernel family indexed by good subsets

The indexing set is the actual set of Boolean monomials whose associated
walk stays in the strip.  No ordering or distinctness assumption is imposed
on a proposed family: both follow here from the crossing fibers of those
walks.  The resulting nonzero coefficient minor is a polynomial in the two
original universal coefficient vectors.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms.EvenDeterminants

open scoped BigOperators Classical
open BooleanWalks EvenWalkDeterminants PolynomialMinors

variable {K : Type*} [CommRing K] {m q : ℕ}

def goodFiberDegree (S : GoodSubset m q) (a : Fin (m - 2 * q)) : ℕ :=
  fiberDegree (height S) m a

def goodFiberColumns (S : GoodSubset m q) (a : Fin (m - 2 * q)) :
    Fin (2 * goodFiberDegree S a + 1) → Fin m :=
  fiberColumns (height S) m (m - 2 * q) (height_zero S) (height_final S)
    (height_step S) a

theorem goodFiberColumns_strictMono (S : GoodSubset m q) (a : Fin (m - 2 * q)) :
    StrictMono (goodFiberColumns S a) :=
  fiberColumns_strictMono (height S) m (m - 2 * q) (height_zero S) (height_final S)
    (height_step S) a

theorem goodFiberColumns_disjoint (S : GoodSubset m q) :
    Function.Injective (fun p : (a : Fin (m - 2 * q)) × Fin (2 * goodFiberDegree S a + 1) =>
      goodFiberColumns S p.1 p.2) :=
  fiberColumns_disjoint (height S) m (m - 2 * q) (height_zero S) (height_final S)
    (height_step S)

theorem goodFiberDegree_sum (S : GoodSubset m q) :
    (∑ a, goodFiberDegree S a) = q := by
  have hq := good_degree_bound S
  exact sum_fiberDegree (height S) m (m - 2 * q) q (height_zero S) (height_final S)
    (height_bound S) (height_step S) (by omega)

theorem goodLeadingExponent_apply (S : GoodSubset m q) (i : Fin m) :
    productLeadingExponent m (goodFiberDegree S) (goodFiberColumns S) i =
      if i ∈ S.val.val then 1 else 0 := by
  change productLeadingExponent m (fun a : Fin (m - 2 * q) => fiberDegree (height S) m a)
    (fiberColumns (height S) m (m - 2 * q) (height_zero S) (height_final S)
      (height_step S)) i = if i ∈ S.val.val then 1 else 0
  rw [EvenWalkDeterminants.productLeadingExponent_apply
    (height S) m (m - 2 * q) (height_zero S) (height_final S)
    (height_bound S) (height_step S) i]
  simp only [height_downward_iff]

/-- Distinct actual monomials index distinct actual leading exponent vectors. -/
theorem goodLeadingExponent_injective (m q : ℕ) :
    Function.Injective (fun S : GoodSubset m q =>
      productLeadingExponent m (goodFiberDegree S) (goodFiberColumns S)) := by
  intro S T h
  apply Subtype.ext
  apply Subtype.ext
  ext i
  have hi := congrArg (fun e : Fin m →₀ ℕ => e i) h
  rw [goodLeadingExponent_apply, goodLeadingExponent_apply] at hi
  by_cases hS : i ∈ S.val.val <;> by_cases hT : i ∈ T.val.val <;>
    simp_all only [if_true, if_false, Nat.one_ne_zero, Nat.zero_ne_one]

def goodDeterminantProduct (b c : Fin m → K) (S : GoodSubset m q) :
    MvPolynomial (Fin m) K :=
  determinantProduct m (goodFiberDegree S) (goodFiberColumns S) b c

theorem goodDeterminantProduct_joint_kernel (b c : Fin m → K) (S : GoodSubset m q) :
    directionalDerivative b (goodDeterminantProduct b c S) = 0 ∧
    directionalDerivative c (goodDeterminantProduct b c S) = 0 :=
  determinantProduct_joint_kernel m (goodFiberDegree S) (goodFiberColumns S) b c

theorem goodDeterminantProduct_homogeneous (b c : Fin m → K) (S : GoodSubset m q) :
    (goodDeterminantProduct b c S).IsHomogeneous q := by
  have h := determinantProduct_homogeneous m (goodFiberDegree S) (goodFiberColumns S) b c
  rw [goodFiberDegree_sum] at h
  exact h

theorem goodDeterminantProduct_degreeOf_le_one [Nontrivial K]
    (b c : Fin m → K) (S : GoodSubset m q) (i : Fin m) :
    (goodDeterminantProduct b c S).degreeOf i ≤ 1 :=
  determinantProduct_degreeOf_le_one m (goodFiberDegree S) (goodFiberColumns S)
    (goodFiberColumns_disjoint S) b c i

/-- The good-by-good coefficient minor is nonzero in the universal parameter
ring.  This includes empty indexing sets and all boundary parameter values. -/
theorem goodUniversalProduct_coefficient_det_ne_zero [IsDomain K] (m q : ℕ) :
    (coefficientMatrix
      (fun S : GoodSubset m q => productLeadingExponent m (goodFiberDegree S) (goodFiberColumns S))
      (fun S : GoodSubset m q => universalProduct (K := K) m
        (goodFiberDegree S) (goodFiberColumns S))).det ≠ 0 := by
  classical
  exact universalProduct_coefficient_det_ne_zero m goodFiberDegree goodFiberColumns
    goodFiberColumns_strictMono (goodLeadingExponent_injective m q)

theorem goodUniversalProduct_linearIndependent [IsDomain K] (m q : ℕ) :
    LinearIndependent (UniversalParameters K m)
      (fun S : GoodSubset m q => universalProduct (K := K) m
        (goodFiberDegree S) (goodFiberColumns S)) := by
  classical
  exact universalProduct_linearIndependent m goodFiberDegree goodFiberColumns
    goodFiberColumns_strictMono (goodLeadingExponent_injective m q)

end PaperVerification.AlternatingForms.EvenDeterminants
