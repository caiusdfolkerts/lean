module

public import PaperVerification.AlternatingFormsEvenBooleanLowerBound
public import PaperVerification.AlternatingFormsEvenGoodDeterminants
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The generic lower bound for the ordinary Boolean quotient

The indexing set is the paper's actual set of good Boolean subsets.  Its
determinant products supply one explicit nonzero polynomial minor in the
original two coefficient vectors.  Wherever this minor is nonzero, the
ordinary Boolean quotient has dimension at least the number of good subsets.
The same bound is established at the generic point of parameter space.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.EvenDeterminants

open scoped BigOperators
open BooleanQuotient BooleanWalks PolynomialMinors

variable {K F : Type*} [Field K] [CommRing F]

def goodCoefficientMinor (m q : ℕ) : UniversalParameters K m :=
  (coefficientMatrix
    (fun S : GoodSubset m q => productLeadingExponent m (goodFiberDegree S) (goodFiberColumns S))
    (fun S : GoodSubset m q => universalProduct (K := K) m
      (goodFiberDegree S) (goodFiberColumns S))).det

theorem goodCoefficientMinor_ne_zero (m q : ℕ) : goodCoefficientMinor (K := K) m q ≠ 0 :=
  goodUniversalProduct_coefficient_det_ne_zero m q

/-- The same minor after any honest coefficient-ring specialization. -/
theorem map_goodCoefficientMinor (m q : ℕ) (φ : UniversalParameters K m →+* F) :
    φ (goodCoefficientMinor m q) =
      (coefficientMatrix
        (fun S : GoodSubset m q => productLeadingExponent m (goodFiberDegree S) (goodFiberColumns S))
        (fun S : GoodSubset m q => goodDeterminantProduct
          (fun i => φ (universalFirst m i)) (fun i => φ (universalSecond m i)) S)).det := by
  rw [goodCoefficientMinor, φ.map_det, coefficientMatrix_map]
  simp only [universalProduct, determinantProduct_map, goodDeterminantProduct]

def evaluateParameters {m : ℕ} (b c : Fin m → K) : UniversalParameters K m →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) (fun z => if z.1 then c z.2 else b z.2)

@[simp] theorem evaluateParameters_first {m : ℕ} (b c : Fin m → K) (i : Fin m) :
    evaluateParameters b c (universalFirst m i) = b i := by
  rw [evaluateParameters, universalFirst, MvPolynomial.eval₂Hom_X']
  rfl

@[simp] theorem evaluateParameters_second {m : ℕ} (b c : Fin m → K) (i : Fin m) :
    evaluateParameters b c (universalSecond m i) = c i := by
  rw [evaluateParameters, universalSecond, MvPolynomial.eval₂Hom_X']
  rfl

theorem evaluate_goodCoefficientMinor {m : ℕ} (q : ℕ) (b c : Fin m → K) :
    evaluateParameters b c (goodCoefficientMinor m q) =
      (coefficientMatrix
        (fun S : GoodSubset m q => productLeadingExponent m (goodFiberDegree S) (goodFiberColumns S))
        (fun S : GoodSubset m q => goodDeterminantProduct b c S)).det := by
  simpa only [evaluateParameters_first, evaluateParameters_second] using
    map_goodCoefficientMinor m q (evaluateParameters b c)

theorem good_boolean_lower_bound_of_minor {m : ℕ} (q : ℕ) (b c : Fin m → K)
    (hminor : evaluateParameters b c (goodCoefficientMinor m q) ≠ 0) :
    Fintype.card (GoodSubset m q) ≤ Module.finrank K (piece b c q) := by
  apply card_le_finrank_booleanPiece_of_coefficient_det_ne_zero m q
    goodFiberDegree goodFiberColumns goodFiberDegree_sum goodFiberColumns_disjoint b c
    (fun S : GoodSubset m q => productLeadingExponent m (goodFiberDegree S) (goodFiberColumns S))
  simpa only [evaluate_goodCoefficientMinor, goodDeterminantProduct] using hminor

abbrev GenericBooleanField (m : ℕ) := FractionRing (UniversalParameters K m)

def genericFirst (m : ℕ) (i : Fin m) : GenericBooleanField (K := K) m :=
  algebraMap (UniversalParameters K m) (GenericBooleanField m) (universalFirst m i)

def genericSecond (m : ℕ) (i : Fin m) : GenericBooleanField (K := K) m :=
  algebraMap (UniversalParameters K m) (GenericBooleanField m) (universalSecond m i)

theorem generic_goodCoefficientMinor_ne_zero (m q : ℕ) :
    (coefficientMatrix
      (fun S : GoodSubset m q => productLeadingExponent m (goodFiberDegree S) (goodFiberColumns S))
      (fun S : GoodSubset m q => goodDeterminantProduct
        (genericFirst (K := K) m) (genericSecond (K := K) m) S)).det ≠ 0 := by
  intro hz
  apply goodCoefficientMinor_ne_zero (K := K) m q
  apply IsFractionRing.injective (UniversalParameters K m) (GenericBooleanField (K := K) m)
  rw [map_zero, map_goodCoefficientMinor]
  exact hz

/-- The generic point has the lower dimension bound, for every degree and
every finite number of variables. -/
theorem good_boolean_generic_lower_bound (m q : ℕ) :
    Fintype.card (GoodSubset m q) ≤
      Module.finrank (GenericBooleanField (K := K) m)
        (piece (genericFirst (K := K) m) (genericSecond (K := K) m) q) := by
  apply card_le_finrank_booleanPiece_of_coefficient_det_ne_zero m q
    goodFiberDegree goodFiberColumns goodFiberDegree_sum goodFiberColumns_disjoint
    (genericFirst m) (genericSecond m)
    (fun S : GoodSubset m q => productLeadingExponent m (goodFiberDegree S) (goodFiberColumns S))
  exact generic_goodCoefficientMinor_ne_zero m q

end PaperVerification.AlternatingForms.EvenDeterminants
