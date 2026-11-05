module

public import PaperVerification.FermionNewtonDegreeCount

/-!
# The full rational Newton basis and its actual contraction ideal

All determinant hypotheses are discharged here for the literal columns.
The rational module is the image of the paper's common-numerator module under
division by its nonzero common denominator. The basis vectors are identified
coordinate by coordinate with equation (7).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial Module
open scoped BigOperators Matrix

variable {F : Type*} [Field F] {n : ℕ}

theorem singleton_weight_ne_zero
    (β : Fin n → F)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) (i : Fin n) : β i ≠ 0 := by
  simpa only [Finset.sum_singleton] using (hβ {i} (Finset.singleton_nonempty i)).ne_zero

def newtonNumeratorBasis
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Module.Basis (Fin n) (P (F := F) (n := n)) (numeratorModule β δ σ) := by
  let c := Classical.choose (exists_commonNumerator_determinant_scalar β δ σ hc hσ hβ)
  have hcdata := Classical.choose_spec (exists_commonNumerator_determinant_scalar β δ σ hc hσ hβ)
  exact numeratorBasisOfDeterminant β δ σ (commonNumeratorMatrix β δ σ hc)
    (singleton_weight_ne_zero β hβ)
    (commonNumeratorMatrix_column_mem β δ σ hc (singleton_weight_ne_zero β hβ))
    (C c) ((isUnit_iff_ne_zero.mpr hcdata.1).map MvPolynomial.C) hcdata.2

@[simp] theorem newtonNumeratorBasis_apply
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) (i : Fin n) :
    ((newtonNumeratorBasis β δ σ hc hσ hβ i : numeratorModule β δ σ) : Fin n → (P (F := F) (n := n))) =
      columnCommonNumerator β δ σ hc i := by
  simp only [newtonNumeratorBasis, numeratorBasisOfDeterminant_apply, commonNumeratorMatrix]

def divideByNegativeDenominator (σ : Fin n → ℤ) :
    (Fin n → P (F := F) (n := n)) →ₗ[P (F := F) (n := n)] (Fin n → RationalFunctions (F := F) (n := n)) where
  toFun a k := algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (a k) /
    algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (negativeDenominator σ)
  map_add' a b := by
    funext k
    simp only [Pi.add_apply, map_add, add_div]
  map_smul' p a := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def, RingHom.id_apply]
    ring

theorem divideByNegativeDenominator_injective (σ : Fin n → ℤ) :
    Function.Injective (divideByNegativeDenominator (F := F) σ) := by
  have hq : algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (negativeDenominator σ) ≠ 0 := by
    intro hz
    exact negativeDenominator_ne_zero σ
      (IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (by simpa using hz))
  intro a b hab
  funext k
  apply IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))
  apply mul_right_cancel₀ (inv_ne_zero hq)
  simpa only [divideByNegativeDenominator, LinearMap.coe_mk, AddHom.coe_mk,
    div_eq_mul_inv] using congrFun hab k

/-- The exact rational module of Section 2.1, realized inside the actual
fraction field of the original polynomial ring. -/
def rationalNewtonModule (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) :
    Submodule (P (F := F) (n := n)) (Fin n → RationalFunctions (F := F) (n := n)) :=
  (numeratorModule β δ σ).map (divideByNegativeDenominator σ)

def newtonFieldBasis
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Module.Basis (Fin n) (P (F := F) (n := n)) (rationalNewtonModule β δ σ) :=
  (newtonNumeratorBasis β δ σ hc hσ hβ).map
    (Submodule.equivMapOfInjective (divideByNegativeDenominator σ)
      (divideByNegativeDenominator_injective σ) (numeratorModule β δ σ))

/-- The constructed basis is exactly the paper's displayed rational columns. -/
@[simp] theorem newtonFieldBasis_apply
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) (i k : Fin n) :
    ((newtonFieldBasis β δ σ hc hσ hβ i : rationalNewtonModule β δ σ) :
      Fin n → RationalFunctions (F := F) (n := n)) k = newtonColumn β δ σ i k := by
  change (((newtonNumeratorBasis β δ σ hc hσ hβ).map
    (Submodule.equivMapOfInjective (divideByNegativeDenominator σ)
      (divideByNegativeDenominator_injective σ) (numeratorModule β δ σ))) i :
      Fin n → RationalFunctions (F := F) (n := n)) k = _
  rw [Module.Basis.map_apply, Submodule.coe_equivMapOfInjective_apply,
    newtonNumeratorBasis_apply]
  change algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (columnCommonNumerator β δ σ hc i k) /
    algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (negativeDenominator σ) = _
  rw [map_columnCommonNumerator]
  have hq : algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (negativeDenominator σ) ≠ 0 := by
    intro hz
    exact negativeDenominator_ne_zero σ
      (IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (by simpa using hz))
  exact mul_div_cancel_left₀ _ hq

def weightedNumeratorMap (β : Fin n → F) : (Fin n → P (F := F) (n := n)) →ₗ[P (F := F) (n := n)] (P (F := F) (n := n)) :=
  ∑ k, (C (β k) : P (F := F) (n := n)) •
    (LinearMap.proj k : (Fin n → P (F := F) (n := n)) →ₗ[P (F := F) (n := n)] P (F := F) (n := n))

@[simp] theorem weightedNumeratorMap_apply (β : Fin n → F) (a : Fin n → P (F := F) (n := n)) :
    weightedNumeratorMap β a = ∑ k, C (β k) * a k := by
  simp only [weightedNumeratorMap, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

/-- The ideal generated by the displayed polynomial contractions equals the
contraction ideal of the full module. The reverse inclusion is proved by the
actual Newton basis expansion, not assumed from a determinant calculation. -/
theorem span_columnContractions_eq_contractionIdeal
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Ideal.span (Set.range (columnContraction β δ σ)) = contractionIdeal β δ σ := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact columnContraction_mem_contractionIdeal β δ σ hc (singleton_weight_ne_zero β hβ) i
  · rintro p ⟨a,ha,hap⟩
    let B := newtonNumeratorBasis β δ σ hc hσ hβ
    let v : numeratorModule β δ σ := ⟨a,ha⟩
    let L := (weightedNumeratorMap β).comp (numeratorModule β δ σ).subtype
    have hL (i : Fin n) : L (B i) = negativeDenominator σ * columnContraction β δ σ i := by
      change weightedNumeratorMap β (B i : Fin n → (P (F := F) (n := n))) = _
      rw [newtonNumeratorBasis_apply, weightedNumeratorMap_apply]
      exact columnCommonNumerator_weighted_sum β δ σ hc (singleton_weight_ne_zero β hβ) i
    have hv : L v = negativeDenominator σ * p := by
      change weightedNumeratorMap β a = _
      simpa only [weightedNumeratorMap_apply] using hap
    have hexp := congrArg L (B.sum_repr v)
    simp only [map_sum, map_smul, hL, hv, smul_eq_mul] at hexp
    have hp : p = ∑ i, B.repr v i * columnContraction β δ σ i := by
      apply mul_left_cancel₀ (negativeDenominator_ne_zero σ)
      rw [Finset.mul_sum]
      simpa only [mul_left_comm] using hexp.symm
    rw [hp]
    apply Ideal.sum_mem
    intro i hi
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)

end PaperVerification.Fermion.Newton
