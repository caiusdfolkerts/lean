module

public import PaperVerification.FermionNewtonBoxes
public import PaperVerification.FermionKoszulColon
public import PaperVerification.FermionFrobenius
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# The actual ordinary-moment comparison and its determinant

The polynomial comparison matrix is obtained by expanding the ordinary power
fields in the already constructed Newton basis.  Its determinant is the
literal difference product, up to a nonzero coefficient scalar.  The Koszul
determinant-colon theorem then identifies the contraction ideal with the
principal colon of the actual ordinary moment ideal.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators Matrix

variable {F : Type*} [Field F] {n : ℕ}

theorem compatible_constant (s : ℕ) (σ : Fin n → ℤ) : Compatible (fun _ ↦ s) σ :=
  ⟨fun _ _ _ _ ↦ le_rfl,fun _ _ _ _ ↦ le_rfl⟩

def differenceMultiplicity (σ : Fin n → ℤ) (i : Fin n) : ℕ := (1 - σ i).toNat

/-- Exactly the product `∏_{i<j}(yᵢ-yⱼ)^(1-σᵢ)` in equation (9). -/
def differenceProduct (σ : Fin n → ℤ) : P (F := F) (n := n) :=
  ∏ e : Edge n, edgeLinear e ^ differenceMultiplicity σ e.1.1

theorem differenceProduct_ne_zero (σ : Fin n → ℤ) : differenceProduct (F := F) σ ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro e he
  exact pow_ne_zero _ (edgeLinear_prime e).ne_zero

theorem edge_product_eq_double_product {R : Type*} [CommMonoid R]
    (f : Fin n → Fin n → R) :
    (∏ e : Edge n, f e.1.1 e.1.2) = ∏ i, ∏ j ∈ Finset.Ioi i, f i j := by
  classical
  have h := Fintype.prod_of_injective
    (Subtype.val : Edge n → Fin n × Fin n) Subtype.val_injective
    (fun e : Edge n ↦ f e.1.1 e.1.2)
    (fun a : Fin n × Fin n ↦ if a.1 < a.2 then f a.1 a.2 else 1)
    (by
      intro a ha
      have hlt : ¬ a.1 < a.2 := fun hh ↦ ha ⟨⟨a,hh⟩,rfl⟩
      simp only [if_neg hlt])
    (by intro e; simp only [if_pos e.property])
  rw [Fintype.prod_prod_type] at h
  simpa only [← Finset.prod_filter,Finset.filter_lt_eq_Ioi] using h

def vandermondeOrientation (F : Type*) [Field F] (n : ℕ) : F :=
  (-1) ^ Fintype.card (Edge n)

theorem vandermondeOrientation_ne_zero : vandermondeOrientation F n ≠ 0 :=
  pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

theorem polynomial_vandermonde_det :
    (Matrix.vandermonde (X : Fin n → P (F := F) (n := n))).det =
      C (vandermondeOrientation F n) * ∏ e : Edge n, edgeLinear e := by
  rw [Matrix.det_vandermonde,← edge_product_eq_double_product]
  have he : (fun e : Edge n ↦ (X e.1.2 - X e.1.1 : P (F := F) (n := n))) =
      (fun e ↦ -edgeLinear e) := by funext e; simp only [edgeLinear,neg_sub]
  rw [he,Finset.prod_neg]
  simp only [vandermondeOrientation,map_pow,map_neg,map_one,Finset.card_univ]

theorem numerator_factor_times_difference
    (s : ℕ) (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1) :
    numeratorDetFactor (F := F) (fun _ ↦ s) σ * differenceProduct σ =
      negativeDenominator σ ^ n * (∏ i, X i ^ s) * ∏ e : Edge n, edgeLinear e := by
  classical
  have he (e : Edge n) :
      edgeLinear (F := F) e ^ (if σ e.1.1 = 1 then 1 else if σ e.1.1 = -1 then n - 1 else 0) *
        edgeLinear e ^ differenceMultiplicity σ e.1.1 =
      (if σ e.1.1 = -1 then edgeLinear e else 1) ^ n * edgeLinear e := by
    rcases hσ e.1.1 with hn | hz | hp
    · have hnpos : 0 < n := by have hh := e.1.1.isLt; omega
      have hexp : n - 1 + 2 = n + 1 := by omega
      simp only [hn,show (-1 : ℤ) ≠ 1 by omega,if_false,if_true,
        differenceMultiplicity,Int.toNat_natCast]
      change edgeLinear (F := F) e ^ (n - 1) * edgeLinear e ^ (2 : ℕ) =
        edgeLinear e ^ n * edgeLinear e
      rw [← pow_add,hexp,pow_succ]
    · simp [hz,differenceMultiplicity]
    · simp [hp,differenceMultiplicity]
  have hprod := congrArg (fun f : Edge n → P (F := F) (n := n) ↦ ∏ e, f e) (funext he)
  simp only [Finset.prod_mul_distrib,Finset.prod_pow] at hprod
  have hQ : negativeDenominator (F := F) σ =
      ∏ e : Edge n, if σ e.1.1 = -1 then edgeLinear e else 1 := by
    simp only [negativeDenominator,Finset.prod_filter]
  simp only [numeratorDetFactor,Fintype.prod_sum_type,hyperplaneLinear,numeratorMultiplicity,
    differenceProduct]
  rw [mul_assoc,hprod,← hQ]
  ring

def ordinaryNumeratorField (β : Fin n → F) (s : ℕ) (σ : Fin n → ℤ) (j : Fin n) :
    numeratorModule β (fun _ ↦ s) σ :=
  ⟨fun k ↦ negativeDenominator σ * X k ^ (s + j.val),
    powerField_mem_numeratorModule β (fun _ ↦ s) σ (s + j.val) (fun _ ↦ Nat.le_add_right _ _)⟩

def ordinaryComparisonMatrix
    (β : Fin n → F) (s : ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Matrix (Fin n) (Fin n) (P (F := F) (n := n)) :=
  fun i j ↦ (newtonNumeratorBasis β (fun _ ↦ s) σ (compatible_constant s σ) hσ hβ).repr
    (ordinaryNumeratorField β s σ j) i

theorem numeratorMatrix_mul_ordinaryComparison
    (β : Fin n → F) (s : ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    commonNumeratorMatrix β (fun _ ↦ s) σ (compatible_constant s σ) *
        ordinaryComparisonMatrix β s σ hσ hβ =
      Matrix.of (fun k j : Fin n ↦ negativeDenominator σ * X k ^ (s + j.val)) := by
  apply Matrix.ext
  intro k j
  have h := congrArg (fun v : numeratorModule β (fun _ ↦ s) σ ↦ v.val k)
    ((newtonNumeratorBasis β (fun _ ↦ s) σ (compatible_constant s σ) hσ hβ).sum_repr
      (ordinaryNumeratorField β s σ j))
  simpa only [Matrix.mul_apply,Matrix.of_apply,commonNumeratorMatrix,ordinaryComparisonMatrix,
    Submodule.coe_sum,Finset.sum_apply,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul,
    newtonNumeratorBasis_apply,ordinaryNumeratorField,mul_comm] using h

theorem ordinaryNumeratorMatrix_det (s : ℕ) (σ : Fin n → ℤ) :
    (Matrix.of (fun k j : Fin n ↦ negativeDenominator (F := F) σ * X k ^ (s + j.val))).det =
      C (vandermondeOrientation F n) *
        (negativeDenominator σ ^ n * (∏ i, X i ^ s) * ∏ e : Edge n, edgeLinear e) := by
  have he : Matrix.of (fun k j : Fin n ↦ negativeDenominator (F := F) σ * X k ^ (s + j.val)) =
      Matrix.of (fun k j ↦ (negativeDenominator σ * X k ^ s) *
        Matrix.vandermonde (X : Fin n → P (F := F) (n := n)) k j) := by
    ext k j
    simp only [Matrix.of_apply,Matrix.vandermonde_apply,pow_add,mul_assoc]
  rw [he,Matrix.det_mul_column,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,polynomial_vandermonde_det]
  ring

/-- The determinant of the actual polynomial basis-comparison map is the
paper's difference product up to a coefficient unit. -/
theorem exists_ordinaryComparison_determinant_scalar
    (β : Fin n → F) (s : ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    ∃ c : F, c ≠ 0 ∧ (ordinaryComparisonMatrix β s σ hσ hβ).det = C c * differenceProduct σ := by
  obtain ⟨c,hc,hdet⟩ := exists_commonNumerator_determinant_scalar β (fun _ ↦ s) σ
    (compatible_constant s σ) hσ hβ
  have h := congrArg Matrix.det (numeratorMatrix_mul_ordinaryComparison β s σ hσ hβ)
  rw [Matrix.det_mul,hdet,ordinaryNumeratorMatrix_det,
    ← numerator_factor_times_difference s σ hσ] at h
  have he : C c * (ordinaryComparisonMatrix β s σ hσ hβ).det =
      C (vandermondeOrientation F n) * differenceProduct σ := by
    apply mul_left_cancel₀ (numeratorDetFactor_ne_zero (F := F) (fun _ ↦ s) σ)
    convert h using 1 <;> ring
  refine ⟨c⁻¹ * vandermondeOrientation F n,
    mul_ne_zero (inv_ne_zero hc) vandermondeOrientation_ne_zero,?_⟩
  apply mul_left_cancel₀ (show (C c : P (F := F) (n := n)) ≠ 0 from C_ne_zero.mpr hc)
  rw [he,← mul_assoc,← map_mul]
  congr 1
  congr 1
  field_simp

theorem ordinaryComparison_contraction
    (β : Fin n → F) (s : ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) (j : Fin n) :
    (∑ i, ordinaryComparisonMatrix β s σ hσ hβ i j * columnContraction β (fun _ ↦ s) σ i) =
      powerMoment (fun _ ↦ 1) β s j := by
  let B := newtonNumeratorBasis β (fun _ ↦ s) σ (compatible_constant s σ) hσ hβ
  let L := (weightedNumeratorMap β).comp (numeratorModule β (fun _ ↦ s) σ).subtype
  have he := congrArg L (B.sum_repr (ordinaryNumeratorField β s σ j))
  have hL (i : Fin n) : L (B i) = negativeDenominator σ * columnContraction β (fun _ ↦ s) σ i := by
    change weightedNumeratorMap β (B i : Fin n → (P (F := F) (n := n))) = _
    rw [newtonNumeratorBasis_apply,weightedNumeratorMap_apply]
    exact columnCommonNumerator_weighted_sum β (fun _ ↦ s) σ
      (compatible_constant s σ) (singleton_weight_ne_zero β hβ) i
  have hO : L (ordinaryNumeratorField β s σ j) =
      negativeDenominator σ * powerMoment (fun _ ↦ 1) β s j := by
    simp only [L,LinearMap.comp_apply,Submodule.subtype_apply,ordinaryNumeratorField,
      weightedNumeratorMap_apply,powerMoment,one_mul,Finset.mul_sum,mul_left_comm]
  simp only [map_sum,map_smul,hL,hO,smul_eq_mul] at he
  apply mul_left_cancel₀ (negativeDenominator_ne_zero σ)
  rw [Finset.mul_sum]
  simpa only [ordinaryComparisonMatrix,B,mul_left_comm] using he

/-- Equation (9), with the literal ordinary power-moment ideal on its left.
No comparison matrix, colon equality, or length is supplied as a hypothesis. -/
theorem ordinary_principalColon_eq_contraction
    (β : Fin n → F) (s : ℕ) (hs : 0 < s) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    principalColon (powerMomentIdeal (fun _ ↦ 1) β s) (differenceProduct σ) =
      contractionIdeal β (fun _ ↦ s) σ := by
  let G := ordinaryComparisonMatrix β s σ hσ hβ
  have hg : Fintype.linearCombination (P (F := F) (n := n)) (columnContraction β (fun _ ↦ s) σ) ∘ₗ
        Matrix.toLin' G =
      Fintype.linearCombination (P (F := F) (n := n)) (fun j : Fin n ↦ powerMoment (fun _ ↦ 1) β s j) := by
    apply (Pi.basisFun (P (F := F) (n := n)) (Fin n)).ext
    intro j
    simp only [LinearMap.comp_apply,Pi.basisFun_apply,Matrix.toLin'_apply,
      Matrix.mulVec_single_one,Fintype.linearCombination_apply_single,one_smul,
      Fintype.linearCombination_apply,smul_eq_mul,Matrix.col_apply]
    simpa only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using
      ordinaryComparison_contraction β s σ hσ hβ j
  have hcol := Koszul.span_colon_det_eq_of_isWeaklyRegular
    (columnContraction β (fun _ ↦ s) σ)
    (fun j : Fin n ↦ powerMoment (fun _ ↦ 1) β s j) (Matrix.toLin' G) hg
    (powerMoments_isWeaklyRegular (fun _ ↦ 1) β s (by simp) hs hβ)
  rw [LinearMap.det_toLin',span_columnContractions_eq_contractionIdeal β (fun _ ↦ s) σ
    (compatible_constant s σ) hσ hβ] at hcol
  obtain ⟨c,hc,hdet⟩ := exists_ordinaryComparison_determinant_scalar β s σ hσ hβ
  change (powerMomentIdeal (fun _ ↦ 1) β s).colon {G.det} = _ at hcol
  rw [show G.det = C c * differenceProduct σ from hdet] at hcol
  rw [← hcol]
  ext p
  simp only [mem_principalColon,Submodule.mem_colon_singleton,smul_eq_mul]
  have hu : IsUnit (C c : P (F := F) (n := n)) := (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  have h := ((powerMomentIdeal (fun _ ↦ 1) β s).unit_mul_mem_iff_mem hu
    (x := p * differenceProduct σ)).symm
  simpa only [mul_left_comm,mul_assoc] using h

end PaperVerification.Fermion.Newton
