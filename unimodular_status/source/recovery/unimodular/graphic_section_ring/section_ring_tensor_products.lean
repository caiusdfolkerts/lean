module

public import Recovery.Unimodular.GraphicSectionRing.ActualSectionRing

/-!
# Ordinary tensor products and multiplication in the actual section ring

For every pair of natural degrees, the ordinary tensor product of the
Cartier power sheaves is identified with the sum power by the identity on
rational section values. The usual tensor multiplication of global sections
then agrees with the previously constructed section-ring multiplication.
Both degree-zero cases are included.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u

namespace Unimodular.GraphicSectionRing.ActualSections

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricSchemes
open scoped TensorProduct BaseSections

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- Passing to the common product cover gives exactly the sum power,
including either degree zero. -/
theorem power_add_isSection_iff (i j : ℕ) (U : X.Opens)
    (s : Γ(rationalFunctions X, U)) :
    (C.pow (i + j)).IsSection U s ↔ ((C.pow i).mul (C.pow j)).IsSection U s := by
  constructor
  · intro hs ab x hx
    have hp := hs ab.1 x hx.1
    have ht := (regularAtSubring X x.val).pow_mem
      (C.transition ab.1 ab.2 x.val hx.1 hx.2) j
    have h := (regularAtSubring X x.val).mul_mem hp ht
    change rationalValueAt X U x s /
      ((C.generator ab.1 : X.functionField) ^ i *
        (C.generator ab.2 : X.functionField) ^ j) ∈ _
    have he :
        (rationalValueAt X U x s / (C.generator ab.1 : X.functionField) ^ (i + j)) *
          ((C.generator ab.1 : X.functionField) /
            (C.generator ab.2 : X.functionField)) ^ j =
        rationalValueAt X U x s /
          ((C.generator ab.1 : X.functionField) ^ i *
            (C.generator ab.2 : X.functionField) ^ j) := by
      rw [pow_add, div_pow]
      field_simp [Units.ne_zero]
      <;> ring
    simpa only [RationalCartierCocycle.pow, Units.val_pow_eq_pow_val, he] using h
  · intro hs a x hx
    have h := hs (a, a) x ⟨hx, hx⟩
    simpa only [RationalCartierCocycle.pow, RationalCartierCocycle.mul,
      Units.val_mul, Units.val_pow_eq_pow_val, pow_add] using h

/-- The comparison between the product cover and the original cover is
literally the identity on every rational section. -/
def powerSumSheafIso (i j : ℕ) :
    ((C.pow i).mul (C.pow j)).sheaf ≅ (C.pow (i + j)).sheaf :=
  ((C.pow i).mul (C.pow j)).sheafIsoOfIsSectionIff (C.pow (i + j))
    (fun U s => (power_add_isSection_iff C i j U s).symm)

@[simp] theorem powerSumSheafIso_value (i j : ℕ) (U : X.Opens)
    (s : Γ(((C.pow i).mul (C.pow j)).sheaf, U)) :
    ((powerSumSheafIso C i j).hom.app U s).val = s.val := rfl

/-- Actual sheaf tensor multiplication for every pair of Cartier powers. -/
def powerTensorSheafIso (i j : ℕ) :
    tensorSheaf (C.pow i).sheaf (C.pow j).sheaf ≅ (C.pow (i + j)).sheaf :=
  (C.pow i).tensorSheafMulIso (C.pow j) ≪≫ powerSumSheafIso C i j

/-- The actual sheaf isomorphism multiplies the rational values of the
ordinary pure tensor section; this holds on every nonempty open. -/
theorem powerTensorSheafIso_pure_value (i j : ℕ) (U : X.Opens) [Nonempty U]
    (s : Γ((C.pow i).sheaf, U)) (t : Γ((C.pow j).sheaf, U)) :
    (C.pow (i + j)).toCartierData.sectionValue U
      ((powerTensorSheafIso C i j).hom.app U
        ((tensorSheafUnit (C.pow i).sheaf (C.pow j).sheaf).app (op U)
          (s ⊗ₜ[Γ(X, U)] t))) =
      (C.pow i).toCartierData.sectionValue U s *
        (C.pow j).toCartierData.sectionValue U t := by
  change rationalValue X U
    (((C.pow i).tensorSheafMulIso (C.pow j)).hom.app U
      ((tensorSheafUnit (C.pow i).sheaf (C.pow j).sheaf).app (op U)
        (s ⊗ₜ[Γ(X, U)] t))).val = _
  rw [RationalCartierCocycle.tensorSheafMulIso_pure_sections]
  exact (C.pow i).sectionProduct_value (C.pow j) U s t

variable (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]

/-- Ordinary multiplication of global sections through the genuine tensor
sheaf isomorphism; its domain is the actual tensor product over the base field. -/
def powerTensorSectionMultiplication (i j : ℕ) :
    Γ((C.pow i).sheaf, ⊤) ⊗[k] Γ((C.pow j).sheaf, ⊤) →ₗ[k]
      Γ((C.pow (i + j)).sheaf, ⊤) :=
  (BaseSections.globalSectionsIso k (powerTensorSheafIso C i j)).toLinearMap.comp
    (moduleSectionMultiplicationOver k (C.pow i).sheaf (C.pow j).sheaf)

/-- The ordinary tensor section product is exactly the actual product
used to construct the graded section ring. -/
@[simp] theorem powerTensorSectionMultiplication_tmul (i j : ℕ)
    (s : Γ((C.pow i).sheaf, ⊤)) (t : Γ((C.pow j).sheaf, ⊤)) :
    powerTensorSectionMultiplication C k i j (s ⊗ₜ[k] t) =
      powerProduct k C i j s t := by
  apply (C.pow (i + j)).toCartierData.globalSectionValue_injective k
  rw [powerProduct_value]
  exact powerTensorSheafIso_pure_value C i j ⊤ s t

/-- Homogeneous multiplication in the actual section ring is induced by
ordinary sheaf tensor multiplication, in every pair of degrees. -/
theorem homogeneousSection_mul_tensor (i j : ℕ)
    (s : Γ((C.pow i).sheaf, ⊤)) (t : Γ((C.pow j).sheaf, ⊤)) :
    homogeneousSection k C i s * homogeneousSection k C j t =
      homogeneousSection k C (i + j)
        (powerTensorSectionMultiplication C k i j (s ⊗ₜ[k] t)) := by
  rw [powerTensorSectionMultiplication_tmul]
  exact homogeneousSection_mul k C i j s t

/-- Equality of the full linear maps on the ordinary tensor product,
not only of a selected family of section products. -/
theorem homogeneousSection_comp_tensorMultiplication (i j : ℕ) :
    (homogeneousSection k C (i + j)).comp (powerTensorSectionMultiplication C k i j) =
      (LinearMap.mul' k (sectionRing k C)).comp
        (TensorProduct.map (homogeneousSection k C i) (homogeneousSection k C j)) := by
  apply TensorProduct.ext'
  intro s t
  change homogeneousSection k C (i + j)
      (powerTensorSectionMultiplication C k i j (s ⊗ₜ[k] t)) =
    homogeneousSection k C i s * homogeneousSection k C j t
  exact (homogeneousSection_mul_tensor C k i j s t).symm

#print axioms power_add_isSection_iff
#print axioms powerTensorSheafIso
#print axioms powerTensorSectionMultiplication_tmul
#print axioms homogeneousSection_comp_tensorMultiplication

end Unimodular.GraphicSectionRing.ActualSections

#check Unimodular.GraphicSectionRing.ActualSections.powerTensorSheafIso
#check Unimodular.GraphicSectionRing.ActualSections.homogeneousSection_comp_tensorMultiplication
