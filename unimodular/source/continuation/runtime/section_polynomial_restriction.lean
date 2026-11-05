module

public import Continuation.Runtime.OrdinarySectionCoordinateRing
public import Continuation.Runtime.PolynomialSectionDegree
public import Recovery.Unimodular.GraphicSectionRing.SectionRingTensorProducts

/-!
# Homogeneous polynomial restriction and actual tensor powers

Polynomial evaluation in genuine degree-one sections is compared, in every
degree, with an actual section of the ordinary tensor power. The product
comparison uses the ordinary sheaf tensor multiplication already constructed
in SectionRingTensorProducts. For a homogeneous polynomial, vanishing of that
actual tensor section is equivalent to membership in the literal evaluation
kernel. No identification of a separately constructed O(d) is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped BaseSections TensorProduct

namespace Unimodular.GraphicSectionRing.ActualSections

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] (C : RationalCartierCocycle X)
  {ι : Type u} (s : ι → Γ(C.sheaf, ⊤))

/-- Evaluation in the actual graded ring has the literal polynomial
evaluation in the function-field polynomial ring as its underlying value. -/
theorem degreeOneSectionMap_val (p : MvPolynomial ι k) :
    (degreeOneSectionMap k C s p).val =
      degreeOnePolynomialEvaluation (algebraMap k X.functionField)
        (fun i => C.toCartierData.sectionValue ⊤ (s i)) p := by
  have he : (sectionRing k C).val.toRingHom.comp
      (degreeOneSectionMap k C s).toRingHom =
      degreeOnePolynomialEvaluation (algebraMap k X.functionField)
        (fun i => C.toCartierData.sectionValue ⊤ (s i)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (degreeOneSectionMap k C s (algebraMap k (MvPolynomial ι k) a)).val = _
      rw [(degreeOneSectionMap k C s).commutes] <;>
        simp only [degreeOnePolynomialEvaluation, MvPolynomial.eval₂Hom_C,
          RingHom.comp_apply] <;> rfl
    · intro i
      change (degreeOneSectionMap k C s (MvPolynomial.X i)).val = _
      calc
        _ = (degreeOneSectionElement k C (s i)).val :=
          congrArg Subtype.val (degreeOneSectionMap_X k C s i)
        _ = AddMonoidAlgebra.single 1 (C.toCartierData.sectionValue ⊤ (s i)) :=
          degreeOneSectionElement_val k C (s i)
        _ = _ := by
          simp only [degreeOnePolynomialEvaluation, MvPolynomial.eval₂Hom_X']
  exact congrArg (fun f : MvPolynomial ι k →+* AddMonoidAlgebra X.functionField ℕ => f p) he

theorem degreeOneSectionMap_coefficient (p : MvPolynomial ι k) (d : ℕ) :
    (degreeOneSectionMap k C s p).val.coeff d =
      MvPolynomial.eval₂Hom (algebraMap k X.functionField)
        (fun i => C.toCartierData.sectionValue ⊤ (s i))
        (MvPolynomial.homogeneousComponent d p) := by
  rw [degreeOneSectionMap_val, degreeOnePolynomialEvaluation_coefficient]

/-- The degree-d section obtained by ordinary polynomial evaluation in the
actual section ring. Its tensor interpretation and multiplication law are
proved below. -/
def homogeneousPolynomialSection (d : ℕ) (p : MvPolynomial ι k) :
    Γ((C.pow d).sheaf, ⊤) :=
  coefficientSection k C d (degreeOneSectionMap k C s p)

/-- The section has exactly the usual rational value of the homogeneous
polynomial in the genuine original degree-one sections. -/
theorem homogeneousPolynomialSection_value (d : ℕ) (p : MvPolynomial ι k)
    (hp : p.IsHomogeneous d) :
    (C.pow d).toCartierData.globalSectionValue k
      (homogeneousPolynomialSection k C s d p) =
      MvPolynomial.eval₂Hom (algebraMap k X.functionField)
        (fun i => C.toCartierData.sectionValue ⊤ (s i)) p := by
  rw [homogeneousPolynomialSection, coefficientSection_value,
    degreeOneSectionMap_coefficient, MvPolynomial.homogeneousComponent_eq_self hp]

/-- A homogeneous polynomial evaluates into precisely the intended actual
homogeneous section space, including degree zero. -/
theorem homogeneousSection_homogeneousPolynomialSection (d : ℕ)
    (p : MvPolynomial ι k) (hp : p.IsHomogeneous d) :
    homogeneousSection k C d (homogeneousPolynomialSection k C s d p) =
      degreeOneSectionMap k C s p := by
  apply Subtype.ext
  apply AddMonoidAlgebra.coeff_injective
  ext j
  rw [homogeneousSection_val, AddMonoidAlgebra.coeff_single_apply,
    homogeneousPolynomialSection, coefficientSection_value]
  by_cases hj : j = d
  · subst j
    rw [if_pos rfl]
  · rw [if_neg (Ne.symm hj), degreeOneSectionMap_coefficient,
      MvPolynomial.homogeneousComponent_of_mem hp, if_neg hj, map_zero]

/-- The homogeneous evaluation multiplies sections by the actual ordinary
tensor-section map, not an assumed substitute multiplication. -/
theorem homogeneousPolynomialSection_mul (d e : ℕ)
    (p q : MvPolynomial ι k) (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e) :
    homogeneousPolynomialSection k C s (d + e) (p * q) =
      powerTensorSectionMultiplication C k d e
        (homogeneousPolynomialSection k C s d p ⊗ₜ[k]
          homogeneousPolynomialSection k C s e q) := by
  apply homogeneousSection_injective k C (d + e)
  rw [homogeneousSection_homogeneousPolynomialSection k C s (d + e) (p * q) (hp.mul hq),
    ← homogeneousSection_mul_tensor,
    homogeneousSection_homogeneousPolynomialSection k C s d p hp,
    homogeneousSection_homogeneousPolynomialSection k C s e q hq, map_mul]

/-- The degree-one coordinate is the original genuine section. -/
theorem homogeneousPolynomialSection_X (i : ι) :
    homogeneousSection k C 1
      (homogeneousPolynomialSection k C s 1 (MvPolynomial.X i)) =
        degreeOneSectionElement k C (s i) := by
  rw [homogeneousSection_homogeneousPolynomialSection k C s 1 (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X k i), degreeOneSectionMap_X]

/-- Actual homogeneous restriction expressed in the ordinary tensor-power
object, through the proved canonical tensor-power isomorphism. -/
def tensorPolynomialSection (d : ℕ) (p : MvPolynomial ι k) :
    Γ(tensorSheafPower C.sheaf d, ⊤) :=
  (BaseSections.globalSectionsIso k (C.tensorSheafPowerIso d)).symm
    (homogeneousPolynomialSection k C s d p)

theorem homogeneousPolynomialSection_eq_zero_iff (d : ℕ)
    (p : MvPolynomial ι k) (hp : p.IsHomogeneous d) :
    homogeneousPolynomialSection k C s d p = 0 ↔
      p ∈ RingHom.ker (degreeOneSectionMap k C s).toRingHom := by
  change _ ↔ degreeOneSectionMap k C s p = 0
  rw [← homogeneousSection_homogeneousPolynomialSection k C s d p hp]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply homogeneousSection_injective k C d
    simpa only [map_zero] using h

/-- The literal evaluation kernel is exactly vanishing of the actual
tensor-power restriction, for every homogeneous polynomial and every degree. -/
theorem tensorPolynomialSection_eq_zero_iff (d : ℕ)
    (p : MvPolynomial ι k) (hp : p.IsHomogeneous d) :
    tensorPolynomialSection k C s d p = 0 ↔
      p ∈ RingHom.ker (degreeOneSectionMap k C s).toRingHom := by
  rw [tensorPolynomialSection]
  rw [LinearEquiv.map_eq_zero_iff]
  exact homogeneousPolynomialSection_eq_zero_iff k C s d p hp

/-- The whole (possibly inhomogeneous) ideal consists exactly of those
polynomials whose actual tensor-power coefficient sections all vanish. -/
theorem mem_kernel_iff_tensorPolynomialSections_zero (p : MvPolynomial ι k) :
    p ∈ RingHom.ker (degreeOneSectionMap k C s).toRingHom ↔
      ∀ d : ℕ, tensorPolynomialSection k C s d p = 0 := by
  change degreeOneSectionMap k C s p = 0 ↔ _
  constructor
  · intro hp d
    apply (BaseSections.globalSectionsIso k (C.tensorSheafPowerIso d)).injective
    change (BaseSections.globalSectionsIso k (C.tensorSheafPowerIso d))
        ((BaseSections.globalSectionsIso k (C.tensorSheafPowerIso d)).symm
          (coefficientSection k C d (degreeOneSectionMap k C s p))) = _
    rw [LinearEquiv.apply_symm_apply, hp, map_zero]
    exact (coefficientSection_eq_zero_iff k C d 0).mpr (by simp)
  · intro hp
    apply coefficientSection_ext k C
    intro d
    have h := congrArg (BaseSections.globalSectionsIso k (C.tensorSheafPowerIso d)) (hp d)
    change (BaseSections.globalSectionsIso k (C.tensorSheafPowerIso d))
        ((BaseSections.globalSectionsIso k (C.tensorSheafPowerIso d)).symm
          (coefficientSection k C d (degreeOneSectionMap k C s p))) = _ at h
    rw [LinearEquiv.apply_symm_apply, map_zero] at h
    rw [h]
    exact ((coefficientSection_eq_zero_iff k C d 0).mpr (by simp)).symm

#print axioms homogeneousPolynomialSection_value
#print axioms homogeneousPolynomialSection_mul
#print axioms tensorPolynomialSection_eq_zero_iff
#print axioms mem_kernel_iff_tensorPolynomialSections_zero

end Unimodular.GraphicSectionRing.ActualSections

end
