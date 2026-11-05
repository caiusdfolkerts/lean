module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The ordinary section ring of a genuine invertible sheaf

The degree-d coefficient is an actual global section of the d-th Cartier
power, embedded in the genuine function field. The recovered tensor-power
isomorphism identifies this power with the ordinary d-fold tensor power.
The ring is the finite graded direct sum, realized inside K(X)[T]; its
homogeneous injections, unique coefficient sections and finite expansion
are proved below. Multiplication is the actual rational product of sections.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators

universe u

namespace Unimodular.GraphicSectionRing.ActualSections

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped BaseSections

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] (C : RationalCartierCocycle X)

/-- The actual values of all global sections of the genuine d-th power. -/
def powerValues (d : ℕ) : Submodule k X.functionField :=
  ((C.pow d).toCartierData.globalSectionValue k).range

theorem mem_powerValues_iff (d : ℕ) (r : X.functionField) :
    r ∈ powerValues k C d ↔
      ∀ i (x : X), x ∈ C.openSet i →
        r / (C.generator i : X.functionField) ^ d ∈ regularAtSubring X x := by
  constructor
  · rintro ⟨s, rfl⟩ i x hx
    exact s.property i ⟨x, trivial⟩ hx
  · intro hr
    let s : Γ(rationalFunctions X, ⊤) := (rationalValue X ⊤).symm r
    have hs : (C.pow d).IsSection ⊤ s := by
      intro i x hx
      change rationalValue X ⊤ s / (C.generator i : X.functionField) ^ d ∈ _
      rw [show rationalValue X ⊤ s = r from (rationalValue X ⊤).apply_symm_apply r]
      exact hr i x.val hx
    refine ⟨⟨s, hs⟩, ?_⟩
    exact (rationalValue X ⊤).apply_symm_apply r

theorem powerValues_mul {i j : ℕ} {r s : X.functionField}
    (hr : r ∈ powerValues k C i) (hs : s ∈ powerValues k C j) :
    r * s ∈ powerValues k C (i + j) := by
  apply (mem_powerValues_iff k C (i + j) (r * s)).mpr
  intro a x hx
  have h := (regularAtSubring X x).mul_mem
    ((mem_powerValues_iff k C i r).mp hr a x hx)
    ((mem_powerValues_iff k C j s).mp hs a x hx)
  simpa only [div_mul_div_comm, pow_add] using h

theorem powerValues_algebraMap_zero (a : k) :
    algebraMap k X.functionField a ∈ powerValues k C 0 := by
  apply (mem_powerValues_iff k C 0 _).mpr
  intro i x hx
  change X.germToFunctionField ⊤ (BaseSections.scalarMap k X ⊤ a) /
    (C.generator i : X.functionField) ^ 0 ∈ _
  rw [pow_zero, div_one]
  exact regular_germ_mem_regularAt X ⊤ (BaseSections.scalarMap k X ⊤ a) x trivial

/-- The usual section ring, represented as the finite sum of its actual
homogeneous rational-value spaces. No generation or Koszul property is assumed. -/
def sectionRing : Subalgebra k (AddMonoidAlgebra X.functionField ℕ) where
  carrier := {p | ∀ d, p.coeff d ∈ powerValues k C d}
  zero_mem' := by intro d; exact (powerValues k C d).zero_mem
  add_mem' := by
    intro p q hp hq d
    exact (powerValues k C d).add_mem (hp d) (hq d)
  one_mem' := by
    intro d
    by_cases hd : d = 0
    · subst d
      simpa [AddMonoidAlgebra.one_def] using powerValues_algebraMap_zero k C (1 : k)
    · simpa [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single_apply, Ne.symm hd]
        using (powerValues k C d).zero_mem
  mul_mem' := by
    classical
    intro p q hp hq d
    rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    rw [Finsupp.sum]
    apply Submodule.sum_mem
    intro j hj
    by_cases hij : i + j = d
    · rw [if_pos hij]
      simpa only [hij] using powerValues_mul k C (hp i) (hq j)
    · rw [if_neg hij]
      exact (powerValues k C d).zero_mem
  algebraMap_mem' a := by
    intro d
    change (AddMonoidAlgebra.single 0 (algebraMap k X.functionField a)).coeff d ∈ _
    by_cases hd : d = 0
    · subst d
      simpa using powerValues_algebraMap_zero k C a
    · simpa [AddMonoidAlgebra.coeff_single_apply, Ne.symm hd]
        using (powerValues k C d).zero_mem

/-- Evaluation is a proved isomorphism from genuine sections onto their image. -/
def powerValueEquiv (d : ℕ) :
    Γ((C.pow d).sheaf, ⊤) ≃ₗ[k] powerValues k C d :=
  LinearEquiv.ofInjective ((C.pow d).toCartierData.globalSectionValue k)
    ((C.pow d).toCartierData.globalSectionValue_injective k)

/-- The degree-d homogeneous injection uses the actual global section. -/
def homogeneousSection (d : ℕ) : Γ((C.pow d).sheaf, ⊤) →ₗ[k] sectionRing k C :=
  LinearMap.codRestrict (sectionRing k C).toSubmodule
    ((AddMonoidAlgebra.lsingle (R := k) d).comp
      ((C.pow d).toCartierData.globalSectionValue k)) (by
      intro s j
      change (AddMonoidAlgebra.single d
        ((C.pow d).toCartierData.globalSectionValue k s)).coeff j ∈ _
      by_cases hdj : d = j
      · subst j
        simpa using (show (C.pow d).toCartierData.globalSectionValue k s ∈ powerValues k C d
          from ⟨s, rfl⟩)
      · simpa [AddMonoidAlgebra.coeff_single_apply, hdj] using (powerValues k C j).zero_mem)

@[simp] theorem homogeneousSection_val (d : ℕ) (s : Γ((C.pow d).sheaf, ⊤)) :
    (homogeneousSection k C d s).val =
      AddMonoidAlgebra.single d ((C.pow d).toCartierData.globalSectionValue k s) := rfl

theorem homogeneousSection_injective (d : ℕ) :
    Function.Injective (homogeneousSection k C d) := by
  intro s t h
  apply (C.pow d).toCartierData.globalSectionValue_injective k
  have he := congrArg (fun p : sectionRing k C => p.val.coeff d) h
  simpa only [homogeneousSection_val, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same] using he

/-- The unique section represented by the degree-d coefficient. -/
def coefficientSection (d : ℕ) (p : sectionRing k C) : Γ((C.pow d).sheaf, ⊤) :=
  (powerValueEquiv k C d).symm ⟨p.val.coeff d, p.property d⟩

@[simp] theorem coefficientSection_value (d : ℕ) (p : sectionRing k C) :
    (C.pow d).toCartierData.globalSectionValue k (coefficientSection k C d p) = p.val.coeff d :=
  LinearEquiv.ofInjective_symm_apply _ _

theorem coefficientSection_eq_zero_iff (d : ℕ) (p : sectionRing k C) :
    coefficientSection k C d p = 0 ↔ p.val.coeff d = 0 := by
  constructor
  · intro h
    rw [← coefficientSection_value k C d p, h, map_zero]
  · intro h
    apply (C.pow d).toCartierData.globalSectionValue_injective k
    rw [coefficientSection_value, map_zero, h]

/-- Every element is the finite sum of its genuine homogeneous sections. -/
theorem sum_homogeneous_sections (p : sectionRing k C) :
    (∑ d ∈ p.val.coeff.support,
      homogeneousSection k C d (coefficientSection k C d p)) = p := by
  apply Subtype.ext
  change (sectionRing k C).val
    (∑ d ∈ p.val.coeff.support, homogeneousSection k C d (coefficientSection k C d p)) = p.val
  rw [map_sum]
  change (∑ d ∈ p.val.coeff.support,
    AddMonoidAlgebra.single d ((C.pow d).toCartierData.globalSectionValue k
      (coefficientSection k C d p))) = p.val
  simp only [coefficientSection_value]
  exact AddMonoidAlgebra.sum_coeff_single p.val

/-- Coefficient sections uniquely determine the actual graded sum. -/
theorem coefficientSection_ext {p q : sectionRing k C}
    (h : ∀ d, coefficientSection k C d p = coefficientSection k C d q) : p = q := by
  apply Subtype.ext
  apply AddMonoidAlgebra.coeff_injective
  ext d
  rw [← coefficientSection_value k C d p, ← coefficientSection_value k C d q, h d]

/-- Product of actual sections, uniquely recovered from their actual rational product. -/
def powerProduct (i j : ℕ) (s : Γ((C.pow i).sheaf, ⊤)) (t : Γ((C.pow j).sheaf, ⊤)) :
    Γ((C.pow (i + j)).sheaf, ⊤) :=
  (powerValueEquiv k C (i + j)).symm
    ⟨(C.pow i).toCartierData.globalSectionValue k s *
      (C.pow j).toCartierData.globalSectionValue k t,
      powerValues_mul k C ⟨s, rfl⟩ ⟨t, rfl⟩⟩

@[simp] theorem powerProduct_value (i j : ℕ)
    (s : Γ((C.pow i).sheaf, ⊤)) (t : Γ((C.pow j).sheaf, ⊤)) :
    (C.pow (i + j)).toCartierData.globalSectionValue k (powerProduct k C i j s t) =
      (C.pow i).toCartierData.globalSectionValue k s *
        (C.pow j).toCartierData.globalSectionValue k t :=
  LinearEquiv.ofInjective_symm_apply _ _

/-- The ring product is exactly the ordinary multiplication of section values. -/
theorem homogeneousSection_mul (i j : ℕ)
    (s : Γ((C.pow i).sheaf, ⊤)) (t : Γ((C.pow j).sheaf, ⊤)) :
    homogeneousSection k C i s * homogeneousSection k C j t =
      homogeneousSection k C (i + j) (powerProduct k C i j s t) := by
  apply Subtype.ext
  change AddMonoidAlgebra.single i _ * AddMonoidAlgebra.single j _ = _
  rw [AddMonoidAlgebra.single_mul_single, homogeneousSection_val, powerProduct_value]
  rfl

/-- Homogeneous pieces are the genuine ordinary tensor powers of the original sheaf. -/
def homogeneousTensorPowerIso (d : ℕ) :
    tensorSheafPower C.sheaf d ≅ (C.pow d).sheaf :=
  C.tensorSheafPowerIso d

#print axioms mem_powerValues_iff
#print axioms sectionRing
#print axioms sum_homogeneous_sections
#print axioms coefficientSection_ext
#print axioms homogeneousSection_mul
#print axioms homogeneousTensorPowerIso

end Unimodular.GraphicSectionRing.ActualSections

#check Unimodular.GraphicSectionRing.ActualSections.homogeneousTensorPowerIso
