module

public import PaperVerification.ToricSectionChartGenerators
public import PaperVerification.ToricBaseSectionNaturality
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-! # Linear changes of an actual finite system of Cartier sections -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (k : Type u) [CommRing k] {ι : Type u}

def sectionLinearForm (c : ι→₀k) : MvPolynomial ι k :=
  c.sum (fun i a=>MvPolynomial.C a*MvPolynomial.X i)

theorem sectionLinearForm_isHomogeneous (c : ι→₀k) :
    (sectionLinearForm k c).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem sectionLinearForm_eval {R : Type u} [CommRing R]
    (F : k→+*R) (v : ι→R) (c : ι→₀k) :
    MvPolynomial.eval₂Hom F v (sectionLinearForm k c)=
      c.sum (fun i a=>F a*v i) := by
  simp only [sectionLinearForm,Finsupp.sum,map_sum,map_mul,
    MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X']

namespace RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X)

/-- The local coefficients of genuine sections are linear over the
actual base ring. -/
def localCoefficientLinear (i : C.index) :
    Γ(C.sheaf,⊤)→ₗ[k]Γ(X,C.openSet i) where
  toFun := C.localCoefficient i
  map_add' s t := by
    by_cases hU : Nonempty (C.openSet i)
    · letI := hU
      apply X.germToFunctionField_injective (C.openSet i)
      have hst : C.toCartierData.sectionValue ⊤ (s+t) =
          C.toCartierData.sectionValue ⊤ s+C.toCartierData.sectionValue ⊤ t :=
        (C.toCartierData.globalSectionValue k).map_add s t
      calc
        X.germToFunctionField (C.openSet i) (C.localCoefficient i (s+t)) =
            C.toCartierData.sectionValue ⊤ (s+t)/(C.generator i : X.functionField) :=
          C.localCoefficient_value i (s+t)
        _ = C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField)+
            C.toCartierData.sectionValue ⊤ t/(C.generator i : X.functionField) := by
          rw [hst,add_div]
        _ = X.germToFunctionField (C.openSet i) (C.localCoefficient i s)+
            X.germToFunctionField (C.openSet i) (C.localCoefficient i t) :=
          congrArg₂ (·+·) (C.localCoefficient_value i s).symm
            (C.localCoefficient_value i t).symm
        _ = X.germToFunctionField (C.openSet i)
            (C.localCoefficient i s+C.localCoefficient i t) :=
          (map_add (X.germToFunctionField (C.openSet i)).hom _ _).symm
    · have hbot : C.openSet i=⊥ := by
        apply le_antisymm
        · intro x hx
          exact False.elim (hU ⟨⟨x,hx⟩⟩)
        · exact bot_le
      letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
      exact Subsingleton.elim _ _
  map_smul' a s := by
    by_cases hU : Nonempty (C.openSet i)
    · letI := hU
      apply X.germToFunctionField_injective (C.openSet i)
      change X.germToFunctionField (C.openSet i) (C.localCoefficient i (a • s))=
        X.germToFunctionField (C.openSet i)
          (BaseSections.scalarMap k X (C.openSet i) a*C.localCoefficient i s)
      calc
        X.germToFunctionField (C.openSet i) (C.localCoefficient i (a • s)) =
            C.toCartierData.globalSectionValue k (a • s)/(C.generator i : X.functionField) :=
          C.localCoefficient_value i (a • s)
        _ = (algebraMap k X.functionField a*C.toCartierData.globalSectionValue k s)/
            (C.generator i : X.functionField) :=
          congrArg (fun z : X.functionField=>z/(C.generator i : X.functionField))
            ((C.toCartierData.globalSectionValue k).map_smul a s)
        _ = algebraMap k X.functionField a*
            (C.toCartierData.globalSectionValue k s/(C.generator i : X.functionField)) :=
          mul_div_assoc _ _ _
        _ = X.germToFunctionField (C.openSet i) (BaseSections.scalarMap k X (C.openSet i) a)*
            X.germToFunctionField (C.openSet i) (C.localCoefficient i s) :=
          congrArg₂ (·*·) (BaseSections.germ_scalarMap k (C.openSet i) a).symm
            (C.localCoefficient_value i s).symm
        _ = X.germToFunctionField (C.openSet i)
            (BaseSections.scalarMap k X (C.openSet i) a*C.localCoefficient i s) :=
          (map_mul (X.germToFunctionField (C.openSet i)).hom _ _).symm
    · have hbot : C.openSet i=⊥ := by
        apply le_antisymm
        · intro x hx
          exact False.elim (hU ⟨⟨x,hx⟩⟩)
        · exact bot_le
      letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
      exact Subsingleton.elim _ _

theorem localCoefficient_linearCombination (s : ι→Γ(C.sheaf,⊤)) (c : ι→₀k)
    (i : C.index) :
    C.localCoefficient i (Finsupp.linearCombination k s c)=
      c.sum (fun j a=>BaseSections.scalarMap k X (C.openSet i) a*
        C.localCoefficient i (s j)) := by
  change C.localCoefficientLinear k i (Finsupp.linearCombination k s c)=_
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    localCoefficientLinear,LinearMap.coe_mk,AddHom.coe_mk,Algebra.smul_def]
  all_goals rfl

/-- The nonvanishing open of a linear combination lies in the union of
the nonvanishing opens of the genuine sections in that combination. -/
theorem nonvanishingOpen_linearCombination_le (s : ι→Γ(C.sheaf,⊤))
    (c : ι→₀k) :
    C.nonvanishingOpen (Finsupp.linearCombination k s c)≤
      ⨆ j,C.nonvanishingOpen (s j) := by
  intro x hx
  by_contra hnone
  have hnone' (j : ι) : x∉C.nonvanishingOpen (s j) :=
    fun hj=>hnone (Opens.mem_iSup.mpr ⟨j,hj⟩)
  obtain ⟨i,hxi⟩ := C.covers x
  have ht := (C.mem_nonvanishingOpen_iff_not_mem_maximalIdeal i _ x hxi).mp hx
  apply ht
  rw [C.localCoefficient_linearCombination k s c i]
  simp only [Finsupp.sum,map_sum,map_mul]
  apply Ideal.sum_mem
  intro j hj
  apply Ideal.mul_mem_left
  exact not_not.mp (fun h=>hnone' j
    ((C.mem_nonvanishingOpen_iff_not_mem_maximalIdeal i (s j) x hxi).mpr h))

theorem nonvanishing_cover_of_spans {κ : Type u}
    (s : ι→Γ(C.sheaf,⊤)) (t : κ→Γ(C.sheaf,⊤))
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤)
    (hspan : ∀ i,∃ c : κ→₀k,Finsupp.linearCombination k t c=s i) :
    (⨆ j,C.nonvanishingOpen (t j))=⊤ := by
  apply top_unique
  rw [← hcover]
  apply iSup_le
  intro i
  obtain ⟨c,hc⟩ := hspan i
  rw [← hc]
  exact C.nonvanishingOpen_linearCombination_le k t c

theorem sectionLinearForm_fieldValue (s : ι→Γ(C.sheaf,⊤)) (c : ι→₀k) :
    C.sectionProjectiveFieldMap k s (sectionLinearForm k c)=
      C.toCartierData.sectionValue ⊤ (Finsupp.linearCombination k s c) := by
  rw [sectionProjectiveFieldMap,sectionLinearForm_eval]
  change _=C.toCartierData.globalSectionValue k (Finsupp.linearCombination k s c)
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    Algebra.smul_def,RingHom.comp_apply]
  rfl

def sectionRatioPolynomialMap (s : ι→Γ(C.sheaf,⊤)) (den : Γ(C.sheaf,⊤)) :
    MvPolynomial ι k→+*Γ(X,C.nonvanishingOpen den) :=
  MvPolynomial.eval₂Hom (BaseSections.scalarMap k X (C.nonvanishingOpen den))
    (fun j=>C.ratioSection (s j) den)

theorem sectionRatioPolynomialMap_germ (s : ι→Γ(C.sheaf,⊤))
    (den : Γ(C.sheaf,⊤)) [Nonempty (C.nonvanishingOpen den)] :
    (X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
        (C.sectionRatioPolynomialMap k s den)=
      MvPolynomial.eval₂Hom
        ((X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤))
        (fun j=>(C.toCartierData.sectionValue ⊤ den)⁻¹*
          C.toCartierData.sectionValue ⊤ (s j)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,sectionRatioPolynomialMap,MvPolynomial.eval₂Hom_C]
    exact BaseSections.germ_scalarMap_top k X _ a
  · intro j
    simp only [RingHom.comp_apply,sectionRatioPolynomialMap,MvPolynomial.eval₂Hom_X',
      C.ratioSection_value,div_eq_mul_inv,mul_comm]

theorem sectionRatioPolynomialMap_linearForm (s : ι→Γ(C.sheaf,⊤))
    (den : Γ(C.sheaf,⊤)) (c : ι→₀k) :
    C.sectionRatioPolynomialMap k s den (sectionLinearForm k c)=
      C.ratioSection (Finsupp.linearCombination k s c) den := by
  by_cases hU : Nonempty (C.nonvanishingOpen den)
  · letI := hU
    apply X.germToFunctionField_injective (C.nonvanishingOpen den)
    rw [C.ratioSection_value]
    change ((X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
      (C.sectionRatioPolynomialMap k s den)) (sectionLinearForm k c)=_
    rw [C.sectionRatioPolynomialMap_germ k s den]
    rw [MvPolynomial.coe_eval₂Hom,homogeneous_eval_scaled _ _ _ _ 1
      (sectionLinearForm_isHomogeneous k c),pow_one]
    rw [← C.sectionLinearForm_fieldValue k s c]
    simp only [sectionProjectiveFieldMap,MvPolynomial.coe_eval₂Hom,div_eq_mul_inv,mul_comm]
  · have hbot : C.nonvanishingOpen den=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X (C.nonvanishingOpen den) hbot
    exact Subsingleton.elim _ _

theorem sectionProjectiveMap_generic (s : ι→Γ(C.sheaf,⊤))
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι)
    [Nonempty (C.nonvanishingOpen (s i))] :
    X.fromSpecStalk (genericPoint X) ≫ C.sectionProjectiveMap k s hcover =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) (MvPolynomial.X i)
        (polynomialVariable_mem_degreeOne k i) (by decide)
        (by simpa only [sectionProjectiveFieldMap,MvPolynomial.eval₂Hom_X'] using
          C.sectionValue_ne_zero_of_nonvanishing (s i)) := by
  rw [← (C.nonvanishingOpen (s i)).fromSpecStalkOfMem_ι
    (genericPoint X) (genericPoint_mem_open X _),Category.assoc,
    C.sectionProjectiveMap_chart k s hcover i]
  exact C.sectionProjectiveChart_generic k s i _

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.nonvanishing_cover_of_spans
