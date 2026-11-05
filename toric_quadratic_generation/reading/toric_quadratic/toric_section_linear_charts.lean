module

public import PaperVerification.ToricSectionLinearSystems

@[expose] public section

/-! # Genuine projective charts at linear combinations of sections -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (k : Type u) [CommRing k] {ι κ : Type u}

def sectionLinearGradedMap (c : ι→κ→₀k) :
    MvPolynomial.homogeneousSubmodule ι k →+*ᵍ
      MvPolynomial.homogeneousSubmodule κ k where
  __ := MvPolynomial.eval₂Hom MvPolynomial.C (fun i=>sectionLinearForm k (c i))
  map_mem {i} {p} hp := by
    apply (MvPolynomial.mem_homogeneousSubmodule i _).mpr
    have hp' : p.IsHomogeneous i := (MvPolynomial.mem_homogeneousSubmodule i p).mp hp
    simpa only [MvPolynomial.coe_eval₂Hom,one_mul] using
      hp'.eval₂ MvPolynomial.C (fun j=>sectionLinearForm k (c j))
        (MvPolynomial.isHomogeneous_C κ) (fun j=>sectionLinearForm_isHomogeneous k (c j))

@[simp] theorem sectionLinearGradedMap_X (c : ι→κ→₀k) (i : ι) :
    sectionLinearGradedMap k c (MvPolynomial.X i)=sectionLinearForm k (c i) := by
  simp [sectionLinearGradedMap]

namespace RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) (s : ι→Γ(C.sheaf,⊤))

theorem sectionProjectiveChart_linearForm_preimage (i : ι) (c : ι→₀k) :
    C.sectionProjectiveChart k s i ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c)=
      (C.nonvanishingOpen (s i)).ι ⁻¹ᵁ
        C.nonvanishingOpen (Finsupp.linearCombination k s c) := by
  have he : unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
      (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
      (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
      (HomogeneousLocalization.Away.isLocalizationElem
        (polynomialVariable_mem_degreeOne k i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
          (sectionLinearForm_isHomogeneous k c)))=
        C.ratioSection (Finsupp.linearCombination k s c) (s i) := by
    unfold HomogeneousLocalization.Away.isLocalizationElem
    rw [unitHomogeneousAwayEvaluation_mk_of_eq_one _ _
      (C.sectionProjectiveChartRingMap_self k s i)]
    simp only [pow_one]
    exact C.sectionRatioPolynomialMap_linearForm k s (s i) c
  rw [sectionProjectiveChart,Scheme.Hom.comp_preimage,Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule ι k)
      (polynomialVariable_mem_degreeOne k i) (by decide)
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (sectionLinearForm_isHomogeneous k c))
      (by decide),
    SpecMap_preimage_basicOpen,CommRingCat.ofHom_apply,he,
    Scheme.Opens.toSpecΓ_preimage_basicOpen,C.ratioSection_basicOpen]
  simp only [Scheme.Hom.preimage_inf,Scheme.Opens.ι_preimage_self,top_inf_eq]

theorem sectionProjectiveMap_linearForm_preimage
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (c : ι→₀k) :
    C.sectionProjectiveMap k s hcover ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c)=
      C.nonvanishingOpen (Finsupp.linearCombination k s c) := by
  ext x
  have hx : x∈⨆ i,C.nonvanishingOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
  have hpre := congrArg (fun U=>((⟨x,hxi⟩ : C.nonvanishingOpen (s i))∈U))
    (C.sectionProjectiveChart_linearForm_preimage k s i c)
  have hpre' : C.sectionProjectiveChart k s i ⟨x,hxi⟩ ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c) ↔
      x ∈ C.nonvanishingOpen (Finsupp.linearCombination k s c) := Iff.of_eq hpre
  have hchart : C.sectionProjectiveMap k s hcover x =
      C.sectionProjectiveChart k s i ⟨x,hxi⟩ :=
    congrArg (fun f : (C.nonvanishingOpen (s i)).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule ι k) => f ⟨x,hxi⟩)
      (C.sectionProjectiveMap_chart k s hcover i)
  change C.sectionProjectiveMap k s hcover x ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c) ↔
      x ∈ C.nonvanishingOpen (Finsupp.linearCombination k s c)
  rw [hchart]
  exact hpre'

variable (den : Γ(C.sheaf,⊤)) (p : MvPolynomial ι k)
    (hp : p.IsHomogeneous 1)
    (hvalue : C.sectionProjectiveFieldMap k s p=C.toCartierData.sectionValue ⊤ den)

theorem sectionRatioPolynomialMap_eq_one
    (hunit : C.sectionRatioPolynomialMap k s den p=1) :
    IsUnit (C.sectionRatioPolynomialMap k s den p) := hunit ▸ isUnit_one

def sectionLinearChartCoordinates
    (hunit : C.sectionRatioPolynomialMap k s den p=1) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k) p→+*
      Γ(X,C.nonvanishingOpen den) :=
  unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionRatioPolynomialMap k s den) p (hunit ▸ isUnit_one)

def sectionLinearChart
    (hunit : C.sectionRatioPolynomialMap k s den p=1) :
    (C.nonvanishingOpen den).toScheme⟶Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  (C.nonvanishingOpen den).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (C.sectionLinearChartCoordinates k s den p hunit)) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) p
      ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)

theorem sectionLinearChart_generic
    (hunit : C.sectionRatioPolynomialMap k s den p=1)
    [Nonempty (C.nonvanishingOpen den)]
    (hη : genericPoint X∈C.nonvanishingOpen den) :
    (C.nonvanishingOpen den).fromSpecStalkOfMem (genericPoint X) hη ≫
        C.sectionLinearChart k s den p hp hunit =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) p
        ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)
        (hvalue.symm ▸ C.sectionValue_ne_zero_of_nonvanishing den) := by
  have hd := C.sectionValue_ne_zero_of_nonvanishing den
  let F := (X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤)
  let v (i : ι) := C.toCartierData.sectionValue ⊤ (s i)
  have hcomp := unitHomogeneousAwayEvaluation_map
    (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionRatioPolynomialMap k s den)
    (X.germToFunctionField (C.nonvanishingOpen den)).hom p (hunit ▸ isUnit_one)
  let E := MvPolynomial.eval₂Hom F
    (fun i=>(C.toCartierData.sectionValue ⊤ den)⁻¹*v i)
  have hEq : (X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
      (C.sectionRatioPolynomialMap k s den)=E :=
    C.sectionRatioPolynomialMap_germ k s den
  have hEp : E p=1 := by
    calc
      E p = (X.germToFunctionField (C.nonvanishingOpen den)).hom
          (C.sectionRatioPolynomialMap k s den p) :=
        congrArg (fun Q : MvPolynomial ι k→+*X.functionField => Q p) hEq.symm
      _ = 1 := by rw [hunit,map_one]
  have hEi : IsUnit (E p) := hEp ▸ isUnit_one
  have heval (F₁ F₂ : MvPolynomial ι k→+*X.functionField)
      (hF : F₁=F₂) (h₁ : IsUnit (F₁ p)) (h₂ : IsUnit (F₂ p)) :
      unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k) F₁ p h₁ =
        unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k) F₂ p h₂ := by
    subst F₂
    rfl
  have hcomp' := hcomp.trans (heval _ E hEq _ hEi)
  unfold sectionLinearChart sectionLinearChartCoordinates
  rw [← Category.assoc,Scheme.Opens.fromSpecStalkOfMem_toSpecΓ,
    ← Category.assoc,← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
      (unitHomogeneousAwayEvaluation _ _ _ _))) ≫ _ = _
  rw [hcomp']
  change projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.eval₂Hom F (fun i=>(C.toCartierData.sectionValue ⊤ den)⁻¹*v i))
      p ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)
        (by exact hEi.ne_zero) = _
  exact projectiveFieldChart_scaled F v (C.toCartierData.sectionValue ⊤ den)⁻¹
    (inv_ne_zero hd) p hp (by decide) (by
      change C.sectionProjectiveFieldMap k s p≠0
      exact hvalue.symm ▸ hd)

include hvalue in
theorem sectionLinearChart_eq
    (hunit : C.sectionRatioPolynomialMap k s den p=1)
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    C.sectionLinearChart k s den p hp hunit=
      (C.nonvanishingOpen den).ι ≫ C.sectionProjectiveMap k s hcover := by
  by_cases hU : Nonempty (C.nonvanishingOpen den)
  · letI := hU
    have hη := genericPoint_mem_open X (C.nonvanishingOpen den)
    let η := (C.nonvanishingOpen den).fromSpecStalkOfMem (genericPoint X) hη
    letI : IsDominant η := genericStalkMapToOpen_isDominant _ hη
    have hηcover : genericPoint X∈⨆ i,C.nonvanishingOpen (s i) := by
      rw [hcover]; trivial
    obtain ⟨i,hηi⟩ := Opens.mem_iSup.mp hηcover
    letI : Nonempty (C.nonvanishingOpen (s i)) := ⟨⟨genericPoint X,hηi⟩⟩
    apply ext_of_isDominant η
    rw [C.sectionLinearChart_generic k s den p hp hvalue hunit hη,
      ← Category.assoc,Scheme.Opens.fromSpecStalkOfMem_ι,
      C.sectionProjectiveMap_generic k s hcover i]
    exact projectiveFieldChart_independent
      (MvPolynomial.homogeneousSubmodule ι k) (C.sectionProjectiveFieldMap k s)
      p (MvPolynomial.X i) ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp)
      (polynomialVariable_mem_degreeOne k i)
      (by decide) (by decide)
      (by exact hvalue.symm ▸ C.sectionValue_ne_zero_of_nonvanishing den)
      (by simpa only [sectionProjectiveFieldMap,MvPolynomial.eval₂Hom_X'] using
        C.sectionValue_ne_zero_of_nonvanishing (s i))
  · letI : IsEmpty (C.nonvanishingOpen den) := not_nonempty_iff.mp hU
    exact isInitialOfIsEmpty.hom_ext _ _

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionLinearChart_eq
