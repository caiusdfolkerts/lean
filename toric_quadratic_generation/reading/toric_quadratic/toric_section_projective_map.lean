module

public import PaperVerification.ToricSectionRatios
public import PaperVerification.ToricProjectiveRatios
public import PaperVerification.ToricDominantFunctionField
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

/-!
# The actual projective morphism defined by generating Cartier sections

The construction uses the genuine ratios in the structure sheaf on the
nonvanishing opens. Compatibility is proved on the generic stalk and then
on each integral overlap by separatedness of Proj. It does not assume a
sections-to-projective-space dictionary.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} [IsIntegral X]

theorem genericStalkMap_isDominant :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec X).def]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint X.functionField,X.fromSpecStalk_closedPoint⟩

theorem genericStalkMapToOpen_isDominant (U : X.Opens)
    (hU : genericPoint X∈U) :
    IsDominant (U.fromSpecStalkOfMem (genericPoint X) hU) := by
  letI : IsDominant
      (U.fromSpecStalkOfMem (genericPoint X) hU ≫ U.ι) := by
    rw [U.fromSpecStalkOfMem_ι]
    exact genericStalkMap_isDominant
  exact IsDominant.of_comp_of_isOpenImmersion _ U.ι

theorem genericStalkMapToOpen_homOfLE {U V : X.Opens}
    (hUV : U≤V) (hU : genericPoint X∈U) (hV : genericPoint X∈V) :
    U.fromSpecStalkOfMem (genericPoint X) hU ≫ X.homOfLE hUV =
      V.fromSpecStalkOfMem (genericPoint X) hV := by
  rw [← cancel_mono V.ι]
  simp only [Category.assoc,Scheme.homOfLE_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- A variable lies in the degree-one piece of the actual polynomial grading. -/
theorem polynomialVariable_mem_degreeOne (k : Type u) [CommRing k]
    {ι : Type u} (i : ι) :
    (MvPolynomial.X i : MvPolynomial ι k) ∈ MvPolynomial.homogeneousSubmodule ι k 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i)

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u}
    (s : ι→Γ(C.sheaf,⊤))

/-- The coordinate map of the chart where the i-th actual section does
not vanish. Its selected coordinate is literally one. -/
def sectionProjectiveChartRingMap (i : ι) :
    MvPolynomial ι k→+*Γ(X,C.nonvanishingOpen (s i)) :=
  MvPolynomial.eval₂Hom
    (BaseSections.scalarMap k X (C.nonvanishingOpen (s i)))
    (fun j=>C.ratioSection (s j) (s i))

@[simp] theorem sectionProjectiveChartRingMap_X (i j : ι) :
    C.sectionProjectiveChartRingMap k s i (MvPolynomial.X j)=
      C.ratioSection (s j) (s i) := by
  simp [sectionProjectiveChartRingMap]

@[simp] theorem sectionProjectiveChartRingMap_self (i : ι) :
    C.sectionProjectiveChartRingMap k s i (MvPolynomial.X i)=1 := by
  simp

/-- The chart map is a morphism of actual schemes through the actual
homogeneous degree-zero localization of the polynomial ring. -/
def sectionProjectiveChart (i : ι) :
    (C.nonvanishingOpen (s i)).toScheme⟶
      Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  (C.nonvanishingOpen (s i)).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
          (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one))) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
      (polynomialVariable_mem_degreeOne k i) (by decide)

def sectionProjectiveFieldMap : MvPolynomial ι k→+*X.functionField :=
  MvPolynomial.eval₂Hom
    ((X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤))
    (fun j=>C.toCartierData.sectionValue ⊤ (s j))

theorem sectionProjectiveChartRingMap_germ (i : ι)
    [Nonempty (C.nonvanishingOpen (s i))] :
    (X.germToFunctionField (C.nonvanishingOpen (s i))).hom.comp
        (C.sectionProjectiveChartRingMap k s i) =
      MvPolynomial.eval₂Hom
        ((X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤))
        (fun j=>(C.toCartierData.sectionValue ⊤ (s i))⁻¹*
          C.toCartierData.sectionValue ⊤ (s j)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,sectionProjectiveChartRingMap,
      MvPolynomial.eval₂Hom_C]
    exact BaseSections.germ_scalarMap_top k X _ a
  · intro j
    rw [RingHom.comp_apply, C.sectionProjectiveChartRingMap_X k s i j,
      MvPolynomial.eval₂Hom_X', C.ratioSection_value]
    simp only [div_eq_mul_inv, mul_comm]

/-- Every local projective chart restricts to the projective point given
by the genuine rational values of the sections. -/
theorem sectionProjectiveChart_generic (i : ι)
    [Nonempty (C.nonvanishingOpen (s i))]
    (hη : genericPoint X∈C.nonvanishingOpen (s i)) :
    (C.nonvanishingOpen (s i)).fromSpecStalkOfMem (genericPoint X) hη ≫
        C.sectionProjectiveChart k s i =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) (MvPolynomial.X i)
        (polynomialVariable_mem_degreeOne k i) (by decide)
        (by simpa [sectionProjectiveFieldMap] using
          C.sectionValue_ne_zero_of_nonvanishing (s i)) := by
  have hs := C.sectionValue_ne_zero_of_nonvanishing (s i)
  let F := (X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤)
  let v (j : ι) := C.toCartierData.sectionValue ⊤ (s j)
  have hcomp := unitHomogeneousAwayEvaluation_map
    (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionProjectiveChartRingMap k s i)
    (X.germToFunctionField (C.nonvanishingOpen (s i))).hom
    (MvPolynomial.X i)
    (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
  let E := MvPolynomial.eval₂Hom F (fun j => (v i)⁻¹ * v j)
  have hEi : IsUnit (E (MvPolynomial.X i)) := by
    have hv : v i ≠ 0 := hs
    simp only [E, MvPolynomial.eval₂Hom_X', inv_mul_cancel₀ hv]
    exact isUnit_one
  have heval (F₁ F₂ : MvPolynomial ι k →+* X.functionField)
      (hF : F₁ = F₂) (h₁ : IsUnit (F₁ (MvPolynomial.X i)))
      (h₂ : IsUnit (F₂ (MvPolynomial.X i))) :
      unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
          F₁ (MvPolynomial.X i) h₁ =
        unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
          F₂ (MvPolynomial.X i) h₂ := by
    subst F₂
    rfl
  have hcomp' := hcomp.trans
    (heval _ E (C.sectionProjectiveChartRingMap_germ k s i) _ hEi)
  unfold sectionProjectiveChart
  rw [← Category.assoc,Scheme.Opens.fromSpecStalkOfMem_toSpecΓ,
    ← Category.assoc,← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      ((X.germToFunctionField (C.nonvanishingOpen (s i))).hom.comp
        (unitHomogeneousAwayEvaluation _ _ _ _))) ≫ _ = _
  rw [hcomp']
  change projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.eval₂Hom F (fun j=>(v i)⁻¹*v j)) (MvPolynomial.X i)
      (polynomialVariable_mem_degreeOne k i) (by decide) (by exact hEi.ne_zero) = _
  exact projectiveFieldChart_scaled F v (v i)⁻¹ (inv_ne_zero hs)
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i) (by decide)
    (by simpa [v] using hs)

theorem sectionProjectiveChart_overlap (i j : ι) :
    X.homOfLE (U := C.nonvanishingOpen (s i)⊓C.nonvanishingOpen (s j))
        inf_le_left ≫ C.sectionProjectiveChart k s i =
      X.homOfLE inf_le_right ≫ C.sectionProjectiveChart k s j := by
  classical
  let U := C.nonvanishingOpen (s i)⊓C.nonvanishingOpen (s j)
  by_cases hU : Nonempty U
  · letI := hU
    letI : Nonempty (C.nonvanishingOpen (s i)) :=
      ⟨⟨(Classical.choice hU).val,(Classical.choice hU).property.1⟩⟩
    letI : Nonempty (C.nonvanishingOpen (s j)) :=
      ⟨⟨(Classical.choice hU).val,(Classical.choice hU).property.2⟩⟩
    have hηU : genericPoint X∈U := genericPoint_mem_open X U
    let η := U.fromSpecStalkOfMem (genericPoint X) hηU
    letI : IsDominant η := genericStalkMapToOpen_isDominant U hηU
    apply ext_of_isDominant η
    rw [← Category.assoc,← Category.assoc,
      genericStalkMapToOpen_homOfLE inf_le_left hηU hηU.1,
      genericStalkMapToOpen_homOfLE inf_le_right hηU hηU.2,
      C.sectionProjectiveChart_generic k s i hηU.1,
      C.sectionProjectiveChart_generic k s j hηU.2]
    exact projectiveFieldChart_independent
      (MvPolynomial.homogeneousSubmodule ι k) (C.sectionProjectiveFieldMap k s)
      (MvPolynomial.X i) (MvPolynomial.X j)
      (polynomialVariable_mem_degreeOne k i) (polynomialVariable_mem_degreeOne k j)
      (by decide) (by decide) _ _
  · letI : IsEmpty U := not_nonempty_iff.mp hU
    exact isInitialOfIsEmpty.hom_ext _ _

/-- Generating sections define an actual global morphism to Proj. -/
def sectionProjectiveMap
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    X⟶Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  (X.openCoverOfIsOpenCover (fun i=>C.nonvanishingOpen (s i)) hcover).glueMorphisms
    (C.sectionProjectiveChart k s) (by
      intro i j
      change Limits.pullback.fst (C.nonvanishingOpen (s i)).ι
          (C.nonvanishingOpen (s j)).ι ≫ C.sectionProjectiveChart k s i =
        Limits.pullback.snd (C.nonvanishingOpen (s i)).ι
          (C.nonvanishingOpen (s j)).ι ≫ C.sectionProjectiveChart k s j
      apply (cancel_epi (isPullback_opens_inf
        (C.nonvanishingOpen (s i)) (C.nonvanishingOpen (s j))).isoPullback.hom).mp
      simpa only [Category.assoc,IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc] using
        C.sectionProjectiveChart_overlap k s i j)

@[reassoc (attr := simp)] theorem sectionProjectiveMap_chart
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι) :
    (C.nonvanishingOpen (s i)).ι ≫ C.sectionProjectiveMap k s hcover =
      C.sectionProjectiveChart k s i := by
  exact (X.openCoverOfIsOpenCover (fun i=>C.nonvanishingOpen (s i)) hcover).ι_glueMorphisms _ _ i

theorem sectionProjectiveChartRingMap_away_variable (i j : ι) :
    unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
      (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
      (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
      (HomogeneousLocalization.Away.isLocalizationElem
        (polynomialVariable_mem_degreeOne k i) (polynomialVariable_mem_degreeOne k j)) =
        C.ratioSection (s j) (s i) := by
  have he := unitHomogeneousAwayEvaluation_mk_of_eq_one
    (MvPolynomial.homogeneousSubmodule ι k) (C.sectionProjectiveChartRingMap k s i)
    (C.sectionProjectiveChartRingMap_self k s i)
    (show (MvPolynomial.X i : MvPolynomial ι k) ∈
      MvPolynomial.homogeneousSubmodule ι k 1 from polynomialVariable_mem_degreeOne k i)
    1 ((MvPolynomial.X j : MvPolynomial ι k) ^ 1)
    (by simpa only [one_smul, pow_one] using polynomialVariable_mem_degreeOne k j)
  simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one,
    C.sectionProjectiveChartRingMap_X k s i j] using he

theorem sectionProjectiveChart_preimage (i j : ι) :
    C.sectionProjectiveChart k s i ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j)=
      (C.nonvanishingOpen (s i)).ι ⁻¹ᵁ C.nonvanishingOpen (s j) := by
  have he := C.sectionProjectiveChartRingMap_away_variable k s i j
  rw [sectionProjectiveChart,Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule ι k)
      (polynomialVariable_mem_degreeOne k i) (by decide)
      (polynomialVariable_mem_degreeOne k j) (by decide),
    SpecMap_preimage_basicOpen,CommRingCat.ofHom_apply,he,
    Scheme.Opens.toSpecΓ_preimage_basicOpen,C.ratioSection_basicOpen]
  simp only [Scheme.Hom.preimage_inf,Scheme.Opens.ι_preimage_self,top_inf_eq]

/-- The projective basic opens have exactly the expected inverse images;
this is a statement about scheme morphisms and actual open subsets. -/
theorem sectionProjectiveMap_preimage
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (j : ι) :
    C.sectionProjectiveMap k s hcover ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j)=
      C.nonvanishingOpen (s j) := by
  ext x
  have hx : x∈⨆ i,C.nonvanishingOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
  have hpre := congrArg (fun U=>((⟨x,hxi⟩ : C.nonvanishingOpen (s i))∈U))
    (C.sectionProjectiveChart_preimage k s i j)
  have hpre' : C.sectionProjectiveChart k s i ⟨x, hxi⟩ ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j) ↔
      x ∈ C.nonvanishingOpen (s j) := Iff.of_eq hpre
  have hchart : C.sectionProjectiveMap k s hcover x =
      C.sectionProjectiveChart k s i ⟨x, hxi⟩ :=
    congrArg (fun f : (C.nonvanishingOpen (s i)).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule ι k) => f ⟨x, hxi⟩)
      (C.sectionProjectiveMap_chart k s hcover i)
  change C.sectionProjectiveMap k s hcover x ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j) ↔
      x ∈ C.nonvanishingOpen (s j)
  rw [hchart]
  exact hpre'

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_chart
