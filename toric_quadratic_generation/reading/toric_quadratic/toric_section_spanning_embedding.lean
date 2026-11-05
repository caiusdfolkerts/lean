module

public import PaperVerification.ToricSectionLinearCharts

@[expose] public section

/-!
# Replacing an embedding system by a finite spanning character system

The old affine coordinate ring is a quotient of its homogeneous chart.
A genuine graded substitution sends every old coordinate to its linear
combination of new coordinates. The resulting map of homogeneous
localizations proves that every old affine coordinate generator remains
available. Thus the replacement preserves the actual closed immersion.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι κ : Type u}
    (s : ι→Γ(C.sheaf,⊤)) (t : κ→Γ(C.sheaf,⊤))
    (c : ι→κ→₀k) (hc : ∀ i,Finsupp.linearCombination k t (c i)=s i)

include hc in
theorem sectionLinearSubstitution_ratioMap (i : ι) :
    (C.sectionRatioPolynomialMap k t (s i)).comp
        (sectionLinearGradedMap k c).toRingHom=
      C.sectionProjectiveChartRingMap k s i := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,sectionLinearGradedMap,MvPolynomial.eval₂Hom_C,
      sectionRatioPolynomialMap,sectionProjectiveChartRingMap]
  · intro j
    change C.sectionRatioPolynomialMap k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X j)) =
        C.sectionProjectiveChartRingMap k s i (MvPolynomial.X j)
    rw [sectionLinearGradedMap_X k c j,
      C.sectionRatioPolynomialMap_linearForm k t (s i) (c j),hc j]
    exact (C.sectionProjectiveChartRingMap_X k s i j).symm

include hc in
theorem sectionLinearSubstitution_unit (i : ι) :
    C.sectionRatioPolynomialMap k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))=1 := by
  change ((C.sectionRatioPolynomialMap k t (s i)).comp
    (sectionLinearGradedMap k c).toRingHom) (MvPolynomial.X i)=1
  rw [C.sectionLinearSubstitution_ratioMap k s t c hc]
  exact C.sectionProjectiveChartRingMap_self k s i

include hc in
theorem sectionLinearSubstitution_fieldValue (i : ι) :
    C.sectionProjectiveFieldMap k t
      (sectionLinearGradedMap k c (MvPolynomial.X i))=
      C.toCartierData.sectionValue ⊤ (s i) := by
  rw [sectionLinearGradedMap_X k c i,C.sectionLinearForm_fieldValue k t (c i),hc i]

theorem sectionLinearSubstitution_chartCoordinates (i : ι) :
    (C.sectionLinearChartCoordinates k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))
      (C.sectionLinearSubstitution_unit k s t c hc i)).comp
      (HomogeneousLocalization.Away.map (sectionLinearGradedMap k c)
        (MvPolynomial.X i))=
      C.sectionProjectiveChartCoordinates k s i := by
  ext z
  obtain ⟨m,p,hp,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (MvPolynomial.homogeneousSubmodule ι k) (polynomialVariable_mem_degreeOne k i) z
  rw [RingHom.comp_apply,HomogeneousLocalization.Away.map_mk]
  unfold sectionLinearChartCoordinates sectionProjectiveChartCoordinates
  rw [unitHomogeneousAwayEvaluation_mk_of_eq_one _ _
      (C.sectionLinearSubstitution_unit k s t c hc i),
    unitHomogeneousAwayEvaluation_mk_of_eq_one _ _
      (C.sectionProjectiveChartRingMap_self k s i)]
  exact congrArg (fun F=>F p) (C.sectionLinearSubstitution_ratioMap k s t c hc i)

theorem sectionLinearSubstitution_chartCoordinates_surjective (i : ι)
    (hgen : Function.Surjective (C.sectionProjectiveChartCoordinates k s i)) :
    Function.Surjective (C.sectionLinearChartCoordinates k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))
      (C.sectionLinearSubstitution_unit k s t c hc i)) := by
  apply Function.Surjective.of_comp
    (g := HomogeneousLocalization.Away.map (sectionLinearGradedMap k c)
      (MvPolynomial.X i))
  change Function.Surjective
    ((C.sectionLinearChartCoordinates k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))
      (C.sectionLinearSubstitution_unit k s t c hc i)).comp
        (HomogeneousLocalization.Away.map (sectionLinearGradedMap k c)
          (MvPolynomial.X i)))
  rw [C.sectionLinearSubstitution_chartCoordinates k s t c hc i]
  exact hgen

include hc in
theorem sectionLinearSubstitution_localPreimmersion
    (hnew : (⨆ j,C.nonvanishingOpen (t j))=⊤) (i : ι)
    (ha : IsAffineOpen (C.nonvanishingOpen (s i)))
    (hgen : Function.Surjective (C.sectionProjectiveChartCoordinates k s i)) :
    IsPreimmersion ((C.nonvanishingOpen (s i)).ι ≫
      C.sectionProjectiveMap k t hnew) := by
  let p := sectionLinearGradedMap k c (MvPolynomial.X i)
  have hp : p.IsHomogeneous 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 p).mp
      ((sectionLinearGradedMap k c).map_mem (polynomialVariable_mem_degreeOne k i))
  have hunit := C.sectionLinearSubstitution_unit k s t c hc i
  rw [← C.sectionLinearChart_eq k t (s i) p hp
    (C.sectionLinearSubstitution_fieldValue k s t c hc i) hunit hnew]
  letI : IsAffine (C.nonvanishingOpen (s i)) := ha
  letI : IsIso (C.nonvanishingOpen (s i)).toSpecΓ := by
    rw [← ha.isoSpec_hom]
    infer_instance
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (C.sectionLinearChartCoordinates k t (s i) p hunit))) :=
    IsClosedImmersion.spec_of_surjective _
      (C.sectionLinearSubstitution_chartCoordinates_surjective k s t c hc i hgen)
  let q := Spec.map (CommRingCat.ofHom
    (C.sectionLinearChartCoordinates k t (s i) p hunit))
  let z := Proj.awayι (MvPolynomial.homogeneousSubmodule κ k) p
    ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)
  letI : IsPreimmersion (C.nonvanishingOpen (s i)).toSpecΓ := by infer_instance
  letI : IsPreimmersion q := by dsimp only [q]; infer_instance
  letI : IsOpenImmersion z := by dsimp only [z]; infer_instance
  change IsPreimmersion ((C.nonvanishingOpen (s i)).toSpecΓ ≫ q ≫ z)
  exact IsPreimmersion.comp _ _

include hc in
theorem sectionLinearSubstitution_preimage
    (hnew : (⨆ j,C.nonvanishingOpen (t j))=⊤) (i : ι) :
    C.sectionProjectiveMap k t hnew ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule κ k)
        (sectionLinearGradedMap k c (MvPolynomial.X i))=
      C.nonvanishingOpen (s i) := by
  rw [sectionLinearGradedMap_X k c i,
    C.sectionProjectiveMap_linearForm_preimage k t hnew (c i),hc i]

include hc in
/-- A spanning replacement of a genuine embedding system remains a
genuine closed immersion, including when the new sections are characters. -/
theorem sectionProjectiveMap_isClosedImmersion_of_spanning_chartGenerators
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hnew : (⨆ j,C.nonvanishingOpen (t j))=⊤)
    {α : Type u} (chooseChart : α→ι)
    (hchosen : (⨆ i,C.nonvanishingOpen (s (chooseChart i)))=⊤)
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s (chooseChart i))))
    (hgen : ∀ i,Function.Surjective
      (C.sectionProjectiveChartCoordinates k s (chooseChart i))) :
    IsClosedImmersion (C.sectionProjectiveMap k t hnew) := by
  let f := C.sectionProjectiveMap k t hnew
  let U (i : α) := C.nonvanishingOpen (s (chooseChart i))
  let V (i : α) := Proj.basicOpen (MvPolynomial.homogeneousSubmodule κ k)
    (sectionLinearGradedMap k c (MvPolynomial.X (chooseChart i)))
  have hlocal (i : α) : IsPreimmersion ((U i).ι ≫ f) :=
    C.sectionLinearSubstitution_localPreimmersion k s t c hc hnew
      (chooseChart i) (ha i) (hgen i)
  letI : SurjectiveOnStalks f := IsZariskiLocalAtSource.of_iSup_eq_top U hchosen
    (fun i=>by letI := hlocal i; infer_instance)
  letI : IsPreimmersion f := by
    refine { isEmbedding := ?_ }
    apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range f f.continuous V
      (V := fun i=>(U i).toScheme) (iV := fun i=>(U i).ι)
    · rintro y ⟨x,rfl⟩
      have hx : x∈⨆ i,U i := by rw [hchosen]; trivial
      obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
      apply Opens.mem_iSup.mpr
      refine ⟨i,?_⟩
      have hp := C.sectionLinearSubstitution_preimage k s t c hc hnew (chooseChart i)
      change x∈C.sectionProjectiveMap k t hnew ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule κ k)
          (sectionLinearGradedMap k c (MvPolynomial.X (chooseChart i)))
      rw [hp]
      exact hxi
    · exact fun i=>(U i).ι.continuous
    · intro i x hx
      have hp := C.sectionLinearSubstitution_preimage k s t c hc hnew (chooseChart i)
      have hxi : x∈U i := by
        change x∈C.nonvanishingOpen (s (chooseChart i))
        rw [← hp]
        exact hx
      exact ⟨⟨x,hxi⟩,rfl⟩
    · intro i
      letI := hlocal i
      exact ((U i).ι ≫ f).isEmbedding
  letI : IsProper f := C.sectionProjectiveMap_isProper k t hnew
  change IsClosedImmersion f
  exact IsClosedImmersion.of_isPreimmersion f f.isClosedMap.isClosed_range

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_isClosedImmersion_of_spanning_chartGenerators
