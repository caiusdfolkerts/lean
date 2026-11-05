module

public import PaperVerification.ToricSectionProjectiveBase
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.LocalAtTarget

@[expose] public section

/-! # A genuine closed immersion from actual affine coordinate generators -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

def sectionProjectiveChartCoordinates (i : ι) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k)
        (MvPolynomial.X i)→+*Γ(X,C.nonvanishingOpen (s i)) :=
  unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
    (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)

theorem sectionProjectiveChart_isPreimmersion (i : ι)
    (hU : IsAffineOpen (C.nonvanishingOpen (s i)))
    (hgen : Function.Surjective (C.sectionProjectiveChartCoordinates k s i)) :
    IsPreimmersion (C.sectionProjectiveChart k s i) := by
  letI : IsAffine (C.nonvanishingOpen (s i)) := hU
  letI : IsIso (C.nonvanishingOpen (s i)).toSpecΓ := by
    rw [← hU.isoSpec_hom]
    infer_instance
  letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (C.sectionProjectiveChartCoordinates k s i))) :=
    IsClosedImmersion.spec_of_surjective _ hgen
  let q := Spec.map (CommRingCat.ofHom (C.sectionProjectiveChartCoordinates k s i))
  let z := Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
    (polynomialVariable_mem_degreeOne k i) (by decide)
  letI : IsPreimmersion (C.nonvanishingOpen (s i)).toSpecΓ := by infer_instance
  letI : IsPreimmersion q := by dsimp only [q]; infer_instance
  letI : IsOpenImmersion z := by dsimp only [z]; infer_instance
  change IsPreimmersion ((C.nonvanishingOpen (s i)).toSpecΓ ≫ q ≫ z)
  exact IsPreimmersion.comp _ _

/-- If some of the nonvanishing affine charts cover X and their actual
ratio maps generate their coordinate rings, the section map is a
preimmersion. No global immersion statement is built into the premise. -/
theorem sectionProjectiveMap_isPreimmersion_of_chartGenerators
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤)
    {κ : Type u} (chooseChart : κ→ι)
    (hchosen : (⨆ i,C.nonvanishingOpen (s (chooseChart i)))=⊤)
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s (chooseChart i))))
    (hgen : ∀ i,Function.Surjective
      (C.sectionProjectiveChartCoordinates k s (chooseChart i))) :
    IsPreimmersion (C.sectionProjectiveMap k s hcover) := by
  let f := C.sectionProjectiveMap k s hcover
  let U (i : κ) := C.nonvanishingOpen (s (chooseChart i))
  let V (i : κ) := Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.X (chooseChart i))
  have hlocal (i : κ) : IsPreimmersion ((U i).ι ≫ f) := by
    change IsPreimmersion ((C.nonvanishingOpen (s (chooseChart i))).ι ≫
      C.sectionProjectiveMap k s hcover)
    rw [C.sectionProjectiveMap_chart k s hcover (chooseChart i)]
    exact C.sectionProjectiveChart_isPreimmersion k s _ (ha i) (hgen i)
  letI : SurjectiveOnStalks f :=
    IsZariskiLocalAtSource.of_iSup_eq_top U hchosen (fun i=>by
      letI := hlocal i
      infer_instance)
  refine { isEmbedding := ?_ }
  apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range f f.continuous V
    (V := fun i=>(U i).toScheme) (iV := fun i=>(U i).ι)
  · rintro y ⟨x,rfl⟩
    have hx : x∈⨆ i,U i := by rw [hchosen]; trivial
    obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
    apply Opens.mem_iSup.mpr
    refine ⟨i,?_⟩
    have hp := C.sectionProjectiveMap_preimage k s hcover (chooseChart i)
    change x ∈ C.sectionProjectiveMap k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k)
        (MvPolynomial.X (chooseChart i))
    rw [hp]
    exact hxi
  · intro i
    exact (U i).ι.continuous
  · intro i x hx
    have hp := C.sectionProjectiveMap_preimage k s hcover (chooseChart i)
    have hxi : x∈U i := by
      change x∈C.nonvanishingOpen (s (chooseChart i))
      rw [← hp]
      exact hx
    exact ⟨⟨x,hxi⟩,rfl⟩
  · intro i
    letI := hlocal i
    exact ((U i).ι ≫ f).isEmbedding

/-- Properness supplies the closed image. Together with the explicit
local coordinate-ring quotients this gives a genuine closed immersion. -/
theorem sectionProjectiveMap_isClosedImmersion_of_chartGenerators
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤)
    {κ : Type u} (chooseChart : κ→ι)
    (hchosen : (⨆ i,C.nonvanishingOpen (s (chooseChart i)))=⊤)
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s (chooseChart i))))
    (hgen : ∀ i,Function.Surjective
      (C.sectionProjectiveChartCoordinates k s (chooseChart i))) :
    IsClosedImmersion (C.sectionProjectiveMap k s hcover) := by
  letI := C.sectionProjectiveMap_isPreimmersion_of_chartGenerators k s
    hcover chooseChart hchosen ha hgen
  letI := C.sectionProjectiveMap_isProper k s hcover
  exact IsClosedImmersion.of_isPreimmersion _
    (C.sectionProjectiveMap k s hcover).isClosedMap.isClosed_range

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_isClosedImmersion_of_chartGenerators
