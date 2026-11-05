module

public import PaperVerification.ToricHomogeneousMonoidCharts
public import PaperVerification.ToricProjectiveRatios
public import PaperVerification.ToricChartOpenImmersions
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

/-!
# Character maps into the actual monomial Proj

The chart morphisms are the genuine Proj affine-chart open immersions.
Their restrictions to the character torus agree as scheme morphisms,
proved through homogeneous ratios in the actual fraction field and
separatedness. Their mutual inverse-image opens are the basic opens of
the literal weight-difference characters.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra AlgebraicGeometry CategoryTheory HomogeneousLocalization
open PaperVerification.ToricSchemes
open scoped BigOperators Classical

variable {ι M : Type*} [AddCommGroup M] (a : ι → M)
    (k : Type u) [Field k]
    [IsDomain (AddMonoidAlgebra k M)]

def homogeneousExponentMap : homogeneousWeightMonoid a →+ M :=
  (AddMonoidHom.snd ℕ M).comp (homogeneousWeightMonoid a).subtype

def homogeneousExponentAlgHom :
    AddMonoidAlgebra k (homogeneousWeightMonoid a) →ₐ[k] AddMonoidAlgebra k M :=
  AddMonoidAlgebra.mapDomainAlgHom k k (homogeneousExponentMap a)

@[simp] theorem homogeneousExponentAlgHom_single (p : homogeneousWeightMonoid a) (r : k) :
    homogeneousExponentAlgHom a k (single p r)=single p.val.2 r := by
  simp [homogeneousExponentAlgHom,homogeneousExponentMap]

@[simp] theorem homogeneousExponentAlgHom_character (j : ι) :
    homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k j)=single (a j) 1 := by
  exact homogeneousExponentAlgHom_single a k (homogeneousWeight a j) 1

theorem homogeneousExponentAlgHom_factor {d : ℕ}
    {f : AddMonoidAlgebra k (homogeneousWeightMonoid a)}
    (hf : f∈homogeneousWeightGrading a k d) (j : ι) :
    homogeneousExponentAlgHom a k f=
      single (d • a j) (1 : k)*dehomogeneousWeightMap a k j f := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  simp only [Finsupp.sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdegree : p.val.1=d := hf p hp
  simp only [homogeneousExponentAlgHom_single,dehomogeneousWeightMap_single,
    single_mul_single,one_mul]
  congr 1
  change p.val.2=d • a j+(p.val.2-p.val.1 • a j)
  rw [hdegree]
  abel

def homogeneousExponentFractionMap :
    AddMonoidAlgebra k (homogeneousWeightMonoid a) →+*
      FractionRing (AddMonoidAlgebra k M) :=
  (algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))).comp
    (homogeneousExponentAlgHom a k).toRingHom

theorem homogeneousExponentFractionMap_character_ne_zero (j : ι) :
    homogeneousExponentFractionMap a k (homogeneousWeightCharacter a k j)≠0 := by
  change algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
    (homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k j))≠0
  rw [homogeneousExponentAlgHom_character]
  simpa only [map_zero] using (IsFractionRing.injective
    (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))).ne
      (show single (a j) (1 : k)≠0 by simp)

theorem dehomogeneousChartMap_fraction (j : ι) :
    (algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))).comp
      (dehomogeneousChartMap a k j).toRingHom=
      homogeneousAwayEvaluation (homogeneousWeightGrading a k)
        (homogeneousExponentFractionMap a k) (homogeneousWeightCharacter a k j)
        (homogeneousExponentFractionMap_character_ne_zero a k j) := by
  ext x
  obtain ⟨d,f,hf,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousWeightGrading a k) (homogeneousWeightCharacter_homogeneous a k j) x
  change algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
    (dehomogeneousChartMap a k j (Away.mk (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter_homogeneous a k j) d f hf)) = _
  rw [dehomogeneousChartMap_mk,homogeneousAwayEvaluation_mk]
  change algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
      (dehomogeneousWeightMap a k j f) =
    algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
      (homogeneousExponentAlgHom a k f) /
        (algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
          (homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k j))) ^ d
  rw [homogeneousExponentAlgHom_character,homogeneousExponentAlgHom_factor a k hf j]
  simp only [smul_eq_mul,mul_one,map_mul,← map_pow,single_pow,one_pow]
  have hne : algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
      (single (d • a j) 1)≠0 := by
    simpa only [map_zero] using (IsFractionRing.injective
      (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))).ne
        (show single (d • a j) (1 : k)≠0 by simp)
  exact (mul_div_cancel_left₀ _ hne).symm

def monomialTorusChart (j : ι) :
    Spec (CommRingCat.of (AddMonoidAlgebra k M))⟶monomialProjectiveScheme a k :=
  Spec.map (CommRingCat.ofHom (dehomogeneousChartMap a k j).toRingHom)≫
    Proj.awayι (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j)
      (homogeneousWeightCharacter_homogeneous a k j) (by decide)

theorem monomialTorusChart_fraction (j : ι) :
    Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra k M)
      (FractionRing (AddMonoidAlgebra k M))))≫monomialTorusChart a k j=
      projectiveFieldChart (homogeneousWeightGrading a k)
        (homogeneousExponentFractionMap a k) (homogeneousWeightCharacter a k j)
        (homogeneousWeightCharacter_homogeneous a k j) (by decide)
        (homogeneousExponentFractionMap_character_ne_zero a k j) := by
  unfold monomialTorusChart projectiveFieldChart
  erw [← Category.assoc,← Spec.map_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (dehomogeneousChartMap_fraction a k j)

theorem monomialTorusChart_independent (i j : ι) :
    monomialTorusChart a k i=monomialTorusChart a k j := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra k M)
    (FractionRing (AddMonoidAlgebra k M))))
  letI : IsDominant g := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker (algebraMap (AddMonoidAlgebra k M)
      (FractionRing (AddMonoidAlgebra k M))) ≤ nilradical (AddMonoidAlgebra k M)
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective _ _)]
    exact bot_le
  letI : (monomialProjectiveScheme a k).IsSeparated :=
    inferInstanceAs ((Proj (homogeneousWeightGrading a k)).IsSeparated)
  apply ext_of_isDominant g
  rw [monomialTorusChart_fraction,monomialTorusChart_fraction]
  exact projectiveFieldChart_independent _ _ _ _
    (homogeneousWeightCharacter_homogeneous a k i)
    (homogeneousWeightCharacter_homogeneous a k j) (by decide) (by decide)
    (homogeneousExponentFractionMap_character_ne_zero a k i)
    (homogeneousExponentFractionMap_character_ne_zero a k j)

def monomialCoordinateChartMap (j : ι) :
    monoidChartScheme k (differenceWeightMonoid a j)⟶monomialProjectiveScheme a k :=
  Spec.map (CommRingCat.ofHom (homogeneousWeightChartEquiv a k j).toAlgHom.toRingHom)≫
    Proj.awayι (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j)
      (homogeneousWeightCharacter_homogeneous a k j) (by decide)

instance monomialCoordinateChartMap_isOpenImmersion (j : ι) :
    IsOpenImmersion (monomialCoordinateChartMap a k j) := by
  letI : IsIso (CommRingCat.ofHom
      (homogeneousWeightChartEquiv a k j).toAlgHom.toRingHom) :=
    (homogeneousWeightChartEquiv a k j).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold monomialCoordinateChartMap
  infer_instance

theorem monomialCoordinateChartMap_torus (j : ι) :
    Spec.map (CommRingCat.ofHom (monoidChartAlgebra k
      (differenceWeightMonoid a j)).val.toRingHom)≫monomialCoordinateChartMap a k j=
        monomialTorusChart a k j := by
  unfold monomialCoordinateChartMap monomialTorusChart
  erw [← Category.assoc,← Spec.map_comp]
  rfl

theorem monomialCoordinateChartMap_opensRange (j : ι) :
    (monomialCoordinateChartMap a k j).opensRange=
      Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j) := by
  letI : IsIso (CommRingCat.ofHom
      (homogeneousWeightChartEquiv a k j).toAlgHom.toRingHom) :=
    (homogeneousWeightChartEquiv a k j).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold monomialCoordinateChartMap
  erw [Scheme.Hom.opensRange_comp_of_isIso,
    Proj.opensRange_awayι]

/-- The second projective coordinate becomes exactly the difference
character on the first affine chart. -/
theorem monomialCoordinateChartMap_preimage_basicOpen (i j : ι) :
    monomialCoordinateChartMap a k i ⁻¹ᵁ
      Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j)=
        PrimeSpectrum.basicOpen (chartCharacter k (differenceWeightMonoid a i)
          (a j-a i) (AddSubmonoid.subset_closure (Set.mem_range_self j))) := by
  unfold monomialCoordinateChartMap
  erw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter_homogeneous a k i) (by decide)
      (homogeneousWeightCharacter_homogeneous a k j) (by decide)]
  change PrimeSpectrum.basicOpen ((homogeneousWeightChartEquiv a k i)
    (HomogeneousLocalization.Away.isLocalizationElem
      (homogeneousWeightCharacter_homogeneous a k i)
      (homogeneousWeightCharacter_homogeneous a k j)))=_
  congr 1
  apply Subtype.ext
  simpa only [HomogeneousLocalization.Away.isLocalizationElem,pow_one,chartCharacter_coe] using
    homogeneousWeightChartEquiv_character_ratio a k i j

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monomialTorusChart_independent
#print axioms PaperVerification.ToricCharacters.monomialCoordinateChartMap_preimage_basicOpen
