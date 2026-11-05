module

public import PaperVerification.ToricGradedProjQuotient
public import PaperVerification.ToricProjectiveMonomialMaps
public import PaperVerification.ToricProjectiveVertexCover
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

@[expose] public section

/-!
# The actual monomial projective closed immersion

The graded polynomial quotient sends the i-th projective coordinate to
the homogeneous character (1,aᵢ). Its Proj is embedded by the actual
graded-ring morphism. All coordinate charts are domains, and the common
character torus is schematically dense. Thus this Proj is the genuine
scheme-theoretic monomial orbit closure, rather than an assumed model.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u v

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra AlgebraicGeometry CategoryTheory HomogeneousLocalization
open PaperVerification.ToricSchemes
open scoped BigOperators Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι : Type u} {M : Type v} [AddCommGroup M] (a : ι→M)
    (k : Type (max u v)) [Field k]

def homogeneousMonomialMap :
    MvPolynomial ι k→ₐ[k]AddMonoidAlgebra k (homogeneousWeightMonoid a) :=
  MvPolynomial.aeval (homogeneousWeightCharacter a k)

@[simp] theorem homogeneousMonomialMap_X (i : ι) :
    homogeneousMonomialMap a k (MvPolynomial.X i)=homogeneousWeightCharacter a k i := by
  simp [homogeneousMonomialMap]

theorem homogeneousMonomialMap_mem {d : ℕ} {p : MvPolynomial ι k}
    (hp : p∈MvPolynomial.homogeneousSubmodule ι k d) :
    homogeneousMonomialMap a k p∈homogeneousWeightGrading a k d := by
  rw [← p.support_sum_monomial_coeff,map_sum]
  apply Submodule.sum_mem
  intro m hm
  rw [homogeneousMonomialMap,MvPolynomial.aeval_monomial,← Algebra.smul_def]
  apply Submodule.smul_mem
  have hd := MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hm
  have hprod := SetLike.prod_pow_mem_graded (homogeneousWeightGrading a k)
    (fun _ : ι=>1) (homogeneousWeightCharacter a k) m
      (F := m.support) (fun i _=>homogeneousWeightCharacter_homogeneous a k i)
  simpa only [Finsupp.prod,smul_eq_mul,mul_one,← hd] using hprod

def homogeneousMonomialGradedMap :
    MvPolynomial.homogeneousSubmodule ι k→+*ᵍhomogeneousWeightGrading a k where
  __ := (homogeneousMonomialMap a k).toRingHom
  map_mem := homogeneousMonomialMap_mem a k

@[simp] theorem homogeneousMonomialGradedMap_X (i : ι) :
    homogeneousMonomialGradedMap a k (MvPolynomial.X i)=
      homogeneousWeightCharacter a k i := homogeneousMonomialMap_X a k i

theorem homogeneousMonomialMap_surjective :
    Function.Surjective (homogeneousMonomialMap a k) := by
  have hchar (p : homogeneousWeightMonoid a) :
      ∃ q : MvPolynomial ι k,homogeneousMonomialMap a k q=single p 1 := by
    refine AddSubmonoid.closure_induction
      (motive := fun x hx=>∃ q : MvPolynomial ι k,
        homogeneousMonomialMap a k q=single (⟨x,hx⟩ : homogeneousWeightMonoid a) 1)
      ?_ ?_ ?_ p.property
    · rintro x ⟨i,rfl⟩
      exact ⟨MvPolynomial.X i,by simp [homogeneousWeightCharacter,homogeneousWeight]⟩
    · exact ⟨1,by rw [map_one]; rfl⟩
    · intro x y hx hy ihx ihy
      obtain ⟨p,hp⟩ := ihx
      obtain ⟨q,hq⟩ := ihy
      exact ⟨p*q,by rw [map_mul,hp,hq]; simp only [single_mul_single,mul_one]; rfl⟩
  intro f
  induction f using AddMonoidAlgebra.induction_on with
  | of p => exact hchar p
  | add f g hf hg =>
      obtain ⟨p,rfl⟩ := hf
      obtain ⟨q,rfl⟩ := hg
      exact ⟨p+q,map_add _ _ _⟩
  | smul r f hf =>
      obtain ⟨p,rfl⟩ := hf
      exact ⟨r • p,map_smul _ _ _⟩

theorem homogeneousMonomialGradedMap_surjective :
    Function.Surjective (homogeneousMonomialGradedMap a k) :=
  homogeneousMonomialMap_surjective a k

def monomialProjectiveEmbedding :
    monomialProjectiveScheme a k⟶Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  Proj.map (homogeneousMonomialGradedMap a k)
    (irrelevant_le_map_of_surjective _ (homogeneousMonomialGradedMap_surjective a k))

instance monomialProjectiveEmbedding_isClosedImmersion :
    IsClosedImmersion (monomialProjectiveEmbedding a k) :=
  projMap_isClosedImmersion_of_surjective _ (homogeneousMonomialGradedMap_surjective a k)

@[simp] theorem monomialProjectiveEmbedding_preimage (i : ι) :
    monomialProjectiveEmbedding a k ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)=
        Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k i) := by
  unfold monomialProjectiveEmbedding
  rw [Proj.map_preimage_basicOpen,homogeneousMonomialGradedMap_X]

variable [IsDomain (AddMonoidAlgebra k M)]

def projectiveMonomialFieldMap :
    MvPolynomial ι k→+*FractionRing (AddMonoidAlgebra k M) :=
  (homogeneousExponentFractionMap a k).comp (homogeneousMonomialGradedMap a k).toRingHom

@[simp] theorem projectiveMonomialFieldMap_X (i : ι) :
    projectiveMonomialFieldMap a k (MvPolynomial.X i)=
      algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
        (single (a i) 1) := by
  simp [projectiveMonomialFieldMap,homogeneousMonomialGradedMap,
    homogeneousMonomialMap,homogeneousExponentFractionMap,homogeneousWeightCharacter,
    homogeneousWeight]

theorem monomialProjectiveEmbedding_torus_generic (i : ι) :
    Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra k M)
      (FractionRing (AddMonoidAlgebra k M))))≫
        monomialTorusChart a k i≫monomialProjectiveEmbedding a k=
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (projectiveMonomialFieldMap a k) (MvPolynomial.X i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i))
        (by decide)
        (by
          change homogeneousExponentFractionMap a k
            (homogeneousMonomialGradedMap a k (MvPolynomial.X i))≠0
          rw [homogeneousMonomialGradedMap_X]
          exact homogeneousExponentFractionMap_character_ne_zero a k i) := by
  erw [← Category.assoc,monomialTorusChart_fraction]
  have hne : homogeneousExponentFractionMap a k
      (homogeneousMonomialGradedMap a k (MvPolynomial.X i)) ≠ 0 := by
    rw [homogeneousMonomialGradedMap_X]
    exact homogeneousExponentFractionMap_character_ne_zero a k i
  have h := projectiveFieldChart_gradedMap (homogeneousMonomialGradedMap a k)
    (irrelevant_le_map_of_surjective _ (homogeneousMonomialGradedMap_surjective a k))
    (homogeneousExponentFractionMap a k) (s := MvPolynomial.X i)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i))
    (by decide) hne
  simpa only [homogeneousMonomialGradedMap_X,monomialProjectiveEmbedding,
    projectiveMonomialFieldMap] using h

variable {K : Type (max u v)} [Field K]

theorem monomialTorusChart_fieldMap (ρ : AddMonoidAlgebra k M→+*K)
    (hρ : Function.Injective ρ) (i : ι) :
    Spec.map (CommRingCat.ofHom ρ)≫monomialTorusChart a k i=
      projectiveFieldChart (homogeneousWeightGrading a k)
        (ρ.comp (homogeneousExponentAlgHom a k).toRingHom)
        (homogeneousWeightCharacter a k i)
        (homogeneousWeightCharacter_homogeneous a k i) (by decide)
        (by
          change ρ (homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k i))≠0
          rw [homogeneousExponentAlgHom_character]
          simpa only [map_zero] using
            hρ.ne (show single (a i) (1:k)≠0 by simp)) := by
  have hne : ρ (single (a i) 1)≠0 := by
    simpa only [map_zero] using hρ.ne (show single (a i) (1:k)≠0 by simp)
  have hE : ρ.comp (dehomogeneousChartMap a k i).toRingHom=
      homogeneousAwayEvaluation (homogeneousWeightGrading a k)
        (ρ.comp (homogeneousExponentAlgHom a k).toRingHom)
        (homogeneousWeightCharacter a k i) (by
          change ρ (homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k i))≠0
          rw [homogeneousExponentAlgHom_character]
          exact hne) := by
    ext z
    obtain ⟨d,p,hp,rfl⟩ := Away.mk_surjective (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter_homogeneous a k i) z
    change ρ (dehomogeneousChartMap a k i
      (Away.mk (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter_homogeneous a k i) d p hp)) = _
    rw [dehomogeneousChartMap_mk,homogeneousAwayEvaluation_mk]
    change ρ (dehomogeneousWeightMap a k i p) =
      ρ (homogeneousExponentAlgHom a k p) /
        ρ (homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k i)) ^ d
    rw [homogeneousExponentAlgHom_character,homogeneousExponentAlgHom_factor a k hp i]
    simp only [smul_eq_mul,mul_one]
    rw [map_mul]
    have hpow : ρ (single (d • a i) 1)=ρ (single (a i) 1)^d := by
      rw [← map_pow,single_pow,one_pow]
    rw [hpow,mul_div_cancel_left₀ _ (pow_ne_zero d hne)]
  unfold monomialTorusChart projectiveFieldChart
  erw [← Category.assoc,← Spec.map_comp]
  exact congrArg (fun F=>Spec.map (CommRingCat.ofHom F)≫_) hE

theorem monomialProjectiveEmbedding_torus_fieldMap
    (ρ : AddMonoidAlgebra k M→+*K) (hρ : Function.Injective ρ) (i : ι) :
    Spec.map (CommRingCat.ofHom ρ)≫monomialTorusChart a k i≫
        monomialProjectiveEmbedding a k=
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        ((ρ.comp (homogeneousExponentAlgHom a k).toRingHom).comp
          (homogeneousMonomialGradedMap a k).toRingHom)
        (MvPolynomial.X i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i))
        (by decide)
        (by
          change ρ (homogeneousExponentAlgHom a k
            (homogeneousMonomialGradedMap a k (MvPolynomial.X i)))≠0
          rw [homogeneousMonomialGradedMap_X,homogeneousExponentAlgHom_character]
          simpa only [map_zero] using
            hρ.ne (show single (a i) (1:k)≠0 by simp)) := by
  erw [← Category.assoc,monomialTorusChart_fieldMap a k ρ hρ i]
  have hne : (ρ.comp (homogeneousExponentAlgHom a k).toRingHom)
      (homogeneousMonomialGradedMap a k (MvPolynomial.X i)) ≠ 0 := by
    change ρ (homogeneousExponentAlgHom a k
      (homogeneousMonomialGradedMap a k (MvPolynomial.X i))) ≠ 0
    rw [homogeneousMonomialGradedMap_X,homogeneousExponentAlgHom_character]
    simpa only [map_zero] using hρ.ne (show single (a i) (1:k)≠0 by simp)
  have h := projectiveFieldChart_gradedMap (homogeneousMonomialGradedMap a k)
    (irrelevant_le_map_of_surjective _ (homogeneousMonomialGradedMap_surjective a k))
    (ρ.comp (homogeneousExponentAlgHom a k).toRingHom) (s := MvPolynomial.X i)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i))
    (by decide) hne
  simpa only [homogeneousMonomialGradedMap_X,monomialProjectiveEmbedding] using h

instance monomialChart_isDomain (i : ι) :
    IsDomain (monoidChartAlgebra k (differenceWeightMonoid a i)) := by
  exact Function.Injective.isDomain
    (monoidChartAlgebra k (differenceWeightMonoid a i)).val.toRingHom Subtype.val_injective

def monomialCoordinateOpenCover : (monomialProjectiveScheme a k).OpenCover :=
  Scheme.Cover.mkOfCovers ι
    (fun i=>monoidChartScheme k (differenceWeightMonoid a i))
    (monomialCoordinateChartMap a k) (by
    intro x
    have hx : x∈⨆ i,Proj.basicOpen (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter a k i) := by
      rw [monomialProjective_coordinate_cover]; trivial
    obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    rw [← monomialCoordinateChartMap_opensRange] at hi
    obtain ⟨y,hy⟩ := hi
    exact ⟨i,y,hy⟩)

instance monomialProjective_isReduced : IsReduced (monomialProjectiveScheme a k) := by
  letI : ∀ i : (monomialCoordinateOpenCover a k).I₀,
      IsReduced ((monomialCoordinateOpenCover a k).X i) := fun i => by
    change IsReduced (monoidChartScheme k (differenceWeightMonoid a i))
    unfold monoidChartScheme
    infer_instance
  exact IsReduced.of_openCover _ (monomialCoordinateOpenCover a k)

def monomialCoordinateGenericPoint (i : ι) :
    monoidChartScheme k (differenceWeightMonoid a i) := ⟨⊥,inferInstance⟩

theorem monomialCoordinateGenericPoint_isGenericPoint (i : ι) :
    IsGenericPoint (monomialCoordinateGenericPoint a k i) Set.univ := by
  change closure ({monomialCoordinateGenericPoint a k i} :
    Set (PrimeSpectrum (monoidChartAlgebra k (differenceWeightMonoid a i))))=Set.univ
  rw [PrimeSpectrum.closure_singleton]
  exact PrimeSpectrum.zeroLocus_bot

theorem monomialTorusChart_denseRange (j : ι) : DenseRange (monomialTorusChart a k j) := by
  let η : Spec (CommRingCat.of (AddMonoidAlgebra k M)) := ⟨⊥,inferInstance⟩
  have hη (i : ι) :
      monomialCoordinateChartMap a k i (monomialCoordinateGenericPoint a k i)=
        monomialTorusChart a k j η := by
    rw [← monomialTorusChart_independent a k i j,
      ← monomialCoordinateChartMap_torus]
    change _=monomialCoordinateChartMap a k i _
    congr 1
    apply PrimeSpectrum.ext
    exact (Ideal.comap_bot_of_injective _ Subtype.val_injective).symm
  intro x
  obtain ⟨i,y,rfl⟩ := (monomialCoordinateOpenCover a k).exists_eq x
  have hclosed : IsClosed ((monomialCoordinateChartMap a k i) ⁻¹'
      closure (Set.range (monomialTorusChart a k j))) :=
    isClosed_closure.preimage (monomialCoordinateChartMap a k i).continuous
  have hmem : monomialCoordinateGenericPoint a k i∈
      (monomialCoordinateChartMap a k i) ⁻¹'
        closure (Set.range (monomialTorusChart a k j)) := by
    change monomialCoordinateChartMap a k i (monomialCoordinateGenericPoint a k i) ∈
      closure (Set.range (monomialTorusChart a k j))
    rw [hη]
    exact subset_closure (Set.mem_range_self η)
  exact ((monomialCoordinateGenericPoint_isGenericPoint a k i).mem_closed_set_iff hclosed).mp
    hmem (Set.mem_univ y)

instance monomialTorusChart_isDominant (j : ι) : IsDominant (monomialTorusChart a k j) :=
  ⟨monomialTorusChart_denseRange a k j⟩

instance monomialTorusChart_isSchemeTheoreticallyDominant (j : ι) :
    IsSchemeTheoreticallyDominant (monomialTorusChart a k j) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monomialProjectiveEmbedding_isClosedImmersion
#print axioms PaperVerification.ToricCharacters.monomialTorusChart_isSchemeTheoreticallyDominant
