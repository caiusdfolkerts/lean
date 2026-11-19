module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Tactic.Push
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

@[expose] public section
noncomputable section

/-! Exact recovered actual monomial-Proj chart proofs. See adjacent source manifest. -/

section Source_ToricNormalChartOverlaps




/-!
# A weight difference cuts out the actual common normal-cone chart

For two lattice points supporting actual fan cones, their difference is
nonnegative on the first cone and zero precisely on its common rays with
the second. Inverting this literal character therefore gives exactly the
common-face chart. This identifies actual projective chart overlaps with
actual fan gluing overlaps.
-/


namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

variable {n : ℕ}

def characterZeroFace (s : Finset (Lattice n)) (z : Lattice n) : Finset (Lattice n) :=
  s.filter (fun u=>integerPairing u z=0)

theorem characterZeroFace_subset (s : Finset (Lattice n)) (z : Lattice n) :
    characterZeroFace s z⊆s := Finset.filter_subset _ _

theorem negative_character_mem_zeroFace (s : Finset (Lattice n)) (z : Lattice n) :
    -z∈dualConeMonoid (characterZeroFace s z) := by
  intro u hu
  have hz := (Finset.mem_filter.mp hu).2
  simp only [integerPairing,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib]
  change 0≤-integerPairing u z
  rw [hz,neg_zero]

theorem character_clears_zeroFace (s : Finset (Lattice n)) (z : Lattice n)
    (hz : z∈dualConeMonoid s) (m : Lattice n)
    (hm : m∈dualConeMonoid (characterZeroFace s z)) :
    ∃ N : ℕ,m+N • z∈dualConeMonoid s := by
  let N := s.sup (fun u=>(-integerPairing u m).toNat)
  refine ⟨N,?_⟩
  intro u hu
  have he : integerPairing u (m+N • z)=
      integerPairing u m+(N : ℤ)*integerPairing u z := by
    simp [integerPairing,Pi.add_apply,Pi.smul_apply,nsmul_eq_mul,
      mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_left_comm,mul_comm]
  rw [he]
  by_cases hzero : integerPairing u z=0
  · rw [hzero,mul_zero,add_zero]
    exact hm u (Finset.mem_filter.mpr ⟨hu,hzero⟩)
  · have hpos : 1≤ integerPairing u z := by have := hz u hu;omega
    have hle : (-integerPairing u m).toNat≤N :=
      Finset.le_sup (f := fun u => (-integerPairing u m).toNat) hu
    have hleZ : (((-integerPairing u m).toNat : ℕ) : ℤ)≤(N : ℤ) := by exact_mod_cast hle
    have hself := Int.self_le_toNat (-integerPairing u m)
    have hN : (0 : ℤ)≤N := Int.natCast_nonneg _
    nlinarith

theorem characterZeroFace_isLocalizationMap (k : Type*) [CommSemiring k]
    (s : Finset (Lattice n)) (z : Lattice n) (hz : z∈dualConeMonoid s) :
    (Submonoid.powers (chartCharacter k (dualConeMonoid s) z hz)).IsLocalizationMap
      (monoidChartInclusion k (dualConeMonoid_antitone (characterZeroFace_subset s z))) :=
  monoidChartInclusion_isLocalizationMap k
    (dualConeMonoid_antitone (characterZeroFace_subset s z)) z hz
    (negative_character_mem_zeroFace s z) (character_clears_zeroFace s z hz)

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (P : LatticePolytope n)

include «Σ» in
theorem vertex_difference_mem_dualCone (v w : Lattice n)
    (hw : embed n w∈P.carrier) (s : Finset (Lattice n))
    (hs : P.normalCone (embed n v)=(latticeRayCone s : Set (Ambient n))) :
    w-v∈dualConeMonoid s := by
  intro u hu
  have hucone : embed n u∈P.normalCone (embed n v) :=
    hs.symm ▸ latticeRayCone_generator s hu
  have h := hucone (embed n w) hw
  change 0≤∑ i,(u i : ℝ)*((w i : ℝ)-(v i : ℝ)) at h
  change 0≤∑ i,u i*(w i-v i)
  exact_mod_cast h

theorem normal_cone_common_rays_eq_characterZeroFace
    (v w : Lattice n) (hv : embed n v∈P.carrier) (hw : embed n w∈P.carrier)
    (s t : Finset (Lattice n)) (hs : s∈«Σ».cones) (ht : t∈«Σ».cones)
    (hvs : P.normalCone (embed n v)=(latticeRayCone s : Set (Ambient n)))
    (hwt : P.normalCone (embed n w)=(latticeRayCone t : Set (Ambient n))) :
    s∩t=characterZeroFace s (w-v) := by
  ext u
  simp only [Finset.mem_inter,characterZeroFace,Finset.mem_filter]
  constructor
  · rintro ⟨hus,hut⟩
    refine ⟨hus,?_⟩
    have hu : embed n u∈P.normalCone (embed n v)∩P.normalCone (embed n w) :=
      ⟨hvs.symm ▸ latticeRayCone_generator s hus,hwt.symm ▸ latticeRayCone_generator t hut⟩
    have hzero := ((P.mem_normalCone_inter_iff _ _ hv hw _).mp hu).2
    change (∑ i,(u i : ℝ)*((w i : ℝ)-(v i : ℝ)))=0 at hzero
    change (∑ i,u i*(w i-v i))=0
    exact_mod_cast hzero
  · rintro ⟨hus,hzero⟩
    refine ⟨hus,?_⟩
    have hur : u∈«Σ».rays := («Σ».mem_rays_iff u).mpr ⟨s,hs,hus⟩
    apply («Σ».ray_mem_cone_iff ht hur).mp
    change embed n u∈(latticeRayCone t : Set (Ambient n))
    rw [← hwt]
    apply ((P.mem_normalCone_inter_iff _ _ hv hw _).mpr
      ⟨hvs.symm ▸ latticeRayCone_generator s hus,?_⟩).2
    change (∑ i,(u i : ℝ)*((w i : ℝ)-(v i : ℝ)))=0
    change (∑ i,u i*(w i-v i))=0 at hzero
    exact_mod_cast hzero

/-- The common-face inclusion has exactly the principal open image
defined by the actual difference of the two vertex weights. -/
theorem normal_chart_intersection_range (k : Type*) [CommRing k]
    (v w : Lattice n) (hv : embed n v∈P.carrier) (hw : embed n w∈P.carrier)
    (s t : Finset (Lattice n)) (hs : s∈«Σ».cones) (ht : t∈«Σ».cones)
    (hvs : P.normalCone (embed n v)=(latticeRayCone s : Set (Ambient n)))
    (hwt : P.normalCone (embed n w)=(latticeRayCone t : Set (Ambient n))) :
    Set.range (coneChartFaceMap k (Finset.inter_subset_left : s∩t⊆s))=
      ((PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid s) (w-v)
        («Σ».vertex_difference_mem_dualCone P v w hw s hvs))).carrier :
          Set (coneChart k s)) := by
  have hz := «Σ».vertex_difference_mem_dualCone P v w hw s hvs
  have heq := «Σ».normal_cone_common_rays_eq_characterZeroFace P v w hv hw s t hs ht hvs hwt
  have hloc_transport (q : Finset (Lattice n))
      (hq : q=characterZeroFace s (w-v)) (hqs : q⊆s) :
      (Submonoid.powers (chartCharacter k (dualConeMonoid s) (w-v) hz)).IsLocalizationMap
        (monoidChartInclusion k (dualConeMonoid_antitone hqs)) := by
    subst q
    exact characterZeroFace_isLocalizationMap k s (w-v) hz
  have hloc := hloc_transport (s∩t) heq Finset.inter_subset_left
  letI : IsOpenImmersion (monoidChartSpecMap k
      (dualConeMonoid_antitone (Finset.inter_subset_left : s∩t⊆s))) :=
    monoidChartSpecMap_isOpenImmersion_of_isLocalizationMap k
      (dualConeMonoid_antitone (Finset.inter_subset_left : s∩t⊆s)) (w-v) hz hloc
  exact congrArg (fun U : TopologicalSpace.Opens
      (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s))) => U.carrier)
    (monoidChartSpecMap_opensRange_of_isLocalizationMap k _ (w-v) hz hloc)

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.normal_chart_intersection_range
end Source_ToricNormalChartOverlaps

section Source_ToricMonomialAffineCharts




/-!
# Coordinate rings of actual affine monomial images

The algebra generated by a family of characters is exactly the semigroup
algebra of the additive monoid generated by their exponents, embedded in
the ambient character algebra. Thus the polynomial coordinate map is
surjective onto this actual chart ring and gives a closed immersion of
affine schemes. This is an affine ingredient of the projective toric
dictionary, not an assertion of that dictionary.
-/


universe u v w

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open AlgebraicGeometry CategoryTheory

section Algebra

variable (k : Type*) [CommRing k]
variable {M : Type*} [AddCommMonoid M]

/-- Taking the additive closure of the exponents and taking the algebra
generated by their characters commute, as actual subalgebras of `k[M]`. -/
theorem monoidChartAlgebra_closure (S : Set M) :
    monoidChartAlgebra k (AddSubmonoid.closure S) =
      Algebra.adjoin k ((fun m : M => single m (1 : k)) '' S) := by
  apply le_antisymm
  · change (monoidChartAlgebra k (AddSubmonoid.closure S)).toSubmodule ≤
      (Algebra.adjoin k ((fun m : M => single m (1 : k)) '' S)).toSubmodule
    rw [monoidChartAlgebra_toSubmodule, characterModule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    induction hm using AddSubmonoid.closure_induction with
    | mem m hm => exact Algebra.subset_adjoin ⟨m, hm, rfl⟩
    | zero =>
        change single (0 : M) (1 : k) ∈
          Algebra.adjoin k ((fun m : M => single m (1 : k)) '' S)
        simpa only [AddMonoidAlgebra.one_def] using (Algebra.adjoin k
          ((fun m : M => single m (1 : k)) '' S)).one_mem
    | add x y hx hy ihx ihy =>
        simpa using (Algebra.adjoin k
          ((fun m : M => single m (1 : k)) '' S)).mul_mem ihx ihy
  · apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨m, hm, rfl⟩
    change single m (1 : k) ∈
      (monoidChartAlgebra k (AddSubmonoid.closure S)).toSubmodule
    rw [monoidChartAlgebra_toSubmodule, characterModule_eq_span]
    exact Submodule.subset_span ⟨m, AddSubmonoid.subset_closure hm, rfl⟩

variable {ι : Type*} (e : ι → M)

/-- The literal polynomial map sending the coordinate indexed by `i`
to the character with exponent `e i`. -/
def affineMonomialMap : MvPolynomial ι k →ₐ[k] AddMonoidAlgebra k M :=
  MvPolynomial.aeval (fun i => single (e i) (1 : k))

@[simp] theorem affineMonomialMap_X (i : ι) :
    affineMonomialMap k e (MvPolynomial.X i) = single (e i) (1 : k) := by
  simp [affineMonomialMap]

theorem affineMonomialMap_range :
    (affineMonomialMap k e).range =
      monoidChartAlgebra k (AddSubmonoid.closure (Set.range e)) := by
  rw [affineMonomialMap, MvPolynomial.aeval_range, monoidChartAlgebra_closure]
  congr 1
  exact Set.range_comp (fun m : M => single m (1 : k)) e

def affineMonomialMapToChart :
    MvPolynomial ι k →ₐ[k]
      monoidChartAlgebra k (AddSubmonoid.closure (Set.range e)) :=
  (affineMonomialMap k e).codRestrict _ (fun f => by
    rw [← affineMonomialMap_range]
    exact ⟨f, rfl⟩)

theorem affineMonomialMapToChart_surjective :
    Function.Surjective (affineMonomialMapToChart k e) := by
  rintro ⟨f, hf⟩
  rw [← affineMonomialMap_range] at hf
  obtain ⟨g, hg⟩ := hf
  exact ⟨g, Subtype.ext hg⟩

end Algebra

variable (k : Type (max u v w)) [CommRing k]
    {M : Type v} [AddCommMonoid M] {ι : Type w} (e : ι → M)

/-- A scheme-theoretic closed immersion into actual affine coordinate
space, derived from the surjective polynomial ring map. -/
theorem affineMonomialChart_isClosedImmersion :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (affineMonomialMapToChart k e).toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ (affineMonomialMapToChart_surjective k e)

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monoidChartAlgebra_closure
#print axioms PaperVerification.ToricCharacters.affineMonomialChart_isClosedImmersion
end Source_ToricMonomialAffineCharts

section Source_ToricHomogeneousMonoidCharts




/-!
# Literal affine charts of a homogeneous monomial ring

For a family of lattice weights `a`, the homogeneous monoid is generated
by `(1,a i)`.  Dehomogenizing at the weight `a j` identifies the actual
degree-zero localization with the subalgebra generated by the characters
`a i-a j`.  The map is the literal character-ratio map.  In particular,
the statement identifies the actual Proj chart, rather than declaring an
abstract affine toric model to be that chart.
-/


namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

variable {ι M : Type*} [AddCommGroup M] (a : ι → M)

def homogeneousWeightMonoid : AddSubmonoid (ℕ × M) :=
  AddSubmonoid.closure (Set.range (fun i => (1,a i)))

def homogeneousWeight (i : ι) : homogeneousWeightMonoid a :=
  ⟨(1,a i),AddSubmonoid.subset_closure (Set.mem_range_self i)⟩

def homogeneousWeightDegree : homogeneousWeightMonoid a →+ ℕ :=
  (AddMonoidHom.fst ℕ M).comp (homogeneousWeightMonoid a).subtype

@[simp] theorem homogeneousWeightDegree_generator (i : ι) :
    homogeneousWeightDegree a (homogeneousWeight a i)=1 := rfl

def differenceWeightMonoid (j : ι) : AddSubmonoid M :=
  AddSubmonoid.closure (Set.range (fun i => a i-a j))

def weightDifference (j : ι) : (ℕ × M) →+ M where
  toFun p := p.2-p.1 • a j
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add,Prod.snd_add,add_nsmul]
    abel

def homogeneousWeightDifference (j : ι) : homogeneousWeightMonoid a →+ M :=
  (weightDifference a j).comp (homogeneousWeightMonoid a).subtype

@[simp] theorem homogeneousWeightDifference_generator (j i : ι) :
    homogeneousWeightDifference a j (homogeneousWeight a i)=a i-a j := by
  simp [homogeneousWeightDifference,weightDifference,homogeneousWeight]

theorem homogeneousWeightDifference_mem (j : ι) (p : homogeneousWeightMonoid a) :
    homogeneousWeightDifference a j p∈differenceWeightMonoid a j := by
  rcases p with ⟨p,hp⟩
  change weightDifference a j p∈differenceWeightMonoid a j
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact AddSubmonoid.subset_closure ⟨i,by simp [weightDifference]⟩
  | zero => simpa using (differenceWeightMonoid a j).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (differenceWeightMonoid a j).add_mem ihx ihy

theorem homogeneousWeightDifference_injOn_degree (j : ι) (d : ℕ) :
    Set.InjOn (homogeneousWeightDifference a j)
      {p | homogeneousWeightDegree a p=d} := by
  intro p hp q hq hpq
  apply Subtype.ext
  apply Prod.ext
  · exact hp.trans hq.symm
  · change p.val.2-p.val.1 • a j=q.val.2-q.val.1 • a j at hpq
    change p.val.1=d at hp
    change q.val.1=d at hq
    rw [hp,hq] at hpq
    exact sub_left_inj.mp hpq

variable (k : Type*) [CommRing k]

abbrev homogeneousWeightGrading : ℕ → Submodule k
    (AddMonoidAlgebra k (homogeneousWeightMonoid a)) :=
  AddMonoidAlgebra.gradeBy k (homogeneousWeightDegree a)

def homogeneousWeightCharacter (i : ι) :
    AddMonoidAlgebra k (homogeneousWeightMonoid a) :=
  single (homogeneousWeight a i) 1

theorem homogeneousWeightCharacter_homogeneous (i : ι) :
    homogeneousWeightCharacter a k i∈homogeneousWeightGrading a k 1 :=
  AddMonoidAlgebra.single_mem_gradeBy _ _ _

def dehomogeneousWeightMap (j : ι) :
    AddMonoidAlgebra k (homogeneousWeightMonoid a) →ₐ[k] AddMonoidAlgebra k M :=
  AddMonoidAlgebra.mapDomainAlgHom k k (homogeneousWeightDifference a j)

@[simp] theorem dehomogeneousWeightMap_single (j : ι)
    (p : homogeneousWeightMonoid a) (r : k) :
    dehomogeneousWeightMap a k j (single p r)=
      single (homogeneousWeightDifference a j p) r := by
  simp [dehomogeneousWeightMap]

@[simp] theorem dehomogeneousWeightMap_self (j : ι) :
    dehomogeneousWeightMap a k j (homogeneousWeightCharacter a k j)=1 := by
  simp [homogeneousWeightCharacter,AddMonoidAlgebra.one_def]

/-- Dehomogenization is injective on each individual homogeneous grade.
This is the injectivity needed for degree-zero localization; the map on
the entire homogeneous ring is intentionally not asserted injective. -/
theorem dehomogeneousWeightMap_eq_zero_iff {j : ι} {d : ℕ}
    {f : AddMonoidAlgebra k (homogeneousWeightMonoid a)}
    (hf : f∈homogeneousWeightGrading a k d) :
    dehomogeneousWeightMap a k j f=0 ↔ f=0 := by
  constructor
  · intro h
    apply AddMonoidAlgebra.coeff_injective
    ext p
    by_cases hp : homogeneousWeightDegree a p=d
    · have hcoef := congrArg (fun g : AddMonoidAlgebra k M =>
          g.coeff (homogeneousWeightDifference a j p)) h
      change f.coeff.mapDomain (homogeneousWeightDifference a j)
          (homogeneousWeightDifference a j p)=0 at hcoef
      rw [Finsupp.mapDomain_apply' {q | homogeneousWeightDegree a q=d}
        f.coeff hf (homogeneousWeightDifference_injOn_degree a j d) hp] at hcoef
      exact hcoef
    · have : f.coeff p=0 := by
        by_contra hne
        exact hp (hf p (Finsupp.mem_support_iff.mpr hne))
      simpa using this
  · intro h
    simp [h]

abbrev homogeneousWeightChart (j : ι) :=
  HomogeneousLocalization.Away (homogeneousWeightGrading a k)
    (homogeneousWeightCharacter a k j)

def homogeneousWeightZeroMap : k →+* homogeneousWeightGrading a k 0 where
  toFun r := ⟨single 0 r,AddMonoidAlgebra.single_mem_gradeBy _ _ _⟩
  map_zero' := by ext; simp
  map_one' := by apply Subtype.ext; exact AddMonoidAlgebra.one_def.symm
  map_add' r s := by ext; simp
  map_mul' r s := by ext; simp

instance homogeneousWeightChartAlgebra (j : ι) : Algebra k (homogeneousWeightChart a k j) :=
  ((HomogeneousLocalization.fromZeroRingHom (homogeneousWeightGrading a k)
    (Submonoid.powers (homogeneousWeightCharacter a k j))).comp
      (homogeneousWeightZeroMap a k)).toAlgebra

def dehomogeneousChartMap (j : ι) :
    homogeneousWeightChart a k j →ₐ[k] AddMonoidAlgebra k M where
  toRingHom :=
    (Localization.awayLift (dehomogeneousWeightMap a k j).toRingHom
      (homogeneousWeightCharacter a k j)
      (by simpa using (isUnit_one : IsUnit (1 : AddMonoidAlgebra k M)))).comp
        (algebraMap (homogeneousWeightChart a k j)
          (Localization.Away (homogeneousWeightCharacter a k j)))
  commutes' r := by
    change Localization.awayLift (dehomogeneousWeightMap a k j).toRingHom
      (homogeneousWeightCharacter a k j)
      (by simpa using (isUnit_one : IsUnit (1 : AddMonoidAlgebra k M)))
      (Localization.mk (single 0 r) ⟨1,0,by simp⟩)=algebraMap k _ r
    simpa using Localization.awayLift_mk
      (dehomogeneousWeightMap a k j).toRingHom
      (homogeneousWeightCharacter a k j) (single 0 r) 1
      (by simp) 0

theorem dehomogeneousChartMap_mk (j : ι) (d : ℕ)
    (f : AddMonoidAlgebra k (homogeneousWeightMonoid a))
    (hf : f∈homogeneousWeightGrading a k (d • (1 : ℕ))) :
    dehomogeneousChartMap a k j
      (HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter_homogeneous a k j) d f hf)=
      dehomogeneousWeightMap a k j f := by
  change Localization.awayLift (dehomogeneousWeightMap a k j).toRingHom
    (homogeneousWeightCharacter a k j)
    (by simpa using (isUnit_one : IsUnit (1 : AddMonoidAlgebra k M)))
    (Localization.mk f ⟨homogeneousWeightCharacter a k j ^ d,d,rfl⟩)=_
  simpa using Localization.awayLift_mk
    (dehomogeneousWeightMap a k j).toRingHom
    (homogeneousWeightCharacter a k j) f 1 (by simp) d

theorem dehomogeneousChartMap_injective (j : ι) :
    Function.Injective (dehomogeneousChartMap a k j) := by
  apply (RingHom.injective_iff_ker_eq_bot (dehomogeneousChartMap a k j).toRingHom).mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨d,f,hf,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousWeightGrading a k) (homogeneousWeightCharacter_homogeneous a k j) x
  change dehomogeneousChartMap a k j _=0 at hx
  rw [dehomogeneousChartMap_mk] at hx
  have hf0 : f=0 := (dehomogeneousWeightMap_eq_zero_iff a k hf).mp hx
  subst f
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk,Localization.mk_zero]

theorem dehomogeneousWeightMap_mem_chart (j : ι)
    (f : AddMonoidAlgebra k (homogeneousWeightMonoid a)) :
    dehomogeneousWeightMap a k j f∈monoidChartAlgebra k (differenceWeightMonoid a j) := by
  induction f using AddMonoidAlgebra.induction_on with
  | of p =>
      change dehomogeneousWeightMap a k j (single p 1)∈_
      rw [dehomogeneousWeightMap_single]
      apply (mem_monoidChartAlgebra k _ _).mpr
      intro m hm
      have hm' : m=homogeneousWeightDifference a j p :=
        Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
      simpa [hm'] using homogeneousWeightDifference_mem a j p
  | add f g hf hg =>
      rw [map_add]
      exact (monoidChartAlgebra k _).add_mem hf hg
  | smul r f hf =>
      rw [map_smul]
      exact (monoidChartAlgebra k _).smul_mem hf r

theorem dehomogeneousChartMap_range (j : ι) :
    (dehomogeneousChartMap a k j).range=
      monoidChartAlgebra k (differenceWeightMonoid a j) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    obtain ⟨d,f,hf,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (homogeneousWeightGrading a k) (homogeneousWeightCharacter_homogeneous a k j) x
    change dehomogeneousChartMap a k j
      (HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter_homogeneous a k j) d f hf)∈_
    rw [dehomogeneousChartMap_mk]
    exact dehomogeneousWeightMap_mem_chart a k j f
  · rw [differenceWeightMonoid,monoidChartAlgebra_closure]
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
    refine ⟨HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter_homogeneous a k j) 1
      (homogeneousWeightCharacter a k i) (by
        simpa using homogeneousWeightCharacter_homogeneous a k i),?_⟩
    change dehomogeneousChartMap a k j
      (HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter_homogeneous a k j) 1
        (homogeneousWeightCharacter a k i) (by
          simpa using homogeneousWeightCharacter_homogeneous a k i)) = single (a i-a j) 1
    rw [dehomogeneousChartMap_mk]
    simp only [homogeneousWeightCharacter,dehomogeneousWeightMap_single,
      homogeneousWeightDifference_generator]

/-- The actual degree-zero localization is the actual difference-character
subalgebra of the character ring. -/
def homogeneousWeightChartEquiv (j : ι) :
    homogeneousWeightChart a k j ≃ₐ[k]
      monoidChartAlgebra k (differenceWeightMonoid a j) :=
  (AlgEquiv.ofInjective (dehomogeneousChartMap a k j)
    (dehomogeneousChartMap_injective a k j)).trans
      (Subalgebra.equivOfEq _ _ (dehomogeneousChartMap_range a k j))

@[simp] theorem homogeneousWeightChartEquiv_character_ratio (j i : ι) :
    (homogeneousWeightChartEquiv a k j
      (HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter_homogeneous a k j) 1
        (homogeneousWeightCharacter a k i) (by
          simpa using homogeneousWeightCharacter_homogeneous a k i)) :
        AddMonoidAlgebra k M)=single (a i-a j) 1 := by
  change dehomogeneousChartMap a k j
    (HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter_homogeneous a k j) 1
      (homogeneousWeightCharacter a k i) _) = _
  rw [dehomogeneousChartMap_mk]
  simp only [homogeneousWeightCharacter,dehomogeneousWeightMap_single,
    homogeneousWeightDifference_generator]

/-- The actual projective scheme of the homogeneous character algebra. -/
def monomialProjectiveScheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Proj (homogeneousWeightGrading a k)

/-- The canonical affine open at a homogeneous coordinate, identified
with the literal difference-character algebra. -/
def monomialProjectiveChartIso (j : ι) :
    (AlgebraicGeometry.Proj.basicOpen (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter a k j)).toScheme ≅
      AlgebraicGeometry.Spec (CommRingCat.of
        (monoidChartAlgebra k (differenceWeightMonoid a j))) :=
  (AlgebraicGeometry.Proj.basicOpenIsoSpec (homogeneousWeightGrading a k)
    (homogeneousWeightCharacter a k j)
    (homogeneousWeightCharacter_homogeneous a k j) (by decide)).trans
      (AlgebraicGeometry.Scheme.Spec.mapIso
        (homogeneousWeightChartEquiv a k j).toRingEquiv.toCommRingCatIso.symm.op)

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.dehomogeneousChartMap_injective
#print axioms PaperVerification.ToricCharacters.homogeneousWeightChartEquiv
end Source_ToricHomogeneousMonoidCharts

section Source_ToricPointedMonoids




/-!
# Minimal generators of a pointed affine semigroup

For a pointed submonoid of an abelian group, every member of a minimal
finite generating set is indecomposable. The proof uses only cancellation
and pointedness, without assuming saturation or normality. This is the
semigroup ingredient of the direct smoothness/cotangent argument.
-/


namespace PaperVerification.ToricCharacters

open scoped Classical

variable {M : Type*} [AddCommGroup M]

def IsPointedMonoid (S : AddSubmonoid M) : Prop :=
  ∀ x∈S, ∀ y∈S, x+y=0 → x=0 ∧ y=0

def IsMonoidAtom (S : AddSubmonoid M) (m : M) : Prop :=
  m∈S ∧ m≠0 ∧ ∀ x∈S, ∀ y∈S, x+y=m → x=0 ∨ y=0

theorem minimalGenerator_not_mem_eraseClosure (S : AddSubmonoid M)
    {G : Finset M} (hG : Minimal (fun T : Finset M => AddSubmonoid.closure (T : Set M)=S) G)
    {g : M} (hg : g∈G) : g∉AddSubmonoid.closure (G.erase g : Set M) := by
  intro hbad
  have heq : AddSubmonoid.closure (G.erase g : Set M)=S := by
    apply le_antisymm
    · rw [← hG.prop]
      exact AddSubmonoid.closure_mono (Finset.erase_subset g G)
    · rw [← hG.prop]
      apply AddSubmonoid.closure_le.mpr
      intro x hx
      by_cases h : x=g
      · simpa [h] using hbad
      · exact AddSubmonoid.subset_closure (Finset.mem_erase.mpr ⟨h,hx⟩)
  exact hG.not_prop_of_lt (Finset.erase_ssubset hg) heq

theorem minimalGenerator_ne_zero (S : AddSubmonoid M)
    {G : Finset M} (hG : Minimal (fun T : Finset M => AddSubmonoid.closure (T : Set M)=S) G)
    {g : M} (hg : g∈G) : g≠0 := by
  intro hz
  apply minimalGenerator_not_mem_eraseClosure S hG hg
  rw [hz]
  exact AddSubmonoid.zero_mem _

/-- Every generated element either avoids one selected generator, or
contains that generator plus another semigroup element. -/
theorem mem_closure_erase_or_add (S : AddSubmonoid M)
    (G : Finset M) (hG : AddSubmonoid.closure (G : Set M)=S)
    (g : M) {x : M} (hx : x∈S) :
    x∈AddSubmonoid.closure (G.erase g : Set M) ∨ ∃ z∈S,x=g+z := by
  rw [← hG] at hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      by_cases h : x=g
      · exact Or.inr ⟨0,S.zero_mem,by simpa [h]⟩
      · exact Or.inl (AddSubmonoid.subset_closure (Finset.mem_erase.mpr ⟨h,hx⟩))
  | zero => exact Or.inl (AddSubmonoid.zero_mem _)
  | add x y hx hy ihx ihy =>
      have hxS : x∈S := hG ▸ hx
      have hyS : y∈S := hG ▸ hy
      rcases ihx with hx'|⟨z,hz,rfl⟩
      · rcases ihy with hy'|⟨z,hz,rfl⟩
        · exact Or.inl (AddSubmonoid.add_mem _ hx' hy')
        · exact Or.inr ⟨x+z,S.add_mem hxS hz,by abel⟩
      · exact Or.inr ⟨z+y,S.add_mem hz hyS,by abel⟩

theorem minimalGenerator_isAtom (S : AddSubmonoid M) (hS : IsPointedMonoid S)
    {G : Finset M} (hG : Minimal (fun T : Finset M => AddSubmonoid.closure (T : Set M)=S) G)
    {g : M} (hg : g∈G) : IsMonoidAtom S g := by
  refine ⟨hG.prop ▸ AddSubmonoid.subset_closure hg,
    minimalGenerator_ne_zero S hG hg, ?_⟩
  intro x hx y hy hxy
  by_contra h
  push_neg at h
  have hx' : x∈AddSubmonoid.closure (G.erase g : Set M) := by
    rcases mem_closure_erase_or_add S G hG.prop g hx with hx'|⟨z,hz,hxg⟩
    · exact hx'
    · have hzy : z+y=0 := by
        apply add_left_cancel (a := g)
        calc
          g+(z+y) = x+y := by rw [hxg]; abel
          _ = g+0 := by simpa using hxy
      exact (h.2 (hS z hz y hy hzy).2).elim
  have hy' : y∈AddSubmonoid.closure (G.erase g : Set M) := by
    rcases mem_closure_erase_or_add S G hG.prop g hy with hy'|⟨z,hz,hyg⟩
    · exact hy'
    · have hzx : z+x=0 := by
        apply add_left_cancel (a := g)
        calc
          g+(z+x) = x+y := by rw [hyg]; abel
          _ = g+0 := by simpa using hxy
      exact (h.1 (hS z hz x hx hzx).2).elim
  apply minimalGenerator_not_mem_eraseClosure S hG hg
  have hsum : x+y∈AddSubmonoid.closure (G.erase g : Set M) :=
    AddSubmonoid.add_mem _ hx' hy'
  simpa only [hxy] using hsum

theorem exists_finite_atom_generators (S : AddSubmonoid M)
    (hS : IsPointedMonoid S) (hfg : S.FG) :
    ∃ G : Finset M, AddSubmonoid.closure (G : Set M)=S ∧
      ∀ g∈G,IsMonoidAtom S g := by
  obtain ⟨G,hG⟩ := hfg.exists_minimal_closure_eq
  exact ⟨G,hG.prop,fun g hg => minimalGenerator_isAtom S hS hG hg⟩

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.exists_finite_atom_generators
end Source_ToricPointedMonoids

section Source_ToricProjectiveVertexMonoids




/-!
# Pointedness of actual monomial vertex charts

At an actual vertex of the convex hull of the weights, strict separation
gives a nonnegative functional on all weight differences, vanishing only
at zero. Additive closure preserves this property, so the corresponding
actual affine Proj chart has a pointed exponent monoid.
-/


namespace PaperVerification.ToricCharacters

open PaperVerification.ToricGeometry PaperVerification.ToricVertexCone
open scoped Classical

theorem nonnegative_strict_on_closure {M : Type*} [AddCommGroup M]
    (S : Set M) (f : M →+ ℝ)
    (hS : ∀ x∈S,0≤f x ∧ (f x=0 → x=0)) :
    ∀ x∈AddSubmonoid.closure S,0≤f x ∧ (f x=0 → x=0) := by
  intro x hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add]
      refine ⟨add_nonneg ihx.1 ihy.1,?_⟩
      intro h
      have hx0 : f x=0 := by linarith [ihy.1]
      have hy0 : f y=0 := by linarith [ihx.1]
      rw [ihx.2 hx0,ihy.2 hy0,zero_add]

theorem pointed_closure_of_positive_functional {M : Type*} [AddCommGroup M]
    (S : Set M) (f : M →+ ℝ)
    (hS : ∀ x∈S,0≤f x ∧ (f x=0 → x=0)) :
    IsPointedMonoid (AddSubmonoid.closure S) := by
  intro x hx y hy hxy
  have hx' := nonnegative_strict_on_closure S f hS x hx
  have hy' := nonnegative_strict_on_closure S f hS y hy
  have he : f x+f y=0 := by rw [← map_add,hxy,map_zero]
  exact ⟨hx'.2 (by linarith),hy'.2 (by linarith)⟩

/-- Every actual vertex weight gives a pointed difference semigroup,
including a one-point hull in dimension zero or in a proper subspace. -/
theorem differenceWeightMonoid_pointed_at_vertex {ι : Type*} [Fintype ι]
    {n : ℕ} (a : ι → Lattice n) (j : ι)
    (hj : embed n (a j)∈
      (convexHull ℝ (Set.range (fun i=>embed n (a i)))).extremePoints ℝ) :
    IsPointedMonoid (differenceWeightMonoid a j) := by
  let s : Finset (Ambient n) := Finset.univ.image (fun i=>embed n (a i))
  have hj' : embed n (a j)∈(convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa [s] using hj
  obtain ⟨h,hh⟩ := exists_strict_vertex_functional s hj'
  let f : Lattice n →+ ℝ := h.toLinearMap.toAddMonoidHom.comp (embed n)
  apply pointed_closure_of_positive_functional _ f
  rintro x ⟨i,rfl⟩
  by_cases he : a i=a j
  · simp [he,f]
  · have her : embed n (a i)≠embed n (a j) := (embed_injective n).ne he
    have hpos : 0<f (a i-a j) := by
      simpa [f,map_sub] using hh (embed n (a i))
        (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩) her
    exact ⟨hpos.le,fun hz=>(hpos.ne' hz).elim⟩

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.differenceWeightMonoid_pointed_at_vertex
end Source_ToricProjectiveVertexMonoids

section Source_ToricRationalFeasibility




/-!
# Rational solutions of finite rational weak linear systems

Fourier--Motzkin elimination is proved over an arbitrary ordered field.
For a system whose coefficients are rational, the same finite eliminated
system works over the rationals and over the reals. Induction on the
number of variables therefore supplies an actual rational solution to
every nonempty real rational polyhedron. Boundary solutions are included;
no strict-feasibility or full-dimensionality assumption is used.
-/


namespace PaperVerification.ToricRationalGeometry

open scoped BigOperators Classical

theorem exists_linear_inequality_variable_iff {K ι : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]
    (a b : ι → K) :
    (∃ t : K,∀ i,0≤a i*t+b i) ↔
      (∀ i,a i=0 → 0≤b i) ∧
      (∀ i j,0<a i → a j<0 → -b i/a i≤-b j/a j) := by
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨fun i hi => by simpa [hi] using ht i,?_⟩
    intro i j hi hj
    have hlo : -b i/a i≤t := (div_le_iff₀ hi).mpr (by nlinarith [ht i])
    have hup : t≤-b j/a j := (le_div_iff_of_neg hj).mpr (by nlinarith [ht j])
    exact hlo.trans hup
  · rintro ⟨hz,hpair⟩
    let L : Finset ι := Finset.univ.filter (fun i => 0<a i)
    let U : Finset ι := Finset.univ.filter (fun i => a i<0)
    have hrow (t : K) (hlo : ∀ i,0<a i → -b i/a i≤t)
        (hup : ∀ i,a i<0 → t≤-b i/a i) : ∀ i,0≤a i*t+b i := by
      intro i
      rcases lt_trichotomy (a i) 0 with hi|hi|hi
      · have := (le_div_iff_of_neg hi).mp (hup i hi)
        nlinarith
      · simpa [hi] using hz i hi
      · have := (div_le_iff₀ hi).mp (hlo i hi)
        nlinarith
    by_cases hL : L.Nonempty
    · obtain ⟨i,hi,hmax⟩ := L.exists_max_image (fun i => -b i/a i) hL
      have hi0 : 0<a i := (Finset.mem_filter.mp hi).2
      refine ⟨-b i/a i,hrow _ ?_ ?_⟩
      · intro j hj
        exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)
      · intro j hj
        exact hpair i j hi0 hj
    · by_cases hU : U.Nonempty
      · obtain ⟨j,hj,hmin⟩ := U.exists_min_image (fun i => -b i/a i) hU
        refine ⟨-b j/a j,hrow _ ?_ ?_⟩
        · intro i hi
          exact (hL ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩).elim
        · intro i hi
          exact hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩)
      · refine ⟨0,hrow _ ?_ ?_⟩
        · intro i hi
          exact (hL ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩).elim
        · intro i hi
          exact (hU ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩).elim

structure RationalAffineRow (n : ℕ) where
  constant : ℚ
  coefficient : Fin n → ℚ

namespace RationalAffineRow

variable {n : ℕ}

def eval {K : Type*} [Field K] [CharZero K] (r : RationalAffineRow n)
    (x : Fin n → K) : K :=
  (r.constant : K)+∑ i,(r.coefficient i : K)*x i

def zeroRow : RationalAffineRow n := ⟨0,fun _=>0⟩

def linearCombination (c d : ℚ) (r s : RationalAffineRow n) : RationalAffineRow n :=
  ⟨c*r.constant+d*s.constant,fun i=>c*r.coefficient i+d*s.coefficient i⟩

@[simp] theorem eval_zero {K : Type*} [Field K] [CharZero K] (x : Fin n → K) :
    (zeroRow : RationalAffineRow n).eval x=0 := by simp [eval,zeroRow]

@[simp] theorem eval_linearCombination {K : Type*} [Field K] [CharZero K]
    (c d : ℚ) (r s : RationalAffineRow n) (x : Fin n → K) :
    (linearCombination c d r s).eval x=(c : K)*r.eval x+(d : K)*s.eval x := by
  simp only [eval,linearCombination,Rat.cast_add,Rat.cast_mul,add_mul,
    Finset.sum_add_distrib,mul_add,mul_assoc,← Finset.mul_sum]
  ring

def zeroFirst (r : RationalAffineRow (n+1)) : RationalAffineRow n :=
  ⟨r.constant,fun i=>r.coefficient i.succ⟩

theorem eval_cons {K : Type*} [Field K] [CharZero K]
    (r : RationalAffineRow (n+1)) (t : K) (x : Fin n → K) :
    r.eval (Fin.cons t x)=(r.coefficient 0 : K)*t+r.zeroFirst.eval x := by
  simp [eval,zeroFirst,Fin.sum_univ_succ,add_assoc,add_comm,add_left_comm]

def eliminate {ι : Type*} (r : ι → RationalAffineRow (n+1)) :
    (ι ⊕ (ι × ι)) → RationalAffineRow n
  | Sum.inl i => if (r i).coefficient 0=0 then (r i).zeroFirst else zeroRow
  | Sum.inr (i,j) =>
      if 0<(r i).coefficient 0 ∧ (r j).coefficient 0<0 then
        linearCombination ((r i).coefficient 0)⁻¹ (-((r j).coefficient 0)⁻¹)
          (r i).zeroFirst (r j).zeroFirst
      else zeroRow

theorem eliminate_feasible_iff {K ι : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]
    (r : ι → RationalAffineRow (n+1)) (x : Fin n → K) :
    (∀ j,0≤(eliminate r j).eval x) ↔
      ∃ t : K,∀ i,0≤(r i).eval (Fin.cons t x) := by
  simp only [eval_cons]
  rw [exists_linear_inequality_variable_iff]
  constructor
  · intro hx
    refine ⟨?_,?_⟩
    · intro i hi
      have hiQ : (r i).coefficient 0=0 := by exact_mod_cast hi
      simpa [eliminate,hiQ] using hx (Sum.inl i)
    · intro i j hi hj
      have hiQ : 0<(r i).coefficient 0 := by exact_mod_cast hi
      have hjQ : (r j).coefficient 0<0 := by exact_mod_cast hj
      have h := hx (Sum.inr (i,j))
      have hijQ : 0<(r i).coefficient 0 ∧ (r j).coefficient 0<0 := ⟨hiQ,hjQ⟩
      simp only [eliminate,if_pos hijQ,eval_linearCombination,
        Rat.cast_inv,Rat.cast_neg] at h
      simpa [div_eq_mul_inv,mul_comm] using (neg_le_neg (sub_nonneg.mp
        (show 0≤((r i).coefficient 0 : K)⁻¹*(r i).zeroFirst.eval x-
          ((r j).coefficient 0 : K)⁻¹*(r j).zeroFirst.eval x by nlinarith)))
  · rintro ⟨hz,hpairs⟩ row
    rcases row with i|⟨i,j⟩
    · by_cases hi : (r i).coefficient 0=0
      · simpa [eliminate,hi] using hz i (by exact_mod_cast hi)
      · simp [eliminate,hi]
    · by_cases hij : 0<(r i).coefficient 0 ∧ (r j).coefficient 0<0
      · have h := hpairs i j (by exact_mod_cast hij.1) (by exact_mod_cast hij.2)
        simp only [eliminate,if_pos hij,eval_linearCombination,
          Rat.cast_inv,Rat.cast_neg]
        have h' : ((r j).coefficient 0 : K)⁻¹*(r j).zeroFirst.eval x≤
            ((r i).coefficient 0 : K)⁻¹*(r i).zeroFirst.eval x := by
          simpa [div_eq_mul_inv,mul_comm] using (neg_le_neg h)
        nlinarith
      · simp [eliminate,hij]

end RationalAffineRow

open RationalAffineRow

/-- Every real solution of finitely many rational weak affine
inequalities can be replaced by a rational solution. -/
theorem rational_feasible_of_real_feasible (n : ℕ) :
    ∀ {ι : Type*} [Fintype ι] (r : ι → RationalAffineRow n),
      (∃ x : Fin n → ℝ,∀ i,0≤(r i).eval x) →
        ∃ y : Fin n → ℚ,∀ i,0≤(r i).eval y := by
  induction n with
  | zero =>
      intro ι hι r h
      obtain ⟨x,hx⟩ := h
      refine ⟨fun i=>Fin.elim0 i,?_⟩
      intro i
      have hi : 0≤((r i).constant : ℝ) := by simpa [eval] using hx i
      simpa [eval] using (Rat.cast_nonneg (K := ℝ)).mp hi
  | succ n ih =>
      intro ι hι r h
      obtain ⟨x,hx⟩ := h
      have hreal : ∃ x' : Fin n → ℝ,∀ j,0≤(eliminate r j).eval x' := by
        refine ⟨Fin.tail x,(eliminate_feasible_iff r (Fin.tail x)).mpr ⟨x 0,?_⟩⟩
        simpa using hx
      obtain ⟨y,hy⟩ := ih (eliminate r) hreal
      obtain ⟨t,ht⟩ := (eliminate_feasible_iff r y).mp hy
      exact ⟨Fin.cons t y,ht⟩

/-- The same statement with an arbitrary finite variable index. -/
theorem rational_matrix_feasible_of_real_feasible {ι κ : Type*}
    [Fintype ι] [Fintype κ] (A : ι → κ → ℚ) (b : ι → ℚ)
    (h : ∃ x : κ → ℝ,∀ i,0≤(b i : ℝ)+∑ j,(A i j : ℝ)*x j) :
    ∃ y : κ → ℚ,∀ i,0≤b i+∑ j,A i j*y j := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let r : ι → RationalAffineRow (Fintype.card κ) :=
    fun i=>⟨b i,fun j=>A i (e j)⟩
  obtain ⟨x,hx⟩ := h
  have hreal : ∃ z : Fin (Fintype.card κ) → ℝ,∀ i,0≤(r i).eval z := by
    refine ⟨fun j=>x (e j),?_⟩
    intro i
    simpa [r,eval,← e.sum_comp] using hx i
  obtain ⟨y,hy⟩ := rational_feasible_of_real_feasible _ r hreal
  refine ⟨fun j=>y (e.symm j),?_⟩
  intro i
  simpa [r,eval,← e.sum_comp] using hy i

end PaperVerification.ToricRationalGeometry

#print axioms PaperVerification.ToricRationalGeometry.rational_matrix_feasible_of_real_feasible
end Source_ToricRationalFeasibility

section Source_ToricRationalConvexRelations




/-!
# Integral homogeneous relations from rational convex geometry

An integral point of the real convex hull of finitely many integral
points admits an integer homogeneous relation with those points and a
strictly positive total degree. This is derived from rational feasibility
and explicit denominator clearing. It applies on all faces, including
zero-dimensional hulls.
-/


namespace PaperVerification.ToricRationalGeometry

open PaperVerification.ToricGeometry
open scoped BigOperators Classical

theorem rational_weights_of_real_weights {κ : Type*} [Fintype κ] {n : ℕ}
    (v : κ → Fin n → ℚ) (m : Fin n → ℚ)
    (w : κ → ℝ) (hw0 : ∀ i,0≤w i) (hw1 : ∑ i,w i=1)
    (hwm : ∀ j,∑ i,w i*(v i j : ℝ)=(m j : ℝ)) :
    ∃ q : κ → ℚ,(∀ i,0≤q i) ∧ ∑ i,q i=1 ∧ ∀ j,∑ i,q i*v i j=m j := by
  let I := κ ⊕ ((Unit ⊕ Fin n) × Bool)
  let A : I → κ → ℚ := fun row i => match row with
    | Sum.inl j => if i=j then 1 else 0
    | Sum.inr (Sum.inl _,false) => 1
    | Sum.inr (Sum.inl _,true) => -1
    | Sum.inr (Sum.inr j,false) => v i j
    | Sum.inr (Sum.inr j,true) => -v i j
  let b : I → ℚ := fun row => match row with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _,false) => -1
    | Sum.inr (Sum.inl _,true) => 1
    | Sum.inr (Sum.inr j,false) => -m j
    | Sum.inr (Sum.inr j,true) => m j
  have hfeasible : ∃ x : κ → ℝ,∀ row,0≤(b row : ℝ)+∑ i,(A row i : ℝ)*x i := by
    refine ⟨w,?_⟩
    intro row
    rcases row with i|⟨tag,sign⟩
    · simpa [A,b,apply_ite,ite_mul] using hw0 i
    · rcases tag with u|j <;> cases sign
      · simp [A,b,hw1]
      · simp [A,b,hw1,Finset.sum_neg_distrib]
      · simp [A,b,mul_comm,hwm j]
      · simp [A,b,mul_comm,hwm j,Finset.sum_neg_distrib]
  obtain ⟨q,hq⟩ := rational_matrix_feasible_of_real_feasible A b hfeasible
  refine ⟨q,?_,?_,?_⟩
  · intro i
    simpa [A,b] using hq (Sum.inl i)
  · have hlo := hq (Sum.inr (Sum.inl (),false))
    have hup := hq (Sum.inr (Sum.inl (),true))
    simp only [A,b,one_mul,neg_one_mul,Finset.sum_neg_distrib] at hlo hup
    linarith
  · intro j
    have hlo := hq (Sum.inr (Sum.inr j,false))
    have hup := hq (Sum.inr (Sum.inr j,true))
    simp only [A,b,neg_mul,Finset.sum_neg_distrib] at hlo hup
    simpa [mul_comm] using le_antisymm (by linarith : ∑ i,v i j*q i≤m j)
      (by linarith : m j≤∑ i,v i j*q i)

/-- A common positive denominator gives nonnegative integer weights. -/
theorem clear_nonnegative_rational_denominators {κ : Type*} [Fintype κ]
    (q : κ → ℚ) (hq : ∀ i,0≤q i) :
    ∃ N : ℕ,0<N ∧ ∃ c : κ → ℕ,∀ i,(c i : ℚ)=(N : ℚ)*q i := by
  let N : ℕ := ∏ i,(q i).den
  have hN : 0<N := Finset.prod_pos (fun i hi => (q i).den_pos)
  let c : κ → ℕ := fun i => (q i).num.toNat*(N/(q i).den)
  refine ⟨N,hN,c,?_⟩
  intro i
  have hdiv : (q i).den∣N := Finset.dvd_prod_of_mem (fun i=>(q i).den)
    (Finset.mem_univ i)
  have hmul : (q i).den*(N/(q i).den)=N := Nat.mul_div_cancel' hdiv
  have hnum : 0≤(q i).num := Rat.num_nonneg.mpr (hq i)
  have hnumcast : ((q i).num.toNat : ℚ)=((q i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hNcast : (N : ℚ)=((q i).den : ℚ)*((N/(q i).den : ℕ) : ℚ) := by
    exact_mod_cast hmul.symm
  change (((q i).num.toNat*(N/(q i).den) : ℕ) : ℚ)=(N : ℚ)*q i
  rw [Nat.cast_mul,hnumcast]
  have hd : ((q i).den : ℚ)≠0 := by exact_mod_cast (q i).den_ne_zero
  calc
    ((q i).num : ℚ) * ((N/(q i).den : ℕ) : ℚ) =
        (N : ℚ) * (((q i).num : ℚ) / ((q i).den : ℚ)) := by
      rw [hNcast]
      field_simp
    _ = (N : ℚ) * q i := congrArg ((N : ℚ) * ·) (q i).num_div_den

theorem integral_relation_of_real_weights {κ : Type*} [Fintype κ] {n : ℕ}
    (v : κ → Lattice n) (m : Lattice n)
    (w : κ → ℝ) (hw0 : ∀ i,0≤w i) (hw1 : ∑ i,w i=1)
    (hwm : ∑ i,w i • embed n (v i)=embed n m) :
    ∃ N : ℕ,0<N ∧ ∃ c : κ → ℕ,(∑ i,c i=N) ∧ ∑ i,c i • v i=N • m := by
  let vQ : κ → Fin n → ℚ := fun i j=>(v i j : ℚ)
  let mQ : Fin n → ℚ := fun j=>(m j : ℚ)
  have hcoord (j : Fin n) : ∑ i,w i*(vQ i j : ℝ)=(mQ j : ℝ) := by
    have := congrFun hwm j
    simpa [vQ,mQ,embed,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using this
  obtain ⟨q,hq0,hq1,hqm⟩ := rational_weights_of_real_weights vQ mQ w hw0 hw1 hcoord
  obtain ⟨N,hN,c,hc⟩ := clear_nonnegative_rational_denominators q hq0
  refine ⟨N,hN,c,?_,?_⟩
  · have hsum : (∑ i,(c i : ℚ))=(N : ℚ) := by
      simp only [hc,← Finset.mul_sum,hq1,mul_one]
    exact_mod_cast hsum
  · ext j
    have hsum : ∑ i,(c i : ℚ)*(v i j : ℚ)=(N : ℚ)*(m j : ℚ) := by
      simp only [hc,mul_assoc,← Finset.mul_sum]
      exact congrArg ((N : ℚ)*·) (hqm j)
    simpa [Finset.sum_apply,Pi.smul_apply,nsmul_eq_mul] using
      (show ∑ i,(c i : ℤ)*v i j=(N : ℤ)*m j by exact_mod_cast hsum)

theorem integral_relation_of_mem_convexHull {n : ℕ} (V : Finset (Lattice n))
    (m : Lattice n) (hm : embed n m∈convexHull ℝ (embed n '' (V : Set (Lattice n)))) :
    ∃ N : ℕ,0<N ∧ ∃ c : V → ℕ,(∑ i,c i=N) ∧ ∑ i,c i • i.val=N • m := by
  have hm' : embed n m∈convexHull ℝ (V.image (embed n) : Set (Ambient n)) := by
    simpa using hm
  obtain ⟨w,hw0,hw1,hwm⟩ := Finset.mem_convexHull'.mp hm'
  have hsum : ∑ i : V,w (embed n i.val)=1 := by
    calc
      ∑ i : V,w (embed n i.val)=∑ i∈V,w (embed n i) := by
        simpa only [Finset.univ_eq_attach] using
          Finset.sum_attach V (fun i => w (embed n i))
      _ = 1 := by
        simpa only [Finset.sum_image (fun x hx y hy hxy => embed_injective n hxy)] using hw1
  have hvec : ∑ i : V,w (embed n i.val) • embed n i.val=embed n m := by
    calc
      ∑ i : V,w (embed n i.val) • embed n i.val=
          ∑ i∈V,w (embed n i) • embed n i := by
        simpa only [Finset.univ_eq_attach] using
          Finset.sum_attach V (fun i => w (embed n i) • embed n i)
      _ = embed n m := by
        simpa only [Finset.sum_image (fun x hx y hy hxy => embed_injective n hxy)] using hwm
  exact integral_relation_of_real_weights (fun i : V=>i.val) m
    (fun i=>w (embed n i.val))
    (fun i=>hw0 _ (Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩)) hsum hvec

theorem integral_relation_of_mem_convexHull_range {κ : Type*} [Fintype κ]
    {n : ℕ} (v : κ → Lattice n) (m : Lattice n)
    (hm : embed n m∈convexHull ℝ (Set.range (fun i=>embed n (v i)))) :
    ∃ N : ℕ,0<N ∧ ∃ c : κ → ℕ,(∑ i,c i=N) ∧ ∑ i,c i • v i=N • m := by
  rw [convexHull_range_eq_exists_affineCombination] at hm
  obtain ⟨s,w,hw0,hw1,hwm⟩ := hm
  let w' : κ → ℝ := fun i=>if i∈s then w i else 0
  have hw'0 (i : κ) : 0≤w' i := by
    by_cases hi : i∈s
    · simpa [w',hi] using hw0 i hi
    · simp [w',hi]
  have hw'1 : ∑ i,w' i=1 := by simpa [w'] using hw1
  have hvec : ∑ i,w' i • embed n (v i)=embed n m := by
    rw [Finset.affineCombination_eq_linear_combination s _ _ hw1] at hwm
    simpa [w',ite_smul] using hwm
  exact integral_relation_of_real_weights v m w' hw'0 hw'1 hvec

end PaperVerification.ToricRationalGeometry

#print axioms PaperVerification.ToricRationalGeometry.integral_relation_of_mem_convexHull
end Source_ToricRationalConvexRelations

section Source_ToricProjectiveVertexCover




/-!
# The actual monomial Proj is covered by its vertex charts

All homogeneous coordinate charts first give the usual Proj cover.
An integral homogeneous relation expresses a power of every coordinate
as a product of vertex coordinates. Hence each coordinate chart lies in
a vertex chart. The finite family of vertex charts therefore covers the
actual projective scheme, with no assumed orbit-face correspondence.
-/


namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricVertexCone
open PaperVerification.ToricRationalGeometry
open scoped BigOperators Classical

variable {ι M : Type*} [AddCommGroup M] (a : ι → M)
    (k : Type*) [CommRing k]

theorem homogeneousWeightCharacter_adjoin :
    Algebra.adjoin (homogeneousWeightGrading a k 0)
      (Set.range (homogeneousWeightCharacter a k))=⊤ := by
  let A := Algebra.adjoin (homogeneousWeightGrading a k 0)
    (Set.range (homogeneousWeightCharacter a k))
  have hchar (p : homogeneousWeightMonoid a) : single p (1 : k)∈A := by
    refine AddSubmonoid.closure_induction
      (motive := fun x hx => single (⟨x,hx⟩ : homogeneousWeightMonoid a) (1 : k)∈A)
      ?_ ?_ ?_ p.property
    · intro x hx
      obtain ⟨i,rfl⟩ := hx
      exact Algebra.subset_adjoin (Set.mem_range_self i)
    · change (1 : AddMonoidAlgebra k (homogeneousWeightMonoid a))∈A
      exact A.one_mem
    · intro x y hx hy ihx ihy
      change single ((⟨x,hx⟩ : homogeneousWeightMonoid a)+⟨y,hy⟩) (1 : k)∈A
      simpa only [single_mul_single,mul_one] using A.mul_mem ihx ihy
  apply top_unique
  intro f hf
  clear hf
  induction f using AddMonoidAlgebra.induction_on with
  | of p => exact hchar p
  | add f g hf hg => exact A.add_mem hf hg
  | smul r f hf =>
      have hr : algebraMap k (AddMonoidAlgebra k (homogeneousWeightMonoid a)) r∈A := by
        exact A.algebraMap_mem (homogeneousWeightZeroMap a k r)
      rw [Algebra.smul_def]
      exact A.mul_mem hr hf

theorem monomialProjective_coordinate_cover :
    (⨆ i,Proj.basicOpen (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter a k i))=⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _
    (fun i=>⟨1,homogeneousWeightCharacter_homogeneous a k i⟩)
    (homogeneousWeightCharacter_adjoin a k)

theorem homogeneousWeightCharacter_relation {κ : Type*} [Fintype κ]
    (j : ι) (v : κ → ι) (N : ℕ) (c : κ → ℕ)
    (hsum : ∑ i,c i=N) (hweight : ∑ i,c i • a (v i)=N • a j) :
    homogeneousWeightCharacter a k j ^ N=
      ∏ i,homogeneousWeightCharacter a k (v i) ^ c i := by
  have he : N • homogeneousWeight a j=∑ i,c i • homogeneousWeight a (v i) := by
    apply Subtype.ext
    apply Prod.ext
    · simpa [homogeneousWeight,Prod.fst_sum] using hsum.symm
    · simpa [homogeneousWeight,Prod.snd_sum] using hweight.symm
  simp [homogeneousWeightCharacter,single_pow,prod_single,he]

theorem basicOpen_le_vertex_cover_of_relation {κ : Type*} [Fintype κ]
    (j : ι) (v : κ → ι) (N : ℕ) (hN : 0<N) (c : κ → ℕ)
    (hsum : ∑ i,c i=N) (hweight : ∑ i,c i • a (v i)=N • a j) :
    Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j)≤
      ⨆ i,Proj.basicOpen (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter a k (v i)) := by
  have hcpos : ∃ i,0<c i := by
    by_contra h
    push_neg at h
    have hzero : ∀ i,c i=0 := fun i=>Nat.eq_zero_of_le_zero (h i)
    have : N=0 := by simpa [hzero] using hsum.symm
    omega
  obtain ⟨i,hi⟩ := hcpos
  have hdiv : homogeneousWeightCharacter a k (v i)∣homogeneousWeightCharacter a k j ^ N := by
    rw [homogeneousWeightCharacter_relation a k j v N c hsum hweight]
    exact (dvd_pow_self _ (ne_of_gt hi)).trans
      (Finset.dvd_prod_of_mem (fun i=>homogeneousWeightCharacter a k (v i)^c i)
        (Finset.mem_univ i))
  have h := Proj.basicOpen_mono (homogeneousWeightGrading a k) _ _ hdiv
  rw [Proj.basicOpen_pow _ _ N hN] at h
  exact h.trans (le_iSup_of_le i le_rfl)

variable [Fintype ι] {n : ℕ}

def vertexWeightIndices (a : ι → Lattice n) : Finset ι :=
  Finset.univ.filter (fun i=>embed n (a i)∈
    (convexHull ℝ (Set.range (fun j=>embed n (a j)))).extremePoints ℝ)

theorem range_vertexWeightIndices (a : ι → Lattice n) :
    Set.range (fun i : vertexWeightIndices a=>embed n (a i.val))=
      (convexHull ℝ (Set.range (fun i=>embed n (a i)))).extremePoints ℝ := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact (Finset.mem_filter.mp i.property).2
  · intro hx
    obtain ⟨i,rfl⟩ := extremePoints_convexHull_subset hx
    exact ⟨⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩⟩,rfl⟩

theorem hull_vertexWeightIndices (a : ι → Lattice n) :
    convexHull ℝ (Set.range (fun i : vertexWeightIndices a=>embed n (a i.val)))=
      convexHull ℝ (Set.range (fun i=>embed n (a i))) := by
  rw [range_vertexWeightIndices]
  simpa using finite_hull_eq_hull_extremePoints
    (Finset.univ.image (fun i=>embed n (a i)))

/-- Actual vertex-coordinate basic opens cover the actual Proj of the
homogeneous monomial algebra. -/
theorem monomialProjective_vertex_cover (a : ι → Lattice n) :
    (⨆ i : vertexWeightIndices a,Proj.basicOpen (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter a k i.val))=⊤ := by
  apply top_le_iff.mp
  rw [← monomialProjective_coordinate_cover a k]
  apply iSup_le
  intro j
  have hj : embed n (a j)∈convexHull ℝ
      (Set.range (fun i : vertexWeightIndices a=>embed n (a i.val))) := by
    rw [hull_vertexWeightIndices]
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  obtain ⟨N,hN,c,hsum,hweight⟩ := integral_relation_of_mem_convexHull_range
    (fun i : vertexWeightIndices a=>a i.val) (a j) hj
  exact basicOpen_le_vertex_cover_of_relation a k j Subtype.val N hN c hsum hweight

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monomialProjective_vertex_cover
end Source_ToricProjectiveVertexCover

section Source_ToricFanSchemeChartIso




/-!
# An actual scheme isomorphism from compatible affine fan charts

The hypotheses below concern literal open immersions of the already
constructed cone schemes. Agreement is tested on the actual dense torus,
and overlap ranges are required to equal the actual common-face chart.
The resulting map is constructed by the genuine fan colimit. Its point
injectivity, open-immersion property, and surjectivity are proved, giving
an actual scheme isomorphism.
-/


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem coneChart_zeroFace_isDominant (s : «Σ».ConeIndex) :
    IsDominant (coneChartFaceMap k (Finset.empty_subset s.val)) := by
  refine ⟨?_⟩
  intro x
  have hg : «Σ».fanChartGenericPoint k s∈
      Set.range (coneChartFaceMap k (Finset.empty_subset s.val)) := by
    exact ⟨«Σ».fanChartGenericPoint k «Σ».zeroConeIndex,
      «Σ».fanChartGenericPoint_faceMap k
        (s := «Σ».zeroConeIndex) (t := s) (Finset.empty_subset s.val)⟩
  have hsub : ({«Σ».fanChartGenericPoint k s} : Set (coneChart k s.val))⊆
      Set.range (coneChartFaceMap k (Finset.empty_subset s.val)) :=
    Set.singleton_subset_iff.mpr hg
  have hcl := closure_mono hsub
  rw [(«Σ».fanChartGenericPoint_isGenericPoint k s).def] at hcl
  exact hcl (Set.mem_univ x)

section ChartFamily

variable {J : Type*} (s : J → Finset (Lattice n)) (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    {Y : Scheme.{u}} [Y.IsSeparated]
    (f : ∀ j,coneChart k (s j)⟶Y)
    [∀ j,IsOpenImmersion (f j)]
    (hT : ∀ i j,
      coneChartFaceMap k (Finset.empty_subset (s i))≫f i=
        coneChartFaceMap k (Finset.empty_subset (s j))≫f j)

include hs hT in
theorem chartFamily_commonFace_agree (i j : J) :
    coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i)≫f i=
      coneChartFaceMap k (Finset.inter_subset_right : s i∩s j⊆s j)≫f j := by
  let t : «Σ».ConeIndex := ⟨s i∩s j,«Σ».downward (s i) (hs i) _ Finset.inter_subset_left⟩
  letI := «Σ».coneChart_isIntegral k t
  letI := «Σ».coneChart_zeroFace_isDominant k t
  apply ext_of_isDominant (coneChartFaceMap k (Finset.empty_subset t.val))
  simpa only [← Category.assoc,coneChartFaceMap_comp] using hT i j

def chartFamilyChoice (t : «Σ».ConeIndex) : J :=
  Classical.choose (hcover t.val t.property)

theorem chartFamilyChoice_subset (t : «Σ».ConeIndex) :
    t.val⊆s («Σ».chartFamilyChoice s hcover t) :=
  Classical.choose_spec (hcover t.val t.property)

def chartFamilyMap (t : «Σ».ConeIndex) : coneChart k t.val⟶Y :=
  coneChartFaceMap k («Σ».chartFamilyChoice_subset s hcover t)≫
    f («Σ».chartFamilyChoice s hcover t)

include hs hT in
theorem chartFamilyMap_torus (t : «Σ».ConeIndex) (j : J) :
    coneChartFaceMap k (Finset.empty_subset t.val)≫
      «Σ».chartFamilyMap k s hcover f t=
        coneChartFaceMap k (Finset.empty_subset (s j))≫f j := by
  simpa only [chartFamilyMap,← Category.assoc,coneChartFaceMap_comp] using
    hT («Σ».chartFamilyChoice s hcover t) j

include hs hT in
theorem chartFamilyMap_naturality {t q : «Σ».ConeIndex} (htq : t.val⊆q.val) :
    coneChartFaceMap k htq≫«Σ».chartFamilyMap k s hcover f q=
      «Σ».chartFamilyMap k s hcover f t := by
  letI := «Σ».coneChart_isIntegral k t
  letI := «Σ».coneChart_zeroFace_isDominant k t
  apply ext_of_isDominant (coneChartFaceMap k (Finset.empty_subset t.val))
  rw [← Category.assoc,coneChartFaceMap_comp,
    «Σ».chartFamilyMap_torus k s hs hcover f hT q («Σ».chartFamilyChoice s hcover t)]
  unfold chartFamilyMap
  rw [← Category.assoc,coneChartFaceMap_comp]

def chartFamilyCocone : Cocone («Σ».coneDiagram k) where
  pt := Y
  «ι» := {
    app := «Σ».chartFamilyMap k s hcover f
    naturality := by
      intro t q h
      change coneChartFaceMap k (leOfHom h)≫«Σ».chartFamilyMap k s hcover f q=
        «Σ».chartFamilyMap k s hcover f t≫𝟙 Y
      exact («Σ».chartFamilyMap_naturality k s hs hcover f hT (leOfHom h)).trans
        (Category.comp_id _).symm }

def chartFamilyDesc : «Σ».fanScheme k⟶Y :=
  colimit.desc («Σ».coneDiagram k) («Σ».chartFamilyCocone k s hs hcover f hT)

@[reassoc] theorem fanChartMap_chartFamilyDesc (t : «Σ».ConeIndex) :
    «Σ».fanChartMap k t≫«Σ».chartFamilyDesc k s hs hcover f hT=
      «Σ».chartFamilyMap k s hcover f t :=
  colimit.ι_desc («Σ».chartFamilyCocone k s hs hcover f hT) t

@[reassoc] theorem familyChart_chartFamilyDesc (j : J) :
    «Σ».fanChartMap k ⟨s j,hs j⟩≫«Σ».chartFamilyDesc k s hs hcover f hT=f j := by
  rw [«Σ».fanChartMap_chartFamilyDesc]
  let t : «Σ».ConeIndex := ⟨s j,hs j⟩
  letI := «Σ».coneChart_isIntegral k t
  letI := «Σ».coneChart_zeroFace_isDominant k t
  apply ext_of_isDominant (coneChartFaceMap k (Finset.empty_subset t.val))
  exact «Σ».chartFamilyMap_torus k s hs hcover f hT t j

include hcover in
theorem familyCharts_cover_fanScheme (x : «Σ».fanScheme k) :
    ∃ j y,«Σ».fanChartMap k ⟨s j,hs j⟩ y=x := by
  obtain ⟨t,y,rfl⟩ := «Σ».fanChartMap_jointly_surjective k x
  let j := «Σ».chartFamilyChoice s hcover t
  let ht := «Σ».chartFamilyChoice_subset s hcover t
  refine ⟨j,coneChartFaceMap k ht y,?_⟩
  exact congrArg (fun g : coneChart k t.val⟶«Σ».fanScheme k => g y)
    («Σ».fanChartMap_naturality k (s := t) (t := ⟨s j,hs j⟩) ht)

theorem chartFamilyDesc_injective
    (hoverlap : ∀ i j,
      Set.range (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i))=
        (f i) ⁻¹' Set.range (f j)) :
    Function.Injective («Σ».chartFamilyDesc k s hs hcover f hT) := by
  intro x y hxy
  obtain ⟨i,xi,rfl⟩ := «Σ».familyCharts_cover_fanScheme k s hs hcover x
  obtain ⟨j,yj,rfl⟩ := «Σ».familyCharts_cover_fanScheme k s hs hcover y
  have h : f i xi=f j yj := by
    simpa only [← Scheme.Hom.comp_apply,«Σ».familyChart_chartFamilyDesc] using hxy
  have hxi : xi∈Set.range
      (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i)) := by
    rw [hoverlap]
    exact ⟨yj,h.symm⟩
  obtain ⟨z,hzi⟩ := hxi
  have hzj : coneChartFaceMap k (Finset.inter_subset_right : s i∩s j⊆s j) z=yj := by
    apply (f j).isOpenEmbedding.injective
    calc
      f j (coneChartFaceMap k (Finset.inter_subset_right : s i∩s j⊆s j) z)=
          f i (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i) z) :=
        congrArg (fun g=>g z) («Σ».chartFamily_commonFace_agree k s hs f hT i j).symm
      _ = f j yj := by rw [hzi,h]
  exact («Σ».fanChartMap_eq_iff k ⟨s i,hs i⟩ ⟨s j,hs j⟩ xi yj).mpr ⟨z,hzi,hzj⟩

theorem chartFamilyDesc_isOpenImmersion
    (hoverlap : ∀ i j,
      Set.range (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i))=
        (f i) ⁻¹' Set.range (f j)) :
    IsOpenImmersion («Σ».chartFamilyDesc k s hs hcover f hT) := by
  apply IsOpenImmersion.of_openCover_source _ («Σ».fanSchemeOpenCover k)
    («Σ».chartFamilyDesc_injective k s hs hcover f hT hoverlap)
  intro t
  change IsOpenImmersion («Σ».fanChartMap k t≫_)
  rw [«Σ».fanChartMap_chartFamilyDesc]
  unfold chartFamilyMap
  letI := «Σ».coneChartFaceMap_isOpenImmersion k _ _
    (hs («Σ».chartFamilyChoice s hcover t)) («Σ».chartFamilyChoice_subset s hcover t)
  infer_instance

theorem chartFamilyDesc_surjective (hY : ∀ y : Y,∃ j x,f j x=y) :
    Function.Surjective («Σ».chartFamilyDesc k s hs hcover f hT) := by
  intro y
  obtain ⟨j,x,rfl⟩ := hY y
  refine ⟨«Σ».fanChartMap k ⟨s j,hs j⟩ x,?_⟩
  rw [← Scheme.Hom.comp_apply,«Σ».familyChart_chartFamilyDesc]

/-- The actual fan colimit is isomorphic to the separated target once
its literal chart maps have the proved common-face overlaps and cover. -/
def chartFamilyIso
    (hoverlap : ∀ i j,
      Set.range (coneChartFaceMap k (Finset.inter_subset_left : s i∩s j⊆s i))=
        (f i) ⁻¹' Set.range (f j))
    (hY : ∀ y : Y,∃ j x,f j x=y) : «Σ».fanScheme k≅Y := by
  let F := «Σ».chartFamilyDesc k s hs hcover f hT
  letI : IsOpenImmersion F := «Σ».chartFamilyDesc_isOpenImmersion k s hs hcover f hT hoverlap
  letI : Surjective F := ⟨«Σ».chartFamilyDesc_surjective k s hs hcover f hT hY⟩
  letI : IsIso F := (isIso_iff_isOpenImmersion_and_surjective F).mpr ⟨inferInstance,inferInstance⟩
  exact asIso F

end ChartFamily

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.chartFamilyIso
end Source_ToricFanSchemeChartIso

section Source_ToricProjectiveRatios




/-!
# Actual projective chart maps from homogeneous ratios

These maps use Mathlib's degree-zero homogeneous localization and its
actual affine open immersion into Proj. Homogeneous scaling cancels in
every fraction, so changing a local frame does not change the induced
projective morphism.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped Classical

section UnitEvaluation

variable {σ A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ→σ) [GradedRing 𝒜]

/-- Homogeneous ratios may be evaluated in any ring when the selected
denominator is a unit. This is the actual affine-chart coordinate map. -/
def unitHomogeneousAwayEvaluation (F : A→+*B) (t : A) (ht : IsUnit (F t)) :
    Away 𝒜 t→+*B :=
  (Localization.awayLift F t ht).comp
    (algebraMap (Away 𝒜 t) (Localization.Away t))

theorem unitHomogeneousAwayEvaluation_mk_of_eq_one (F : A→+*B)
    {t : A} (ht : F t=1) {d : ℕ} (htd : t∈𝒜 d)
    (m : ℕ) (p : A) (hp : p∈𝒜 (m • d)) :
    unitHomogeneousAwayEvaluation 𝒜 F t (ht ▸ isUnit_one)
        (Away.mk 𝒜 htd m p hp)=F p := by
  change Localization.awayLift F t (ht ▸ isUnit_one)
    (Localization.mk p ⟨t^m,m,rfl⟩)=_
  rw [Localization.awayLift_mk F t p 1 (by simpa only [mul_one] using ht)]
  simp

theorem unitHomogeneousAwayEvaluation_map (F : A→+*B) (G : B→+*D)
    (t : A) (ht : IsUnit (F t)) :
    G.comp (unitHomogeneousAwayEvaluation 𝒜 F t ht)=
      unitHomogeneousAwayEvaluation 𝒜 (G.comp F) t (ht.map G) := by
  have h : G.comp (Localization.awayLift F t ht)=
      Localization.awayLift (G.comp F) t (ht.map G) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers t)
    ext a
    simp only [RingHom.comp_apply,Localization.awayLift,IsLocalization.Away.lift_eq]
  exact congrArg (fun f=>f.comp (algebraMap (Away 𝒜 t) (Localization.Away t))) h

end UnitEvaluation

section HomogeneousEvaluation

variable {σ A K : Type u} [CommRing A] [Field K] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ→σ) [GradedRing 𝒜]

def homogeneousAwayEvaluation (F : A→+*K) (t : A) (ht : F t≠0) :
    Away 𝒜 t→+*K :=
  (Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht)).comp
    (algebraMap (Away 𝒜 t) (Localization.Away t))

theorem homogeneousAwayEvaluation_mk (F : A→+*K) {t : A} (ht : F t≠0)
    {d : ℕ} (htd : t∈𝒜 d) (m : ℕ) (p : A) (hp : p∈𝒜 (m • d)) :
    homogeneousAwayEvaluation 𝒜 F t ht (Away.mk 𝒜 htd m p hp)=
      F p/(F t)^m := by
  change Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht)
    (Localization.mk p ⟨t^m,m,rfl⟩)=_
  rw [Localization.awayLift_mk F t p (F t)⁻¹ (mul_inv_cancel₀ ht)]
  simp only [div_eq_mul_inv,inv_pow]

theorem homogeneousAwayEvaluation_awayMap (F : A→+*K)
    {t q x : A} {d : ℕ} (hq : q∈𝒜 d) (hx : x=t*q)
    (ht : F t≠0) (hxx : F x≠0) :
    (homogeneousAwayEvaluation 𝒜 F x hxx).comp (awayMap 𝒜 hq hx)=
      homogeneousAwayEvaluation 𝒜 F t ht := by
  let G : Localization.Away t→+*Localization.Away x :=
    Localization.awayLift (algebraMap A (Localization.Away x)) t
      (isUnit_of_dvd_unit (map_dvd _ ⟨q,hx⟩)
        (IsLocalization.Away.algebraMap_isUnit x))
  have hG : (Localization.awayLift F x (isUnit_iff_ne_zero.mpr hxx)).comp G =
      Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers t)
    ext a
    simp only [RingHom.comp_apply,G,Localization.awayLift,IsLocalization.Away.lift_eq]
  ext a
  change Localization.awayLift F x (isUnit_iff_ne_zero.mpr hxx)
      ((awayMap 𝒜 hq hx a).val) =
    Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht) a.val
  rw [val_awayMap]
  exact congrArg (fun g=>g a.val) hG

/-- An actual morphism into a genuine affine chart of Proj. -/
def projectiveFieldChart (F : A→+*K) (t : A) {d : ℕ}
    (htd : t∈𝒜 d) (hd : 0<d) (ht : F t≠0) :
    Spec (CommRingCat.of K)⟶Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (homogeneousAwayEvaluation 𝒜 F t ht)) ≫
    Proj.awayι 𝒜 t htd hd

theorem projectiveFieldChart_mul (F : A→+*K) (t q x : A)
    {d e : ℕ} (htd : t∈𝒜 d) (hqe : q∈𝒜 e) (hd : 0<d)
    (hx : x=t*q) (ht : F t≠0) (hxx : F x≠0) :
    projectiveFieldChart 𝒜 F t htd hd ht =
      projectiveFieldChart 𝒜 F x (hx ▸ SetLike.mul_mem_graded htd hqe)
        (hd.trans_le (Nat.le_add_right d e)) hxx := by
  unfold projectiveFieldChart
  rw [← homogeneousAwayEvaluation_awayMap 𝒜 F hqe hx ht hxx,
    CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc,
    Proj.SpecMap_awayMap_awayι]

/-- A nonzero homogeneous coordinate may be chosen arbitrarily. -/
theorem projectiveFieldChart_independent (F : A→+*K) (t q : A)
    {d e : ℕ} (htd : t∈𝒜 d) (hqe : q∈𝒜 e) (hd : 0<d) (he : 0<e)
    (ht : F t≠0) (hq : F q≠0) :
    projectiveFieldChart 𝒜 F t htd hd ht =
      projectiveFieldChart 𝒜 F q hqe he hq := by
  have hp : F (t*q)≠0 := by rw [map_mul]; exact mul_ne_zero ht hq
  rw [projectiveFieldChart_mul 𝒜 F t q (t*q) htd hqe hd rfl ht hp,
    projectiveFieldChart_mul 𝒜 F q t (t*q) hqe htd he (mul_comm t q) hq hp]
  rfl

end HomogeneousEvaluation

section PolynomialScaling

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι R K : Type u} [CommRing R] [Field K]

/-- Scaling all variables multiplies a homogeneous polynomial by the
corresponding scalar power, over any field and in every degree. -/
theorem homogeneous_eval_scaled (F : R→+*K) (v : ι→K) (c : K)
    (p : MvPolynomial ι R) (d : ℕ) (hp : p.IsHomogeneous d) :
    p.eval₂ F (fun i=>c*v i)=c^d*p.eval₂ F v := by
  rw [MvPolynomial.eval₂_eq,MvPolynomial.eval₂_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp_rw [mul_pow,Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum,← hp.degree_eq_sum_deg_support hm]
  ring

theorem homogeneousAwayEvaluation_scaled (F : R→+*K) (v : ι→K) (c : K)
    (hc : c≠0) (t : MvPolynomial ι R) {d : ℕ} (htd : t.IsHomogeneous d)
    (ht : t.eval₂ F v≠0) :
    homogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F (fun i=>c*v i)) t
        (by rw [MvPolynomial.coe_eval₂Hom,homogeneous_eval_scaled F v c t d htd]
            exact mul_ne_zero (pow_ne_zero _ hc) ht) =
    homogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F v) t ht := by
  ext z
  have htd' : t ∈ MvPolynomial.homogeneousSubmodule ι R d := htd
  obtain ⟨m,p,hp,rfl⟩ :=
    Away.mk_surjective (MvPolynomial.homogeneousSubmodule ι R) htd' z
  have hscaled : (MvPolynomial.eval₂Hom F (fun i=>c*v i)) t ≠ 0 := by
    change t.eval₂ F (fun i=>c*v i) ≠ 0
    rw [homogeneous_eval_scaled F v c t d htd]
    exact mul_ne_zero (pow_ne_zero _ hc) ht
  have hleft := homogeneousAwayEvaluation_mk (MvPolynomial.homogeneousSubmodule ι R)
    (MvPolynomial.eval₂Hom F (fun i=>c*v i)) hscaled htd' m p hp
  have hright := homogeneousAwayEvaluation_mk (MvPolynomial.homogeneousSubmodule ι R)
    (MvPolynomial.eval₂Hom F v) ht htd' m p hp
  refine hleft.trans (Eq.trans ?_ hright.symm)
  change p.eval₂ F (fun i=>c*v i) / (t.eval₂ F (fun i=>c*v i))^m =
    p.eval₂ F v / (t.eval₂ F v)^m
  rw [homogeneous_eval_scaled F v c p (m • d) hp,
    homogeneous_eval_scaled F v c t d htd,mul_pow]
  simp only [smul_eq_mul,Nat.mul_comm m d,pow_mul]
  field_simp [hc,ht]

/-- Frame rescaling leaves the actual morphism to projective space
unchanged, because its actual homogeneous-localization map is unchanged. -/
theorem projectiveFieldChart_scaled (F : R→+*K) (v : ι→K) (c : K)
    (hc : c≠0) (t : MvPolynomial ι R) {d : ℕ} (htd : t.IsHomogeneous d)
    (hd : 0<d) (ht : t.eval₂ F v≠0) :
    projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F (fun i=>c*v i)) t htd hd
        (by rw [MvPolynomial.coe_eval₂Hom,homogeneous_eval_scaled F v c t d htd]
            exact mul_ne_zero (pow_ne_zero _ hc) ht) =
    projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F v) t htd hd ht := by
  unfold projectiveFieldChart
  rw [homogeneousAwayEvaluation_scaled F v c hc t htd ht]

end PolynomialScaling
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.projectiveFieldChart_independent
#print axioms PaperVerification.ToricSchemes.projectiveFieldChart_scaled
end Source_ToricProjectiveRatios

section Source_ToricProjectiveMonomialMaps




/-!
# Character maps into the actual monomial Proj

The chart morphisms are the genuine Proj affine-chart open immersions.
Their restrictions to the character torus agree as scheme morphisms,
proved through homogeneous ratios in the actual fraction field and
separatedness. Their mutual inverse-image opens are the basic opens of
the literal weight-difference characters.
-/


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
end Source_ToricProjectiveMonomialMaps

section Source_ToricMonomialFanIso




/-!
# The genuine monomial Proj is the scheme of its recovered normal fan

The affine coordinate rings, open immersions, torus restrictions, and
common-face overlaps are identified explicitly. The conclusion is an
isomorphism of actual schemes, obtained from their actual affine charts.
No fan presentation is included in the hypotheses on the monomial Proj.
-/


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u v

namespace PaperVerification.ToricCharacters

open AlgebraicGeometry CategoryTheory
open scoped Classical

section IndependentUniverses

variable (k : Type u) [CommRing k] {G : Type*} [AddCommGroup G]

def monoidChartEqIso {S T : AddSubmonoid G} (h : S=T) :
    monoidChartScheme k S≅monoidChartScheme k T :=
  eqToIso (congrArg (monoidChartScheme k) h)

theorem monoidChartEqIso_torus {S T : AddSubmonoid G} (h : S=T) :
    Spec.map (CommRingCat.ofHom (monoidChartAlgebra k S).val.toRingHom)≫
        (monoidChartEqIso k h).hom=
      Spec.map (CommRingCat.ofHom (monoidChartAlgebra k T).val.toRingHom) := by
  subst T
  exact Category.comp_id _

theorem monoidChartEqIso_preimage_character {S T : AddSubmonoid G} (h : S=T)
    (z : G) (hzS : z∈S) (hzT : z∈T) :
    (monoidChartEqIso k h).hom ⁻¹ᵁ PrimeSpectrum.basicOpen (chartCharacter k T z hzT)=
      PrimeSpectrum.basicOpen (chartCharacter k S z hzS) := by
  subst T
  rfl

end IndependentUniverses

section ToSpec

variable (k : Type (max u v)) [CommRing k] {G : Type v} [AddCommGroup G]

theorem monoidChartEqIso_toSpec {S T : AddSubmonoid G} (h : S=T) :
    (monoidChartEqIso k h).hom≫
        Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k T)))=
      Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k S))) := by
  subst T
  exact Category.id_comp _

end ToSpec

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical

variable {n : ℕ} (k : Type u) [CommRing k]

theorem coneChart_zeroFace_eq_torus (s : Finset (Lattice n)) :
    coneChartFaceMap k (Finset.empty_subset s)=
      (zeroConeChartIso k n).hom≫
        Spec.map (CommRingCat.ofHom (monoidChartAlgebra k (dualConeMonoid s)).val.toRingHom) := by
  change Spec.map _=Spec.map _≫Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  apply Subtype.ext
  change (f : AddMonoidAlgebra k (Lattice n))=
    zeroConeChartAlgEquiv k n
      ((zeroConeChartAlgEquiv k n).symm (f : AddMonoidAlgebra k (Lattice n)))
  exact ((zeroConeChartAlgEquiv k n).apply_symm_apply
    (f : AddMonoidAlgebra k (Lattice n))).symm

end PaperVerification.ToricGeometry

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}
    («Σ» : SmoothCompleteFan n) (P : LatticePolytope n)
    (a : ι → Lattice n) (k : Type u) [Field k]
    (s : vertexWeightIndices a → Finset (Lattice n))
    (hdual : ∀ j,dualConeMonoid (s j)=differenceWeightMonoid a j.val)

local instance monomialNormalFan_target_isSeparated :
    (monomialProjectiveScheme a k).IsSeparated :=
  inferInstanceAs ((Proj (homogeneousWeightGrading a k)).IsSeparated)

def monomialFanChart (j : vertexWeightIndices a) :
    coneChart k (s j)⟶monomialProjectiveScheme a k :=
  (monoidChartEqIso k (hdual j)).hom≫monomialCoordinateChartMap a k j.val

instance monomialFanChart_isOpenImmersion (j : vertexWeightIndices a) :
    IsOpenImmersion (monomialFanChart a k s hdual j) := by
  unfold monomialFanChart
  letI : IsOpenImmersion (monomialCoordinateChartMap a k j.val) :=
    monomialCoordinateChartMap_isOpenImmersion a k j.val
  exact IsOpenImmersion.comp _ _

set_option maxHeartbeats 2000000 in
theorem monomialFanChart_torus (j : vertexWeightIndices a) :
    coneChartFaceMap k (Finset.empty_subset (s j))≫monomialFanChart a k s hdual j=
      (zeroConeChartIso k n).hom≫monomialTorusChart a k j.val := by
  erw [monomialFanChart,coneChart_zeroFace_eq_torus k (s j),Category.assoc,
    ← Category.assoc (Spec.map (CommRingCat.ofHom
      (monoidChartAlgebra k (dualConeMonoid (s j))).val.toRingHom)),
    monoidChartEqIso_torus k (hdual j),monomialCoordinateChartMap_torus a k j.val]

theorem monomialFanChart_torus_agree (i j : vertexWeightIndices a) :
    coneChartFaceMap k (Finset.empty_subset (s i))≫monomialFanChart a k s hdual i=
      coneChartFaceMap k (Finset.empty_subset (s j))≫monomialFanChart a k s hdual j := by
  rw [monomialFanChart_torus,monomialFanChart_torus,monomialTorusChart_independent a k i.val j.val]

theorem monomialFanChart_opensRange (j : vertexWeightIndices a) :
    (monomialFanChart a k s hdual j).opensRange=
      Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j.val) := by
  change ((monoidChartEqIso k (hdual j)).hom≫
    monomialCoordinateChartMap a k j.val).opensRange=_
  erw [Scheme.Hom.opensRange_comp_of_isIso,monomialCoordinateChartMap_opensRange]

set_option maxHeartbeats 2000000 in
theorem monomialFanChart_preimage_range (i j : vertexWeightIndices a)
    (hz : a j.val-a i.val∈dualConeMonoid (s i)) :
    (monomialFanChart a k s hdual i) ⁻¹'
        Set.range (monomialFanChart a k s hdual j)=
      ((PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid (s i))
        (a j.val-a i.val) hz)).carrier : Set (coneChart k (s i))) := by
  let e : coneChart k (s i)≅monoidChartScheme k (differenceWeightMonoid a i.val) :=
    monoidChartEqIso k (hdual i)
  let f : monoidChartScheme k (differenceWeightMonoid a i.val)⟶
      monomialProjectiveScheme a k := monomialCoordinateChartMap a k i.val
  let U : (monomialProjectiveScheme a k).Opens :=
    Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j.val)
  have h₁ := congrArg (fun V : (monomialProjectiveScheme a k).Opens =>
    (e.hom≫f) ⁻¹ᵁ V) (monomialFanChart_opensRange a k s hdual j)
  have h₃ := congrArg
    (fun V : (monoidChartScheme k (differenceWeightMonoid a i.val)).Opens => e.hom ⁻¹ᵁ V)
    (monomialCoordinateChartMap_preimage_basicOpen a k i.val j.val)
  have h₄ := monoidChartEqIso_preimage_character k (hdual i)
    (a j.val-a i.val) hz (AddSubmonoid.subset_closure (Set.mem_range_self j.val))
  have ho : (e.hom≫f) ⁻¹ᵁ (monomialFanChart a k s hdual j).opensRange=
      PrimeSpectrum.basicOpen (chartCharacter k (dualConeMonoid (s i))
        (a j.val-a i.val) hz) :=
    h₁.trans ((Scheme.Hom.comp_preimage e.hom f U).trans (h₃.trans h₄))
  exact congrArg (fun V : (coneChart k (s i)).Opens => V.carrier) ho

theorem monomialFanChart_cover (y : monomialProjectiveScheme a k) :
    ∃ j x,monomialFanChart a k s hdual j x=y := by
  have hy : y∈⨆ j : vertexWeightIndices a,
      Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j.val) := by
    rw [monomialProjective_vertex_cover]
    trivial
  obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  rw [← monomialFanChart_opensRange a k s hdual j] at hj
  obtain ⟨x,hx⟩ := hj
  exact ⟨j,x,hx⟩

/-- The normal fan chart scheme is the actual monomial projective
scheme, with its specified character torus unchanged. -/
def monomialNormalFanIso
    (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    (hv : ∀ j : vertexWeightIndices a,embed n (a j.val)∈P.carrier)
    (hnormal : ∀ j : vertexWeightIndices a,P.normalCone (embed n (a j.val))=
      (latticeRayCone (s j) : Set (Ambient n))) :
    «Σ».fanScheme k≅monomialProjectiveScheme a k := by
  let f := monomialFanChart a k s hdual
  have hT := monomialFanChart_torus_agree a k s hdual
  refine «Σ».chartFamilyIso k s hs hcover f hT ?_
    (monomialFanChart_cover a k s hdual)
  intro i j
  rw [monomialFanChart_preimage_range a k s hdual i j
    («Σ».vertex_difference_mem_dualCone P (a i.val) (a j.val) (hv j) (s i) (hnormal i))]
  exact «Σ».normal_chart_intersection_range P k (a i.val) (a j.val) (hv i) (hv j)
    (s i) (s j) (hs i) (hs j) (hnormal i) (hnormal j)

theorem monomialNormalFanIso_chart
    (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    (hv : ∀ j : vertexWeightIndices a,embed n (a j.val)∈P.carrier)
    (hnormal : ∀ j : vertexWeightIndices a,P.normalCone (embed n (a j.val))=
      (latticeRayCone (s j) : Set (Ambient n))) (j : vertexWeightIndices a) :
    «Σ».fanChartMap k ⟨s j,hs j⟩≫
        («Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal).hom=
      monomialFanChart a k s hdual j :=
  «Σ».familyChart_chartFamilyDesc k s hs hcover (monomialFanChart a k s hdual)
    (monomialFanChart_torus_agree a k s hdual) j

theorem monomialNormalFanIso_torus
    (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    (hv : ∀ j : vertexWeightIndices a,embed n (a j.val)∈P.carrier)
    (hnormal : ∀ j : vertexWeightIndices a,P.normalCone (embed n (a j.val))=
      (latticeRayCone (s j) : Set (Ambient n))) (j : vertexWeightIndices a) :
    «Σ».splitTorusOpenMap k≫
        («Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal).hom=
      monomialTorusChart a k j.val := by
  rw [splitTorusOpenMap,Category.assoc]
  have hnat := «Σ».fanChartMap_naturality k
    (s := «Σ».zeroConeIndex) (t := ⟨s j,hs j⟩)
    (Finset.empty_subset (s j) : «Σ».zeroConeIndex.val⊆(⟨s j,hs j⟩ : «Σ».ConeIndex).val)
  change (zeroConeChartIso k n).inv≫(«Σ».fanChartMap k «Σ».zeroConeIndex≫_)=_
  rw [← hnat,Category.assoc,monomialNormalFanIso_chart,monomialFanChart_torus]
  simp only [← Category.assoc,Iso.inv_hom_id,Category.id_comp]

end PaperVerification.ToricGeometry.SmoothCompleteFan
end Source_ToricMonomialFanIso

section Source_ToricGradedProjQuotient




/-!
# Surjective graded homomorphisms and genuine closed Proj embeddings

A homogeneous element of a graded quotient has a homogeneous preimage:
take the required degree component of any preimage. Consequently the
degree-zero localized maps are surjective. The actual Proj morphism is
therefore a closed immersion on the standard affine open cover.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped Classical
open HomogeneousIdeal

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ→σ} {ℬ : ℕ→τ} [GradedRing 𝒜] [GradedRing ℬ]

theorem graded_surjective_homogeneous_preimage (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) {d : ℕ} {b : B} (hb : b∈ℬ d) :
    ∃ a : A,a∈𝒜 d ∧ f a=b := by
  obtain ⟨a,rfl⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 a d,(DirectSum.decompose 𝒜 a d).property,?_⟩
  rw [f.map_directSumDecompose,DirectSum.decompose_of_mem_same ℬ hb]

theorem irrelevant_le_map_of_surjective (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) : ℬ₊≤𝒜₊.map f := by
  apply (HomogeneousIdeal.irrelevant_le ℬ).mpr
  intro d hd b hb
  obtain ⟨a,ha,rfl⟩ := graded_surjective_homogeneous_preimage f hf hb
  exact Ideal.mem_map_of_mem f
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd ha)

theorem homogeneousAway_map_surjective (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) {d : ℕ} {s : A} (hs : s∈𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨m,b,hb,rfl⟩ := Away.mk_surjective ℬ (f.map_mem hs) z
  obtain ⟨a,ha,rfl⟩ := graded_surjective_homogeneous_preimage f hf hb
  exact ⟨Away.mk 𝒜 hs m a ha,by simp⟩

/-- The literal Proj morphism of a graded quotient is a closed immersion.
The proof uses surjectivity of its actual affine coordinate homomorphisms. -/
theorem projMap_isClosedImmersion_of_surjective (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) :
    IsClosedImmersion (Proj.map f (irrelevant_le_map_of_surjective f hf)) := by
  let h := irrelevant_le_map_of_surjective f hf
  let F := Proj.map f h
  let J := Σ d : {d : ℕ // 0<d}, {s : A // s∈𝒜 d.val}
  let U (j : J) := Proj.basicOpen 𝒜 j.2.val
  have hcover : (⨆ j,U j)=⊤ := by
    apply Proj.iSup_basicOpen_eq_top
    apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
    intro d hd a ha
    exact Ideal.subset_span ⟨⟨⟨d,hd⟩,⟨a,ha⟩⟩,rfl⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top U hcover
  intro j
  let eA := Proj.basicOpenIsoSpec 𝒜 j.2.val j.2.property j.1.property
  let eB := Proj.basicOpenIsoSpec ℬ (f j.2.val)
    (f.map_mem j.2.property) j.1.property
  let g := Spec.map (CommRingCat.ofHom (Away.map f j.2.val))
  letI : IsClosedImmersion g := IsClosedImmersion.spec_of_surjective _
    (homogeneousAway_map_surjective f hf j.2.property)
  let r : (Proj.basicOpen ℬ (f j.2.val)).toScheme ⟶
      (Proj.basicOpen 𝒜 j.2.val).toScheme := F ∣_ U j
  have hsq : (eB.inv ≫ (Proj.basicOpen ℬ (f j.2.val)).ι) ≫ F =
      g ≫ eA.inv ≫ (U j).ι :=
    Proj.awayι_comp_map f h j.1.property j.2.val j.2.property
  have hcanonical : (Proj.basicOpen ℬ (f j.2.val)).ι ≫ F =
      (eB.hom ≫ g ≫ eA.inv) ≫ (U j).ι := by
    have h := congrArg (fun q => eB.hom ≫ q) hsq
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h
  have heq : r = eB.hom ≫ g ≫ eA.inv := by
    apply (cancel_mono (Proj.basicOpen 𝒜 j.2.val).ι).mp
    exact (morphismRestrict_ι F (U j)).trans hcanonical
  letI : IsClosedImmersion (g ≫ eA.inv) := IsClosedImmersion.comp g eA.inv
  have hclosed : IsClosedImmersion (eB.hom ≫ g ≫ eA.inv) :=
    IsClosedImmersion.comp eB.hom (g ≫ eA.inv)
  change IsClosedImmersion r
  exact heq.symm ▸ hclosed

variable {K : Type u} [Field K]

theorem homogeneousAwayEvaluation_gradedMap (f : 𝒜→+*ᵍℬ)
    (F : B→+*K) {d : ℕ} {s : A} (hs : s∈𝒜 d) (hne : F (f s)≠0) :
    (homogeneousAwayEvaluation ℬ F (f s) hne).comp (Away.map f s)=
      homogeneousAwayEvaluation 𝒜 (F.comp f.toRingHom) s hne := by
  ext z
  obtain ⟨m,a,ha,rfl⟩ := Away.mk_surjective 𝒜 hs z
  simp only [RingHom.comp_apply,Away.map_mk,homogeneousAwayEvaluation_mk]
  rfl

theorem projectiveFieldChart_gradedMap (f : 𝒜→+*ᵍℬ)
    (h : ℬ₊≤𝒜₊.map f) (F : B→+*K) {d : ℕ} {s : A}
    (hs : s∈𝒜 d) (hd : 0<d) (hne : F (f s)≠0) :
    projectiveFieldChart ℬ F (f s) (f.map_mem hs) hd hne≫Proj.map f h=
      projectiveFieldChart 𝒜 (F.comp f.toRingHom) s hs hd hne := by
  unfold projectiveFieldChart
  rw [Category.assoc,Proj.awayι_comp_map f h hd s hs,
    ← Category.assoc,← Spec.map_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (homogeneousAwayEvaluation_gradedMap f F hs hne)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.projMap_isClosedImmersion_of_surjective
end Source_ToricGradedProjQuotient

section Source_ToricMonomialProjectiveEmbedding




/-!
# The actual monomial projective closed immersion

The graded polynomial quotient sends the i-th projective coordinate to
the homogeneous character (1,aᵢ). Its Proj is embedded by the actual
graded-ring morphism. All coordinate charts are domains, and the common
character torus is schematically dense. Thus this Proj is the genuine
scheme-theoretic monomial orbit closure, rather than an assumed model.
-/


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
end Source_ToricMonomialProjectiveEmbedding

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.monomialNormalFanIso
#print axioms PaperVerification.ToricCharacters.monomialProjectiveEmbedding_isClosedImmersion
#eval "RECOVERED_PROJECTIVE_FOUNDATIONS_END"
