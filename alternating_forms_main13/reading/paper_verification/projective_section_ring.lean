module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The actual complete section ring of a projective spectrum

The degree-d piece is the existing group of global sections of the
actual twisting sheaf O(d).  These groups are additive subgroups of the
same product of localization rings.  Their pointwise multiplication
therefore defines the complete section ring independently of any
comparison with the original graded ring.

The canonical map sends a homogeneous element r to the actual section
r/1.  If its component maps are bijective, the resulting canonical ring
map is an isomorphism.  No multiplication is transported from the desired
conclusion, and no section is replaced by a polynomial surrogate.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.ProjectiveSectionRing

open AlgebraicGeometry
open scoped DirectSum
open ProjectiveSpectrum.TwistingSheaf

universe u
variable {A : Type u} {σ : Type*} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The existing actual global-section subgroup, in nonnegative degree. -/
abbrev sectionPiece (d : ℕ) :
    AddSubgroup (∀ x : (⊤ : (Proj 𝒜).Opens),Localizations 𝒜 x.1) :=
  sectionsAddSubgroup 𝒜 (d : ℤ) ⊤

/-- This is literally the actual global section group of the twisting
sheaf, with its existing addition. -/
def sectionPieceEquiv (d : ℕ) :
    sectionPiece 𝒜 d ≃+ Γ(Proj.twistingSheaf 𝒜 (d : ℤ),⊤) :=
  AddEquiv.refl _

set_option backward.isDefEq.respectTransparency false in
instance sectionPieceGradedMonoid : SetLike.GradedMonoid (sectionPiece 𝒜) where
  one_mem := by
    change (isLocallyFraction 𝒜 (0 : ℤ)).pred
      (fun x : (⊤ : (Proj 𝒜).Opens) => (1 : Localizations 𝒜 x.1))
    convert (isLocallyFraction_val (𝒜 := 𝒜) (1 : Γ(Proj 𝒜,⊤))) using 1 <;>
      funext x <;> simp only [Proj.one_apply,HomogeneousLocalization.val_one]
  mul_mem := by
    intro a b f g hf hg
    change (isLocallyFraction 𝒜 ((a+b : ℕ) : ℤ)).pred (f*g)
    simpa only [Nat.cast_add] using isLocallyFraction_mul hf hg

/-- The actual complete section ring, with independently defined
pointwise homogeneous products. -/
abbrev SectionRing := ⨁ d : ℕ,sectionPiece 𝒜 d

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Multiplication of homogeneous elements is the literal product of
their values in the localizations. -/
theorem of_mul_of (a b : ℕ) (s : sectionPiece 𝒜 a) (t : sectionPiece 𝒜 b) :
    DirectSum.of (fun d ↦ sectionPiece 𝒜 d) a s *
      DirectSum.of (fun d ↦ sectionPiece 𝒜 d) b t =
    DirectSum.of (fun d ↦ sectionPiece 𝒜 d) (a+b)
      ⟨s.1*t.1,by
        change (isLocallyFraction 𝒜 ((a+b : ℕ) : ℤ)).pred (s.1*t.1)
        simpa only [Nat.cast_add] using isLocallyFraction_mul s.2 t.2⟩ :=
  by
    classical
    refine (DirectSum.of_mul_of
      (A := fun d : ℕ ↦ ↥(sectionPiece 𝒜 d)) s t).trans ?_
    apply congrArg (DirectSum.of (fun d : ℕ ↦ ↥(sectionPiece 𝒜 d)) (a+b))
    exact Subtype.ext rfl

/-- The canonical component map is the existing r/1 section map. -/
abbrev componentMap (d : ℕ) : 𝒜 d →+ sectionPiece 𝒜 d :=
  Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤

@[simp] theorem componentMap_apply (d : ℕ) (r : 𝒜 d)
    (x : (⊤ : (Proj 𝒜).Opens)) :
    (componentMap 𝒜 d r).1 x=Localization.mk (r : A) 1 := rfl

/-- Extend the actual canonical component maps to the external direct sum. -/
def directSumMap : (⨁ d : ℕ,𝒜 d) →+* SectionRing 𝒜 :=
  DirectSum.toSemiring
    (fun d ↦ (DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d).comp
      (componentMap 𝒜 d))
    (by
      change DirectSum.of (fun j ↦ sectionPiece 𝒜 j) 0
        (componentMap 𝒜 0 ⟨1,SetLike.GradedOne.one_mem⟩)=1
      rw [DirectSum.one_def]
      apply congrArg (DirectSum.of (fun j ↦ sectionPiece 𝒜 j) 0)
      apply Subtype.ext
      funext x
      change Localization.mk (1 : A) 1=1
      simp only [Localization.mk_one_eq_algebraMap,map_one])
    (by
      intro a b r s
      change DirectSum.of (fun j ↦ sectionPiece 𝒜 j) (a+b)
          (componentMap 𝒜 (a+b) ⟨(r : A)*(s : A),SetLike.mul_mem_graded r.2 s.2⟩)=
        DirectSum.of (fun j ↦ sectionPiece 𝒜 j) a (componentMap 𝒜 a r) *
          DirectSum.of (fun j ↦ sectionPiece 𝒜 j) b (componentMap 𝒜 b s)
      rw [DirectSum.of_mul_of]
      apply congrArg (DirectSum.of (fun j ↦ sectionPiece 𝒜 j) (a+b))
      apply Subtype.ext
      funext x
      change Localization.mk ((r : A)*(s : A)) 1=
        Localization.mk (r : A) 1*Localization.mk (s : A) 1
      simp only [Localization.mk_one_eq_algebraMap,map_mul])

@[simp] theorem directSumMap_of (d : ℕ) (r : 𝒜 d) :
    directSumMap 𝒜 (DirectSum.of (fun j ↦ 𝒜 j) d r)=
      DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d (componentMap 𝒜 d r) :=
  DirectSum.toSemiring_of _ _ _ _ _

theorem directSumMap_toAddMonoidHom :
    (directSumMap 𝒜).toAddMonoidHom=DirectSum.map (componentMap 𝒜) := by
  apply DirectSum.addHom_ext
  intro d r
  change directSumMap 𝒜 (DirectSum.of (fun j ↦ 𝒜 j) d r)=_
  rw [directSumMap_of,DirectSum.map_of]

/-- The canonical coordinate-ring to complete-section-ring map. -/
def canonicalMap : A →+* SectionRing 𝒜 :=
  (directSumMap 𝒜).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- On every homogeneous element this map is exactly the corresponding
actual global section r/1 placed in its own degree. -/
theorem canonicalMap_homogeneous (d : ℕ) (r : 𝒜 d) :
    canonicalMap 𝒜 (r : A)=
      DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d
        (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤ r) := by
  change directSumMap 𝒜 (DirectSum.decompose 𝒜 (r : A))=_
  rw [DirectSum.decompose_coe,directSumMap_of]
  rfl

/-- Componentwise completeness proves bijectivity of the canonical map
to the already-defined actual section ring. -/
theorem canonicalMap_bijective
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)) :
    Function.Bijective (canonicalMap 𝒜) := by
  have hm : Function.Bijective (DirectSum.map (componentMap 𝒜)) :=
    ⟨(DirectSum.map_injective _).2 (fun d ↦ (h d).1),
      (DirectSum.map_surjective _).2 (fun d ↦ (h d).2)⟩
  have hd : Function.Bijective (directSumMap 𝒜) := by
    change Function.Bijective (directSumMap 𝒜).toAddMonoidHom
    rw [directSumMap_toAddMonoidHom]
    exact hm
  exact hd.comp (DirectSum.decomposeRingEquiv 𝒜).bijective

/-- The canonical isomorphism with the actual complete section ring,
once the actual section comparison is proved in every degree. -/
def completeSectionRingEquiv
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)) :
    A ≃+* SectionRing 𝒜 :=
  RingEquiv.ofBijective (canonicalMap 𝒜) (canonicalMap_bijective 𝒜 h)

@[simp] theorem completeSectionRingEquiv_apply
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)) (r : A) :
    completeSectionRingEquiv 𝒜 h r=canonicalMap 𝒜 r := rfl

theorem completeSectionRingEquiv_homogeneous
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤))
    (d : ℕ) (r : 𝒜 d) :
    completeSectionRingEquiv 𝒜 h (r : A)=
      DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d
        (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤ r) :=
  canonicalMap_homogeneous 𝒜 d r

/-- The canonical comparison identifies each original homogeneous piece
with exactly the corresponding actual direct-sum section piece, in both
directions.  This records the grading, not only the abstract ring. -/
theorem completeSectionRingEquiv_mem_degree_iff
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤))
    (d : ℕ) (x : SectionRing 𝒜) :
    (∃ r : 𝒜 d,completeSectionRingEquiv 𝒜 h (r : A)=x) ↔
      ∃ s : sectionPiece 𝒜 d,DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d s=x := by
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨componentMap 𝒜 d r,(completeSectionRingEquiv_homogeneous 𝒜 h d r).symm⟩
  · rintro ⟨s,rfl⟩
    obtain ⟨r,hr⟩ := (h d).surjective s
    refine ⟨r,?_⟩
    rw [completeSectionRingEquiv_homogeneous]
    exact congrArg (DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d) hr


section Scalars

variable {K : Type*} [CommRing K] [Algebra K A]

/-- Scalars act by their canonical constant sections.  This algebra
structure is defined before and independently of any completeness proof. -/
instance sectionRingAlgebra : Algebra K (SectionRing 𝒜) :=
  ((canonicalMap 𝒜).comp (algebraMap K A)).toAlgebra

/-- The canonical coordinate map also preserves its original scalars. -/
def canonicalAlgHom : A →ₐ[K] SectionRing 𝒜 where
  toRingHom := canonicalMap 𝒜
  commutes' _ := rfl

/-- For degree-zero scalars the algebra map is exactly their actual
constant section, in degree zero of the complete section ring. -/
theorem algebraMap_eq_degreeZero_section (c : K)
    (hc : algebraMap K A c∈𝒜 0) :
    algebraMap K (SectionRing 𝒜) c=
      DirectSum.of (fun d ↦ sectionPiece 𝒜 d) 0
        (Proj.toTwistingSheaf 𝒜 (rfl : (0 : ℤ)=0) ⊤ ⟨algebraMap K A c,hc⟩) :=
  canonicalMap_homogeneous 𝒜 0 ⟨algebraMap K A c,hc⟩

/-- The canonical complete-section comparison is an isomorphism over
the original scalar ring, not merely an abstract ring isomorphism. -/
def completeSectionAlgEquiv
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)) :
    A ≃ₐ[K] SectionRing 𝒜 where
  toRingEquiv := completeSectionRingEquiv 𝒜 h
  commutes' _ := rfl

@[simp] theorem completeSectionAlgEquiv_apply
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)) (r : A) :
    completeSectionAlgEquiv (K := K) 𝒜 h r=canonicalMap 𝒜 r := rfl

end Scalars

end PaperVerification.ProjectiveSectionRing
