module

public import PaperVerification.AlternatingFormsCompleteSectionRing
public import PaperVerification.AlternatingFormsOddTorPure
public import PaperVerification.AlternatingFormsBarEquivTransport

/-!
# Ordinary Tor of the actual complete odd Plucker section ring

The coefficient algebra here is the independently defined direct sum of
actual global twisting-sheaf sections.  The canonical graded algebra
isomorphism carries the original augmented monomial basis to that ring.
Its literal bar complex therefore computes ordinary Tor for this actual
section ring.  The internal pieces below are images of the original
homogeneous bar subcomplexes, and their equality with the transported
original Tor pieces is proved rather than used as a definition.

Every size at least two is included, including the singleton maximal
interval.  The separate one-plane polynomial boundary must be joined
before this file can support an all-size principal statement.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace PaperVerification.AlternatingForms

open CategoryTheory HomologicalComplex MvPolynomial
open PaperVerification.ProjectiveSectionRing

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "A" => MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
  isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "S" => SectionRing (oddProjectiveGrading (K := K) k t)
local notation "e" => oddCompleteSectionRingEquiv (K := K) k t hs
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "ε" => oddAugmentation (K := K) k t
local notation "I" => OddPositiveStandardIndex (K := K) k t hs

/-- The actual augmentation of the complete section ring, via the
proved canonical coordinate comparison. -/
def oddSectionAugmentation : S →ₐ[K] K :=
  BarEquivTransport.augmentation e ε

/-- The genuine unit-plus-positive basis of the actual complete section
ring.  Its vectors are the actual homogeneous global sections. -/
def oddSectionAugmentedBasis : Module.Basis (Option I) K S :=
  BarEquivTransport.basis e B

@[simp] theorem oddSectionAugmentedBasis_none :
    oddSectionAugmentedBasis (K := K) k t hs none=1 :=
  BarEquivTransport.basis_unit e B (oddAugmentedBasis_none k t hs)

@[simp] theorem oddSectionAugmentation_positive (i : I) :
    oddSectionAugmentation (K := K) k t hs (oddSectionAugmentedBasis (K := K) k t hs (some i))=0 :=
  BarEquivTransport.augmentation_positive e ε B
    (oddAugmentation_positive k t hs) i

/-- These submodules are identified below with exactly the actual
degree-d direct-sum section summands, not arbitrary transported labels. -/
def oddSectionDegree (d : ℕ) : Submodule K S :=
  (oddProjectiveGrading (K := K) k t d).map (e).toLinearEquiv.toLinearMap

theorem oddSectionDegree_mem_iff (d : ℕ) (x : S) :
    x∈oddSectionDegree (K := K) k t hs d ↔
      ∃ s : sectionPiece (oddProjectiveGrading (K := K) k t) d,
        DirectSum.of (fun j ↦ sectionPiece (oddProjectiveGrading (K := K) k t) j) d s=x := by
  constructor
  · rintro ⟨r,hr,he⟩
    exact (completeSectionRingEquiv_mem_degree_iff
      (oddProjectiveGrading (K := K) k t) (odd_allSizes_bijective_toTwistingSheaf_top k t hs)
      d x).mp ⟨⟨r,hr⟩,he⟩
  · intro hx
    obtain ⟨r,hr⟩ := (completeSectionRingEquiv_mem_degree_iff
      (oddProjectiveGrading (K := K) k t) (odd_allSizes_bijective_toTwistingSheaf_top k t hs)
      d x).mpr hx
    exact ⟨r,r.2,hr⟩

theorem oddSectionAugmentedBasis_homogeneous (i : I) :
    oddSectionAugmentedBasis (K := K) k t hs (some i)∈
      oddSectionDegree (K := K) k t hs (oddPositiveDegree k t hs i) := by
  refine ⟨B (some i),?_,rfl⟩
  change B (some i)∈HomogeneousQuotientProjective.grading _ _ _
  rw [HomogeneousQuotientProjective.grading_eq_piece]
  exact oddAugmentedBasis_homogeneous k t hs i

/-- The residue used by actual Tor is the original coefficient field. -/
def oddSectionResidueEquivField :
    BarFree.Residue (oddSectionAugmentation (K := K) k t hs) ≃ₐ[K] K :=
  BarFree.residueEquivCoefficients (oddSectionAugmentation (K := K) k t hs)

/-- The actual original and complete-section bar complexes have the
proved identity-on-coefficient-words comparison. -/
def oddSectionBarIso :
    BarFree.reducedComplex ε B
        (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs) ≅
      BarFree.reducedComplex (oddSectionAugmentation (K := K) k t hs)
        (oddSectionAugmentedBasis (K := K) k t hs) (oddSectionAugmentedBasis_none (K := K) k t hs)
        (oddSectionAugmentation_positive (K := K) k t hs) :=
  BarEquivTransport.reducedComplexIso e ε B
    (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs)

/-- Ordinary Tor over the actual section algebra, computed by its
genuine normalized free bar resolution. -/
def oddSectionNormalizedBarTorIso (r : ℕ) :
    BarFree.TorOverCoefficients (oddSectionAugmentation (K := K) k t hs) r ≅
      (BarFree.reducedComplex (oddSectionAugmentation (K := K) k t hs)
        (oddSectionAugmentedBasis (K := K) k t hs) (oddSectionAugmentedBasis_none (K := K) k t hs)
        (oddSectionAugmentation_positive (K := K) k t hs)).homology r :=
  BarFree.reducedBarTorIso _ _ _ _ r

/-- This is an isomorphism of the actual derived tensor objects for
the original quotient ring and the actual complete section ring. -/
def oddSectionTorIso (r : ℕ) :
    BarFree.TorOverCoefficients ε r ≅
      BarFree.TorOverCoefficients (oddSectionAugmentation (K := K) k t hs) r :=
  BarEquivTransport.torIso e ε B
    (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs) r

/-- Inclusion of the original homogeneous-degree subcomplex into the
genuine normalized bar complex of the complete section ring. -/
def oddSectionInternalDegreeInclusionChain (N : ℕ) :
    oddInternalDegreeComplex (K := K) k t hs N ⟶
      BarFree.reducedComplex (oddSectionAugmentation (K := K) k t hs)
        (oddSectionAugmentedBasis (K := K) k t hs) (oddSectionAugmentedBasis_none (K := K) k t hs)
        (oddSectionAugmentation_positive (K := K) k t hs) :=
  oddInternalDegreeInclusionChain k t hs N ≫ (oddSectionBarIso (K := K) k t hs).hom

/-- Literal internal-degree images in the actual ordinary Tor of the
complete section ring.  The definition uses the actual bar subcomplex,
its actual inclusion, and the proved derived-functor comparison. -/
def oddSectionTorInternalPiece (r N : ℕ) :
    Submodule K (BarFree.TorOverCoefficients (oddSectionAugmentation (K := K) k t hs) r) :=
  LinearMap.range
    ((HomologicalComplex.homologyMap (oddSectionInternalDegreeInclusionChain (K := K) k t hs N) r ≫
      (oddSectionNormalizedBarTorIso (K := K) k t hs r).inv).hom)

/-- The two genuine definitions of the corresponding Tor piece agree
through the proved ordinary-Tor isomorphism. -/
theorem oddSectionTorInternalPiece_eq_map (r N : ℕ) :
    oddSectionTorInternalPiece (K := K) k t hs r N=
      (oddTorInternalPiece k t hs r N).map
        (oddSectionTorIso (K := K) k t hs r).toLinearEquiv.toLinearMap :=
  BarEquivTransport.subcomplex_homology_image e ε B
    (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs) r
    (oddInternalDegreeComplex k t hs N) (oddInternalDegreeInclusionChain k t hs N)

set_option maxHeartbeats 4000000 in
/-- The standard homological Koszul conclusion for the actual complete
section ring, in every homological and internal degree. -/
theorem oddSection_actual_Tor_internal_degree (r N : ℕ) :
    oddSectionTorInternalPiece (K := K) k t hs r N=if N=r then ⊤ else ⊥ := by
  exact (oddSectionTorInternalPiece_eq_map (K := K) k t hs r N).trans
    (BarEquivTransport.map_diagonal_submodule
      (oddSectionTorIso (K := K) k t hs r).toLinearEquiv
      (oddTorInternalPiece (K := K) k t hs r N) N r
      (odd_actual_Tor_internal_degree (K := K) k t hs r N))

set_option maxHeartbeats 4000000 in
/-- These genuine internal-degree images exhaust the whole actual Tor
group, excluding a vacuous choice of purported degree pieces. -/
theorem oddSectionTorInternalPieces_iSup (r : ℕ) :
    (⨆ N,oddSectionTorInternalPiece (K := K) k t hs r N)=⊤ := by
  apply top_unique
  have hd : oddSectionTorInternalPiece (K := K) k t hs r r=⊤ := by
    simpa only [ite_true] using oddSection_actual_Tor_internal_degree (K := K) k t hs r r
  rw [←hd]
  exact le_iSup (fun N ↦ oddSectionTorInternalPiece (K := K) k t hs r N) r

end PaperVerification.AlternatingForms
