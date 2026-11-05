module

public import PaperVerification.AlternatingFormsOnePlaneCompleteSectionRing
public import PaperVerification.AlternatingFormsOnePlaneDegreeFaithfulness
public import PaperVerification.ModuleCatRingEquivTorElementary

/-!
# Actual graded Tor of the one-plane complete section ring

The original variable Koszul resolution is changed to the actual complete
section algebra through the proved canonical algebra isomorphism.  The
result is an actual projective resolution over that algebra.  Its free
internal degrees remain the degrees of the original coefficient monomials
plus the exterior degree, and the coefficient monomials become the actual
homogeneous global sections.  Tensor degree pieces are defined as images
of those actual free pieces under tensoring with the coefficient residue.

The tensor comparison keeps pure tensors unchanged.  It proves both the
vanishing of the actual differentials after tensoring and the asserted
internal-degree images.  Ordinary Tor concentration then follows through
the actual derived-functor comparison.  No abstract Koszul-invariance or
unproved section-ring comparison is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.AlternatingForms.OnePlaneSectionKoszul

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open PaperVerification.ProjectiveSectionRing

universe u

variable {K : Type u} [Field K] [CharZero K] (k : ℕ)

local notation "n" => 2*k+1
local notation "A" => OnePlaneKoszul.Ring K n
local notation "Q" => OnePlaneKoszul.Residue K n
local notation "S" => SectionRing (onePlaneProjectiveGrading (K := K) k)
local notation "e" => onePlaneCompleteSectionRingEquiv (K := K) k
local notation "E" => ModuleCatRingEquivTor.scalarChange
  (AlgEquiv.toRingEquiv (onePlaneCompleteSectionRingEquiv (K := K) k))
local notation "X" => ModuleCat.of A Q

/-- The actual coefficient residue, with its scalar action changed
through the canonical complete-section algebra isomorphism. -/
abbrev coefficientModule : ModuleCat S := (E).obj X

def coefficientAugmentation : S →ₐ[K] K :=
  ((OnePlaneKoszul.residueEquivField K n).toAlgHom.comp
    (Ideal.Quotient.mkₐ K (OnePlaneKoszul.augmentationIdeal K n))).comp (e).symm.toAlgHom

/-- This is exactly the scalar action of the section algebra on its
coefficient residue, expressed in the original coefficient field. -/
theorem coefficientModule_smul (s : S) (q : coefficientModule (K := K) k) :
    OnePlaneKoszul.residueEquivField K n (s • q)=
      coefficientAugmentation (K := K) k s*OnePlaneKoszul.residueEquivField K n q := by
  have h := ModuleCatRingEquivTor.scalarChange_quotient_smul (e).toRingEquiv
    (OnePlaneKoszul.augmentationIdeal K n) s (show Q from q)
  have h' := congrArg (fun x : Q => OnePlaneKoszul.residueEquivField K n x) h
  exact h'.trans (by rw [map_mul]; rfl)

/-- The actual coefficient module is isomorphic to the original field,
with the action specified in coefficientModule_smul. -/
def coefficientFieldEquiv :
    ((ModuleCat.restrictScalars (algebraMap K S)).obj (coefficientModule (K := K) k)) ≃ₗ[K] K :=
  (ModuleCatRingEquivTor.coefficientsIso e X).toLinearEquiv.symm.trans
    ((ModuleCatRingEquivTor.nativeScalarsEquiv (R := K) (T := A) Q).trans
      (OnePlaneKoszul.residueEquivField K n).toLinearEquiv)

/-- The actual variable resolution, now a projective resolution over
the actual complete section algebra. -/
def resolution : ProjectiveResolution (coefficientModule (K := K) k) :=
  ModuleCatRingEquivTor.resolution (e).toRingEquiv (OnePlaneKoszul.resolution K n)

def tensorComplex : ChainComplex (ModuleCat S) ℕ :=
  (((tensoringLeft (ModuleCat S)).obj (coefficientModule k)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (resolution (K := K) k).complex

/-- The genuine tensor differential vanishes, as proved in the original
variable resolution and transported through the actual tensor comparison. -/
theorem tensorComplex_d (i j : ℕ) : (tensorComplex (K := K) k).d i j=0 := by
  exact ModuleCatRingEquivTor.resolutionTensor_d_eq_zero (e).toRingEquiv X X
    (OnePlaneKoszul.resolution K n) (OnePlaneKoszul.residueTensorComplex_d K n) i j

def tensorHomologyIso (r : ℕ) :
    (tensorComplex (K := K) k).homology r ≅ (tensorComplex (K := K) k).X r :=
  ModuleCatRingEquivTor.homologyIsoOfZeroDifferentials (tensorComplex (K := K) k)
    (tensorComplex_d (K := K) k) r

abbrev freeTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K S)).obj ((resolution (K := K) k).complex.X r)

abbrev tensorTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K S)).obj ((tensorComplex (K := K) k).X r)

/-- This is the identity on the original coefficient vectors, with the
proved compatible original-field scalar action. -/
def freeTermIso (r : ℕ) :
    OnePlaneKoszul.freeTermOverK K n r ≅ freeTermOverK (K := K) k r :=
  ModuleCatRingEquivTor.coefficientsIso e ((OnePlaneKoszul.complex K n).X r)

def tensorTermIso (r : ℕ) :
    tensorTermOverK (K := K) k r ≅ OnePlaneKoszul.tensorTermOverK K n r :=
  ModuleCatRingEquivTor.tensorIsoOverCoefficients e X ((OnePlaneKoszul.complex K n).X r)

def freeGrading (r : ℕ) : TauCeti.InternalGrading K (freeTermOverK (K := K) k r) ℕ :=
  (OnePlaneKoszul.freeGrading K n r).map (freeTermIso k r).toLinearEquiv

/-- The actual changed free basis uses the corresponding original
coefficient monomial as a literal homogeneous global section. -/
theorem freeMonomial_image (r : ℕ) (d : Fin n →₀ ℕ)
    (I : Set.powersetCard (Fin n) r) :
    (freeTermIso (K := K) k r).hom (OnePlaneKoszul.freeMonomialBasis K n r (d,I))=
      e (OnePlaneKoszul.coordinateMonomial K n d) •
        (freeTermIso k r).hom (OnePlaneKoszul.freeBasis K n r I) := by
  rw [OnePlaneKoszul.freeMonomialBasis_apply]
  change OnePlaneKoszul.coordinateMonomial K n d • OnePlaneKoszul.freeBasis K n r I=
    (e).symm (e (OnePlaneKoszul.coordinateMonomial K n d)) • OnePlaneKoszul.freeBasis K n r I
  rw [(e).symm_apply_apply]

/-- Coefficient monomials really belong to the original homogeneous
pieces used to form the actual complete section ring. -/
theorem coordinateMonomial_mem_original_degree (d : Fin n →₀ ℕ) :
    OnePlaneKoszul.coordinateMonomial K n d∈onePlaneProjectiveGrading (K := K) k d.degree := by
  change OnePlaneKoszul.coordinateMonomial K n d∈HomogeneousQuotientProjective.grading _ _ _
  rw [HomogeneousQuotientProjective.grading_eq_piece]
  simpa only [OnePlaneKoszul.coordinateBasis_apply,OnePlaneKoszul.originalDegree] using
    OnePlaneKoszul.coordinateBasis_mem_originalDegree K n d

def differentialOverK (r : ℕ) :
    freeTermOverK (K := K) k (r+1) →ₗ[K] freeTermOverK (K := K) k r :=
  ((ModuleCat.restrictScalars (algebraMap K S)).map
    ((resolution (K := K) k).complex.d (r+1) r)).hom

/-- The changed actual free resolution still preserves its original
internal degree in every homological degree. -/
theorem differentialOverK_homogeneous (r N : ℕ)
    (z : freeTermOverK (K := K) k (r+1))
    (hz : z∈(freeGrading k (r+1)).piece N) :
    differentialOverK k r z∈(freeGrading k r).piece N := by
  rw [freeGrading,TauCeti.InternalGrading.map_piece] at hz ⊢
  obtain ⟨w,hw,rfl⟩ := hz
  refine ⟨OnePlaneKoszul.differentialOverK K n r w,
    OnePlaneKoszul.differentialOverK_homogeneous K n r N w hw,?_⟩
  rfl

/-- Tensoring an actual free vector with the unit of the actual
coefficient residue, over the complete section algebra. -/
def specializeFree (r : ℕ) :
    freeTermOverK (K := K) k r →ₗ[K] tensorTermOverK (K := K) k r :=
  ((ModuleCat.restrictScalars (algebraMap K S)).map
    (ModuleCatRingEquivTor.tensorWithVector (coefficientModule (K := K) k)
      ((resolution (K := K) k).complex.X r)
      (show coefficientModule (K := K) k from (1 : Q)))).hom

theorem specializeFree_natural (r : ℕ) (z : OnePlaneKoszul.freeTermOverK K n r) :
    (tensorTermIso (K := K) k r).hom
        (specializeFree k r ((freeTermIso k r).hom z))=
      OnePlaneKoszul.specializeFree K n r z :=
  ModuleCatRingEquivTor.tensorIsoOverCoefficients_hom_tmul e X
    ((OnePlaneKoszul.complex K n).X r) (1 : Q) z

/-- The internal pieces are literal images of the homogeneous parts of
the actual changed free resolution. -/
def tensorDegreePiece (r N : ℕ) : Submodule K (tensorTermOverK (K := K) k r) :=
  ((freeGrading k r).piece N).map (specializeFree k r)

theorem map_tensorDegreePiece (r N : ℕ) :
    (tensorDegreePiece (K := K) k r N).map (tensorTermIso k r).hom.hom=
      OnePlaneKoszul.tensorDegreePiece K n r N := by
  unfold tensorDegreePiece freeGrading
  rw [TauCeti.InternalGrading.map_piece,←Submodule.map_comp,←Submodule.map_comp]
  change ((OnePlaneKoszul.freeGrading K n r).piece N).map _=
    ((OnePlaneKoszul.freeGrading K n r).piece N).map _
  congr 1

theorem tensorDegreePiece_eq (r N : ℕ) :
    tensorDegreePiece (K := K) k r N=if N=r then ⊤ else ⊥ := by
  apply Submodule.map_injective_of_injective
    (f := (tensorTermIso k r).hom.hom) (tensorTermIso k r).toLinearEquiv.injective
  rw [map_tensorDegreePiece,OnePlaneKoszul.tensorDegreePiece_eq]
  by_cases h : N=r
  · simp only [if_pos h,Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr (tensorTermIso k r).toLinearEquiv.surjective).symm
  · simp only [if_neg h,Submodule.map_bot]

/-- Actual ordinary Tor over the actual complete section algebra. -/
def TorOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K S)).obj
    (((Tor (ModuleCat S) r).obj (coefficientModule k)).obj (coefficientModule k))

/-- The actual changed resolution computes this actual derived Tor. -/
def torTermIso (r : ℕ) : TorOverK (K := K) k r ≅ tensorTermOverK (K := K) k r :=
  (ModuleCat.restrictScalars (algebraMap K S)).mapIso
    ((resolution k).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat S)).obj (coefficientModule k)) r ≪≫
        tensorHomologyIso k r)

/-- The ordinary Tor internal pieces come from the actual tensor images
above, using the actual derived-functor comparison. -/
def torInternalPiece (r N : ℕ) : Submodule K (TorOverK (K := K) k r) :=
  (tensorDegreePiece k r N).map (torTermIso k r).inv.hom

/-- Every homological and internal degree of the one-plane complete
section ring satisfies the usual homological Koszul concentration. -/
theorem actual_section_Tor_internal_degree (r N : ℕ) :
    torInternalPiece (K := K) k r N=if N=r then ⊤ else ⊥ := by
  rw [torInternalPiece,tensorDegreePiece_eq]
  by_cases h : N=r
  · simp only [if_pos h,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (torTermIso k r).toLinearEquiv.symm.surjective
  · simp only [if_neg h,Submodule.map_bot]

theorem torInternalPieces_iSup (r : ℕ) :
    (⨆ N,torInternalPiece (K := K) k r N)=⊤ := by
  apply top_unique
  have hd : torInternalPiece (K := K) k r r=⊤ := by
    simpa only [if_true] using actual_section_Tor_internal_degree (K := K) k r r
  rw [←hd]
  exact le_iSup (fun N ↦ torInternalPiece (K := K) k r N) r

end PaperVerification.AlternatingForms.OnePlaneSectionKoszul
