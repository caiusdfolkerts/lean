module

public import PaperVerification.AlternatingFormsOnePlaneTor
public import PaperVerification.AlternatingFormsPolynomialTorGrading
public import PaperVerification.AlternatingFormsBasisDegree
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Weight

/-!
# Internal degrees on ordinary Tor of the one-plane quotient

The original degree-one Plucker classes are the variables under the
explicit polynomial isomorphism.  The free-term basis consists of their
literal monomials times exterior basis vectors, with degree `degree d+r`.
After tensoring the actual projective resolution, the degree pieces are
images of those original subspaces.  Positive coefficient monomials
vanish in the actual augmentation quotient, while the diagonal images
exhaust the term.  Transport through the actual derived-tensor
comparison then gives the usual internal-degree concentration.

All proof bodies in this reconstructed file are uncompiled in this run.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.AlternatingForms.OnePlaneKoszul

open MvPolynomial CategoryTheory CategoryTheory.Limits

universe u
variable (K : Type u) [Field K] (n : ℕ)

local notation "P" => Ring K n
local notation "Q" => Residue K n
local notation "J" => augmentationIdeal K n

abbrev freeTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj ((complex K n).X r)

abbrev tensorTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj ((residueTensorComplex K n).X r)

instance freeTerm_isScalarTower (r : ℕ) : IsScalarTower K P (freeTermOverK K n r) :=
  IsScalarTower.of_compHom K P ((complex K n).X r)

def freeBasis (r : ℕ) :
    Module.Basis (Set.powersetCard (Fin n) r) P (freeTermOverK K n r) :=
  (Pi.basisFun P (Fin n)).exteriorPower r

def coordinateMonomial (d : Fin n →₀ ℕ) : P :=
  (polynomialEquiv K n).symm (monomial d (1 : K))

theorem polynomialEquiv_symm_eq_coordinate_evaluation :
    (polynomialEquiv K n).symm.toAlgHom=aeval (generator K n) := by
  ext i
  change (polynomialEquiv K n).symm (X i)=aeval (generator K n) (X i)
  rw [polynomialEquiv_symm_X,aeval_X]

/-- The coefficient basis consists of literal monomials in the
original Plucker-coordinate classes. -/
theorem coordinateMonomial_eq_evaluation (d : Fin n →₀ ℕ) :
    coordinateMonomial K n d=aeval (generator K n) (monomial d (1 : K)) := by
  exact AlgHom.congr_fun (polynomialEquiv_symm_eq_coordinate_evaluation K n) _

def coordinateBasis : Module.Basis (Fin n →₀ ℕ) K P :=
  (MvPolynomial.basisMonomials (Fin n) K).map (polynomialEquiv K n).symm.toLinearEquiv

@[simp] theorem coordinateBasis_apply (d : Fin n →₀ ℕ) :
    coordinateBasis K n d=coordinateMonomial K n d := by
  rw [coordinateBasis,Module.Basis.map_apply,MvPolynomial.coe_basisMonomials]
  rfl

def freeMonomialBasis (r : ℕ) :
    Module.Basis ((Fin n →₀ ℕ) × Set.powersetCard (Fin n) r) K (freeTermOverK K n r) :=
  (coordinateBasis K n).smulTower (freeBasis K n r)

theorem freeMonomialBasis_apply (r : ℕ)
    (d : Fin n →₀ ℕ) (I : Set.powersetCard (Fin n) r) :
    freeMonomialBasis K n r (d,I)=coordinateMonomial K n d • freeBasis K n r I := by
  rw [freeMonomialBasis,Module.Basis.smulTower_apply,coordinateBasis_apply]

def freeGrading (r : ℕ) : TauCeti.InternalGrading K (freeTermOverK K n r) ℕ :=
  BasisDegree.grading (freeMonomialBasis K n r) (fun a ↦ a.1.degree+r)

def specializeFree (r : ℕ) : freeTermOverK K n r →ₗ[K] tensorTermOverK K n r :=
  ((ModuleCat.restrictScalars (algebraMap K P)).map
    (ModuleCat.ofHom (TensorProduct.mk P Q (⋀[P]^r (Fin n → P)) 1))).hom

theorem specializeFree_apply (r : ℕ) (z : freeTermOverK K n r) :
    specializeFree K n r z=1 ⊗ₜ[P] z := rfl

theorem augmentationIdeal_map :
    (augmentationIdeal K n).map (polynomialEquiv K n).toRingHom=
      Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) K)) := by
  rw [augmentationIdeal,Ideal.map_span,←Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext i
  exact polynomialEquiv_generator K n i

def polynomialResidueEquiv : Q ≃ₐ[K] PolynomialKoszul.Residue K n :=
  Ideal.quotientEquivAlg _ _ (polynomialEquiv K n) (augmentationIdeal_map K n).symm

/-- The residue of the original one-plane quotient is explicitly the
coefficient field, with all original degree-one coordinates acting as zero. -/
def residueEquivField : Q ≃ₐ[K] K :=
  (polynomialResidueEquiv K n).trans (PolynomialKoszul.residueEquivField K n)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem residueEquivField_mk (p : P) :
    residueEquivField K n (Ideal.Quotient.mk J p)=
      MvPolynomial.constantCoeff (polynomialEquiv K n p) := by
  rw [residueEquivField,AlgEquiv.trans_apply,polynomialResidueEquiv,
    Ideal.quotientEquivAlg_mk,PolynomialKoszul.residueEquivField_mk]

theorem monomial_mem_augmentationIdeal {d : Fin n →₀ ℕ} (hd : d≠0) :
    coordinateMonomial K n d∈J := by
  change (polynomialEquiv K n).symm (monomial d (1 : K))∈J
  change (polynomialEquiv K n).toRingEquiv.symm (monomial d (1 : K))∈J
  rw [Ideal.symm_apply_mem_of_equiv_iff]
  change (monomial d (1 : K) : MvPolynomial (Fin n) K) ∈
    Ideal.map (polynomialEquiv K n).toRingHom (augmentationIdeal K n)
  rw [augmentationIdeal_map]
  exact PolynomialKoszul.monomial_mem_coordinateIdeal K n hd

theorem specializeFree_monomial_ne_zero (r : ℕ) (d : Fin n →₀ ℕ)
    (I : Set.powersetCard (Fin n) r) (hd : d≠0) :
    specializeFree K n r (freeMonomialBasis K n r (d,I))=0 := by
  rw [freeMonomialBasis_apply,specializeFree_apply,TensorProduct.tmul_smul,
    TensorProduct.smul_tmul',residue_smul_eq_zero K n _
      (monomial_mem_augmentationIdeal K n hd),TensorProduct.zero_tmul]
  rfl

def tensorDegreePiece (r N : ℕ) : Submodule K (tensorTermOverK K n r) :=
  ((freeGrading K n r).piece N).map (specializeFree K n r)

theorem tensorDegreePiece_eq_bot (r N : ℕ) (hNr : N≠r) :
    tensorDegreePiece K n r N=⊥ := by
  apply le_antisymm ?_ bot_le
  rintro z ⟨w,hw,rfl⟩
  change specializeFree K n r w=0
  change w∈BasisDegree.piece (freeMonomialBasis K n r) (fun a ↦ a.1.degree+r) N at hw
  rw [BasisDegree.piece_eq_span] at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨d,I⟩,hd,rfl⟩ := hw
    apply specializeFree_monomial_ne_zero K n r d I
    intro hz
    subst d
    simp only [map_zero,zero_add,Set.mem_setOf_eq] at hd
    exact hNr hd.symm
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul c x hx ih => rw [map_smul,ih,smul_zero]

set_option backward.isDefEq.respectTransparency false in
theorem specializeFree_surjective (r : ℕ) : Function.Surjective (specializeFree K n r) := by
  intro z
  change Q ⊗[P] (⋀[P]^r (Fin n → P)) at z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a w
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨(p • w : ⋀[P]^r (Fin n → P)),?_⟩
    change (1 : Q) ⊗ₜ[P] (p • w)=Ideal.Quotient.mk J p ⊗ₜ[P] w
    calc
      _ = (p • (1 : Q)) ⊗ₜ[P] w := (TensorProduct.smul_tmul p (1 : Q) w).symm
      _ = _ := congrArg (fun a : Q => a ⊗ₜ[P] w)
        (show p • (1 : Q)=Ideal.Quotient.mk J p from by
          change Ideal.Quotient.mk J p * (1 : Q)=Ideal.Quotient.mk J p
          exact mul_one (Ideal.Quotient.mk J p))
  · intro x y hx hy
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    exact ⟨u+v,map_add _ _ _⟩

theorem tensorDegreePieces_iSup (r : ℕ) : (⨆ N,tensorDegreePiece K n r N)=⊤ := by
  simp only [tensorDegreePiece]
  rw [←Submodule.map_iSup,(freeGrading K n r).isInternal.submodule_iSup_eq_top,
    Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (specializeFree_surjective K n r)

theorem tensorDegreePiece_diagonal (r : ℕ) : tensorDegreePiece K n r r=⊤ := by
  have hle : (⨆ N,tensorDegreePiece K n r N)≤tensorDegreePiece K n r r := by
    apply iSup_le
    intro N
    by_cases h : N=r
    · subst N; exact le_rfl
    · rw [tensorDegreePiece_eq_bot K n r N h]
      exact bot_le
  rw [tensorDegreePieces_iSup] at hle
  exact top_unique hle

theorem tensorDegreePiece_eq (r N : ℕ) :
    tensorDegreePiece K n r N=if N=r then ⊤ else ⊥ := by
  by_cases h : N=r
  · subst N; rw [if_pos rfl,tensorDegreePiece_diagonal]
  · rw [if_neg h,tensorDegreePiece_eq_bot K n r N h]

/-- These are the images of the original free internal-degree pieces,
with their genuine direct-sum property proved from those images. -/
def tensorGrading (r : ℕ) : TauCeti.InternalGrading K (tensorTermOverK K n r) ℕ where
  piece := tensorDegreePiece K n r
  isInternal := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · intro N
      by_cases h : N=r
      · subst N
        have hz : (⨆ M≠r,tensorDegreePiece K n r M)=⊥ := by
          apply le_antisymm ?_ bot_le
          apply iSup_le
          intro M
          apply iSup_le
          intro hM
          rw [tensorDegreePiece_eq_bot K n r M hM]
        rw [hz]
        exact disjoint_bot_right
      · rw [tensorDegreePiece_eq_bot K n r N h]
        exact disjoint_bot_left
    · exact tensorDegreePieces_iSup K n r

def TorOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj
    (((Tor (ModuleCat P) r).obj (ModuleCat.of P Q)).obj (ModuleCat.of P Q))

def torTermIsoOverK (r : ℕ) : TorOverK K n r ≅ tensorTermOverK K n r :=
  (ModuleCat.restrictScalars (algebraMap K P)).mapIso (residueTorIso K n r)

def torGrading (r : ℕ) : TauCeti.InternalGrading K (TorOverK K n r) ℕ :=
  (tensorGrading K n r).map (torTermIsoOverK K n r).toLinearEquiv.symm

/-- Concentration of the actual polynomial Tor, with degree pieces
obtained from actual homogeneous monomial terms of the actual resolution. -/
theorem actual_onePlane_Tor_degree (r N : ℕ) :
    (torGrading K n r).piece N=if N=r then ⊤ else ⊥ := by
  rw [torGrading,TauCeti.InternalGrading.map_piece]
  change (tensorDegreePiece K n r N).map _=_
  rw [tensorDegreePiece_eq]
  by_cases h : N=r
  · simp only [if_pos h,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (torTermIsoOverK K n r).toLinearEquiv.symm.surjective
  · simp only [if_neg h,Submodule.map_bot]

end PaperVerification.AlternatingForms.OnePlaneKoszul
