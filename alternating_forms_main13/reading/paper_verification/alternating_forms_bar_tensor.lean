module

public import PaperVerification.AlternatingFormsBarResolution
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# The actual Tor complex and the normalized reduced bar complex

Tensoring the explicit free resolution with the augmentation residue kills
the first multiplication term. The surviving differential is exactly the
negative adjacent-product differential in the original positive basis.
The comparison is an isomorphism of actual chain complexes.
-/

@[expose] public section
noncomputable section
open scoped BigOperators TensorProduct

namespace PaperVerification.AlternatingForms.BarFree

open CategoryTheory CategoryTheory.Limits
open PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [CommRing K] [CommRing A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

def specialize : Words I A →ₗ[K] Words I K :=
  Finsupp.mapRange.linearMap ε.toLinearMap

@[simp] theorem specialize_apply (z : Words I A) (L : List I) :
    specialize ε z L=ε (z L) := rfl

@[simp] theorem specialize_single (L : List I) (a : A) :
    specialize ε (Finsupp.single L a)=Finsupp.single L (ε a) := by
  classical
  ext T
  by_cases h : L=T <;> simp [specialize_apply,Finsupp.single_apply,h]

theorem specialize_smul (a : A) (z : Words I A) :
    specialize ε (a • z)=ε a • specialize ε z := by
  ext L
  simp only [specialize_apply,Finsupp.smul_apply,smul_eq_mul,map_mul]

theorem specialize_lift (z : Words I K) : specialize ε (lift z)=z := by
  ext L
  rw [specialize_apply,lift_apply,ε.commutes]
  rfl

include hε in
theorem specialize_front (z : Words I A) : specialize ε (front B z)=0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw,add_zero]
  | single L a =>
    cases L with
    | nil => simp only [front_single,frontBasis,smul_zero,map_zero]
    | cons i L =>
      rw [front_single,specialize_smul]
      change ε a • specialize ε (Finsupp.single L (B (some i)))=0
      rw [specialize_single,hε,Finsupp.single_zero,smul_zero]

theorem specialize_internal (z : Words I A) :
    specialize ε (internal B z)=
      PaperVerification.ReducedBarBasis.differential B (specialize ε z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw]
  | single L a =>
    rw [internal_single,specialize_smul,specialize_lift,specialize_single,
      PaperVerification.ReducedBarBasis.differential_single]

include hε in
theorem specialize_differential (z : Words I A) :
    specialize ε (differential B z)=
      -PaperVerification.ReducedBarBasis.differential B (specialize ε z) := by
  change specialize ε (front B z-internal B z)=_
  rw [map_sub,specialize_front ε B hε,specialize_internal,zero_sub]

theorem specialize_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A r) : specialize ε z∈lengthPiece I K r := by
  rw [mem_lengthPiece_iff] at hz ⊢
  intro L hL
  rw [specialize_apply,hz L hL,map_zero]

def specializePiece (r : ℕ) : lengthPiece I A r →ₗ[K] lengthPiece I K r :=
  LinearMap.codRestrict _
    ((specialize ε).comp ((lengthPiece I A r).subtype.restrictScalars K))
    (fun z ↦ specialize_mem_lengthPiece ε z.val z.property)

theorem reducedDifferential_mem_lengthPiece {r : ℕ} (z : Words I K)
    (hz : z∈lengthPiece I K (r+1)) :
    PaperVerification.ReducedBarBasis.differential B z∈lengthPiece I K r := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r+1 at hL
    rw [PaperVerification.ReducedBarBasis.differential_single,one_smul]
    simpa only [hL,Nat.add_sub_cancel] using reducedDifferentialBasis_mem_lengthPiece B L
  | zero => simpa only [map_zero] using (lengthPiece I K r).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I K r).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I K r).smul_mem a ih

def reducedDegreeDifferential (r : ℕ) :
    lengthPiece I K (r+1) →ₗ[K] lengthPiece I K r :=
  LinearMap.codRestrict _
    ((PaperVerification.ReducedBarBasis.differential B).comp
      (lengthPiece I K (r+1)).subtype)
    (fun z ↦ reducedDifferential_mem_lengthPiece B z.val z.property)

/-- The literal pointwise negative of the actual adjacent-product map.
Its formula is stated explicitly, so the construction does not depend
on inferring a second additive-group dictionary for a space of maps. -/
def negativeReducedDegreeDifferential (r : ℕ) :
    lengthPiece I K (r+1) →ₗ[K] lengthPiece I K r where
  toFun z := ⟨-(PaperVerification.ReducedBarBasis.differential B z.val),
    (lengthPiece I K r).neg_mem
      (reducedDifferential_mem_lengthPiece B z.val z.property)⟩
  map_add' x y := by
    apply Subtype.ext
    change -(PaperVerification.ReducedBarBasis.differential B (x.val+y.val))=
      -(PaperVerification.ReducedBarBasis.differential B x.val)+
        -(PaperVerification.ReducedBarBasis.differential B y.val)
    rw [map_add,neg_add]
  map_smul' c z := by
    apply Subtype.ext
    change -(PaperVerification.ReducedBarBasis.differential B (c • z.val))=
      c • -(PaperVerification.ReducedBarBasis.differential B z.val)
    rw [map_smul,smul_neg]

@[simp] theorem negativeReducedDegreeDifferential_apply (r : ℕ)
    (z : lengthPiece I K (r+1)) :
    negativeReducedDegreeDifferential B r z=-(reducedDegreeDifferential B r z) := rfl

include hunit hε in
theorem negativeReducedDifferential_comp (r : ℕ) :
    (negativeReducedDegreeDifferential B r).comp (negativeReducedDegreeDifferential B (r+1))=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change -PaperVerification.ReducedBarBasis.differential B
    (-PaperVerification.ReducedBarBasis.differential B z.val)=0
  rw [map_neg,neg_neg,PaperVerification.ReducedBarBasis.differential_squared ε B hunit hε]

def reducedComplex : ChainComplex (ModuleCat K) ℕ :=
  ChainComplex.of (fun r ↦ ModuleCat.of K (lengthPiece I K r))
    (fun r ↦ ModuleCat.ofHom (negativeReducedDegreeDifferential B r))
    (fun r ↦ ModuleCat.hom_ext (negativeReducedDifferential_comp ε B hunit hε r))

include hunit hε in
@[simp] theorem reducedComplex_d (r : ℕ) :
    (reducedComplex ε B hunit hε).d (r+1) r=
      ModuleCat.ofHom (negativeReducedDegreeDifferential B r) := by
  simp [reducedComplex]

def tensorComplex : ChainComplex (ModuleCat A) ℕ :=
  (((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat A)).obj
    (ModuleCat.of A (Residue ε))).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (resolution ε B hunit hε).complex

def tensorComplexOverK : ChainComplex (ModuleCat K) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap K A)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (tensorComplex ε B hunit hε)

include hunit hε in
/-- The tensor differential on a pure tensor, reduced through the actual
functorial complex before any comparison of coefficient bases. -/
@[simp] theorem tensorComplexOverK_d_tmul (r : ℕ) (q : Residue ε)
    (z : lengthPiece I A (r+1)) :
    (tensorComplexOverK ε B hunit hε).d (r+1) r (q ⊗ₜ[A] z)=
      q ⊗ₜ[A] degreeDifferential B r z := by
  simp only [tensorComplexOverK,tensorComplex,Functor.mapHomologicalComplex_obj_d,
    resolution,complex_d,ModuleCat.restrictScalars.map_apply,
    CategoryTheory.MonoidalCategory.curriedTensor_obj_map,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,ModuleCat.ofHom_apply]
  rfl

def tensorTermAlgebraEquiv (r : ℕ) :
    (Residue ε ⊗[A] lengthPiece I A r) ≃ₗ[A]
      ({L : List I // L.length=r} →₀ Residue ε) := by
  classical
  exact (TensorProduct.congr (LinearEquiv.refl A (Residue ε))
    (Finsupp.supportedEquivFinsupp (M := A) (R := A) {L : List I | L.length=r})).trans
      (TensorProduct.finsuppScalarRight A A (Residue ε) {L : List I // L.length=r})

set_option backward.isDefEq.respectTransparency false in
def restrictTensorDomainEquiv {X Y : Type u} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] [Module K Y] [IsScalarTower K A Y]
    (e : X ≃ₗ[A] Y) :
    ((ModuleCat.restrictScalars (algebraMap K A)).obj (ModuleCat.of A X)) ≃ₗ[K] Y where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' c x := by
    exact (e.map_smul (algebraMap K A c) (show X from x)).trans
      (algebraMap_smul A c (e (show X from x)))

def tensorTermEquiv (r : ℕ) :
    (tensorComplexOverK ε B hunit hε).X r ≃ₗ[K] lengthPiece I K r :=
  (restrictTensorDomainEquiv (tensorTermAlgebraEquiv (I := I) ε r)).trans
    ((Finsupp.mapRange.linearEquiv (residueEquivCoefficients ε).toLinearEquiv).trans
      (Finsupp.supportedEquivFinsupp (M := K) (R := K) {L : List I | L.length=r}).symm)

@[simp] theorem residueEquivCoefficients_mk (a : A) :
    residueEquivCoefficients ε (Ideal.Quotient.mk (residueIdeal ε) a)=ε a :=
  Ideal.quotientKerAlgEquivOfSurjective_mk (augmentation_surjective ε) a

theorem residueEquivCoefficients_smul (a : A) (q : Residue ε) :
    residueEquivCoefficients ε (a • q)=ε a * residueEquivCoefficients ε q := by
  change residueEquivCoefficients ε
    (Ideal.Quotient.mk (residueIdeal ε) a*q)=_
  rw [map_mul,residueEquivCoefficients_mk]

set_option backward.isDefEq.respectTransparency false in
include hunit hε in
theorem tensorTermEquiv_coordinate (r : ℕ) (q : Residue ε)
    (z : lengthPiece I A r) (L : {L : List I // L.length=r}) :
    (Finsupp.supportedEquivFinsupp (M := K) (R := K) {L : List I | L.length=r})
      (tensorTermEquiv ε B hunit hε r (q ⊗ₜ[A] z)) L=
        ε (z.val L.val) * residueEquivCoefficients ε q := by
  classical
  simp only [tensorTermEquiv,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
    Finsupp.mapRange.linearEquiv_apply,Finsupp.mapRange_apply]
  erw [LinearEquiv.apply_symm_apply]
  simp only [Finsupp.mapRange_apply]
  change residueEquivCoefficients ε (tensorTermAlgebraEquiv ε r (q ⊗ₜ[A] z) L)=_
  have h : tensorTermAlgebraEquiv ε r (q ⊗ₜ[A] z) L=z.val L.val • q := by
    exact TensorProduct.finsuppScalarRight_apply_tmul_apply (R := A) (S := A) q
      ((Finsupp.supportedEquivFinsupp (M := A) (R := A)
        {L : List I | L.length=r})
          (show Finsupp.supported A A {L : List I | L.length=r} from z)) L
  rw [h,residueEquivCoefficients_smul]

set_option backward.isDefEq.respectTransparency false in
include hunit hε in
theorem tensorTermEquiv_tmul (r : ℕ) (q : Residue ε) (z : lengthPiece I A r) :
    tensorTermEquiv ε B hunit hε r (q ⊗ₜ[A] z)=
      residueEquivCoefficients ε q • specializePiece ε r z := by
  apply (Finsupp.supportedEquivFinsupp (M := K) (R := K)
    {L : List I | L.length=r}).injective
  ext L
  rw [tensorTermEquiv_coordinate]
  change ε (z.val L.val)*residueEquivCoefficients ε q=
    residueEquivCoefficients ε q*ε (z.val L.val)
  exact mul_comm _ _

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
include hunit hε in
theorem tensorTermEquiv_comm (r : ℕ) :
    (tensorTermEquiv ε B hunit hε (r+1)).toModuleIso.hom ≫
        (reducedComplex ε B hunit hε).d (r+1) r =
      (tensorComplexOverK ε B hunit hε).d (r+1) r ≫
        (tensorTermEquiv ε B hunit hε r).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro q x
    simp only [ModuleCat.hom_comp,LinearMap.comp_apply,ModuleCat.comp_apply]
    rw [tensorComplexOverK_d_tmul,reducedComplex_d]
    change -(reducedDegreeDifferential B r
        (tensorTermEquiv ε B hunit hε (r+1) (q ⊗ₜ[A] x)))=
      tensorTermEquiv ε B hunit hε r (q ⊗ₜ[A] degreeDifferential B r x)
    rw [tensorTermEquiv_tmul,tensorTermEquiv_tmul,map_smul]
    apply Subtype.ext
    change -(residueEquivCoefficients ε q •
      PaperVerification.ReducedBarBasis.differential B (specialize ε x.val))=
      residueEquivCoefficients ε q • specialize ε (differential B x.val)
    rw [specialize_differential ε B hε,smul_neg]
  · intro x y hx hy
    simp only [ModuleCat.comp_apply,ModuleCat.hom_comp,LinearMap.comp_apply,map_add] at hx hy ⊢
    exact congrArg₂ (· + ·) hx hy

def tensorComplexIso : tensorComplexOverK ε B hunit hε ≅ reducedComplex ε B hunit hε :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦ (tensorTermEquiv ε B hunit hε r).toModuleIso) (by
      intro i j hij
      change j+1=i at hij
      subst i
      exact tensorTermEquiv_comm ε B hunit hε j)

def tensorHomologyRestrictionIso (r : ℕ) :
    (tensorComplexOverK ε B hunit hε).homology r ≅
      (ModuleCat.restrictScalars (algebraMap K A)).obj
        ((tensorComplex ε B hunit hε).homology r) := by
  change (((tensorComplex ε B hunit hε).sc r).map
      (ModuleCat.restrictScalars (algebraMap K A))).homology ≅
    (ModuleCat.restrictScalars (algebraMap K A)).obj
      ((tensorComplex ε B hunit hε).sc r).homology
  exact ((tensorComplex ε B hunit hε).sc r).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap K A))

def TorOverCoefficients (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K A)).obj
    (((Tor (ModuleCat A) r).obj (ModuleCat.of A (Residue ε))).obj
      (ModuleCat.of A (Residue ε)))

/-- The normalized reduced bar homology is identified with actual Tor. -/
def reducedBarTorIso (r : ℕ) :
    TorOverCoefficients ε r ≅ (reducedComplex ε B hunit hε).homology r :=
  (ModuleCat.restrictScalars (algebraMap K A)).mapIso
      (torIso ε B hunit hε (ModuleCat.of A (Residue ε)) r) ≪≫
    (tensorHomologyRestrictionIso ε B hunit hε r).symm ≪≫
    HomologicalComplex.homologyMapIso (tensorComplexIso ε B hunit hε) r

end PaperVerification.AlternatingForms.BarFree
