module

public import Recovery.Unimodular.KoszulSupport.PaperVerification.NoncommutativeBarResolution
public import Recovery.Unimodular.KoszulSupport.PaperVerification.AugmentationBalancedTensor
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Ordinary noncommutative augmentation Tor and its reduced bar complex

Tensoring the explicit free resolution with the augmentation residue kills
the first multiplication term. The surviving differential is exactly the
negative adjacent-product differential in the original positive basis.
The comparison is an isomorphism of actual chain complexes.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct

namespace PaperVerification.NoncommutativeBar

open CategoryTheory CategoryTheory.Limits
open PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [CommRing K] [Ring A] [Algebra K A]
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

/-- The actual free module in bar degree `r`. -/
abbrev freeObject (r : ℕ) : ModuleCat.{u} A := ModuleCat.of A (lengthPiece I A r)

/-- Identity on elements, with a proof that the inherited scalar action
agrees with the categorical restriction-of-scalars action. -/
def freeGroundEquiv (r : ℕ) : lengthPiece I A r ≃ₗ[K]
    AugmentationCoinvariants.baseObject (K := K) (freeObject (I := I) (A := A) r) where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c z := by
    change c • z=(algebraMap K A c) • z
    exact (IsScalarTower.algebraMap_smul A c z).symm

def liftPiece (r : ℕ) : lengthPiece I K r →ₗ[K] lengthPiece I A r where
  toFun z := ⟨lift z.val,lift_mem_lengthPiece (A := A) z.val z.property⟩
  map_add' z w := Subtype.ext (map_add (lift (A := A)) z.val w.val)
  map_smul' c z := Subtype.ext (map_smul (lift (A := A)) c z.val)

@[simp] theorem specializePiece_smul (r : ℕ) (a : A) (z : lengthPiece I A r) :
    specializePiece ε r (a • z)=ε a • specializePiece ε r z := by
  apply Subtype.ext
  exact specialize_smul ε a z.val

/-- Specialization kills exactly the augmentation relations needed to
factor through actual coinvariants of the actual free bar module. -/
def coinvariantToReduced (r : ℕ) :
    AugmentationCoinvariants.object ε (freeObject (I := I) (A := A) r) →ₗ[K]
      lengthPiece I K r := by
  change ((AugmentationCoinvariants.baseObject (K := K) (freeObject (I := I) (A := A) r)) ⧸
    AugmentationCoinvariants.relations ε (freeObject (I := I) (A := A) r)) →ₗ[K]
      lengthPiece I K r
  let F : AugmentationCoinvariants.baseObject (K := K)
      (freeObject (I := I) (A := A) r) →ₗ[K] lengthPiece I K r :=
    (specializePiece ε r).comp
      (freeGroundEquiv (K := K) (A := A) (I := I) r).symm.toLinearMap
  refine (AugmentationCoinvariants.relations ε (freeObject (I := I) (A := A) r)).liftQ
    (R₂ := K) (M₂ := ↥(lengthPiece I K r)) (τ₁₂ := RingHom.id K) F ?_
  apply Submodule.span_le.mpr
  rintro z ⟨a,ha,m,rfl⟩
  change specializePiece ε r (a • m)=0
  rw [specializePiece_smul,ha,zero_smul]

@[simp] theorem coinvariantToReduced_quotient (r : ℕ) (z : lengthPiece I A r) :
    coinvariantToReduced ε r
      (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r) z)=
        specializePiece ε r z := rfl

def reducedToCoinvariant (r : ℕ) : lengthPiece I K r →ₗ[K]
    AugmentationCoinvariants.object ε (freeObject (I := I) (A := A) r) :=
  (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)).comp
    ((freeGroundEquiv (K := K) (A := A) (I := I) r).toLinearMap.comp
      (liftPiece (K := K) (A := A) (I := I) r))

theorem reduced_coinvariant_inverse (r : ℕ) (z : lengthPiece I K r) :
    coinvariantToReduced ε r (reducedToCoinvariant ε r z)=z := by
  apply Subtype.ext
  exact specialize_lift ε z.val

theorem coinvariant_specialize_inverse (r : ℕ) (z : Words I A)
    (hz : z∈lengthPiece I A r) :
    reducedToCoinvariant ε r (specializePiece ε r ⟨z,hz⟩)=
      AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r) ⟨z,hz⟩ := by
  have hs : z∈Submodule.span A
      ((fun L : List I ↦ Finsupp.single L (1 : A)) '' {L | L.length=r}) := by
    rwa [←lengthPiece_eq_span]
  revert hz
  induction hs using Submodule.span_induction with
  | mem z hz =>
      rintro hmem
      obtain ⟨L,hL,rfl⟩ := hz
      change AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)
        ⟨lift (specialize ε (Finsupp.single L 1)),_⟩=
          AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)
            ⟨Finsupp.single L 1,_⟩
      congr 1
      apply Subtype.ext
      change lift (specialize ε (Finsupp.single L 1))=Finsupp.single L 1
      rw [specialize_single,map_one,lift_single,one_smul]
  | zero =>
      intro hz
      change reducedToCoinvariant ε r (specializePiece ε r 0)=
        AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r) 0
      rw [map_zero,map_zero,map_zero]
  | add z w hz hw ihz ihw =>
      intro hsum
      have hz' : z∈lengthPiece I A r := by rwa [lengthPiece_eq_span]
      have hw' : w∈lengthPiece I A r := by rwa [lengthPiece_eq_span]
      change reducedToCoinvariant ε r (specializePiece ε r (⟨z,hz'⟩+⟨w,hw'⟩))=
        AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)
          (⟨z,hz'⟩+⟨w,hw'⟩)
      rw [map_add,map_add,map_add,ihz hz',ihw hw']
  | smul a z hz ih =>
      intro hsmul
      have hz' : z∈lengthPiece I A r := by rwa [lengthPiece_eq_span]
      change reducedToCoinvariant ε r (specializePiece ε r (a • ⟨z,hz'⟩))=
        AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r) (a • ⟨z,hz'⟩)
      rw [specializePiece_smul,map_smul,ih hz',AugmentationCoinvariants.quotient_smul]

def coinvariantTermEquiv (r : ℕ) :
    AugmentationCoinvariants.object ε (freeObject (I := I) (A := A) r) ≃ₗ[K]
      lengthPiece I K r :=
  LinearEquiv.ofLinearMap (coinvariantToReduced ε r) (reducedToCoinvariant ε r)
    (by
      apply LinearMap.ext
      intro z
      exact reduced_coinvariant_inverse ε r z)
    (by
      apply LinearMap.ext
      intro z
      refine Quotient.inductionOn' z ?_
      intro x
      exact coinvariant_specialize_inverse ε r x.val x.property)

@[simp] theorem coinvariantTermEquiv_quotient (r : ℕ) (z : lengthPiece I A r) :
    coinvariantTermEquiv ε r
      (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r) z)=
        specializePiece ε r z := rfl

def coinvariantComplex : ChainComplex (ModuleCat K) ℕ :=
  ((AugmentationCoinvariants.functor ε).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (resolution ε B hunit hε).complex

include hunit hε in
@[simp] theorem coinvariantComplex_d_quotient (r : ℕ) (z : lengthPiece I A (r+1)) :
    (coinvariantComplex ε B hunit hε).d (r+1) r
      (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) (r+1)) z)=
        AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)
          (degreeDifferential B r z) := by
  simp only [coinvariantComplex,Functor.mapHomologicalComplex_obj_d,resolution,
    complex_d,AugmentationCoinvariants.map_quotient,ModuleCat.ofHom_apply]
  rfl

include hunit hε in
theorem coinvariantTermEquiv_comm (r : ℕ) :
    (coinvariantTermEquiv ε (r+1)).toModuleIso.hom ≫
        (reducedComplex ε B hunit hε).d (r+1) r=
      (coinvariantComplex ε B hunit hε).d (r+1) r ≫
        (coinvariantTermEquiv ε r).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  change (reducedComplex ε B hunit hε).d (r+1) r
      (coinvariantTermEquiv ε (r+1)
        (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) (r+1)) x))=
    coinvariantTermEquiv ε r ((coinvariantComplex ε B hunit hε).d (r+1) r
      (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) (r+1)) x))
  rw [coinvariantComplex_d_quotient,reducedComplex_d]
  change -(reducedDegreeDifferential B r
      (coinvariantTermEquiv ε (r+1)
        (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) (r+1)) x)))=
    coinvariantTermEquiv ε r
      (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)
        (degreeDifferential B r x))
  rw [coinvariantTermEquiv_quotient,coinvariantTermEquiv_quotient]
  apply Subtype.ext
  exact (specialize_differential ε B hε x.val).symm

def coinvariantComplexIso : coinvariantComplex ε B hunit hε ≅ reducedComplex ε B hunit hε :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦ (coinvariantTermEquiv ε r).toModuleIso) (by
      intro i j hij
      change j+1=i at hij
      subst i
      exact coinvariantTermEquiv_comm ε B hunit hε j)

/-- The augmentation residue really is the coefficient module with the
left action through the original augmentation. -/
def residueAugmentationEquiv :
    Residue ε ≃ₗ[A] AugmentationCoinvariants.augmentationModule ε where
  toFun := residueEquivCoefficients ε
  invFun := (residueEquivCoefficients ε).symm
  left_inv := (residueEquivCoefficients ε).left_inv
  right_inv := (residueEquivCoefficients ε).right_inv
  map_add' := (residueEquivCoefficients ε).map_add
  map_smul' a q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change ε (a*x)=ε a*ε x
    exact map_mul ε a x

/-- Actual ordinary augmentation Tor, computed by the actual adjacent-product
complex.  Ordinary augmentation tensoring is independently identified with
the balanced tensor product by `AugmentationCoinvariants.balancedEquiv`. -/
def ordinaryTorReducedBarIso (r : ℕ) :
    AugmentationCoinvariants.augmentationTor ε r ≅
      (reducedComplex ε B hunit hε).homology r :=
  ((AugmentationCoinvariants.derived ε r).mapIso
      (residueAugmentationEquiv ε).toModuleIso).symm ≪≫
    derivedCoinvariantsIso ε B hunit hε r ≪≫
      HomologicalComplex.homologyMapIso (coinvariantComplexIso ε B hunit hε) r

end PaperVerification.NoncommutativeBar
