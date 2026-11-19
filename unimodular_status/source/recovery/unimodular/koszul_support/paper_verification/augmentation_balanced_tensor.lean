module

public import Recovery.Unimodular.KoszulSupport.PaperVerification.AugmentationCoinvariants
public import Recovery.Unimodular.KoszulSupport.TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic

/-!
# Augmentation coinvariants are the ordinary balanced tensor product

This is the explicit comparison `K ⊗_A M ≃ M/(ker ε)M` for an arbitrary
possibly noncommutative augmented algebra.  The tensor on the left is the
actual quotient of the ground-ring tensor product by the balancing
relations, with the right `A` action on `K` defined through the augmentation.
The maps are `c ⊗ m ↦ c [m]` and `[m] ↦ 1 ⊗ m`, and both inverse laws are
proved.  This identifies the functor being derived in the companion file
with ordinary augmentation tensoring, without a commutativity assumption
on `A` or an assumed bar-homology comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.AugmentationCoinvariants

open CategoryTheory MulOpposite

universe u
variable {K A : Type u} [CommRing K] [Ring A] [Algebra K A]

/-- The coefficient ring carrying the specified right augmentation action. -/
def RightResidue (ε : A →ₐ[K] K) := K

variable (ε : A →ₐ[K] K)

def rightResidueValue (c : RightResidue ε) : K := c

local instance balancedGroundModule (M : ModuleCat.{u} A) : Module K M :=
  Module.compHom M (algebraMap K A)

instance : AddCommGroup (RightResidue ε) := inferInstanceAs (AddCommGroup K)
instance : Module K (RightResidue ε) := inferInstanceAs (Module K K)

def rightAugmentation : Aᵐᵒᵖ →+* K where
  toFun a := ε a.unop
  map_one' := ε.map_one
  map_mul' a b := by
    change ε (b.unop*a.unop)=ε a.unop*ε b.unop
    rw [map_mul,mul_comm]
  map_zero' := ε.map_zero
  map_add' a b := ε.map_add _ _

instance : Module Aᵐᵒᵖ (RightResidue ε) :=
  Module.compHom (RightResidue ε) (rightAugmentation ε)

local instance originalModule (M : ModuleCat.{u} A) :
    Module A (baseObject (K := K) M) := inferInstanceAs (Module A M)

/-- The actual ordinary tensor product with the right augmentation module. -/
abbrev Balanced (M : ModuleCat.{u} A) :=
  TauCeti.BalancedTensorProduct K A (RightResidue ε) (baseObject (K := K) M)

def balancedEvaluation (M : ModuleCat.{u} A) :
    RightResidue ε →ₗ[K] baseObject (K := K) M →ₗ[K] object ε M :=
  LinearMap.mk₂ K (fun c m => rightResidueValue ε c • quotient ε M m)
    (by
      intro c d m
      change (rightResidueValue ε c+rightResidueValue ε d) • quotient ε M m=_
      exact add_smul _ _ _)
    (by
      intro k c m
      change (k*rightResidueValue ε c) • quotient ε M m=_
      exact mul_smul _ _ _)
    (by
      intro c m n
      rw [map_add,smul_add])
    (by
      intro k c m
      rw [map_smul,smul_comm])

theorem balancedEvaluation_balanced (M : ModuleCat.{u} A)
    (a : A) (c : RightResidue ε) (m : M) :
    balancedEvaluation ε M (op a • c) m=balancedEvaluation ε M c (a • m) := by
  change (ε a*(rightResidueValue ε c)) • quotient ε M m=(rightResidueValue ε c) • quotient ε M (a • m)
  rw [quotient_smul,smul_smul,mul_comm]

def balancedToCoinvariants (M : ModuleCat.{u} A) : Balanced ε M →ₗ[K] object ε M :=
  TauCeti.BalancedTensorProduct.lift (balancedEvaluation ε M)
    (balancedEvaluation_balanced ε M)

@[simp] theorem balancedToCoinvariants_tmul (M : ModuleCat.{u} A)
    (c : RightResidue ε) (m : M) :
    balancedToCoinvariants ε M (TauCeti.BalancedTensorProduct.tmul K A c m)=
      (rightResidueValue ε c) • quotient ε M m := by
  rw [balancedToCoinvariants,TauCeti.BalancedTensorProduct.lift_tmul]
  rfl

def toBalanced (M : ModuleCat.{u} A) : baseObject (K := K) M →ₗ[K] Balanced ε M :=
  TauCeti.BalancedTensorProduct.mk K A (show RightResidue ε from (1 : K))

theorem relations_le_toBalanced_kernel (M : ModuleCat.{u} A) :
    relations ε M≤LinearMap.ker (toBalanced ε M) := by
  apply Submodule.span_le.mpr
  rintro x ⟨a,ha,m,rfl⟩
  apply LinearMap.mem_ker.mpr
  rw [toBalanced, TauCeti.BalancedTensorProduct.mk_apply]
  have h := TauCeti.BalancedTensorProduct.balance K A a
    (show RightResidue ε from (1 : K)) m
  have hz : op a • (show RightResidue ε from (1 : K))=0 := by
    change ε a*1=0
    rw [ha,zero_mul]
  rw [hz,TauCeti.BalancedTensorProduct.zero_tmul] at h
  exact h.symm

def coinvariantsToBalanced (M : ModuleCat.{u} A) : object ε M →ₗ[K] Balanced ε M :=
  (relations ε M).liftQ (toBalanced ε M) (relations_le_toBalanced_kernel ε M)

@[simp] theorem coinvariantsToBalanced_quotient (M : ModuleCat.{u} A) (m : M) :
    coinvariantsToBalanced ε M (quotient ε M m)=
      TauCeti.BalancedTensorProduct.tmul K A (show RightResidue ε from (1 : K)) m := by
  rw [coinvariantsToBalanced,quotient_apply]
  erw [Submodule.liftQ_apply]
  exact TauCeti.BalancedTensorProduct.mk_apply K A _ _

/-- An actual linear equivalence with the literal balanced tensor quotient. -/
def balancedEquiv (M : ModuleCat.{u} A) : Balanced ε M ≃ₗ[K] object ε M :=
  LinearEquiv.ofLinearMap (balancedToCoinvariants ε M) (coinvariantsToBalanced ε M)
    (by
      apply LinearMap.ext
      intro x
      refine Quotient.inductionOn' x ?_
      intro m
      change balancedToCoinvariants ε M (coinvariantsToBalanced ε M (quotient ε M m))=
        quotient ε M m
      rw [coinvariantsToBalanced_quotient,balancedToCoinvariants_tmul]
      change (1 : K) • quotient ε M m=quotient ε M m
      exact one_smul _ _)
    (by
      apply TauCeti.BalancedTensorProduct.hom_ext
      intro c m
      change coinvariantsToBalanced ε M
        (balancedToCoinvariants ε M (TauCeti.BalancedTensorProduct.tmul K A c m))=
          TauCeti.BalancedTensorProduct.tmul K A c m
      rw [balancedToCoinvariants_tmul,map_smul,coinvariantsToBalanced_quotient,
        ←TauCeti.BalancedTensorProduct.smul_tmul]
      congr 1
      change (rightResidueValue ε c)*1=c
      exact mul_one _)

@[simp] theorem balancedEquiv_tmul (M : ModuleCat.{u} A)
    (c : RightResidue ε) (m : M) :
    balancedEquiv ε M (TauCeti.BalancedTensorProduct.tmul K A c m)=
      (rightResidueValue ε c) • quotient ε M m := by
  exact balancedToCoinvariants_tmul ε M c m

end PaperVerification.AugmentationCoinvariants
