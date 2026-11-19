module

public import PaperVerification.QuadraticCommutatorQuotient
public import PaperVerification.AlternatingFormsCubicJacobi
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The two actual exterior forms define the central enveloping comparison

Injectivity of the literal cubic wedge map proves both independence of the
two bracket directions and their centrality in the actual associative
commutator quotient.  The comparison with Mathlib's ordinary enveloping
algebra therefore has no centrality or rank hypothesis left over.

The additional comparison with the conventional tensor-annihilator
definition of a quadratic dual is required separately; this module does
not label the commutator presentation as that dual by definition.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TwoStepDual

open TwoStepCentralLie
open QuadraticCommutatorQuotient

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [DecidableEq ν]

def formBilinear (f : ⋀[K]^2 (ν → K)) :
    (ν → K) →ₗ[K] (ν → K) →ₗ[K] K :=
  Matrix.toBilin' (orbitExteriorCoefficientMatrix f)

theorem formBilinear_self (f : ⋀[K]^2 (ν → K)) (v : ν → K) : formBilinear f v v=0 := by
  have h : formBilinear f v v= -formBilinear f v v := by
    simp only [formBilinear,Matrix.toBilin'_apply]
    calc
      (∑ i,∑ j,v i*orbitExteriorCoefficientMatrix f i j*v j)=
          ∑ i,∑ j,v j*orbitExteriorCoefficientMatrix f j i*v i := Finset.sum_comm
      _ = -(∑ i,∑ j,v i*orbitExteriorCoefficientMatrix f i j*v j) := by
        rw [←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [orbitExteriorCoefficientMatrix_skew f i j]
        ring
  have htwo : (2 : K)*formBilinear f v v=0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

set_option maxHeartbeats 800000 in
@[simp] theorem formBilinear_basis (f : ⋀[K]^2 (ν → K)) (i j : ν) :
    formBilinear f (Pi.basisFun K ν i) (Pi.basisFun K ν j)=
      orbitExteriorCoefficientMatrix f i j := by
  rw [formBilinear,Pi.basisFun_apply,Pi.basisFun_apply]
  exact Matrix.toBilin'_single _ i j

def bracketData (f g : ⋀[K]^2 (ν → K)) :
    TwoStepCentralLie.Data (K := K) (V := ν → K) (Z := K × K) where
  bilinear := LinearMap.mk₂ K (fun v w => (formBilinear f v w,formBilinear g v w))
    (by intros; simp only [map_add,LinearMap.add_apply,Prod.mk_add_mk])
    (by intros; simp only [map_smul,LinearMap.smul_apply,Prod.smul_mk])
    (by intros; simp only [map_add,Prod.mk_add_mk])
    (by intros; simp only [map_smul,Prod.smul_mk])
  alternating v := by
    change (formBilinear f v v,formBilinear g v v)=(0,0)
    rw [formBilinear_self,formBilinear_self]

@[simp] theorem bracketData_basis (f g : ⋀[K]^2 (ν → K)) (i j : ν) :
    (bracketData f g).bilinear (Pi.basisFun K ν i) (Pi.basisFun K ν j)=
      (orbitExteriorCoefficientMatrix f i j,orbitExteriorCoefficientMatrix g i j) := by
  change (formBilinear f (Pi.basisFun K ν i) (Pi.basisFun K ν j),
    formBilinear g (Pi.basisFun K ν i) (Pi.basisFun K ν j))=_
  rw [formBilinear_basis,formBilinear_basis]

theorem pair_linear_expansion {A : Type*} [AddCommGroup A] [Module K A]
    (L : (K × K) →ₗ[K] A) (a b : K) :
    L (a,b)=a • L (1,0)+b • L (0,1) := by
  have h : (a,b)=a • (1,0)+b • (0,1) := by simp
  rw [h,map_add,map_smul,map_smul]

variable [Nonempty ν]

/-- Cubic injectivity already forces independence of the two original
forms.  No separate generic independence hypothesis is needed. -/
theorem scalar_relation_trivial (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1))
    (a b : K) (hab : a • f+b • g=0) : a=0 ∧ b=0 := by
  let i : ν := Classical.choice inferInstance
  let v : ⋀[K]^1 (ν → K) :=
    (exteriorPower.oneEquiv K (ν → K)).symm (Pi.basisFun K ν i)
  have hv : (orbitExteriorRelationMap f g 1) (a • v,b • v)=0 := by
    have h := congrArg (fun F : ⋀[K]^2 (ν → K) => exteriorPower.wedge K (ν → K) 2 1 F v) hab
    simpa only [orbitExteriorRelationMap,LinearMap.coprod_apply,map_add,map_smul,
      LinearMap.add_apply,LinearMap.smul_apply,map_zero,LinearMap.zero_apply] using h
  have he : (a • v,b • v)=(0,0) := hinj (hv.trans (map_zero _).symm)
  have ha := congrArg
    (fun x : ⋀[K]^1 (ν → K) => (exteriorPower.oneEquiv K (ν → K) x) i)
    (congrArg Prod.fst he)
  have hb := congrArg
    (fun x : ⋀[K]^1 (ν → K) => (exteriorPower.oneEquiv K (ν → K) x) i)
    (congrArg Prod.snd he)
  constructor
  · simpa [v,Pi.basisFun_apply] using ha
  · simpa [v,Pi.basisFun_apply] using hb

/-- The actual ordered-pair bracket map has both central directions in
its range, as a consequence of the cubic map alone. -/
theorem bracketMap_surjective (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    Function.Surjective (bracketMap (bracketData f g)) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro φ hφ
  change (bracketMap (bracketData f g)).dualMap φ=0 at hφ
  change φ=0
  let a := φ (1,0)
  let b := φ (0,1)
  have hrel : a • f+b • g=0 := by
    apply orbitExteriorCoefficientMatrix_injective
    funext i j
    have he := LinearMap.congr_fun hφ (Pi.basisFun K (ν × ν) (i,j))
    simp only [LinearMap.dualMap_apply,LinearMap.comp_apply,
      bracketMap,Module.Basis.constr_basis,bracketData_basis,LinearMap.zero_apply] at he
    rw [pair_linear_expansion] at he
    change _=orbitExteriorCoefficient i j 0
    simp only [orbitExteriorCoefficientMatrix,map_add,map_smul,map_zero,smul_eq_mul]
    dsimp only [a,b]
    simpa only [orbitExteriorCoefficientMatrix,smul_eq_mul,mul_comm] using he
  obtain ⟨ha,hb⟩ := scalar_relation_trivial f g hinj a b hrel
  apply LinearMap.ext
  rintro ⟨x,y⟩
  rw [pair_linear_expansion]
  change x • a+y • b=0
  rw [ha,hb,smul_zero,smul_zero,add_zero]

def actualCentralMap (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    (K × K) →ₗ[K] QuadraticCommutatorQuotient.Algebra (bracketData f g) :=
  centralMap (bracketData f g) (bracketMap_surjective f g hinj)

/-- Jacobi proves centrality in the actual free-associative quotient,
using the coefficients of the two literal exterior forms. -/
theorem actual_generator_central (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    ∀ i z, Commute (QuadraticCommutatorQuotient.X (bracketData f g) i)
      (actualCentralMap f g hinj z) := by
  let D := bracketData f g
  let C := actualCentralMap f g hinj
  have hc := CubicJacobi.generator_commutes_of_cubic_injective f g hinj
    (QuadraticCommutatorQuotient.X D) (C (1,0)) (C (0,1)) (by
      intro i j
      change commutator (QuadraticCommutatorQuotient.X D i)
        (QuadraticCommutatorQuotient.X D j)=_
      rw [X_commutator D (bracketMap_surjective f g hinj),bracketData_basis]
      exact pair_linear_expansion C _ _)
  intro i z
  rcases z with ⟨a,b⟩
  change Commute (QuadraticCommutatorQuotient.X D i) (C (a,b))
  rw [pair_linear_expansion]
  change _*_=_*_
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,(hc i).1.eq,(hc i).2.eq]

/-- For the original forms with injective cubic wedge map, the
commutator presentation is the actual enveloping algebra of the literal
two-step Lie algebra.  Centrality and bracket surjectivity have been
proved and are not hypotheses of this result. -/
def actualCommutatorEnvelopingEquiv (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    QuadraticCommutatorQuotient.Algebra (bracketData f g) ≃ₐ[K]
      UniversalEnvelopingAlgebra K (TwoStepCentralLie.LieSpace (bracketData f g)) :=
  envelopingEquiv (bracketData f g) (bracketMap_surjective f g hinj)
    (actual_generator_central f g hinj)

end PaperVerification.AlternatingForms.TwoStepDual
