module

public import PaperVerification.AlternatingFormsOrbitExteriorCoordinates
public import PaperVerification.AlternatingFormsOrbitExterior
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The actual cubic wedge map forces central commutators

This is the linear-algebra step in Proposition 5.3.  The hypothesis is
injectivity of the literal map `(u,v) ↦ f∧u+g∧v`, rather than a statement
about an abstract expected Hilbert function.  The conclusion applies to
any associative algebra whose generator commutators have coefficients
given by the actual two exterior forms.  Jacobi and separation by linear
functionals prove that the two commutator directions are central.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.CubicJacobi

variable {K : Type*} [Field K] {ν : Type*}

def coefficient (i j k : ν) : (⋀[K]^3 (ν → K)) →ₗ[K] K :=
  exteriorPower.alternatingMapToDual K (ν → K) 3
    ![LinearMap.proj i, LinearMap.proj j, LinearMap.proj k]

theorem coefficient_word (i j k : ν) (w : Fin 3 → ν → K) :
    coefficient i j k (exteriorPower.ιMulti K 3 w) =
      w 0 i*w 1 j*w 2 k-w 0 i*w 1 k*w 2 j-
        w 0 j*w 1 i*w 2 k+w 0 j*w 1 k*w 2 i+
        w 0 k*w 1 i*w 2 j-w 0 k*w 1 j*w 2 i := by
  simp only [coefficient, exteriorPower.alternatingMapToDual_apply_ιMulti,
    Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, LinearMap.proj_apply]

theorem wedge_word_one (w : Fin 2 → ν → K) (v : ν → K) :
    exteriorPower.wedge K (ν → K) 2 1 (exteriorPower.ιMulti K 2 w)
      ((exteriorPower.oneEquiv K (ν → K)).symm v) =
        exteriorPower.ιMulti K 3 ![w 0,w 1,v] := by
  apply Subtype.ext
  simp only [exteriorPower.wedge, DirectSum.gMulLHom_apply_apply,
    SetLike.coe_gMul, exteriorPower.oneEquiv_symm_apply,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, Matrix.vecTail, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Function.comp_def, Matrix.cons_val_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, mul_one]
  rw [mul_assoc]

/-- The six-term coefficient formula is obtained from the actual exterior
pairing, with every sign fixed by that pairing. -/
theorem coefficient_wedge_one (f : ⋀[K]^2 (ν → K)) (v : ν → K) (i j k : ν) :
    coefficient i j k
      (exteriorPower.wedge K (ν → K) 2 1 f
        ((exteriorPower.oneEquiv K (ν → K)).symm v)) =
      orbitExteriorCoefficientMatrix f i j*v k-
        orbitExteriorCoefficientMatrix f i k*v j+
        orbitExteriorCoefficientMatrix f j k*v i := by
  have h : coefficient (K := K) i j k ∘ₗ
        (exteriorPower.wedge K (ν → K) 2 1).flip
          ((exteriorPower.oneEquiv K (ν → K)).symm v) =
      v k • orbitExteriorCoefficient i j-v j • orbitExteriorCoefficient i k+
        v i • orbitExteriorCoefficient j k := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.flip_apply, wedge_word_one, coefficient_word,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      orbitExteriorCoefficient_word, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply,Matrix.cons_val_succ,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
    ring
  have he := LinearMap.congr_fun h f
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    orbitExteriorCoefficientMatrix, mul_comm] using he

variable [Fintype ν] [DecidableEq ν]

theorem eq_zero_of_coefficients (z : ⋀[K]^3 (ν → K))
    (hz : ∀ i j k, coefficient (K := K) i j k z=0) : z=0 := by
  letI : LinearOrder ν := linearOrderOfSTO WellOrderingRel
  let b := Pi.basisFun K ν
  apply (b.exteriorPower 3).repr.injective
  ext s
  rw [map_zero, Finsupp.zero_apply, exteriorPower.basis_repr_apply]
  let a := Set.powersetCard.ofFinEmbEquiv.symm s
  have hd : exteriorPower.ιMultiDual K 3 b s =
      coefficient (K := K) (a 0) (a 1) (a 2) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, coefficient_word,
      Matrix.det_fin_three, Matrix.of_apply, b, Module.Basis.coord_apply,
      Pi.basisFun_repr, a]
  rw [hd]
  exact hz _ _ _

def vectorRelationMap (f g : ⋀[K]^2 (ν → K)) :
    ((ν → K) × (ν → K)) →ₗ[K] (⋀[K]^3 (ν → K)) :=
  (orbitExteriorRelationMap f g 1).comp
    (((exteriorPower.oneEquiv K (ν → K)).symm).prodCongr
      (exteriorPower.oneEquiv K (ν → K)).symm).toLinearMap

theorem vectorRelationMap_injective (f g : ⋀[K]^2 (ν → K))
    (h : Function.Injective (orbitExteriorRelationMap f g 1)) :
    Function.Injective (vectorRelationMap f g) :=
  h.comp (((exteriorPower.oneEquiv K (ν → K)).symm).prodCongr
    (exteriorPower.oneEquiv K (ν → K)).symm).injective

theorem coefficient_vectorRelationMap (f g : ⋀[K]^2 (ν → K))
    (v w : ν → K) (i j k : ν) :
    coefficient i j k (vectorRelationMap f g (v,w)) =
      orbitExteriorCoefficientMatrix f i j*v k-
        orbitExteriorCoefficientMatrix f i k*v j+
        orbitExteriorCoefficientMatrix f j k*v i+
      (orbitExteriorCoefficientMatrix g i j*w k-
        orbitExteriorCoefficientMatrix g i k*w j+
        orbitExteriorCoefficientMatrix g j k*w i) := by
  simp only [vectorRelationMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply, orbitExteriorRelationMap, LinearMap.coprod_apply,
    map_add, coefficient_wedge_one]

section Centrality

variable {A : Type*} [Ring A] [Algebra K A]

def commutator (x y : A) : A := x*y-y*x

theorem commutator_jacobi (x y z : A) :
    commutator x (commutator y z)-commutator y (commutator x z)+
      commutator z (commutator x y)=0 := by
  unfold commutator
  noncomm_ring

theorem commutator_linear (x z₁ z₂ : A) (a b : K) :
    commutator x (a • z₁+b • z₂) =
      a • commutator x z₁+b • commutator x z₂ := by
  simp only [commutator, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    smul_sub]
  abel

/-- Injectivity of the actual cubic wedge map proves the two commutator
directions commute with every original generator, in any associative
algebra satisfying the displayed quadratic commutator equations. -/
theorem generator_commutes_of_cubic_injective
    (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1))
    (X : ν → A) (z₁ z₂ : A)
    (hcomm : ∀ i j, commutator (X i) (X j) =
      orbitExteriorCoefficientMatrix f i j • z₁+
        orbitExteriorCoefficientMatrix g i j • z₂) :
    ∀ i, Commute (X i) z₁ ∧ Commute (X i) z₂ := by
  have hdual (φ : Module.Dual K A) :
      (fun i => φ (commutator (X i) z₁))=0 ∧
        (fun i => φ (commutator (X i) z₂))=0 := by
    let v : ν → K := fun i => φ (commutator (X i) z₁)
    let w : ν → K := fun i => φ (commutator (X i) z₂)
    have hz : vectorRelationMap f g (v,w)=0 := by
      apply eq_zero_of_coefficients
      intro i j k
      rw [coefficient_vectorRelationMap]
      have hj := commutator_jacobi (X i) (X j) (X k)
      rw [hcomm j k, hcomm i k, hcomm i j, commutator_linear,
        commutator_linear, commutator_linear] at hj
      have hh := congrArg φ hj
      simp only [map_add, map_sub, map_smul, map_zero, smul_eq_mul] at hh
      change _=0
      dsimp [v,w]
      linear_combination hh
    have he : (v,w)=(0,0) := vectorRelationMap_injective f g hinj
      (hz.trans (map_zero _).symm)
    exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
  intro i
  constructor
  · apply sub_eq_zero.mp
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro φ
    exact congrFun (hdual φ).1 i
  · apply sub_eq_zero.mp
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro φ
    exact congrFun (hdual φ).2 i

end Centrality
end PaperVerification.AlternatingForms.CubicJacobi
