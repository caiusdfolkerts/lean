module

public import PaperVerification.AlternatingFormsOrbitSlotBasis
public import PaperVerification.AlternatingFormsOrbitExterior
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.FieldSimp

/-!
# A genuine generic normal form for a pair of two-forms in dimension three

A single coefficient minor defines a nonempty principal open in the full
space of pairs. On it, explicit row reduction and a determinant-one shear
produce the monomial relations e₀∧e₁ and e₁∧e₂. No assertion about dominant
maps having rational preimages is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace PaperVerification.AlternatingForms.ThreeNormalForm

variable {K : Type*} [Field K]

def slotRow : Fin 3 → Fin 3 := ![0,0,1]
def slotCol : Fin 3 → Fin 3 := ![1,2,2]

theorem slots : OrbitPairSlots slotRow slotCol := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [slotRow,slotCol]
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [slotRow,slotCol,Fin.exists_fin_succ]

def formEquiv : (Fin 3 → K) ≃ₗ[K] (⋀[K]^2 (Fin 3 → K)) := orbitSlotLinearEquiv slots

def formBasis : Module.Basis (Fin 3) K (⋀[K]^2 (Fin 3 → K)) := orbitSlotBasis slots

def coefficientMinor (c d : Fin 3 → K) : K := c 0*d 2-d 0*c 2

def shear (a b : K) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun x := ![x 0+b*x 1,x 1,x 2+a*x 1]
  invFun x := ![x 0-b*x 1,x 1,x 2-a*x 1]
  left_inv x := by ext i; fin_cases i <;> simp <;> ring
  right_inv x := by ext i; fin_cases i <;> simp <;> ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

def shearBasis (a b : K) : Module.Basis (Fin 3) K (Fin 3 → K) :=
  (Pi.basisFun K (Fin 3)).map (shear a b)

def first (B : Module.Basis (Fin 3) K (Fin 3 → K)) : ⋀[K]^2 (Fin 3 → K) :=
  exteriorPower.ιMulti K 2 ![B 0,B 1]

def second (B : Module.Basis (Fin 3) K (Fin 3 → K)) : ⋀[K]^2 (Fin 3 → K) :=
  exteriorPower.ιMulti K 2 ![B 1,B 2]

theorem first_coordinates (a b : K) :
    (formEquiv (K := K)).symm (first (shearBasis a b))=![1,a,0] := by
  funext i
  fin_cases i <;>
    simp [formEquiv,orbitSlotLinearEquiv_symm_apply,orbitExteriorCoefficientMatrix,
      first,shearBasis,Module.Basis.map_apply,shear,orbitExteriorCoefficient_word,
      slotRow,slotCol,Pi.basisFun_apply,Pi.single_apply]

theorem second_coordinates (a b : K) :
    (formEquiv (K := K)).symm (second (shearBasis a b))=![0,b,1] := by
  funext i
  fin_cases i <;>
    simp [formEquiv,orbitSlotLinearEquiv_symm_apply,orbitExteriorCoefficientMatrix,
      second,shearBasis,Module.Basis.map_apply,shear,orbitExteriorCoefficient_word,
      slotRow,slotCol,Pi.basisFun_apply,Pi.single_apply]

/-- Explicit generator row reduction on the full coefficient principal open. -/
theorem normal_form (c d : Fin 3 → K) (hD : coefficientMinor c d≠0) :
    ∃ B : Module.Basis (Fin 3) K (Fin 3 → K),
      Submodule.span K ({formEquiv c,formEquiv d} : Set (⋀[K]^2 (Fin 3 → K)))=
        Submodule.span K ({first B,second B} : Set (⋀[K]^2 (Fin 3 → K))) := by
  let a := (d 2*c 1-c 2*d 1)/coefficientMinor c d
  let b := (c 0*d 1-d 0*c 1)/coefficientMinor c d
  let B := shearBasis a b
  let F := first B
  let G := second B
  have hF : (formEquiv (K := K)).symm F=![1,a,0] := first_coordinates a b
  have hG : (formEquiv (K := K)).symm G=![0,b,1] := second_coordinates a b
  have hf : formEquiv c=c 0 • F+c 2 • G := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,hF,hG,LinearEquiv.symm_apply_apply]
    ext i
    fin_cases i <;> simp [a,b] <;> field_simp [hD] <;> (try simp only [coefficientMinor]) <;> ring
  have hg : formEquiv d=d 0 • F+d 2 • G := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,hF,hG,LinearEquiv.symm_apply_apply]
    ext i
    fin_cases i <;> simp [a,b] <;> field_simp [hD] <;> (try simp only [coefficientMinor]) <;> ring
  have hF' : F=(d 2/coefficientMinor c d) • formEquiv c+
      (-c 2/coefficientMinor c d) • formEquiv d := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply,hF]
    ext i
    fin_cases i <;> simp [a,b] <;> field_simp [hD] <;> (try simp only [coefficientMinor]) <;> ring
  have hG' : G=(-d 0/coefficientMinor c d) • formEquiv c+
      (c 0/coefficientMinor c d) • formEquiv d := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply,hG]
    ext i
    fin_cases i <;> simp [a,b] <;> field_simp [hD] <;> (try simp only [coefficientMinor]) <;> ring
  refine ⟨B,le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · rw [hf]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [F])))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [G])))
    · rw [hg]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [F])))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [G])))
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · rw [show first B=F from rfl,hF']
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [show second B=G from rfl,hG']
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

def principalPolynomial : MvPolynomial (Fin 3 ⊕ Fin 3) K :=
  MvPolynomial.X (.inl 0)*MvPolynomial.X (.inr 2)-
    MvPolynomial.X (.inr 0)*MvPolynomial.X (.inl 2)

theorem principalPolynomial_eval (y : (Fin 3 ⊕ Fin 3) → K) :
    MvPolynomial.eval y principalPolynomial=
      coefficientMinor (fun i => y (.inl i)) (fun i => y (.inr i)) := by
  simp [principalPolynomial,coefficientMinor]

def canonicalPoint : (Fin 3 ⊕ Fin 3) → K := Sum.elim ![1,0,0] ![0,0,1]

theorem principalPolynomial_canonical :
    MvPolynomial.eval (canonicalPoint (K := K)) principalPolynomial=1 := by
  norm_num [principalPolynomial_eval,coefficientMinor,canonicalPoint]

theorem principalPolynomial_ne_zero : (principalPolynomial (K := K))≠0 := by
  intro hz
  have h := principalPolynomial_canonical (K := K)
  rw [hz,map_zero] at h
  exact zero_ne_one h

theorem formsFromCoordinates (y : (Fin 3 ⊕ Fin 3) → K) :
    orbitFormsFromCoordinates (formBasis (K := K)) y=
      (formEquiv (fun i => y (.inl i)),formEquiv (fun i => y (.inr i))) := by
  apply Prod.ext <;>
    simp only [orbitFormsFromCoordinates,formBasis,orbitSlotBasis_apply,formEquiv,
      orbitSlotLinearEquiv_apply,orbitTwoFormOfSlots]

theorem coordinateForms_map {M : Type*} [AddCommGroup M] [Module K M]
    (e : (Fin 3 → K) ≃ₗ[K] M)
    (b₂ : Module.Basis (Fin 3) K (⋀[K]^2 (Fin 3 → K)))
    (y : (Fin 3 ⊕ Fin 3) → K) :
    orbitFormsFromCoordinates (b₂.map (orbitExteriorPowerEquiv e 2)) y=
      (exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).1,
       exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).2) := by
  simp only [orbitFormsFromCoordinates,Module.Basis.map_apply,
    orbitExteriorPowerEquiv_apply,map_sum,map_smul]

theorem exterior_map_pair {M : Type*} [AddCommGroup M] [Module K M]
    (e : (Fin 3 → K) ≃ₗ[K] M) (u v : Fin 3 → K) :
    exteriorPower.map 2 e.toLinearMap (exteriorPower.ιMulti K 2 ![u,v])=
      exteriorPower.ιMulti K 2 ![e u,e v] := by
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The normal form exists on an explicitly nonempty principal open in
all pairs of forms on an arbitrary three-dimensional vector space. -/
theorem generic_normal_form {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (hdim : Module.finrank K M=3) :
    ∃ b₂ : Module.Basis (Fin 3) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin 3 ⊕ Fin 3) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 → ∃ B : Module.Basis (Fin 3) K M,
          Submodule.span K ({(orbitFormsFromCoordinates b₂ y).1,
            (orbitFormsFromCoordinates b₂ y).2} : Set (⋀[K]^2 M))=
          Submodule.span K ({exteriorPower.ιMulti K 2 ![B 0,B 1],
            exteriorPower.ιMulti K 2 ![B 1,B 2]} : Set (⋀[K]^2 M)) := by
  let e : (Fin 3 → K) ≃ₗ[K] M := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun,hdim])
  refine ⟨formBasis.map (orbitExteriorPowerEquiv e 2),principalPolynomial,
    principalPolynomial_ne_zero,?_,?_⟩
  · exact ⟨canonicalPoint,by rw [principalPolynomial_canonical]; exact one_ne_zero⟩
  · intro y hy
    rw [principalPolynomial_eval] at hy
    obtain ⟨B,hB⟩ := normal_form (fun i => y (.inl i)) (fun i => y (.inr i)) hy
    refine ⟨B.map e,?_⟩
    have hmap := congrArg (Submodule.map (exteriorPower.map 2 e.toLinearMap)) hB
    rw [coordinateForms_map,formsFromCoordinates]
    simpa only [Submodule.map_span,Set.image_insert_eq,Set.image_singleton,first,second,
      exterior_map_pair,Module.Basis.map_apply] using hmap

end PaperVerification.AlternatingForms.ThreeNormalForm
