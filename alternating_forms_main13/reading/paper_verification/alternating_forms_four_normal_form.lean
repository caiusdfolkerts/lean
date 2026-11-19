module

public import PaperVerification.AlternatingFormsFourPfaffian
public import PaperVerification.AlternatingFormsOrbitExterior
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Pi

/-!
# The actual generic normal form in dimension four

The displayed polynomial is nonzero at an explicit pair of forms. On its
principal open, the two distinct Pfaffian roots give two decomposable forms;
their four factors are a basis. Their span is exactly the original relation
span. This proves existence of a genuine vector-space normal form, rather
than relying on any assertion about preimages of a dominant orbit map.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace PaperVerification.AlternatingForms.FourNormalForm
open FourPfaffian

variable {K : Type*} [Field K]

def first (B : Module.Basis (Fin 4) K (Fin 4 → K)) : ⋀[K]^2 (Fin 4 → K) :=
  exteriorPower.ιMulti K 2 ![B 0,B 1]

def second (B : Module.Basis (Fin 4) K (Fin 4 → K)) : ⋀[K]^2 (Fin 4 → K) :=
  exteriorPower.ιMulti K 2 ![B 2,B 3]

theorem formEquiv_pencil (c d : Fin 6 → K) (t : K) :
    formEquiv (pencil c d t)=formEquiv c-t • formEquiv d := by
  rw [←map_smul,←map_sub]
  rfl

theorem span_pencil_pair (c d : Fin 6 → K) (r s : K) (hrs : r≠s) :
    Submodule.span K ({formEquiv c,formEquiv d} : Set (⋀[K]^2 (Fin 4 → K)))=
      Submodule.span K ({formEquiv (pencil c d r),formEquiv (pencil c d s)} :
        Set (⋀[K]^2 (Fin 4 → K))) := by
  have hsr : s-r≠0 := sub_ne_zero.mpr hrs.symm
  have hf : formEquiv c=(s/(s-r)) • formEquiv (pencil c d r)+
      (-r/(s-r)) • formEquiv (pencil c d s) := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,pencil]
    field_simp [hsr]
    ring
  have hg : formEquiv d=(1/(s-r)) • formEquiv (pencil c d r)+
      (-1/(s-r)) • formEquiv (pencil c d s) := by
    apply (formEquiv (K := K)).symm.injective
    rw [map_add,map_smul,map_smul,LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,pencil]
    field_simp [hsr]
    ring
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · rw [hf]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [hg]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl) <;> rw [formEquiv_pencil]
    all_goals
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- On the explicit Pfaffian principal open, the actual relation span is the
span of two disjoint exterior basis monomials. -/
theorem normal_form [CharZero K] [IsAlgClosed K] (c d : Fin 6 → K)
    (ha : pfaffian d≠0) (hD : discriminant c d≠0)
    (hR : pivotResultant c d≠0) :
    ∃ B : Module.Basis (Fin 4) K (Fin 4 → K),
      Submodule.span K ({formEquiv c,formEquiv d} : Set (⋀[K]^2 (Fin 4 → K)))=
        Submodule.span K ({first B,second B} : Set (⋀[K]^2 (Fin 4 → K))) := by
  obtain ⟨r,s,hrs,hr,hs⟩ := quadratic_distinct_roots
    (pfaffian d) (-polar c d) (pfaffian c) ha (by simpa [discriminant] using hD)
  have hpr : pfaffian (pencil c d r)=0 := by
    rw [pfaffian_pencil]
    simpa only [neg_mul,sub_eq_add_neg] using hr
  have hps : pfaffian (pencil c d s)=0 := by
    rw [pfaffian_pencil]
    simpa only [neg_mul,sub_eq_add_neg] using hs
  have hcr := pencil_pivot_ne_zero c d hR r hpr
  have hcs := pencil_pivot_ne_zero c d hR s hps
  have hdet : (factorMatrix (pencil c d r) (pencil c d s)).det≠0 := by
    rw [factorMatrix_det _ _ hcr hcs hpr hps]
    exact distinct_root_polar_ne_zero c d ha r s hrs hpr hps
  let B := factorBasis (pencil c d r) (pencil c d s) hdet
  have hfirst : first B=formEquiv (pencil c d r) := by
    rw [decomposable_of_pfaffian_zero _ hcr hpr]
    simp only [first,B,factorBasis_apply,factorMatrix,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hsecond : second B=formEquiv (pencil c d s) := by
    rw [decomposable_of_pfaffian_zero _ hcs hps]
    simp only [second,B,factorBasis_apply,factorMatrix,Matrix.cons_val_succ,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    rfl
  exact ⟨B,by rw [hfirst,hsecond]; exact span_pencil_pair c d r s hrs⟩

def principalPolynomial : MvPolynomial (Fin 6 ⊕ Fin 6) K :=
  let c := fun i : Fin 6 => MvPolynomial.X (Sum.inl i)
  let d := fun i : Fin 6 => MvPolynomial.X (Sum.inr i)
  pfaffian d*discriminant c d*pivotResultant c d

theorem principalPolynomial_eval (y : (Fin 6 ⊕ Fin 6) → K) :
    MvPolynomial.eval y principalPolynomial=
      pfaffian (fun i => y (.inr i))*
        discriminant (fun i => y (.inl i)) (fun i => y (.inr i))*
        pivotResultant (fun i => y (.inl i)) (fun i => y (.inr i)) := by
  simp [principalPolynomial,pfaffian,discriminant,polar,pivotResultant]

/-- This pair is F+G,F+2G with F=e₀∧e₁ and
G=(e₀+e₂)∧(e₁+e₃). Both simple root forms meet the same pivot chart. -/
def canonicalPoint : (Fin 6 ⊕ Fin 6) → K :=
  Sum.elim ![2,0,1,-1,0,1] ![3,0,2,-2,0,2]

theorem principalPolynomial_canonical :
    MvPolynomial.eval (canonicalPoint (K := K)) principalPolynomial= -2 := by
  norm_num [principalPolynomial_eval,pfaffian,discriminant,polar,pivotResultant,canonicalPoint]

theorem principalPolynomial_ne_zero [CharZero K] : (principalPolynomial (K := K))≠0 := by
  intro hz
  have h := principalPolynomial_canonical (K := K)
  rw [hz,map_zero] at h
  norm_num at h

theorem formsFromCoordinates (y : (Fin 6 ⊕ Fin 6) → K) :
    orbitFormsFromCoordinates (formBasis (K := K)) y=
      (formEquiv (fun i => y (.inl i)),formEquiv (fun i => y (.inr i))) := by
  apply Prod.ext <;>
    simp only [orbitFormsFromCoordinates,formBasis,orbitSlotBasis_apply,formEquiv,
      orbitSlotLinearEquiv_apply,orbitTwoFormOfSlots]

theorem coordinateForms_map {M : Type*} [AddCommGroup M] [Module K M]
    (e : (Fin 4 → K) ≃ₗ[K] M)
    (b₂ : Module.Basis (Fin 6) K (⋀[K]^2 (Fin 4 → K)))
    (y : (Fin 6 ⊕ Fin 6) → K) :
    orbitFormsFromCoordinates (b₂.map (orbitExteriorPowerEquiv e 2)) y=
      (exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).1,
       exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ y).2) := by
  simp only [orbitFormsFromCoordinates,Module.Basis.map_apply,
    orbitExteriorPowerEquiv_apply,map_sum,map_smul]

theorem exterior_map_pair {M : Type*} [AddCommGroup M] [Module K M]
    (e : (Fin 4 → K) ≃ₗ[K] M) (u v : Fin 4 → K) :
    exteriorPower.map 2 e.toLinearMap (exteriorPower.ιMulti K 2 ![u,v])=
      exteriorPower.ιMulti K 2 ![e u,e v] := by
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Actual normal forms for all pairs in a nonempty principal open of the
full coefficient space, on an arbitrary four-dimensional vector space. -/
theorem generic_normal_form [CharZero K] [IsAlgClosed K]
    {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (hdim : Module.finrank K M=4) :
    ∃ b₂ : Module.Basis (Fin 6) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin 6 ⊕ Fin 6) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 → ∃ B : Module.Basis (Fin 4) K M,
          Submodule.span K ({(orbitFormsFromCoordinates b₂ y).1,
            (orbitFormsFromCoordinates b₂ y).2} : Set (⋀[K]^2 M))=
          Submodule.span K ({exteriorPower.ιMulti K 2 ![B 0,B 1],
            exteriorPower.ιMulti K 2 ![B 2,B 3]} : Set (⋀[K]^2 M)) := by
  let e : (Fin 4 → K) ≃ₗ[K] M := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun,hdim])
  refine ⟨formBasis.map (orbitExteriorPowerEquiv e 2),principalPolynomial,
    principalPolynomial_ne_zero,?_,?_⟩
  · exact ⟨canonicalPoint,by rw [principalPolynomial_canonical]; norm_num⟩
  · intro y hy
    rw [principalPolynomial_eval] at hy
    have hpair := (mul_ne_zero_iff.mp hy).1
    have hR := (mul_ne_zero_iff.mp hy).2
    have ha := (mul_ne_zero_iff.mp hpair).1
    have hD := (mul_ne_zero_iff.mp hpair).2
    obtain ⟨B,hB⟩ := normal_form (fun i => y (.inl i)) (fun i => y (.inr i)) ha hD hR
    refine ⟨B.map e,?_⟩
    have hmap := congrArg (Submodule.map (exteriorPower.map 2 e.toLinearMap)) hB
    rw [coordinateForms_map,formsFromCoordinates]
    simpa only [Submodule.map_span,Set.image_insert_eq,Set.image_singleton,first,second,
      exterior_map_pair,Module.Basis.map_apply] using hmap

end PaperVerification.AlternatingForms.FourNormalForm
