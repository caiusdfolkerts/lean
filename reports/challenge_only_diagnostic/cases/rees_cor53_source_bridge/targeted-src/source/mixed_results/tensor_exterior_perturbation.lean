module
public import shared_results.part002
public import shared_results.part003
public import mixed_results.compatible_projection_perturbation
public import graph_foundation.part012

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.TensorExteriorPerturbation -/
section

/-! # Finite exterior perturbation of a split coefficient complex

Only the number of exterior generators is used as a decreasing degree.
The coefficient complex may have infinite rank and its homotopy may be
arbitrary. The projection remains exactly the original tensor projection
when it intertwines the added coefficient operators.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.TensorExteriorPerturbation
open Classical CommAlg HomologicalPerturbation
open scoped TensorProduct
universe u
variable {K X H W : Type u} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup H] [Module K H]
  [Fintype W] [LinearOrder W]

def differential (T : W → Module.End K X) :
    Module.End K (X ⊗[K] Simplicial.Ambient W K) :=
  ∑ w, TensorProduct.map (T w) (Simplicial.contraction w)

@[simp] theorem differential_tmul (T : W → Module.End K X)
    (x : X) (z : Simplicial.Ambient W K) :
    differential T (x ⊗ₜ[K] z) = ∑ w, T w x ⊗ₜ[K] Simplicial.contraction w z := by
  simp only [differential,LinearMap.sum_apply,TensorProduct.map_tmul]

variable {I : Type*} (b : Module.Basis I K X)

def basis : Module.Basis (I × Finset W) K (X ⊗[K] Simplicial.Ambient W K) :=
  b.tensorProduct Simplicial.basis

theorem differential_decreasing (T : W → Module.End K X) :
    DegreeDecreasing (basis (W := W) b) (fun a => a.2.card) (differential T) := by
  rintro ⟨i,F⟩ ⟨j,G⟩ hcard
  rw [basis,Module.Basis.tensorProduct_apply,differential_tmul,map_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro w hw
  rw [Simplicial.contraction_basis]
  by_cases hwF : w ∈ F
  · rw [if_pos hwF, TensorProduct.tmul_smul, Units.smul_def,
      ← Int.cast_smul_eq_zsmul K, map_smul, Finsupp.smul_apply]
    have hne : F.erase w ≠ G := by
      intro he
      rw [← he] at hcard
      exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hwF)) hcard
    simp only [Module.Basis.tensorProduct_repr_tmul_apply,Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hne.symm,zero_smul,smul_zero,mul_zero,zero_mul]
  · rw [if_neg hwF,TensorProduct.tmul_zero,map_zero,Finsupp.zero_apply]

variable (C : LinearContraction (R := K) (M := X) (H := H))

theorem homotopy_nonincreasing :
    DegreeNonincreasing (basis (W := W) b) (fun a => a.2.card)
      (C.tensorRight (Simplicial.Ambient W K)).h := by
  rintro ⟨i,F⟩ ⟨j,G⟩ hcard
  have hne : F ≠ G := by intro he; simpa only [he,lt_self_iff_false] using hcard
  rw [basis,Module.Basis.tensorProduct_apply,C.tensorRight_h_tmul]
  simp only [Module.Basis.tensorProduct_repr_tmul_apply,Module.Basis.repr_self,
    Finsupp.single_eq_of_ne hne.symm,zero_smul,smul_zero,mul_zero,zero_mul]

variable (T : W → Module.End K X) (U : W → Module.End K H)
  (hp : ∀ w, C.projection.comp (T w)=(U w).comp C.projection)

include hp in
theorem projection_differential :
    (C.tensorRight (Simplicial.Ambient W K)).projection.comp (differential T)=
      (differential U).comp (C.tensorRight (Simplicial.Ambient W K)).projection := by
  apply TensorProduct.ext'
  intro x z
  change (C.tensorRight (Simplicial.Ambient W K)).projection
    (differential T (x ⊗ₜ[K] z))=
      differential U ((C.tensorRight (Simplicial.Ambient W K)).projection (x ⊗ₜ[K] z))
  rw [differential_tmul,map_sum,C.tensorRight_projection_tmul,differential_tmul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [C.tensorRight_projection_tmul]
  have hh := LinearMap.congr_fun (hp w) x
  change C.projection (T w x)=U w (C.projection x) at hh
  rw [hh]

variable (hsquare :
  ((C.tensorRight (Simplicial.Ambient W K)).d+differential T)*
    ((C.tensorRight (Simplicial.Ambient W K)).d+differential T)=0)

def retract : LinearDeformationRetract
    (R := K) (M := X ⊗[K] Simplicial.Ambient W K) (H := H ⊗[K] Simplicial.Ambient W K) :=
  (C.tensorRight (Simplicial.Ambient W K)).perturbByDegree
    (basis b) (fun a => a.2.card) (differential T) (differential_decreasing b T)
    (homotopy_nonincreasing b C) hsquare

include hp in
theorem retract_projection :
    (retract b C T hsquare).projection=(C.tensorRight (Simplicial.Ambient W K)).projection :=
  (C.tensorRight (Simplicial.Ambient W K)).transferredProjection_eq
    (differential T) (differential U)
    ((C.tensorRight (Simplicial.Ambient W K)).leftPerturbationUnit
      (basis b) (fun a => a.2.card) (differential T) (differential_decreasing b T)
      (homotopy_nonincreasing b C))
    ((C.tensorRight (Simplicial.Ambient W K)).leftPerturbationUnit_val
      (basis b) (fun a => a.2.card) (differential T) (differential_decreasing b T)
      (homotopy_nonincreasing b C))
    (projection_differential C T U hp)

include hp in
theorem retract_target : (retract b C T hsquare).targetD=differential U :=
  (C.tensorRight (Simplicial.Ambient W K)).transferredDifferential_eq
    (differential T) (differential U)
    ((C.tensorRight (Simplicial.Ambient W K)).leftPerturbationUnit
      (basis b) (fun a => a.2.card) (differential T) (differential_decreasing b T)
      (homotopy_nonincreasing b C))
    ((C.tensorRight (Simplicial.Ambient W K)).leftPerturbationUnit_val
      (basis b) (fun a => a.2.card) (differential T) (differential_decreasing b T)
      (homotopy_nonincreasing b C))
    (projection_differential C T U hp)

end FourPapers.TensorExteriorPerturbation

end
end
end

end
