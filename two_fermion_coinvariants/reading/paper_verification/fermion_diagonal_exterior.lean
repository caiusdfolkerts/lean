module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.Pi

/-!
# Genuine diagonal changes of the odd generators

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped Classical
variable {A ι : Type*} [CommRing A]

def diagonalUnitLinearEquiv (w : ι → Aˣ) : (ι → A) ≃ₗ[A] (ι → A) where
  toFun x i := (w i : A)*x i
  invFun x i := (↑((w i)⁻¹) : A)*x i
  left_inv x := by funext i; simp [mul_assoc]
  right_inv x := by funext i; simp [mul_assoc]
  map_add' x y := by funext i; simp [mul_add]
  map_smul' c x := by funext i; simp [mul_left_comm]

def exteriorDiagonalUnitEquiv (w : ι → Aˣ) :
    ExteriorAlgebra A (ι → A) ≃ₐ[A] ExteriorAlgebra A (ι → A) :=
  AlgEquiv.ofAlgHom
    (ExteriorAlgebra.map (diagonalUnitLinearEquiv w).toLinearMap)
    (ExteriorAlgebra.map (diagonalUnitLinearEquiv w).symm.toLinearMap)
    (by
      rw [ExteriorAlgebra.map_comp_map]
      have h : (diagonalUnitLinearEquiv w).toLinearMap.comp
          (diagonalUnitLinearEquiv w).symm.toLinearMap=LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact (diagonalUnitLinearEquiv w).apply_symm_apply x
      rw [h,ExteriorAlgebra.map_id])
    (by
      rw [ExteriorAlgebra.map_comp_map]
      have h : (diagonalUnitLinearEquiv w).symm.toLinearMap.comp
          (diagonalUnitLinearEquiv w).toLinearMap=LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact (diagonalUnitLinearEquiv w).symm_apply_apply x
      rw [h,ExteriorAlgebra.map_id])

def exteriorGenerator (i : ι) : ExteriorAlgebra A (ι → A) :=
  ExteriorAlgebra.ι A (Pi.single i 1)

@[simp] theorem exteriorDiagonalUnitEquiv_generator (w : ι → Aˣ) (i : ι) :
    exteriorDiagonalUnitEquiv w (exteriorGenerator (A := A) i)=
      (w i : A) • exteriorGenerator i := by
  change ExteriorAlgebra.map (diagonalUnitLinearEquiv w).toLinearMap
    (ExteriorAlgebra.ι A (Pi.single i 1))=_
  rw [ExteriorAlgebra.map_apply_ι]
  change ExteriorAlgebra.ι A (diagonalUnitLinearEquiv w (Pi.single i 1))=_
  have h : diagonalUnitLinearEquiv w (Pi.single i 1)=(w i : A) • Pi.single i 1 := by
    funext j
    by_cases hji : j=i
    · subst j; simp [diagonalUnitLinearEquiv]
    · simp [diagonalUnitLinearEquiv,Pi.single_apply,hji,Ne.symm hji]
  rw [h,map_smul]
  rfl

@[simp] theorem exteriorDiagonalUnitEquiv_symm_generator (w : ι → Aˣ) (i : ι) :
    (exteriorDiagonalUnitEquiv w).symm (exteriorGenerator (A := A) i)=
      (↑((w i)⁻¹) : A) • exteriorGenerator i := by
  change ExteriorAlgebra.map (diagonalUnitLinearEquiv w).symm.toLinearMap
    (ExteriorAlgebra.ι A (Pi.single i 1))=_
  rw [ExteriorAlgebra.map_apply_ι]
  change ExteriorAlgebra.ι A ((diagonalUnitLinearEquiv w).symm (Pi.single i 1))=_
  have h : (diagonalUnitLinearEquiv w).symm (Pi.single i 1)=
      (↑((w i)⁻¹) : A) • Pi.single i 1 := by
    funext j
    by_cases hji : j=i
    · subst j; simp [diagonalUnitLinearEquiv]
    · simp [diagonalUnitLinearEquiv,Pi.single_apply,hji,Ne.symm hji]
  rw [h,map_smul]
  rfl

abbrev ClusterExterior (A : Type*) [CommRing A] (ι : Type*) :=
  ExteriorAlgebra A ((ι ⊕ ι) → A)

def clusterTheta (i : ι) : ClusterExterior A ι := exteriorGenerator (Sum.inl i)
def clusterXi (i : ι) : ClusterExterior A ι := exteriorGenerator (Sum.inr i)

def pairedOddUnitEquiv (unitA unitB : ι → Aˣ) :
    ClusterExterior A ι ≃ₐ[A] ClusterExterior A ι :=
  exteriorDiagonalUnitEquiv (Sum.elim unitB unitA)

@[simp] theorem pairedOddUnitEquiv_theta (unitA unitB : ι → Aˣ) (i : ι) :
    pairedOddUnitEquiv unitA unitB (clusterTheta i)=(unitB i : A) • clusterTheta i :=
  exteriorDiagonalUnitEquiv_generator _ _

@[simp] theorem pairedOddUnitEquiv_xi (unitA unitB : ι → Aˣ) (i : ι) :
    pairedOddUnitEquiv unitA unitB (clusterXi i)=(unitA i : A) • clusterXi i :=
  exteriorDiagonalUnitEquiv_generator _ _

@[simp] theorem pairedOddUnitEquiv_symm_theta (unitA unitB : ι → Aˣ) (i : ι) :
    (pairedOddUnitEquiv unitA unitB).symm (clusterTheta i)=
      (↑((unitB i)⁻¹) : A) • clusterTheta i :=
  exteriorDiagonalUnitEquiv_symm_generator _ _

@[simp] theorem pairedOddUnitEquiv_symm_xi (unitA unitB : ι → Aˣ) (i : ι) :
    (pairedOddUnitEquiv unitA unitB).symm (clusterXi i)=
      (↑((unitA i)⁻¹) : A) • clusterXi i :=
  exteriorDiagonalUnitEquiv_symm_generator _ _

end PaperVerification.Fermion
