module
public import shared_results.part018_koszul_summand_projection
public import mixed_results.exterior_sum_tensor

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.KoszulAugmentation -/
section

/-! # Literal exterior augmentation and deleting one Koszul family -/

section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace FourPapers.KoszulAugmentation
open Classical CommAlg
open scoped TensorProduct
universe u
variable {K A B V W : Type u} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Fintype V] [Fintype W]
  [LinearOrder V] [LinearOrder W]

def exterior : Simplicial.Ambient V K →ₐ[K] K :=
  ExteriorAlgebra.lift K ⟨(0 : (V → K) →ₗ[K] K), by intro x; simp⟩

@[simp] theorem exterior_ι (x : V → K) : exterior (ExteriorAlgebra.ι K x)=0 := by
  rw [exterior,ExteriorAlgebra.lift_ι_apply,LinearMap.zero_apply]

theorem exterior_involute (z : Simplicial.Ambient V K) :
    exterior (CliffordAlgebra.involute z)=exterior z := by
  have he : (exterior (K := K) (V := V)).comp CliffordAlgebra.involute=exterior := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro x
    change exterior (CliffordAlgebra.involute (ExteriorAlgebra.ι K x)) =
      exterior (ExteriorAlgebra.ι K x)
    simp only [CliffordAlgebra.involute_ι,map_neg,exterior_ι,neg_zero]
  exact DFunLike.congr_fun he z

theorem exterior_basis (F : Finset V) :
    exterior (Simplicial.basis (k := K) F)=if F=∅ then 1 else 0 := by
  rw [Simplicial.basis,Module.Basis.exteriorAlgebra_eq_prod_map_sort,map_list_prod]
  by_cases hF : F=∅
  · subst F
    simp
  · rw [if_neg hF]
    obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    apply List.prod_eq_zero
    apply List.mem_map.mpr
    refine ⟨ExteriorAlgebra.ι K (Pi.basisFun K V v),?_,exterior_ι _⟩
    apply List.mem_map.mpr
    refine ⟨Pi.basisFun K V v,?_,rfl⟩
    exact List.mem_map.mpr ⟨v,(Finset.mem_sort _).mpr hv,rfl⟩

def augmentation (f : A →ₐ[K] B) :
    (A ⊗[K] Simplicial.Ambient V K) →ₐ[K] B :=
  (Algebra.TensorProduct.rid K K B).toAlgHom.comp (Algebra.TensorProduct.map f exterior)

@[simp] theorem augmentation_tmul (f : A →ₐ[K] B) (a : A)
    (z : Simplicial.Ambient V K) :
    augmentation f (a ⊗ₜ[K] z)=exterior z • f a := rfl

theorem augmentation_tmul_basis (f : A →ₐ[K] B) (a : A) (F : Finset V) :
    augmentation f (a ⊗ₜ[K] Simplicial.basis F)=if F=∅ then f a else 0 := by
  rw [augmentation_tmul,exterior_basis]
  split_ifs <;> simp only [one_smul,zero_smul]

theorem rightExterior_join (z : Simplicial.Ambient V K) (w : Simplicial.Ambient W K) :
    KoszulSummandProjection.rightExterior (ExteriorSumTensor.join (z ⊗ₜ[K] w))=
      exterior z • w := by
  have hl : (KoszulSummandProjection.rightVector (K := K) (V := V) (W := W)).comp
      ExteriorSumTensor.leftVector=0 := by
    apply LinearMap.ext
    intro x
    rfl
  have hr : (KoszulSummandProjection.rightVector (K := K) (V := V) (W := W)).comp
      ExteriorSumTensor.rightVector=LinearMap.id := by
    apply LinearMap.ext
    intro x
    rfl
  have hz : ExteriorAlgebra.map (0 : (V → K) →ₗ[K] (W → K))=
      (Algebra.ofId K (Simplicial.Ambient W K)).comp exterior := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro x
    change ExteriorAlgebra.map (0 : (V → K) →ₗ[K] (W → K)) (ExteriorAlgebra.ι K x) =
      algebraMap K (Simplicial.Ambient W K) (exterior (ExteriorAlgebra.ι K x))
    simp only [ExteriorAlgebra.map_apply_ι,LinearMap.zero_apply,map_zero,exterior_ι]
  rw [ExteriorSumTensor.join_tmul,map_mul]
  change ExteriorAlgebra.map KoszulSummandProjection.rightVector
      (ExteriorAlgebra.map ExteriorSumTensor.leftVector z)*
    ExteriorAlgebra.map KoszulSummandProjection.rightVector
      (ExteriorAlgebra.map ExteriorSumTensor.rightVector w)=_
  have hleft := DFunLike.congr_fun
    (ExteriorAlgebra.map_comp_map
      (ExteriorSumTensor.leftVector (K := K) (V := V) (W := W))
      KoszulSummandProjection.rightVector) z
  rw [hl,hz] at hleft
  change ExteriorAlgebra.map KoszulSummandProjection.rightVector
      (ExteriorAlgebra.map ExteriorSumTensor.leftVector z) =
        algebraMap K (Simplicial.Ambient W K) (exterior z) at hleft
  have hright := DFunLike.congr_fun
    (ExteriorAlgebra.map_comp_map
      (ExteriorSumTensor.rightVector (K := K) (V := V) (W := W))
      KoszulSummandProjection.rightVector) w
  rw [hr,ExteriorAlgebra.map_id] at hright
  change ExteriorAlgebra.map KoszulSummandProjection.rightVector
      (ExteriorAlgebra.map ExteriorSumTensor.rightVector w) = w at hright
  rw [hleft,hright]
  exact Algebra.smul_def (exterior z) w |>.symm

theorem right_join_tmul (f : A →ₐ[K] B) (a : A)
    (z : Simplicial.Ambient V K) (w : Simplicial.Ambient W K) :
    KoszulSummandProjection.right f
      (a ⊗ₜ[K] ExteriorSumTensor.join (z ⊗ₜ[K] w))=
      augmentation f (a ⊗ₜ[K] z) ⊗ₜ[K] w := by
  rw [KoszulSummandProjection.right,Algebra.TensorProduct.map_tmul,rightExterior_join,
    augmentation_tmul,TensorProduct.tmul_smul,TensorProduct.smul_tmul']

end FourPapers.KoszulAugmentation

end
end
end

end
