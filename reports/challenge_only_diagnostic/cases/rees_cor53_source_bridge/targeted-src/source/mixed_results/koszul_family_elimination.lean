module
public import mixed_results.tensor_koszul_split
public import mixed_results.koszul_augmentation
public import mixed_results.deformation_retract_transport
public import shared_results.part018_parity_homology_retract

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.KoszulFamilyElimination -/
section

/-! # Multiplicative elimination of an augmented Koszul family

A split augmented first Koszul complex remains a quasi-isomorphism after
adjoining any finite second family. The projection is the literal algebra
projection that deletes the first exterior variables. Its bijectivity on
homology is proved by a finite exterior perturbation; consequently this is
an equivalence of the actual homology algebras, with their original products.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.KoszulFamilyElimination
open Classical CommAlg HomologicalPerturbation
open scoped TensorProduct
universe u
variable {K A B V W : Type u} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Fintype V] [LinearOrder V]
  [Fintype W] [LinearOrder W]
  (f : V → A) (g : W → A) (F : A →ₐ[K] B)
  (C : LinearContraction (R := K) (M := A ⊗[K] Simplicial.Ambient V K) (H := B))
  (hd : C.d=TensorExteriorKoszul.differential (K := K) (M := A) f)
  (hp : C.projection=(KoszulAugmentation.augmentation (V := V) F).toLinearMap)

local instance : LinearOrder (V ⊕ W) :=
  LinearOrder.lift' (fun z : V ⊕ W => (toLex z : Lex (V ⊕ W))) (fun _ _ h => h)

def coefficientBasis := Module.Free.chooseBasis K (A ⊗[K] Simplicial.Ambient V K)

include hp in
theorem projection_rightOperator (w : W) :
    C.projection.comp (TensorKoszulSplit.rightOperator (V := V) g w)=
      (Algebra.lsmul K K B (F (g w))).comp C.projection := by
  apply TensorProduct.ext'
  intro a z
  change C.projection (TensorKoszulSplit.rightOperator g w (a ⊗ₜ[K] z))=
    F (g w)*C.projection (a ⊗ₜ[K] z)
  rw [hp,TensorKoszulSplit.rightOperator_tmul]
  change KoszulAugmentation.augmentation F
      ((g w*a) ⊗ₜ[K] CliffordAlgebra.involute z)=
    F (g w)*KoszulAugmentation.augmentation F (a ⊗ₜ[K] z)
  rw [KoszulAugmentation.augmentation_tmul,KoszulAugmentation.augmentation_tmul,
    KoszulAugmentation.exterior_involute,map_mul,Algebra.mul_smul_comm]

include hd in
theorem perturbed_square :
    ((C.tensorRight (Simplicial.Ambient W K)).d+
      TensorExteriorPerturbation.differential (TensorKoszulSplit.rightOperator (V := V) g))*
    ((C.tensorRight (Simplicial.Ambient W K)).d+
      TensorExteriorPerturbation.differential (TensorKoszulSplit.rightOperator (V := V) g))=0 := by
  change (C.d.rTensor (Simplicial.Ambient W K)+_)*
    (C.d.rTensor (Simplicial.Ambient W K)+_)=0
  rw [hd]
  exact TensorKoszulSplit.splitDifferential_square f g

def tensorRetract : LinearDeformationRetract
    (R := K) (M := (A ⊗[K] Simplicial.Ambient V K) ⊗[K] Simplicial.Ambient W K)
    (H := B ⊗[K] Simplicial.Ambient W K) :=
  TensorExteriorPerturbation.retract (coefficientBasis (K := K) (A := A) (V := V)) C
    (TensorKoszulSplit.rightOperator g) (perturbed_square f g C hd)

def retract : LinearDeformationRetract
    (R := K) (M := A ⊗[K] Simplicial.Ambient (V ⊕ W) K)
    (H := B ⊗[K] Simplicial.Ambient W K) :=
  (tensorRetract f g C hd).changeSource TensorKoszulSplit.join

include hd in
theorem retract_source : (retract f g C hd).sourceD=
    TensorExteriorKoszul.differential (K := K) (M := A) (Sum.elim f g) := by
  apply LinearMap.ext
  intro z
  change (TensorKoszulSplit.join (K := K) (A := A) (V := V) (W := W))
    ((C.d.rTensor (Simplicial.Ambient W K) +
      TensorExteriorPerturbation.differential (TensorKoszulSplit.rightOperator (V := V) g) :
        Module.End K ((A ⊗[K] Simplicial.Ambient V K) ⊗[K] Simplicial.Ambient W K))
      (TensorKoszulSplit.join.symm z)) = _
  rw [hd]
  change TensorKoszulSplit.join
    (TensorKoszulSplit.splitDifferential f g (TensorKoszulSplit.join.symm z))=_
  rw [← TensorKoszulSplit.differential_join,LinearEquiv.apply_symm_apply]

include hp in
theorem retract_target : (retract f g C hd).targetD=
    TensorExteriorKoszul.differential (K := K) (M := B) (fun w => F (g w)) :=
  TensorExteriorPerturbation.retract_target
    (coefficientBasis (K := K) (A := A) (V := V)) C
    (TensorKoszulSplit.rightOperator g) (fun w => Algebra.lsmul K K B (F (g w)))
    (projection_rightOperator g F C hp) (perturbed_square f g C hd)

include hp in
theorem retract_projection : (retract f g C hd).projection=
    (KoszulSummandProjection.right (V := V) (W := W) F).toLinearMap := by
  have he : (tensorRetract f g C hd).projection=
      (C.tensorRight (Simplicial.Ambient W K)).projection :=
    TensorExteriorPerturbation.retract_projection
      (coefficientBasis (K := K) (A := A) (V := V)) C
      (TensorKoszulSplit.rightOperator g) (fun w => Algebra.lsmul K K B (F (g w)))
      (projection_rightOperator g F C hp) (perturbed_square f g C hd)
  have hj : (C.tensorRight (Simplicial.Ambient W K)).projection=
      (KoszulSummandProjection.right F).toLinearMap.comp TensorKoszulSplit.join.toLinearMap := by
    apply TensorProduct.ext'
    intro x w
    induction x using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul,map_zero]
    | add x y hx hy =>
        simp only [TensorProduct.add_tmul,map_add,LinearMap.comp_apply] at *
        exact congrArg₂ (·+·) hx hy
    | tmul a z =>
        rw [C.tensorRight_projection_tmul,hp]
        exact (KoszulAugmentation.right_join_tmul F a z w).symm
  apply LinearMap.ext
  intro z
  change (tensorRetract f g C hd).projection (TensorKoszulSplit.join.symm z)=_
  rw [he,hj]
  change KoszulSummandProjection.right F
    (TensorKoszulSplit.join (TensorKoszulSplit.join.symm z))=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The comparison is induced by the literal algebra projection. -/
def homologyEquiv :
    (TensorExteriorKoszul.parityDifferential (K := K) (Sum.elim f g)).Homology ≃ₐ[K]
      (TensorExteriorKoszul.parityDifferential (K := K) (fun w => F (g w))).Homology :=
  ParityDifferential.homologyEquivOfRetract _ _ (KoszulSummandProjection.right F)
    (retract f g C hd) (retract_source f g C hd)
    (retract_target f g F C hd hp) (retract_projection f g F C hd hp)

end FourPapers.KoszulFamilyElimination

end
end
end

end
