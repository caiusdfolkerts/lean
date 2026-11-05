module
public import graph_foundation.part013
public import shared_results.part018_parity_homology_selected_projection

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.KoszulSummandProjection -/
section

/-! # Literal differential algebra projections deleting Koszul variables

The exterior map is induced by the coordinate projection of free modules.
Terms deleted by that projection have coefficient zero after the stated
algebra map. This gives the two actual algebra projections in a Koszul
change-of-rings comparison, with all signs and products preserved.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace FourPapers.KoszulSummandProjection
open Classical CommAlg
open scoped TensorProduct
universe u
variable {K A B V W : Type u} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Fintype V] [Fintype W]
  [LinearOrder V] [LinearOrder W]

def rightVector : (V ⊕ W → K) →ₗ[K] (W → K) :=
  LinearMap.pi (fun w => LinearMap.proj (Sum.inr w))

def leftVector : (V ⊕ W → K) →ₗ[K] (V → K) :=
  LinearMap.pi (fun v => LinearMap.proj (Sum.inl v))

def rightExterior : Simplicial.Ambient (V ⊕ W) K →ₐ[K] Simplicial.Ambient W K :=
  ExteriorAlgebra.map (rightVector (K := K) (V := V) (W := W))

def leftExterior : Simplicial.Ambient (V ⊕ W) K →ₐ[K] Simplicial.Ambient V K :=
  ExteriorAlgebra.map (leftVector (K := K) (V := V) (W := W))

theorem right_coordinate (w : W) :
    ((Pi.basisFun K W).coord w).comp (rightVector (K := K) (V := V)) =
      (Pi.basisFun K (V ⊕ W)).coord (Sum.inr w) := by
  apply LinearMap.ext
  intro x
  rfl

theorem left_coordinate (v : V) :
    ((Pi.basisFun K V).coord v).comp (leftVector (K := K) (W := W)) =
      (Pi.basisFun K (V ⊕ W)).coord (Sum.inl v) := by
  apply LinearMap.ext
  intro x
  rfl

theorem rightExterior_contraction (w : W) (z : Simplicial.Ambient (V ⊕ W) K) :
    rightExterior (Simplicial.contraction (Sum.inr w) z) =
      Simplicial.contraction w (rightExterior z) := by
  change ExteriorAlgebra.map rightVector
    (CliffordAlgebra.contractLeft ((Pi.basisFun K (V ⊕ W)).coord (Sum.inr w)) z) =
      CliffordAlgebra.contractLeft ((Pi.basisFun K W).coord w)
        (ExteriorAlgebra.map rightVector z)
  rw [ExteriorAlgebra.contractLeft_map, right_coordinate]

theorem leftExterior_contraction (v : V) (z : Simplicial.Ambient (V ⊕ W) K) :
    leftExterior (Simplicial.contraction (Sum.inl v) z) =
      Simplicial.contraction v (leftExterior z) := by
  change ExteriorAlgebra.map leftVector
    (CliffordAlgebra.contractLeft ((Pi.basisFun K (V ⊕ W)).coord (Sum.inl v)) z) =
      CliffordAlgebra.contractLeft ((Pi.basisFun K V).coord v)
        (ExteriorAlgebra.map leftVector z)
  rw [ExteriorAlgebra.contractLeft_map, left_coordinate]

def right (f : A →ₐ[K] B) :
    (A ⊗[K] Simplicial.Ambient (V ⊕ W) K) →ₐ[K]
      (B ⊗[K] Simplicial.Ambient W K) :=
  Algebra.TensorProduct.map f rightExterior

def left (f : A →ₐ[K] B) :
    (A ⊗[K] Simplicial.Ambient (V ⊕ W) K) →ₐ[K]
      (B ⊗[K] Simplicial.Ambient V K) :=
  Algebra.TensorProduct.map f leftExterior

theorem right_differential (f : A →ₐ[K] B) (x : V ⊕ W → A) (y : W → B)
    (hz : ∀ v, f (x (Sum.inl v))=0) (hy : ∀ w, f (x (Sum.inr w))=y w)
    (z : A ⊗[K] Simplicial.Ambient (V ⊕ W) K) :
    right f (TensorExteriorKoszul.differential x z) =
      TensorExteriorKoszul.differential y (right f z) := by
  letI : LinearOrder (V ⊕ W) :=
    LinearOrder.lift' (fun z : V ⊕ W => (toLex z : Lex (V ⊕ W))) (fun _ _ h => h)
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a z =>
      rw [TensorExteriorKoszul.differential_tmul,map_sum,Fintype.sum_sum_type]
      simp only [right,Algebra.TensorProduct.map_tmul,smul_eq_mul,map_mul,hz,
        zero_mul,TensorProduct.zero_tmul,Finset.sum_const_zero,zero_add]
      rw [TensorExteriorKoszul.differential_tmul]
      apply Finset.sum_congr rfl
      intro w hw
      rw [hy,rightExterior_contraction]
      rfl

theorem left_differential (f : A →ₐ[K] B) (x : V ⊕ W → A) (y : V → B)
    (hx : ∀ v, f (x (Sum.inl v))=y v) (hz : ∀ w, f (x (Sum.inr w))=0)
    (z : A ⊗[K] Simplicial.Ambient (V ⊕ W) K) :
    left f (TensorExteriorKoszul.differential x z) =
      TensorExteriorKoszul.differential y (left f z) := by
  letI : LinearOrder (V ⊕ W) :=
    LinearOrder.lift' (fun z : V ⊕ W => (toLex z : Lex (V ⊕ W))) (fun _ _ h => h)
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a z =>
      rw [TensorExteriorKoszul.differential_tmul,map_sum,Fintype.sum_sum_type]
      simp only [left,Algebra.TensorProduct.map_tmul,smul_eq_mul,map_mul,hz,
        zero_mul,TensorProduct.zero_tmul,Finset.sum_const_zero,add_zero]
      rw [TensorExteriorKoszul.differential_tmul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [hx,leftExterior_contraction]
      rfl

end FourPapers.KoszulSummandProjection

end
end
end


end
