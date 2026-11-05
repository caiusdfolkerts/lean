module

public import PaperVerification.FermionCoefficientBoxBasis
public import PaperVerification.FermionColorRational
public import TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower

/-!
# The genuine exterior-tensor representations in the multiplicity blocks

Every factor carries the actual exterior power of the standard GL2 action.
Their tensor action is defined by applying those maps to pure tensors. The
independent product group and its diagonal subgroup are both retained. The
diagonal eigenvalues and polynomiality follow from these original maps, not
from an action transported along the proposed quotient decomposition.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct DirectSum

namespace PaperVerification.Fermion.ColorPaths

open Endpoint Paths

variable (R : Type*) [CommRing R] {n : ℕ}

/-- Independent standard exterior-power actions at the original indices. -/
def independentExteriorColorRepresentation (m : MultiplicityVector n) :
    Representation R (Fin n → Matrix.GeneralLinearGroup (Fin 2) R)
      (ExteriorColorTensor R m) where
  toFun g := PiTensorProduct.map (fun i ↦ (TauCeti.extPowerRep R 2 (m i).val) (g i))
  map_one' := by
    simp only [Pi.one_apply,map_one,PiTensorProduct.map_one]
  map_mul' g h := by
    simp only [Pi.mul_apply,map_mul,PiTensorProduct.map_mul]

/-- The diagonal GL2 subgroup acts by the same matrix on each factor. -/
def diagonalExteriorColorRepresentation (m : MultiplicityVector n) :
    Representation R (Matrix.GeneralLinearGroup (Fin 2) R) (ExteriorColorTensor R m) where
  toFun g := PiTensorProduct.map (fun i ↦ (TauCeti.extPowerRep R 2 (m i).val) g)
  map_one' := by simp only [map_one,PiTensorProduct.map_one]
  map_mul' g h := by simp only [map_mul,PiTensorProduct.map_mul]

@[simp] theorem independentExteriorColorRepresentation_diagonal
    (m : MultiplicityVector n) (g : Matrix.GeneralLinearGroup (Fin 2) R) :
    independentExteriorColorRepresentation R m (fun _ ↦ g)=
      diagonalExteriorColorRepresentation R m g := rfl

@[simp] theorem diagonalExteriorColorRepresentation_tprod
    (m : MultiplicityVector n) (g : Matrix.GeneralLinearGroup (Fin 2) R)
    (x : ∀ i,⋀[R]^((m i).val) (Fin 2 → R)) :
    diagonalExteriorColorRepresentation R m g (PiTensorProduct.tprod R x)=
      PiTensorProduct.tprod R (fun i ↦ (TauCeti.extPowerRep R 2 (m i).val) g (x i)) :=
  PiTensorProduct.map_tprod _ _

theorem localColorEigenvalue (t : Fin 2 → R) (a : Mark) :
    (∏ i∈markSubset a,t i)=markColor (t 0) (t 1) a := by
  cases a <;> simp [markSubset,markColor]

theorem wordColor_eq_prod_wordMark (u v : R) (W : Finset (OddIndex n)) :
    wordColor u v W=∏ i,markColor u v (wordMark W i) := by
  rw [←wordColor_wordOfMarks]
  exact congrArg (wordColor u v) ((marksWordEquiv n).right_inv W).symm

@[simp] theorem coloringExteriorIndexEquiv_val (m : MultiplicityVector n)
    (T : MultiplicityColoring m) (i : Fin n) :
    ((coloringExteriorIndexEquiv m T) i).val=markSubset (wordMark T.val i) := rfl

/-- The naturally defined tensor action has the original color eigenvalue.
This calculation does not use an equivalence with the strict quotient. -/
theorem diagonalExteriorColorRepresentation_basis (m : MultiplicityVector n)
    (t : Fin 2 → Rˣ) (T : MultiplicityColoring m) :
    diagonalExteriorColorRepresentation R m (TauCeti.diagGL t)
        (exteriorColorTensorBasis R m T)=
      wordColor (t 0 : R) (t 1 : R) T.val • exteriorColorTensorBasis R m T := by
  rw [exteriorColorTensorBasis_apply,diagonalExteriorColorRepresentation_tprod]
  have h (i : Fin n) :
      (TauCeti.extPowerRep R 2 (m i).val) (TauCeti.diagGL t)
        ((Pi.basisFun R (Fin 2)).exteriorPower (m i).val
          ((coloringExteriorIndexEquiv m T) i))=
      markColor (t 0 : R) (t 1 : R) (wordMark T.val i) •
        (Pi.basisFun R (Fin 2)).exteriorPower (m i).val
          ((coloringExteriorIndexEquiv m T) i) := by
    rw [Representation.exteriorPower_apply,
      (Pi.basisFun R (Fin 2)).map_exteriorPower_of_apply
        (TauCeti.stdRep R 2 (TauCeti.diagGL t)) (fun j ↦ (t j : R))
        (TauCeti.stdRep_diagGL_apply_basisFun t),coloringExteriorIndexEquiv_val,
      localColorEigenvalue]
  simp only [h]
  rw [(PiTensorProduct.tprod R).map_smul_univ,wordColor_eq_prod_wordMark]

variable {F : Type*} [Field F]

/-- The character of each genuine exterior tensor is the coloring factor
printed in equation (22). -/
theorem diagonalExteriorColorRepresentation_character (m : MultiplicityVector n)
    (t : Fin 2 → Fˣ) :
    Representation.character (V := ExteriorColorTensor F m)
      (diagonalExteriorColorRepresentation F m) (TauCeti.diagGL t)=
      ((t 0 : F)+(t 1 : F))^singleCount m*
        ((t 0 : F)*(t 1 : F))^doubleCount m := by
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace F (exteriorColorTensorBasis F m),Matrix.trace]
  rw [←coloring_color_sum (t 0 : F) (t 1 : F) m]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Matrix.diag_apply,LinearMap.toMatrix_apply,diagonalExteriorColorRepresentation_basis]
  simp only [map_smul,Module.Basis.repr_self,Finsupp.smul_apply,
    Finsupp.single_eq_same,smul_eq_mul,mul_one]

/-- Polynomiality of the natural tensor action follows entrywise from the
polynomiality of the actual exterior powers; the tensor factors may have
different exterior degrees. -/
theorem diagonalExteriorColorRepresentation_polynomial (m : MultiplicityVector n) :
    TauCeti.IsPolynomialRep (diagonalExteriorColorRepresentation ℂ m) := by
  let b (i : Fin n) := (Pi.basisFun ℂ (Fin 2)).exteriorPower (m i).val
  let B := _root_.Basis.piTensorProduct b
  apply (TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions B).mpr
  intro a c
  have he : (fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ ↦
      LinearMap.toMatrix B B (diagonalExteriorColorRepresentation ℂ m g) a c)=
      ∏ i,fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ ↦
        LinearMap.toMatrix (b i) (b i) (TauCeti.extPowerRep ℂ 2 (m i).val g) (a i) (c i) := by
    funext g
    simp only [B,LinearMap.toMatrix_apply,_root_.Basis.piTensorProduct_apply,
      diagonalExteriorColorRepresentation,MonoidHom.coe_mk,OneHom.coe_mk,
      PiTensorProduct.map_tprod,_root_.Basis.piTensorProduct_repr_tprod_apply,
      Finset.prod_apply]
  rw [he]
  apply Subalgebra.prod_mem
  intro i hi
  exact (TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions (b i)).mp
    ((TauCeti.isPolynomialRep_stdRep 2).exteriorPower (m i).val) (a i) (c i)

end PaperVerification.Fermion.ColorPaths

namespace PaperVerification.Fermion.TypeA

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- Polynomial coefficients carry the trivial group action, as in the paper. -/
def exteriorCoefficientRepresentation (m : MultiplicityVector n) :
    Representation F (Matrix.GeneralLinearGroup (Fin 2) F)
      (ExteriorCoefficientBlock (F := F) m) :=
  (Representation.trivial F (Matrix.GeneralLinearGroup (Fin 2) F)
    (CoefficientQuotient (F := F) m)).tprod
      (ColorPaths.diagonalExteriorColorRepresentation F m)

theorem coefficientTrivialRepresentation_polynomial (hn : 0<n) (m : MultiplicityVector n) :
    TauCeti.IsPolynomialRep
      (Representation.trivial ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ)
        (CoefficientQuotient (F := ℂ) m)) := by
  apply (TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions
    (coefficientBoxBasis (F := ℂ) hn m)).mpr
  intro a b
  convert (TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions ℂ 2).algebraMap_mem
    (if a=b then (1 : ℂ) else 0) using 1
  funext g
  simp only [LinearMap.toMatrix_apply,Representation.trivial_apply,
    Module.Basis.repr_self,Finsupp.single_apply,Pi.algebraMap_apply,
    Algebra.algebraMap_self_apply,eq_comm]

theorem exteriorCoefficientRepresentation_polynomial (hn : 0<n) (m : MultiplicityVector n) :
    TauCeti.IsPolynomialRep (exteriorCoefficientRepresentation (F := ℂ) m) :=
  (coefficientTrivialRepresentation_polynomial hn m).tprod
    (ColorPaths.diagonalExteriorColorRepresentation_polynomial m)

/-- The target direct sum has its original tensor representations. In
particular its action is independent of any comparison with the quotient. -/
def admissibleExteriorRepresentation :
    Representation F (Matrix.GeneralLinearGroup (Fin 2) F)
      (⨁ m : {m : MultiplicityVector n // Admissible m},
        ExteriorCoefficientBlock (F := F) m.val) :=
  Representation.directSum (fun m ↦ exteriorCoefficientRepresentation m.val)

theorem admissibleExteriorRepresentation_rational (hn : 0<n) :
    TauCeti.IsRationalRep (admissibleExteriorRepresentation (F := ℂ) (n := n)) :=
  TauCeti.IsRationalRep.directSum
    (V := fun m : {m : MultiplicityVector n // Admissible m} ↦
      ExteriorCoefficientBlock (F := ℂ) m.val)
    (σ := fun m ↦ exteriorCoefficientRepresentation (F := ℂ) m.val)
    (fun m ↦ (exteriorCoefficientRepresentation_polynomial hn m.val).isRationalRep)

end PaperVerification.Fermion.TypeA
