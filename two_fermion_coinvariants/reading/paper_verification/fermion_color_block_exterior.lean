module

public import PaperVerification.FermionColorMultiplicityEnumeration
public import PaperVerification.FermionMultiplicityQuotientDecomposition
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Actual exterior-power factors for the multiplicity blocks

The four original marks are identified explicitly with the subsets of the
standard two-element basis. The cardinality of that subset is the original
mark degree. Mathlib's exterior-power and tensor-product bases therefore
identify a block's actual coloring module with the tensor of the genuine
exterior powers of the two-dimensional color space. This is a vector-space
identification; equivariance must be proved separately, not assumed here.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped DirectSum
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.ColorPaths

open Endpoint Paths

/-- The local subset of the original theta/xi basis, in its fixed order. -/
def markSubset : Mark → Finset (Fin 2)
  | .unmarked => ∅
  | .theta => {0}
  | .xi => {1}
  | .double => {0,1}

def subsetMark (s : Finset (Fin 2)) : Mark :=
  if (0 : Fin 2)∈s then if (1 : Fin 2)∈s then .double else .theta
  else if (1 : Fin 2)∈s then .xi else .unmarked

@[simp] theorem subsetMark_markSubset (a : Mark) : subsetMark (markSubset a)=a := by
  cases a <;> simp [subsetMark,markSubset]

@[simp] theorem markSubset_subsetMark (s : Finset (Fin 2)) : markSubset (subsetMark s)=s := by
  ext i
  fin_cases i <;>
    by_cases h0 : (0 : Fin 2)∈s <;> by_cases h1 : (1 : Fin 2)∈s <;>
    simp [subsetMark,markSubset,h0,h1]

def markSubsetEquiv : Mark ≃ Finset (Fin 2) :=
  ⟨markSubset,subsetMark,subsetMark_markSubset,markSubset_subsetMark⟩

@[simp] theorem markSubset_card (a : Mark) : (markSubset a).card=markDegree a := by
  cases a <;> simp [markSubset,markDegree]

/-- Degree preservation identifies the exact local exterior-power indices. -/
def localColorExteriorIndexEquiv (m : Fin 3) :
    LocalColorFiber m ≃ Set.powersetCard (Fin 2) m.val :=
  markSubsetEquiv.subtypeEquiv (fun a ↦ by
    change markDegree a=m.val ↔ (markSubset a).card=m.val
    rw [markSubset_card])

variable {n : ℕ}

def coloringExteriorIndexEquiv (m : MultiplicityVector n) :
    MultiplicityColoring m ≃ (∀ i,Set.powersetCard (Fin 2) (m i).val) :=
  (coloringLocalEquiv m).trans (Equiv.piCongrRight fun i ↦ localColorExteriorIndexEquiv (m i))

variable (R : Type*) [CommRing R]

/-- The tensor of the genuine exterior powers, not an abstract vector space
whose dimension was chosen to match the desired formula. -/
abbrev ExteriorColorTensor (m : MultiplicityVector n) :=
  ⨂[R] i : Fin n, (⋀[R]^((m i).val) (Fin 2 → R))

/-- The standard additive group of the actual tensor of exterior powers. -/
instance exteriorColorTensorAddCommGroup (m : MultiplicityVector n) :
    AddCommGroup (ExteriorColorTensor R m) :=
  inferInstanceAs (AddCommGroup (⨂[R] i : Fin n, (⋀[R]^((m i).val) (Fin 2 → R))))

def exteriorColorTensorBasis (m : MultiplicityVector n) :
    Module.Basis (MultiplicityColoring m) R (ExteriorColorTensor R m) :=
  (_root_.Basis.piTensorProduct
    (fun i ↦ (Pi.basisFun R (Fin 2)).exteriorPower (m i).val)).reindex
      (coloringExteriorIndexEquiv m).symm

/-- The basis vectors are the actual pure tensors of ordered exterior words. -/
@[simp] theorem exteriorColorTensorBasis_apply (m : MultiplicityVector n)
    (T : MultiplicityColoring m) :
    exteriorColorTensorBasis R m T=
      PiTensorProduct.tprod R (fun i ↦
        (Pi.basisFun R (Fin 2)).exteriorPower (m i).val
          ((coloringExteriorIndexEquiv m T) i)) := by
  simp only [exteriorColorTensorBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    _root_.Basis.piTensorProduct_apply]

/-- Number of swaps from theta-then-xi order to increasing index order. -/
def colorCrossings (W : Finset (OddIndex n)) : ℕ :=
  ∑ i∈W.toRight,(W.toLeft.filter (fun j ↦ i<j)).card

/-- The orientation correction is an actual unit over every coefficient ring. -/
def colorReorderUnit (W : Finset (OddIndex n)) : Rˣ :=
  (-1 : Rˣ)^colorCrossings W

/-- The tensor basis with the required theta-then-xi orientation. The equality
with the original exterior word and equivariance are separate theorems; the
unit twist here does not assert either without proof. -/
def signedExteriorColorTensorBasis (m : MultiplicityVector n) :
    Module.Basis (MultiplicityColoring m) R (ExteriorColorTensor R m) :=
  (exteriorColorTensorBasis R m).unitsSMul (fun T ↦ colorReorderUnit R T.val)

@[simp] theorem signedExteriorColorTensorBasis_apply (m : MultiplicityVector n)
    (T : MultiplicityColoring m) :
    signedExteriorColorTensorBasis R m T=
      colorReorderUnit R T.val • exteriorColorTensorBasis R m T :=
  Module.Basis.unitsSMul_apply T

variable (C : Type*) [AddCommGroup C] [Module R C]

/-- An arbitrary actual coefficient module is retained unchanged in the
left tensor factor; no freeness or finite-dimensional assumption is added. -/
def coefficientColorTensorEquiv (m : MultiplicityVector n) :
    (MultiplicityColoring m → C) ≃ₗ[R] C ⊗[R] ExteriorColorTensor R m :=
  (Finsupp.linearEquivFunOnFinite R C (MultiplicityColoring m)).symm |>.trans
    ((TensorProduct.finsuppScalarRight R R C (MultiplicityColoring m)).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R C) (exteriorColorTensorBasis R m).repr.symm))

@[simp] theorem coefficientColorTensorEquiv_single (m : MultiplicityVector n)
    (T : MultiplicityColoring m) (c : C) :
    coefficientColorTensorEquiv R C m (Pi.single T c)=
      c ⊗ₜ[R] exteriorColorTensorBasis R m T := by
  simp only [coefficientColorTensorEquiv,LinearEquiv.trans_apply,
    Finsupp.linearEquivFunOnFinite_symm_single,
    TensorProduct.finsuppScalarRight_symm_apply_single,TensorProduct.congr_tmul,
    LinearEquiv.refl_apply,Module.Basis.repr_symm_single,one_smul]

/-- The coefficient/tensor equivalence including the explicit orientation
unit. This is the candidate for the natural equivariant comparison. -/
def signedCoefficientColorTensorEquiv (m : MultiplicityVector n) :
    (MultiplicityColoring m → C) ≃ₗ[R] C ⊗[R] ExteriorColorTensor R m :=
  (Finsupp.linearEquivFunOnFinite R C (MultiplicityColoring m)).symm |>.trans
    ((TensorProduct.finsuppScalarRight R R C (MultiplicityColoring m)).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R C)
        (signedExteriorColorTensorBasis R m).repr.symm))

@[simp] theorem signedCoefficientColorTensorEquiv_single (m : MultiplicityVector n)
    (T : MultiplicityColoring m) (c : C) :
    signedCoefficientColorTensorEquiv R C m (Pi.single T c)=
      c ⊗ₜ[R] (colorReorderUnit R T.val • exteriorColorTensorBasis R m T) := by
  simp only [signedCoefficientColorTensorEquiv,LinearEquiv.trans_apply,
    Finsupp.linearEquivFunOnFinite_symm_single,
    TensorProduct.finsuppScalarRight_symm_apply_single,TensorProduct.congr_tmul,
    LinearEquiv.refl_apply,Module.Basis.repr_symm_single,one_smul,
    signedExteriorColorTensorBasis_apply]

end PaperVerification.Fermion.ColorPaths

namespace PaperVerification.Fermion.TypeA

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The vector-space form of the special fiber in Theorem 8.1, with the
original colon quotients and genuine exterior-power tensor factors.
Inadmissible coefficient quotients are zero by `inadmissible_coefficientIdeal_eq_top`.
Equivariance of this map is an additional obligation. -/
def initialExteriorTensorEquiv (hn : 0<n) :
    StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₗ[F]
      ⨁ m : MultiplicityVector n,
        CoefficientQuotient (F := F) m ⊗[F] ColorPaths.ExteriorColorTensor F m :=
  (initialMultiplicityDirectSumEquiv hn).trans
    (DirectSum.congrLinearEquiv fun m ↦
      ColorPaths.coefficientColorTensorEquiv F (CoefficientQuotient (F := F) m) m)

/-- The same actual initial quotient comparison with the orientation unit
retained. No action is defined by transporting along this equivalence. -/
def initialSignedExteriorTensorEquiv (hn : 0<n) :
    StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₗ[F]
      ⨁ m : MultiplicityVector n,
        CoefficientQuotient (F := F) m ⊗[F] ColorPaths.ExteriorColorTensor F m :=
  (initialMultiplicityDirectSumEquiv hn).trans
    (DirectSum.congrLinearEquiv fun m ↦
      ColorPaths.signedCoefficientColorTensorEquiv F (CoefficientQuotient (F := F) m) m)

end PaperVerification.Fermion.TypeA
