module

public import PaperVerification.FermionNaturalColorBasis
public import PaperVerification.FermionAdmissibleExteriorBlocks
public import PaperVerification.FermionIndependentColorAction
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RepresentationTheory.Basic

/-!
# The natural exterior-tensor coordinates of the actual initial quotient

The tensor basis is normalized by the proved, nonzero orientation coefficient
of the literal ordered exterior multiplication map. This construction does
not presume an explicit sign formula and does not transport a group action.
The actual quotient and its actual coefficient-ideal decomposition are kept
throughout. 
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct DirectSum

namespace PaperVerification.Fermion.NaturalColor

open Exterior

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionNaturalColorBlocks_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- The coefficient comes from a proof about the actual exterior product. -/
def assemblyScalar (m : MultiplicityVector n) (T : MultiplicityColoring m) : F :=
  Classical.choose (assemble_basis_unit (F := F) m T)

theorem assemblyScalar_ne_zero (m : MultiplicityVector n) (T : MultiplicityColoring m) :
    assemblyScalar (F := F) m T≠0 :=
  (Classical.choose_spec (assemble_basis_unit (F := F) m T)).1

theorem assemble_basis_scalar (m : MultiplicityVector n) (T : MultiplicityColoring m) :
    assemble (fun i ↦ (m i).val) (ColorPaths.exteriorColorTensorBasis F m T)=
      assemblyScalar (F := F) m T • (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T.val :=
  (Classical.choose_spec (assemble_basis_unit (F := F) m T)).2

/-- Normalize each genuine tensor basis vector by its proved orientation unit. -/
def normalizedTensorBasis (m : MultiplicityVector n) :
    Module.Basis (MultiplicityColoring m) F (ColorPaths.ExteriorColorTensor F m) :=
  (ColorPaths.exteriorColorTensorBasis F m).unitsSMul
    (fun T ↦ (Units.mk0 (assemblyScalar m T) (assemblyScalar_ne_zero m T))⁻¹)

/-- The normalized basis maps to precisely the original theta-then-xi word. -/
theorem assemble_normalizedTensorBasis (m : MultiplicityVector n)
    (T : MultiplicityColoring m) :
    assemble (fun i ↦ (m i).val) (normalizedTensorBasis (F := F) m T)=
      (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T.val := by
  simp only [normalizedTensorBasis,Module.Basis.unitsSMul_apply,Units.smul_def,map_smul]
  rw [assemble_basis_scalar]
  change (assemblyScalar (F := F) m T)⁻¹ •
    (assemblyScalar (F := F) m T • (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T.val)=_
  rw [smul_smul,inv_mul_cancel₀ (assemblyScalar_ne_zero m T),one_smul]

variable (C : Type*) [AddCommGroup C] [Module F C]

/-- Coefficients are unchanged; only the proved orientation normalization
appears in the exterior tensor factor. -/
def coefficientEquiv (m : MultiplicityVector n) :
    (MultiplicityColoring m → C) ≃ₗ[F] C ⊗[F] ColorPaths.ExteriorColorTensor F m :=
  (Finsupp.linearEquivFunOnFinite F C (MultiplicityColoring m)).symm |>.trans
    ((TensorProduct.finsuppScalarRight F F C (MultiplicityColoring m)).symm.trans
      (TensorProduct.congr (LinearEquiv.refl F C) (normalizedTensorBasis m).repr.symm))

@[simp] theorem coefficientEquiv_single (m : MultiplicityVector n)
    (T : MultiplicityColoring m) (c : C) :
    coefficientEquiv C m (Pi.single T c)=c ⊗ₜ[F] normalizedTensorBasis m T := by
  simp only [coefficientEquiv,LinearEquiv.trans_apply,
    Finsupp.linearEquivFunOnFinite_symm_single,
    TensorProduct.finsuppScalarRight_symm_apply_single,TensorProduct.congr_tmul,
    LinearEquiv.refl_apply,Module.Basis.repr_symm_single,one_smul]

@[simp] theorem coefficientEquiv_symm_tmul_basis (m : MultiplicityVector n)
    (T : MultiplicityColoring m) (c : C) :
    (coefficientEquiv C m).symm (c ⊗ₜ[F] normalizedTensorBasis m T)=Pi.single T c := by
  rw [←coefficientEquiv_single C m T c,LinearEquiv.symm_apply_apply]

/-- The genuine independent tensor of the standard exterior-power actions.
The matrix acts on the original two coordinates before applying exterior powers. -/
def exteriorRepresentation (m : MultiplicityVector n) :
    Representation F (Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
      (ColorPaths.ExteriorColorTensor F m) where
  toFun g := PiTensorProduct.map
    (fun i ↦ exteriorPower.map (m i).val (colorLinear (g i).val))
  map_one' := by
    simp only [Pi.one_apply,Units.val_one,colorLinear_one,exteriorPower.map_id,
      PiTensorProduct.map_id,Module.End.one_eq_id]
  map_mul' g h := by
    change PiTensorProduct.map (fun i ↦ exteriorPower.map (m i).val
      (colorLinear ((g i).val*(h i).val)))=
      (PiTensorProduct.map (fun i ↦ exteriorPower.map (m i).val (colorLinear (g i).val))).comp
        (PiTensorProduct.map (fun i ↦ exteriorPower.map (m i).val (colorLinear (h i).val)))
    rw [←PiTensorProduct.map_comp]
    congr 1
    funext i
    rw [colorLinear_mul,exteriorPower.map_comp]

end PaperVerification.Fermion.NaturalColor

namespace PaperVerification.Fermion.TypeA

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

local instance FermionNaturalColorBlocks_localInst_2 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective

/-- The original quotient, the original colon ideals, and the natural tensor
coordinates. This is independent of any proposed group action. -/
def naturalInitialFunctionEquiv (hn : 0<n) :
    StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₗ[F]
      ((m : MultiplicityVector n) → ExteriorCoefficientBlock (F := F) m) :=
  ((initialCoefficientEquiv hn).trans regroupCoefficientEquiv).trans
    (LinearEquiv.piCongrRight fun m ↦
      NaturalColor.coefficientEquiv (CoefficientQuotient (F := F) m) m)

/-- Restrict exactly the zero blocks, using the independently proved
inadmissible-colon-ideal theorem and the ordinary finite direct-sum equivalence. -/
def naturalInitialAdmissibleEquiv (hn : 0<n) :
    StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₗ[F]
      ⨁ m : {m : MultiplicityVector n // Admissible m},
        ExteriorCoefficientBlock (F := F) m.val :=
  (naturalInitialFunctionEquiv hn).trans
    ((restrictAdmissibleColorBlocksEquiv hn).trans
      (DirectSum.linearEquivFunOnFintype F
        {m : MultiplicityVector n // Admissible m}
        (fun m ↦ ExteriorCoefficientBlock (F := F) m.val)).symm)

/-- The actual coefficient projection of one literal polynomial/exterior word. -/
theorem coefficientProjection_tmul_basis (W : Finset (OddIndex n))
    (p : PolynomialRing F n) :
    coefficientProjection (p ⊗ₜ[F] (Pi.basisFun F (OddIndex n)).ExteriorAlgebra W)=
      Pi.single W (Ideal.Quotient.mk (coefficientIdeal (wordMultiplicityVector W)) p) := by
  classical
  have ht : p ⊗ₜ[F] (Pi.basisFun F (OddIndex n)).ExteriorAlgebra W=
      p • superPolynomialBasis (K := F) W := by
    rw [superPolynomialBasis_apply]
    simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  have hr : (superPolynomialBasis (K := F)).repr
      (p ⊗ₜ[F] (Pi.basisFun F (OddIndex n)).ExteriorAlgebra W)=Finsupp.single W p := by
    rw [ht,map_smul,Module.Basis.repr_self]
    simp
  funext T
  rw [coefficientProjection_apply,hr]
  by_cases h : T=W
  · subst T; simp
  · simp [Finsupp.single_apply,Pi.single_apply,h,Ne.symm h]

/-- Regrouping an actual coefficient singleton retains its original word. -/
theorem regroupCoefficientEquiv_single_word (W : Finset (OddIndex n))
    (c : CoefficientQuotient (F := F) (wordMultiplicityVector W)) :
    regroupCoefficientEquiv (F := F) (Pi.single W c)=
      Pi.single (wordMultiplicityVector W)
        (Pi.single (⟨W,rfl⟩ : MultiplicityColoring (wordMultiplicityVector W)) c) := by
  classical
  funext m T
  by_cases hm : wordMultiplicityVector W=m
  · subst m
    by_cases hT : T.val=W
    · have hT' : T=(⟨W,rfl⟩ : MultiplicityColoring (wordMultiplicityVector W)) :=
        Subtype.ext hT
      subst T
      obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective c
      simp [regroupCoefficientEquiv]
    · have hT' : T≠(⟨W,rfl⟩ : MultiplicityColoring (wordMultiplicityVector W)) := by
        intro h
        exact hT (congrArg Subtype.val h)
      simp [regroupCoefficientEquiv,Pi.single_apply,hT,Ne.symm hT,hT',Ne.symm hT']
  · have hT : T.val≠W := by
      intro h
      exact hm (by simpa only [h] using T.property)
    simp [regroupCoefficientEquiv,Pi.single_apply,hm,Ne.symm hm,hT,Ne.symm hT]

/-- On an original quotient word, the new coordinates are exactly the
normalized natural exterior tensor; the polynomial representative is unchanged. -/
theorem naturalInitialFunctionEquiv_mk_word (hn : 0<n)
    (W : Finset (OddIndex n)) (p : PolynomialRing F n) :
    naturalInitialFunctionEquiv hn
      (strictInitialProjection (data (F := F) hn)
        (p ⊗ₜ[F] (Pi.basisFun F (OddIndex n)).ExteriorAlgebra W))=
      Pi.single (wordMultiplicityVector W)
        (Ideal.Quotient.mk (coefficientIdeal (wordMultiplicityVector W)) p ⊗ₜ[F]
          NaturalColor.normalizedTensorBasis (wordMultiplicityVector W) ⟨W,rfl⟩) := by
  classical
  simp only [naturalInitialFunctionEquiv,LinearEquiv.trans_apply,
    initialCoefficientEquiv_mk,coefficientProjection_tmul_basis,
    regroupCoefficientEquiv_single_word]
  funext m
  rw [LinearEquiv.piCongrRight_apply]
  by_cases hm : wordMultiplicityVector W=m
  · subst m
    simp only [Pi.single_eq_same,NaturalColor.coefficientEquiv_single]
  · simp only [Pi.single_eq_of_ne (Ne.symm hm)]
    exact (NaturalColor.coefficientEquiv (CoefficientQuotient (F := F) m) m).map_zero

/-- The inverse natural coordinates send a normalized pure tensor to the
actual quotient class of its ordered exterior product. -/
theorem naturalInitialFunctionEquiv_symm_basis (hn : 0<n)
    (m : MultiplicityVector n) (T : MultiplicityColoring m) (p : PolynomialRing F n) :
    (naturalInitialFunctionEquiv hn).symm
      (Pi.single m (Ideal.Quotient.mk (coefficientIdeal m) p ⊗ₜ[F]
        NaturalColor.normalizedTensorBasis m T))=
      strictInitialProjection (data (F := F) hn)
        (p ⊗ₜ[F] NaturalColor.assemble (fun i ↦ (m i).val)
          (NaturalColor.normalizedTensorBasis m T)) := by
  classical
  rw [NaturalColor.assemble_normalizedTensorBasis]
  rcases T with ⟨W,hW⟩
  subst m
  rw [←naturalInitialFunctionEquiv_mk_word hn W p,LinearEquiv.symm_apply_apply]

/-- The defining quotient formula holds for every exterior tensor, not only
for basis tensors. It fixes the multiplication intended in the paper. -/
theorem naturalInitialFunctionEquiv_symm_tmul (hn : 0<n)
    (m : MultiplicityVector n) (p : PolynomialRing F n)
    (x : ColorPaths.ExteriorColorTensor F m) :
    (naturalInitialFunctionEquiv hn).symm
      (Pi.single m (Ideal.Quotient.mk (coefficientIdeal m) p ⊗ₜ[F] x))=
      strictInitialProjection (data (F := F) hn)
        (p ⊗ₜ[F] NaturalColor.assemble (fun i ↦ (m i).val) x) := by
  classical
  let L : ColorPaths.ExteriorColorTensor F m →ₗ[F]
      StrictMultiplicityInitialQuotient (data (F := F) hn) :=
    (naturalInitialFunctionEquiv hn).symm.toLinearMap.comp
      ((LinearMap.single F (fun j ↦ ExteriorCoefficientBlock (F := F) j) m).comp
        (TensorProduct.mk F (CoefficientQuotient (F := F) m)
          (ColorPaths.ExteriorColorTensor F m) (Ideal.Quotient.mk (coefficientIdeal m) p)))
  let R : ColorPaths.ExteriorColorTensor F m →ₗ[F]
      StrictMultiplicityInitialQuotient (data (F := F) hn) :=
    (strictInitialProjection (data (F := F) hn)).toLinearMap.comp
      ((TensorProduct.mk F (PolynomialRing F n) (ExteriorAlgebra F (OddModule F n)) p).comp
        (NaturalColor.assemble (fun i ↦ (m i).val)))
  have h : L=R := (NaturalColor.normalizedTensorBasis m).ext fun T ↦
    naturalInitialFunctionEquiv_symm_basis hn m T p
  exact LinearMap.congr_fun h x

/-- The target map is the identity on polynomial coefficient classes and
the actual exterior power of the original color matrix at each index. -/
def naturalBlockMap (A : Fin n → Matrix (Fin 2) (Fin 2) F)
    (m : MultiplicityVector n) :
    ExteriorCoefficientBlock (F := F) m →ₗ[F] ExteriorCoefficientBlock (F := F) m :=
  TensorProduct.map LinearMap.id
    (PiTensorProduct.map fun i ↦ exteriorPower.map (m i).val (NaturalColor.colorLinear (A i)))

def naturalFunctionMap (A : Fin n → Matrix (Fin 2) (Fin 2) F) :
    ((m : MultiplicityVector n) → ExteriorCoefficientBlock (F := F) m) →ₗ[F]
      ((m : MultiplicityVector n) → ExteriorCoefficientBlock (F := F) m) :=
  LinearMap.piMap (naturalBlockMap A)

@[simp] theorem naturalFunctionMap_single
    (A : Fin n → Matrix (Fin 2) (Fin 2) F) (m : MultiplicityVector n)
    (z : ExteriorCoefficientBlock (F := F) m) :
    naturalFunctionMap A (Pi.single m z)=Pi.single m (naturalBlockMap A m z) := by
  classical
  funext j
  by_cases h : j=m
  · subst j; simp [naturalFunctionMap,LinearMap.piMap]
  · simp [naturalFunctionMap,LinearMap.piMap,Pi.single_apply,h,Ne.symm h]

/-- Equivariance on an entire actual coefficient block, derived from the
pure-tensor quotient formula and the original exterior multiplication. -/
theorem naturalInitialFunctionEquiv_symm_block (hn : 0<n)
    (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (m : MultiplicityVector n) (z : ExteriorCoefficientBlock (F := F) m) :
    (naturalInitialFunctionEquiv hn).symm
      (Pi.single m (naturalBlockMap (fun i ↦ (g i).val) m z))=
      ColorAction.initialQuotientEquiv g (data (F := F) hn)
        ((naturalInitialFunctionEquiv hn).symm (Pi.single m z)) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero (naturalBlockMap (F := F) (fun i ↦ (g i).val) m),Pi.single_zero,
        (naturalInitialFunctionEquiv (F := F) hn).symm.map_zero]
      exact (ColorAction.initialQuotientEquiv g (data (F := F) hn)).map_zero.symm
  | add z w hz hw =>
      simp only [map_add,Pi.single_add,hz,hw]
  | tmul c x =>
      obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [naturalBlockMap,TensorProduct.map_tmul,LinearMap.id_apply]
      rw [naturalInitialFunctionEquiv_symm_tmul,naturalInitialFunctionEquiv_symm_tmul]
      simp only [strictInitialProjection,ColorAction.initialQuotientEquiv_mk]
      change strictInitialProjection (data (F := F) hn)
        (p ⊗ₜ[F] NaturalColor.assemble (fun i ↦ (m i).val)
          (PiTensorProduct.map (fun i ↦ exteriorPower.map (m i).val
            (NaturalColor.colorLinear (g i).val)) x))=
        strictInitialProjection (data (F := F) hn)
          (ColorAction.indexAmbient (fun i ↦ (g i).val)
            (p ⊗ₜ[F] NaturalColor.assemble (fun i ↦ (m i).val) x))
      simp only [ColorAction.indexAmbient,Algebra.TensorProduct.map_tmul,AlgHom.id_apply]
      congr 1
      congr 1
      exact (NaturalColor.assemble_natural (fun i ↦ (m i).val)
        (fun i ↦ (g i).val) x).symm

/-- The natural comparison intertwines independently defined actions for
all independent color changes; no action is defined by this equivalence. -/
theorem naturalInitialFunctionEquiv_equivariant (hn : 0<n)
    (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (x : StrictMultiplicityInitialQuotient (data (F := F) hn)) :
    naturalInitialFunctionEquiv hn (ColorAction.initialQuotientEquiv g (data (F := F) hn) x)=
      naturalFunctionMap (fun i ↦ (g i).val) (naturalInitialFunctionEquiv hn x) := by
  classical
  let e := naturalInitialFunctionEquiv (F := F) hn
  have h : e.symm.toLinearMap.comp (naturalFunctionMap (fun i ↦ (g i).val))=
      (ColorAction.initialQuotientEquiv g (data (F := F) hn)).toLinearMap.comp e.symm.toLinearMap := by
    apply LinearMap.pi_ext
    intro m z
    change e.symm (naturalFunctionMap (fun i ↦ (g i).val) (Pi.single m z))=_
    rw [naturalFunctionMap_single]
    exact naturalInitialFunctionEquiv_symm_block hn g m z
  have hx := LinearMap.congr_fun h (e x)
  change e.symm (naturalFunctionMap (fun i ↦ (g i).val) (e x))=
    ColorAction.initialQuotientEquiv g (data (F := F) hn) (e.symm (e x)) at hx
  rw [e.symm_apply_apply] at hx
  exact (congrArg e hx.symm).trans (e.apply_symm_apply _)

/-- The full admissible-index comparison retains the actual independent
GL(2)^n action; equality is given in every original direct-sum component. -/
theorem naturalInitialAdmissibleEquiv_equivariant (hn : 0<n)
    (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (x : StrictMultiplicityInitialQuotient (data (F := F) hn))
    (m : {m : MultiplicityVector n // Admissible m}) :
    (naturalInitialAdmissibleEquiv hn
      (ColorAction.initialQuotientEquiv g (data (F := F) hn) x)) m=
      naturalBlockMap (fun i ↦ (g i).val) m.val
        ((naturalInitialAdmissibleEquiv hn x) m) := by
  change (naturalInitialFunctionEquiv hn
      (ColorAction.initialQuotientEquiv g (data (F := F) hn) x)) m.val=
    naturalBlockMap (fun i ↦ (g i).val) m.val ((naturalInitialFunctionEquiv hn x) m.val)
  exact congrFun (naturalInitialFunctionEquiv_equivariant hn g x) m.val

/-- The target carries the ordinary direct sum of independent exterior
representations and trivial actions on the actual colon quotients. -/
def naturalAdmissibleRepresentation :
    Representation F (Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
      (⨁ m : {m : MultiplicityVector n // Admissible m},
        ExteriorCoefficientBlock (F := F) m.val) :=
  Representation.directSum fun m ↦
    (Representation.trivial F (Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
      (CoefficientQuotient (F := F) m.val)).tprod
      (NaturalColor.exteriorRepresentation m.val)

@[simp] theorem naturalAdmissibleRepresentation_apply
    (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (x : ⨁ m : {m : MultiplicityVector n // Admissible m},
      ExteriorCoefficientBlock (F := F) m.val)
    (m : {m : MultiplicityVector n // Admissible m}) :
    naturalAdmissibleRepresentation (F := F) g x m=
      naturalBlockMap (fun i ↦ (g i).val) m.val (x m) := rfl

/-- Full equivariance of the admissible direct-sum equivalence for the
original GL(2)^n actions on both sides. -/
theorem naturalInitialAdmissibleEquiv_intertwines (hn : 0<n)
    (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (x : StrictMultiplicityInitialQuotient (data (F := F) hn)) :
    naturalInitialAdmissibleEquiv hn (ColorAction.initialQuotientEquiv g (data (F := F) hn) x)=
      naturalAdmissibleRepresentation g (naturalInitialAdmissibleEquiv hn x) := by
  ext m
  rw [naturalAdmissibleRepresentation_apply]
  exact naturalInitialAdmissibleEquiv_equivariant hn g x m

/-- Multiplication under the natural comparison is exactly polynomial
multiplication and the original exterior product, for every pair of pure
coefficient tensors. These tensors span all blocks, so the formula specifies
the entire multiplication and its actual exterior signs. -/
theorem naturalInitialFunctionEquiv_symm_mul (hn : 0<n)
    (m l : MultiplicityVector n) (p q : PolynomialRing F n)
    (x : ColorPaths.ExteriorColorTensor F m) (y : ColorPaths.ExteriorColorTensor F l) :
    (naturalInitialFunctionEquiv hn).symm
      (Pi.single m (Ideal.Quotient.mk (coefficientIdeal m) p ⊗ₜ[F] x)) *
    (naturalInitialFunctionEquiv hn).symm
      (Pi.single l (Ideal.Quotient.mk (coefficientIdeal l) q ⊗ₜ[F] y))=
      strictInitialProjection (data (F := F) hn)
        ((p*q) ⊗ₜ[F] (NaturalColor.assemble (fun i ↦ (m i).val) x *
          NaturalColor.assemble (fun i ↦ (l i).val) y)) := by
  rw [naturalInitialFunctionEquiv_symm_tmul,naturalInitialFunctionEquiv_symm_tmul,
    ←map_mul,Algebra.TensorProduct.tmul_mul_tmul]

end PaperVerification.Fermion.TypeA
