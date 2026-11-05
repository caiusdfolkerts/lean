module

public import PaperVerification.FermionColorGradedDecomposition

/-!
# The tensor-power and determinant form printed in Section 8.2

The target uses the actual standard tensor-power action and actual
determinant character. Tau Ceti's top-exterior-power comparison identifies
that character with the determinant line. Character comparison here is
noncanonical, exactly as the paper permits for the original quotient.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped DirectSum
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.ColorPaths

variable {F : Type*} [Field F] {n : ℕ}

abbrev TensorDeterminantColorSpace (m : MultiplicityVector n) :=
  (⨂[F]^(singleCount m) (Fin 2 → F)) ⊗[F] F

instance tensorDeterminantColorSpaceAddCommGroup (m : MultiplicityVector n) :
    AddCommGroup (TensorDeterminantColorSpace (F := F) m) :=
  inferInstanceAs (AddCommGroup ((⨂[F]^(singleCount m) (Fin 2 → F)) ⊗[F] F))

/-- Standard tensor power tensored with the genuine determinant power. -/
def tensorDeterminantColorRepresentation (m : MultiplicityVector n) :
    Representation F (Matrix.GeneralLinearGroup (Fin 2) F)
      (TensorDeterminantColorSpace (F := F) m) :=
  (TauCeti.tensorPowerRep F 2 (singleCount m)).tprod
    (TauCeti.detPowerRep F 2 (doubleCount m : ℤ))

theorem tensorDeterminantColorRepresentation_character
    (m : MultiplicityVector n) (t : Fin 2 → Fˣ) :
    Representation.character (k := F) (V := TensorDeterminantColorSpace (F := F) m)
      (tensorDeterminantColorRepresentation (F := F) m) (TauCeti.diagGL t)=
      ((t 0 : F)+(t 1 : F))^singleCount m*
        ((t 0 : F)*(t 1 : F))^doubleCount m := by
  have ht : Representation.character (k := F) (V := TensorDeterminantColorSpace (F := F) m)
      (tensorDeterminantColorRepresentation (F := F) m) (TauCeti.diagGL t)=
      (TauCeti.tensorPowerRep F 2 (singleCount m)).character (TauCeti.diagGL t)*
      (TauCeti.detPowerRep F 2 (doubleCount m : ℤ)).character (TauCeti.diagGL t) := by
    exact congrFun (Representation.char_tensor (k := F)
      (V := ⨂[F]^(singleCount m) (Fin 2 → F)) (W := F)
      (TauCeti.tensorPowerRep F 2 (singleCount m))
      (TauCeti.detPowerRep F 2 (doubleCount m : ℤ))) (TauCeti.diagGL t)
  rw [ht,TauCeti.char_tensorPowerRep,TauCeti.char_detPowerRep]
  simp only [zpow_natCast,Units.val_pow_eq_pow_val,Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply,Matrix.det_fin_two,TauCeti.diagGL_apply,
    show (0 : Fin 2)≠1 by decide,show (1 : Fin 2)≠0 by decide,
    if_true,if_false,mul_zero,sub_zero]

theorem tensorDeterminantColorRepresentation_polynomial (m : MultiplicityVector n) :
    TauCeti.IsPolynomialRep (tensorDeterminantColorRepresentation (F := ℂ) m) :=
  (TauCeti.isPolynomialRep_tensorPowerRep 2 (singleCount m)).tprod
    (TauCeti.isPolynomialRep_detPowerRep_of_nonneg (Int.natCast_nonneg _))

/-- This comparison concerns the actual original actions on both tensor
spaces, not an action defined by transporting through an equivalence. -/
theorem exteriorTensor_equiv_tensorDeterminant (m : MultiplicityVector n) :
    Nonempty ((diagonalExteriorColorRepresentation ℂ m).Equiv
      (tensorDeterminantColorRepresentation (F := ℂ) m)) :=
  TauCeti.IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    (W := ExteriorColorTensor ℂ m) (W' := TensorDeterminantColorSpace (F := ℂ) m)
    (ρ := diagonalExteriorColorRepresentation ℂ m)
    (σ := tensorDeterminantColorRepresentation (F := ℂ) m)
    (diagonalExteriorColorRepresentation_polynomial m).isRationalRep
    (tensorDeterminantColorRepresentation_polynomial m).isRationalRep
    (fun t ↦ by rw [diagonalExteriorColorRepresentation_character,
      tensorDeterminantColorRepresentation_character])

end PaperVerification.Fermion.ColorPaths

namespace PaperVerification.Fermion.TypeA

variable {n : ℕ}

abbrev GradedPaperColorBlock (m : MultiplicityVector n) (k : ℕ) :=
  coefficientPolynomialPiece (F := ℂ) m k ⊗[ℂ]
    ColorPaths.TensorDeterminantColorSpace (F := ℂ) m

instance gradedPaperColorBlockAddCommGroup (m : MultiplicityVector n) (k : ℕ) :
    AddCommGroup (GradedPaperColorBlock m k) :=
  inferInstanceAs (AddCommGroup (coefficientPolynomialPiece (F := ℂ) m k ⊗[ℂ]
    ColorPaths.TensorDeterminantColorSpace (F := ℂ) m))

def gradedPaperColorBlockRepresentation (m : MultiplicityVector n) (k : ℕ) :
    Representation ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ) (GradedPaperColorBlock m k) :=
  (Representation.trivial ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (coefficientPolynomialPiece (F := ℂ) m k)).tprod
      (ColorPaths.tensorDeterminantColorRepresentation (F := ℂ) m)

def gradedPaperColorRepresentation (k : ℕ) :
    Representation ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ)
      (⨁ m : {m : MultiplicityVector n // Admissible m},GradedPaperColorBlock m.val k) :=
  Representation.directSum (fun m ↦ gradedPaperColorBlockRepresentation m.val k)

theorem gradedPaperColorBlockRepresentation_polynomial
    (hn : 0<n) (m : MultiplicityVector n) (k : ℕ) :
    TauCeti.IsPolynomialRep (gradedPaperColorBlockRepresentation m k) := by
  apply TauCeti.IsPolynomialRep.tprod _
    (ColorPaths.tensorDeterminantColorRepresentation_polynomial m)
  apply (TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions
    (coefficientPolynomialPieceBasis (F := ℂ) hn m k)).mpr
  intro a b
  convert (TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions ℂ 2).algebraMap_mem
    (if a=b then (1 : ℂ) else 0) using 1
  funext g
  simp [LinearMap.toMatrix_apply,Representation.trivial_apply,
    Module.Basis.repr_self,Finsupp.single_apply,eq_comm]

theorem gradedPaperColorRepresentation_rational (hn : 0<n) (k : ℕ) :
    TauCeti.IsRationalRep (gradedPaperColorRepresentation (n := n) k) :=
  TauCeti.IsRationalRep.directSum
    (V := fun m : {m : MultiplicityVector n // Admissible m} ↦ GradedPaperColorBlock m.val k)
    (σ := fun m ↦ gradedPaperColorBlockRepresentation m.val k)
    (fun m ↦ (gradedPaperColorBlockRepresentation_polynomial hn m.val k).isRationalRep)

theorem gradedPaperColorBlock_character_eq (hn : 0<n)
    (m : MultiplicityVector n) (k : ℕ) (t : Fin 2 → ℂˣ) :
    Representation.character (k := ℂ) (V := GradedPaperColorBlock m k)
      (gradedPaperColorBlockRepresentation m k) (TauCeti.diagGL t)=
      Representation.character (k := ℂ) (V := GradedExteriorCoefficientBlock (F := ℂ) m k)
        (gradedExteriorCoefficientRepresentation (F := ℂ) m k) (TauCeti.diagGL t) := by
  letI := Module.Finite.of_basis (coefficientPolynomialPieceBasis (F := ℂ) hn m k)
  letI := Module.Finite.of_basis (ColorPaths.exteriorColorTensorBasis ℂ m)
  have hp := congrFun (Representation.char_tensor (k := ℂ)
    (V := coefficientPolynomialPiece (F := ℂ) m k)
    (W := ColorPaths.TensorDeterminantColorSpace (F := ℂ) m)
    (Representation.trivial ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ)
      (coefficientPolynomialPiece (F := ℂ) m k))
    (ColorPaths.tensorDeterminantColorRepresentation (F := ℂ) m)) (TauCeti.diagGL t)
  have he := congrFun (Representation.char_tensor (k := ℂ)
    (V := coefficientPolynomialPiece (F := ℂ) m k)
    (W := ColorPaths.ExteriorColorTensor ℂ m)
    (Representation.trivial ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ)
      (coefficientPolynomialPiece (F := ℂ) m k))
    (ColorPaths.diagonalExteriorColorRepresentation ℂ m)) (TauCeti.diagGL t)
  change Representation.character (k := ℂ)
    ((Representation.trivial ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ)
      (coefficientPolynomialPiece (F := ℂ) m k)).tprod
      (ColorPaths.tensorDeterminantColorRepresentation (F := ℂ) m)) (TauCeti.diagGL t)=_
  change _=Representation.character (k := ℂ)
    ((Representation.trivial ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ)
      (coefficientPolynomialPiece (F := ℂ) m k)).tprod
      (ColorPaths.diagonalExteriorColorRepresentation ℂ m)) (TauCeti.diagGL t)
  rw [hp,he,Pi.mul_apply,Pi.mul_apply,
    ColorPaths.tensorDeterminantColorRepresentation_character,
    ColorPaths.diagonalExteriorColorRepresentation_character]

theorem gradedPaperColor_character_eq (hn : 0<n) (k : ℕ) (t : Fin 2 → ℂˣ) :
    Representation.character (k := ℂ)
      (V := ⨁ m : {m : MultiplicityVector n // Admissible m}, GradedPaperColorBlock m.val k)
      (gradedPaperColorRepresentation (n := n) k) (TauCeti.diagGL t)=
      Representation.character (k := ℂ)
        (V := ⨁ m : {m : MultiplicityVector n // Admissible m},
          GradedExteriorCoefficientBlock (F := ℂ) m.val k)
        (gradedAdmissibleExteriorRepresentation (F := ℂ) (n := n) k)
        (TauCeti.diagGL t) := by
  letI : ∀ m : {m : MultiplicityVector n // Admissible m},
      Module.Finite ℂ (GradedPaperColorBlock m.val k) :=
    fun m ↦ (gradedPaperColorBlockRepresentation_polynomial hn m.val k).finite
  letI : ∀ m : {m : MultiplicityVector n // Admissible m},
      Module.Finite ℂ (GradedExteriorCoefficientBlock (F := ℂ) m.val k) :=
    fun m ↦ (gradedExteriorCoefficientRepresentation_polynomial hn m.val k).finite
  change LinearMap.trace ℂ _ (DirectSum.lmap
      (fun m : {m : MultiplicityVector n // Admissible m} ↦
        gradedPaperColorBlockRepresentation m.val k (TauCeti.diagGL t)))=
    LinearMap.trace ℂ _ (DirectSum.lmap
      (fun m : {m : MultiplicityVector n // Admissible m} ↦
        gradedExteriorCoefficientRepresentation m.val k (TauCeti.diagGL t)))
  rw [trace_directSum_lmap,trace_directSum_lmap]
  exact Finset.sum_congr rfl (fun m _ ↦ gradedPaperColorBlock_character_eq hn m.val k t)

/-- The exact tensor-power/determinant form of the paper's noncanonical
module decomposition in every original polynomial degree. -/
theorem polynomialPiece_paper_module_decomposition (hn : 0<n) (k : ℕ) :
    Nonempty ((polynomialPieceColorRepresentation (F := ℂ) hn k).Equiv
      (gradedPaperColorRepresentation (n := n) k)) :=
  TauCeti.IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    (W := polynomialPiece (F := ℂ) hn k)
    (W' := ⨁ m : {m : MultiplicityVector n // Admissible m}, GradedPaperColorBlock m.val k)
    (ρ := polynomialPieceColorRepresentation (F := ℂ) hn k)
    (σ := gradedPaperColorRepresentation (n := n) k)
    (polynomialPieceColorRepresentation_polynomial hn k).isRationalRep
    (gradedPaperColorRepresentation_rational hn k)
    (fun t ↦ (polynomialPiece_character_eq_gradedAdmissible hn k t).trans
      (gradedPaperColor_character_eq hn k t).symm)

end PaperVerification.Fermion.TypeA
