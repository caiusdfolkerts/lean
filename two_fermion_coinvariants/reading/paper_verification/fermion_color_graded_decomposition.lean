module

public import PaperVerification.FermionCoefficientHilbert
public import PaperVerification.FermionColorModuleDecomposition
public import PaperVerification.FermionColorPolynomialRational

/-!
# The actual polynomial-degree module decomposition in Section 8.2

Both sides retain their independently defined polynomial grading and their
original group actions. The coefficient spaces are images of homogeneous
polynomials in the literal colon quotients. The comparison uses the proved
characters and polynomiality, followed by the pinned rational-character
theorem over the complex numbers. No decomposition or character equality is
assumed as a premise.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped DirectSum
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.TypeA

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

abbrev GradedExteriorCoefficientBlock (m : MultiplicityVector n) (k : ℕ) :=
  coefficientPolynomialPiece (F := F) m k ⊗[F] ColorPaths.ExteriorColorTensor F m

instance gradedExteriorCoefficientBlockAddCommGroup (m : MultiplicityVector n) (k : ℕ) :
    AddCommGroup (GradedExteriorCoefficientBlock (F := F) m k) :=
  inferInstanceAs (AddCommGroup
    (coefficientPolynomialPiece (F := F) m k ⊗[F] ColorPaths.ExteriorColorTensor F m))

/-- Trivial action on actual polynomial coefficients, standard exterior
action on the original two-dimensional color space. -/
def gradedExteriorCoefficientRepresentation (m : MultiplicityVector n) (k : ℕ) :
    Representation F (Matrix.GeneralLinearGroup (Fin 2) F)
      (GradedExteriorCoefficientBlock (F := F) m k) :=
  (Representation.trivial F (Matrix.GeneralLinearGroup (Fin 2) F)
    (coefficientPolynomialPiece (F := F) m k)).tprod
      (ColorPaths.diagonalExteriorColorRepresentation F m)

def gradedAdmissibleExteriorRepresentation (k : ℕ) :
    Representation F (Matrix.GeneralLinearGroup (Fin 2) F)
      (⨁ m : {m : MultiplicityVector n // Admissible m},
        GradedExteriorCoefficientBlock (F := F) m.val k) :=
  Representation.directSum (fun m ↦ gradedExteriorCoefficientRepresentation m.val k)

theorem gradedExteriorCoefficientRepresentation_polynomial
    (hn : 0<n) (m : MultiplicityVector n) (k : ℕ) :
    TauCeti.IsPolynomialRep
      (gradedExteriorCoefficientRepresentation (F := ℂ) m k) := by
  apply TauCeti.IsPolynomialRep.tprod _
    (ColorPaths.diagonalExteriorColorRepresentation_polynomial m)
  apply (TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions
    (coefficientPolynomialPieceBasis (F := ℂ) hn m k)).mpr
  intro a b
  convert (TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions ℂ 2).algebraMap_mem
    (if a=b then (1 : ℂ) else 0) using 1
  funext g
  simp [LinearMap.toMatrix_apply,Representation.trivial_apply,
    Module.Basis.repr_self,Finsupp.single_apply,eq_comm]

theorem gradedAdmissibleExteriorRepresentation_rational (hn : 0<n) (k : ℕ) :
    TauCeti.IsRationalRep (gradedAdmissibleExteriorRepresentation (F := ℂ) (n := n) k) :=
  TauCeti.IsRationalRep.directSum
    (V := fun m : {m : MultiplicityVector n // Admissible m} ↦
      GradedExteriorCoefficientBlock (F := ℂ) m.val k)
    (σ := fun m ↦ gradedExteriorCoefficientRepresentation (F := ℂ) m.val k)
    (fun m ↦ (gradedExteriorCoefficientRepresentation_polynomial hn m.val k).isRationalRep)

theorem gradedExteriorCoefficientRepresentation_character (hn : 0<n)
    (m : MultiplicityVector n) (hm : Admissible m) (k : ℕ) (t : Fin 2 → Fˣ) :
    Representation.character (k := F) (V := GradedExteriorCoefficientBlock (F := F) m k)
      (gradedExteriorCoefficientRepresentation (F := F) m k) (TauCeti.diagGL t)=
      (ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m).coeff k*
        ((t 0 : F)+(t 1 : F))^ColorPaths.singleCount m*
        ((t 0 : F)*(t 1 : F))^ColorPaths.doubleCount m := by
  letI := Module.Finite.of_basis (coefficientPolynomialPieceBasis (F := F) hn m k)
  letI := Module.Finite.of_basis (ColorPaths.exteriorColorTensorBasis F m)
  have ht : Representation.character (k := F) (V := GradedExteriorCoefficientBlock (F := F) m k)
      (gradedExteriorCoefficientRepresentation (F := F) m k) (TauCeti.diagGL t)=
      (Representation.trivial F (Matrix.GeneralLinearGroup (Fin 2) F)
        (coefficientPolynomialPiece (F := F) m k)).character (TauCeti.diagGL t)*
      (ColorPaths.diagonalExteriorColorRepresentation F m).character (TauCeti.diagGL t) := by
    exact congrFun (Representation.char_tensor (k := F)
      (V := coefficientPolynomialPiece (F := F) m k) (W := ColorPaths.ExteriorColorTensor F m)
      (Representation.trivial F (Matrix.GeneralLinearGroup (Fin 2) F)
        (coefficientPolynomialPiece (F := F) m k))
      (ColorPaths.diagonalExteriorColorRepresentation F m)) (TauCeti.diagGL t)
  rw [ht,ColorPaths.diagonalExteriorColorRepresentation_character]
  have htriv :
      (Representation.trivial F (Matrix.GeneralLinearGroup (Fin 2) F)
        (coefficientPolynomialPiece (F := F) m k)).character (TauCeti.diagGL t)=
        (Module.finrank F (coefficientPolynomialPiece (F := F) m k) : F) := by
    change LinearMap.trace F _ LinearMap.id=_
    exact LinearMap.trace_id F (coefficientPolynomialPiece (F := F) m k)
  rw [htriv,coefficientPolynomialPiece_finrank hn m hm]
  exact (mul_assoc _ _ _).symm

theorem gradedAdmissibleExteriorRepresentation_character (hn : 0<n)
    (k : ℕ) (t : Fin 2 → Fˣ) :
    Representation.character (k := F)
      (V := ⨁ m : {m : MultiplicityVector n // Admissible m},
        GradedExteriorCoefficientBlock (F := F) m.val k)
      (gradedAdmissibleExteriorRepresentation (F := F) (n := n) k) (TauCeti.diagGL t)=
      (∑ m : MultiplicityVector n,if Admissible m then
        ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m*
          (Polynomial.C (t 0 : F)+Polynomial.C (t 1 : F))^ColorPaths.singleCount m*
          (Polynomial.C (t 0 : F)*Polynomial.C (t 1 : F))^ColorPaths.doubleCount m
        else 0).coeff k := by
  letI : ∀ m : {m : MultiplicityVector n // Admissible m},
      Module.Finite F (GradedExteriorCoefficientBlock (F := F) m.val k) := by
    intro m
    letI := Module.Finite.of_basis (coefficientPolynomialPieceBasis (F := F) hn m.val k)
    letI := Module.Finite.of_basis (ColorPaths.exteriorColorTensorBasis F m.val)
    change Module.Finite F (_ ⊗[F] _)
    infer_instance
  change LinearMap.trace F _ (DirectSum.lmap
    (fun m : {m : MultiplicityVector n // Admissible m} ↦
      gradedExteriorCoefficientRepresentation m.val k (TauCeti.diagGL t)))=_
  rw [trace_directSum_lmap]
  change (∑ m : {m : MultiplicityVector n // Admissible m},
    (gradedExteriorCoefficientRepresentation m.val k).character (TauCeti.diagGL t))=_
  simp only [gradedExteriorCoefficientRepresentation_character hn _ (Subtype.property _)]
  rw [←Finset.sum_subtype
    (Finset.univ.filter (fun m : MultiplicityVector n ↦ Admissible m))
    (by intro m; simp) (fun m ↦
      (ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m).coeff k*
        ((t 0 : F)+(t 1 : F))^ColorPaths.singleCount m*
        ((t 0 : F)*(t 1 : F))^ColorPaths.doubleCount m),Finset.sum_filter,
    Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : Admissible m
  · simp only [h,if_true,←map_add,←map_mul,←map_pow,Polynomial.coeff_mul_C]
  · simp only [h,if_false,Polynomial.coeff_zero]

/-- Equality of the independently defined actual characters in every
polynomial degree. -/
theorem polynomialPiece_character_eq_gradedAdmissible (hn : 0<n)
    (k : ℕ) (t : Fin 2 → ℂˣ) :
    Representation.character (k := ℂ) (V := polynomialPiece (F := ℂ) hn k)
      (polynomialPieceColorRepresentation (F := ℂ) hn k) (TauCeti.diagGL t)=
      Representation.character (k := ℂ)
        (V := ⨁ m : {m : MultiplicityVector n // Admissible m},
          GradedExteriorCoefficientBlock (F := ℂ) m.val k)
        (gradedAdmissibleExteriorRepresentation (F := ℂ) (n := n) k)
        (TauCeti.diagGL t) := by
  have h01 : (TauCeti.diagGL t).val 0 1=0 := by
    change (TauCeti.diagGL t : Matrix (Fin 2) (Fin 2) ℂ) 0 1=0
    simp only [TauCeti.diagGL_apply,show (0 : Fin 2)≠1 by decide,if_false]
  have h10 : (TauCeti.diagGL t).val 1 0=0 := by
    change (TauCeti.diagGL t : Matrix (Fin 2) (Fin 2) ℂ) 1 0=0
    simp only [TauCeti.diagGL_apply,show (1 : Fin 2)≠0 by decide,if_false]
  rw [gradedAdmissibleExteriorRepresentation_character hn]
  change LinearMap.trace ℂ _
    (polynomialPieceColorRepresentation hn k (TauCeti.diagGL t))=_
  rw [polynomialPieceColorRepresentation_diagonal hn k (TauCeti.diagGL t) h01 h10,
    equation_22_diagonal_trace hn k (TauCeti.diagGL t) h01 h10]
  congr 1

/-- The noncanonical decomposition claimed in Section 8.2, in every
original polynomial degree, with the actual coefficient colon quotient
pieces and the natural exterior-power actions. -/
theorem polynomialPiece_module_decomposition (hn : 0<n) (k : ℕ) :
    Nonempty ((polynomialPieceColorRepresentation (F := ℂ) hn k).Equiv
      (gradedAdmissibleExteriorRepresentation (F := ℂ) (n := n) k)) :=
  TauCeti.IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    (W := polynomialPiece (F := ℂ) hn k)
    (W' := ⨁ m : {m : MultiplicityVector n // Admissible m},
      GradedExteriorCoefficientBlock (F := ℂ) m.val k)
    (ρ := polynomialPieceColorRepresentation (F := ℂ) hn k)
    (σ := gradedAdmissibleExteriorRepresentation (F := ℂ) (n := n) k)
    (polynomialPieceColorRepresentation_polynomial hn k).isRationalRep
    (gradedAdmissibleExteriorRepresentation_rational hn k)
    (polynomialPiece_character_eq_gradedAdmissible hn k)

end PaperVerification.Fermion.TypeA
