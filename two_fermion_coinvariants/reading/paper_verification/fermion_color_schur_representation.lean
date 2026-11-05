module

public import PaperVerification.GLTwoSymmetricIrreducible
public import PaperVerification.FermionColorTensorDeterminant
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Data.Fintype.Card

/-!
# The full graded Schur decomposition of the original two-color quotient

Every summand below has its independently defined Sym^a(C²) tensor det^b
representation. Its copy index is finite and has exactly the displayed
binomial-difference times polynomial-box coefficient size. The decomposition
compares the genuine original degree-piece representation with this direct
sum, using their proved rational characters. All summands are irreducible;
the previous file proves that two labels are equivalent precisely when both
labels agree. Counting the copies of a fixed label gives, coefficient by
coefficient in every polynomial degree, the multiplicity polynomial printed
in Section 8.2. The degree and tensor-length ranges are unrestricted.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct DirectSum

namespace PaperVerification.Fermion.ColorSchur

open ColorPaths TypeA

variable {n : ℕ}

/-- The exact nonnegative polynomial-box dimension in degree k. -/
def boxMultiplicity (m : MultiplicityVector n) (k : ℕ) : ℕ :=
  (multiplicityBoxPolynomial (Polynomial.X : Polynomial ℕ) m).coeff k

/-- The same integral box polynomial, evaluated in any coefficient field. -/
theorem boxMultiplicity_cast {F : Type*} [Field F]
    (m : MultiplicityVector n) (k : ℕ) :
    (boxMultiplicity m k : F)=
      (multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m).coeff k := by
  have h : (multiplicityBoxPolynomial (Polynomial.X : Polynomial ℕ) m).map
      (Nat.castRingHom F)=multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m := by
    simp [multiplicityBoxPolynomial,qNumber,Polynomial.map_prod,Polynomial.map_sum]
  simpa only [boxMultiplicity,Polynomial.coeff_map,Nat.coe_castRingHom] using
    congrArg (fun p : Polynomial F ↦ p.coeff k) h

theorem tensor_det_schur_value {F : Type*} [Field F]
    (ell d : ℕ) (u v : F) (hv : v≠0) :
    (u+v)^ell*(u*v)^d=
      ∑ j : Fin (ell/2+1), (ballotMultiplicity ell j.val : F)*
        schurValue (ell-2*j.val) (d+j.val) u v := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ (ballotMultiplicity ell j : F)*
      schurValue (ell-2*j) (d+j) u v) (ell/2+1),
    tensor_power_schur_value ell u v hv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [schurValue,pow_add]
  ring

/-- There are literally boxMultiplicity*ballotMultiplicity copies of each
summand contributed by an admissible vector and its tensor-power label. -/
abbrev GradedSchurIndex (n k : ℕ) :=
  Σ m : {m : MultiplicityVector n // Admissible m},
    Σ j : Fin (singleCount m.val/2+1),
      Fin (boxMultiplicity m.val k*ballotMultiplicity (singleCount m.val) j.val)

def schurA {k : ℕ} (z : GradedSchurIndex n k) : ℕ :=
  singleCount z.1.val-2*z.2.1.val

def schurB {k : ℕ} (z : GradedSchurIndex n k) : ℕ :=
  doubleCount z.1.val+z.2.1.val

/-- A direct sum of the actual standard Schur representations, not an
action defined by transport from the quotient. -/
def gradedSchurRepresentation (n k : ℕ) :
    Representation ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ)
      (⨁ z : GradedSchurIndex n k, SchurSpace ℂ (schurA z) (schurB z)) :=
  Representation.directSum (fun z ↦ schurRepresentation ℂ (schurA z) (schurB z))

theorem gradedSchurRepresentation_rational (n k : ℕ) :
    TauCeti.IsRationalRep (gradedSchurRepresentation n k) := by
  change TauCeti.IsRationalRep (Representation.directSum
    (fun z : GradedSchurIndex n k ↦ schurRepresentation ℂ (schurA z) (schurB z)))
  exact TauCeti.IsRationalRep.directSum (n := 2) (ι := GradedSchurIndex n k)
    (V := fun z : GradedSchurIndex n k ↦ SchurSpace ℂ (schurA z) (schurB z))
    (σ := fun z : GradedSchurIndex n k ↦ schurRepresentation ℂ (schurA z) (schurB z))
    (fun z : GradedSchurIndex n k ↦
      (schurRepresentation_polynomial (schurA z) (schurB z)).isRationalRep)

theorem gradedSchurRepresentation_character (n k : ℕ) (t : Fin 2 → ℂˣ) :
    Representation.character (k := ℂ)
      (V := ⨁ z : GradedSchurIndex n k, SchurSpace ℂ (schurA z) (schurB z))
      (gradedSchurRepresentation n k) (TauCeti.diagGL t)=
      ∑ m : {m : MultiplicityVector n // Admissible m},
        (multiplicityBoxPolynomial (Polynomial.X : Polynomial ℂ) m.val).coeff k*
          ((t 0 : ℂ)+(t 1 : ℂ))^singleCount m.val*
          ((t 0 : ℂ)*(t 1 : ℂ))^doubleCount m.val := by
  change LinearMap.trace ℂ _ (DirectSum.lmap
    (fun z : GradedSchurIndex n k ↦
      schurRepresentation ℂ (schurA z) (schurB z) (TauCeti.diagGL t)))=_
  rw [trace_lmap]
  change (∑ z : GradedSchurIndex n k,
    Representation.character (k := ℂ) (V := SchurSpace ℂ (schurA z) (schurB z))
      (schurRepresentation ℂ (schurA z) (schurB z)) (TauCeti.diagGL t))=_
  simp only [schurRepresentation_character,GradedSchurIndex,Fintype.sum_sigma,
    schurA,schurB,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro m hm
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum,←tensor_det_schur_value (singleCount m.val)
    (doubleCount m.val) (t 0 : ℂ) (t 1 : ℂ) (Units.ne_zero _),boxMultiplicity_cast]

/-- The trace on every actual polynomial-degree quotient piece, with the
full admissible multiplicity sum. -/
theorem polynomialPiece_character_sum (hn : 0<n) (k : ℕ) (t : Fin 2 → ℂˣ) :
    Representation.character (k := ℂ) (V := polynomialPiece (F := ℂ) hn k)
      (polynomialPieceColorRepresentation (F := ℂ) hn k) (TauCeti.diagGL t)=
      ∑ m : {m : MultiplicityVector n // Admissible m},
        (multiplicityBoxPolynomial (Polynomial.X : Polynomial ℂ) m.val).coeff k*
          ((t 0 : ℂ)+(t 1 : ℂ))^singleCount m.val*
          ((t 0 : ℂ)*(t 1 : ℂ))^doubleCount m.val := by
  letI : ∀ m : {m : MultiplicityVector n // Admissible m},
      Module.Finite ℂ (GradedExteriorCoefficientBlock (F := ℂ) m.val k) :=
    fun m ↦ (gradedExteriorCoefficientRepresentation_polynomial hn m.val k).finite
  rw [polynomialPiece_character_eq_gradedAdmissible hn]
  change LinearMap.trace ℂ _ (DirectSum.lmap
    (fun m : {m : MultiplicityVector n // Admissible m} ↦
      gradedExteriorCoefficientRepresentation m.val k (TauCeti.diagGL t)))=_
  rw [trace_lmap]
  change (∑ m : {m : MultiplicityVector n // Admissible m},
    Representation.character (k := ℂ)
      (V := GradedExteriorCoefficientBlock (F := ℂ) m.val k)
      (gradedExteriorCoefficientRepresentation (F := ℂ) m.val k)
      (TauCeti.diagGL t))=_
  exact Finset.sum_congr rfl (fun m _ ↦
    gradedExteriorCoefficientRepresentation_character hn m.val m.property k t)

/-- The original quotient, with its original action in every polynomial
degree, is equivariantly isomorphic to the displayed irreducible sum. -/
theorem polynomialPiece_schur_decomposition (hn : 0<n) (k : ℕ) :
    Nonempty ((polynomialPieceColorRepresentation (F := ℂ) hn k).Equiv
      (gradedSchurRepresentation n k)) := by
  apply TauCeti.IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    (n := 2) (W := polynomialPiece (F := ℂ) hn k)
    (W' := ⨁ z : GradedSchurIndex n k, SchurSpace ℂ (schurA z) (schurB z))
    (ρ := polynomialPieceColorRepresentation (F := ℂ) hn k)
    (σ := gradedSchurRepresentation n k)
    (polynomialPieceColorRepresentation_polynomial hn k).isRationalRep
    (gradedSchurRepresentation_rational n k)
  intro t
  rw [polynomialPiece_character_sum hn,gradedSchurRepresentation_character]

theorem every_schur_summand_irreducible (n k : ℕ) (z : GradedSchurIndex n k) :
    Representation.IsIrreducible (k := ℂ)
      (V := SchurSpace ℂ (schurA z) (schurB z))
      (schurRepresentation ℂ (schurA z) (schurB z)) :=
  schurRepresentation_irreducible _ _

/-- The printed multiplicity polynomial, with the negative lower-binomial
index at j=0 interpreted as zero by ballotMultiplicity. -/
def schurMultiplicityPolynomial (n a b : ℕ) : Polynomial ℕ :=
  ∑ m : {m : MultiplicityVector n // Admissible m},
    ∑ j : Fin (singleCount m.val/2+1),
      if singleCount m.val-2*j.val=a ∧ doubleCount m.val+j.val=b then
        Polynomial.C (ballotMultiplicity (singleCount m.val) j.val)*
          multiplicityBoxPolynomial (Polynomial.X : Polynomial ℕ) m.val
      else 0

/-- Number of irreducible copies of this label in the genuine decomposition. -/
def schurCopyMultiplicity (n k a b : ℕ) : ℕ :=
  Fintype.card {z : GradedSchurIndex n k // schurA z=a ∧ schurB z=b}

/-- The full polynomial multiplicity formula, in every polynomial degree,
with no upper cutoff and with all boundary labels retained. -/
theorem schurCopyMultiplicity_eq_coefficient (n k a b : ℕ) :
    schurCopyMultiplicity n k a b=(schurMultiplicityPolynomial n a b).coeff k := by
  unfold schurCopyMultiplicity
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [GradedSchurIndex,Fintype.sum_sigma,schurA,schurB,
    schurMultiplicityPolynomial,Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : singleCount m.val-2*j.val=a ∧ doubleCount m.val+j.val=b
  · simp only [h,true_and,if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      one_mul,Polynomial.coeff_C_mul,boxMultiplicity,Nat.cast_id] <;>
      exact Nat.mul_comm _ _
  · simp only [h,if_false,Finset.sum_const,nsmul_zero,Polynomial.coeff_zero]

/-- A fixed label counts exactly the copies equivalent to that actual
Schur representation; this is not merely a name attached to a summand. -/
theorem summand_equivalent_iff_label (n k a b : ℕ) (z : GradedSchurIndex n k) :
    Nonempty ((schurRepresentation ℂ (schurA z) (schurB z)).Equiv
      (schurRepresentation ℂ a b)) ↔ schurA z=a ∧ schurB z=b :=
  schurRepresentation_equiv_iff _ _ _ _

end PaperVerification.Fermion.ColorSchur
