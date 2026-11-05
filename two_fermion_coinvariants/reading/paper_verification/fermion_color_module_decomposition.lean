module

public import PaperVerification.FermionExteriorColorRepresentation
public import TauCeti.LinearAlgebra.Trace.Pi

/-!
# A genuine module comparison for the original total color representation

The target has the natural tensor action on the literal coefficient colon
quotients and actual exterior powers. Its character is computed independently.
The exact pinned rational-character theorem then compares it with the actual
original strict quotient representation. This file concerns the total module;
the comparison in each polynomial degree remains a separate construction.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped DirectSum
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion

section DirectSumTrace
variable {F J : Type*} [Field F] [Fintype J] [DecidableEq J]
  (M : J → Type*) [∀ j,AddCommGroup (M j)] [∀ j,Module F (M j)]
  [∀ j,Module.Finite F (M j)]

theorem trace_directSum_lmap (f : ∀ j,M j →ₗ[F] M j) :
    LinearMap.trace F (⨁ j,M j) (DirectSum.lmap f)=
      ∑ j,LinearMap.trace F (M j) (f j) := by
  let e := DirectSum.linearEquivFunOnFintype F J M
  have he : e.conj (DirectSum.lmap f)=LinearMap.piMap f := by
    apply LinearMap.ext
    intro x
    funext j
    change f j ((e.symm x) j)=f j (x j)
    rfl
  rw [←LinearMap.trace_conj' (DirectSum.lmap f) e,he,LinearMap.trace_piMap]

end DirectSumTrace

namespace TypeA

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem coefficientBoxCard (hn : 0<n) (m : MultiplicityVector n) :
    (Fintype.card (StrictWordPolynomialIndex (fun _ : Fin n ↦ 1) (canonicalWord m)) : F)=
      if Admissible m then ColorPaths.multiplicityBoxPolynomial (1 : F) m else 0 := by
  have h := ColorPaths.strictWord_q_sum (1 : F) (canonicalWord m)
  simpa only [one_pow,Finset.sum_const,Finset.card_univ,nsmul_one,
    strictWord_iff_admissible,canonicalWord_multiplicity,
    ColorPaths.word_bounds_eq_arrival,ColorPaths.multiplicityBoxPolynomial] using h

theorem coefficientQuotient_finite (hn : 0<n) (m : MultiplicityVector n) :
    Module.Finite F (CoefficientQuotient (F := F) m) :=
  Module.Finite.of_basis (coefficientBoxBasis hn m)

theorem exteriorCoefficientBlock_finite (hn : 0<n) (m : MultiplicityVector n) :
    Module.Finite F (ExteriorCoefficientBlock (F := F) m) := by
  letI := coefficientQuotient_finite (F := F) hn m
  letI := Module.Finite.of_basis (ColorPaths.exteriorColorTensorBasis F m)
  infer_instance

/-- Character computed from the genuine tensor action and the actual colon
quotient basis. Inadmissible summands vanish as actual modules. -/
theorem exteriorCoefficientRepresentation_character (hn : 0<n)
    (m : MultiplicityVector n) (t : Fin 2 → Fˣ) :
    Representation.character (k := F) (V := ExteriorCoefficientBlock (F := F) m)
      (exteriorCoefficientRepresentation (F := F) m) (TauCeti.diagGL t)=
      if Admissible m then
        ColorPaths.multiplicityBoxPolynomial (1 : F) m*
          ((t 0 : F)+(t 1 : F))^ColorPaths.singleCount m*
          ((t 0 : F)*(t 1 : F))^ColorPaths.doubleCount m else 0 := by
  letI := coefficientQuotient_finite (F := F) hn m
  letI := Module.Finite.of_basis (ColorPaths.exteriorColorTensorBasis F m)
  have ht : Representation.character (k := F) (V := ExteriorCoefficientBlock (F := F) m)
      (exteriorCoefficientRepresentation (F := F) m) (TauCeti.diagGL t)=
      (Representation.trivial F (Matrix.GeneralLinearGroup (Fin 2) F)
        (CoefficientQuotient (F := F) m)).character (TauCeti.diagGL t)*
      (ColorPaths.diagonalExteriorColorRepresentation F m).character (TauCeti.diagGL t) := by
    exact congrFun (Representation.char_tensor (k := F)
      (V := CoefficientQuotient (F := F) m) (W := ColorPaths.ExteriorColorTensor F m)
      (Representation.trivial F (Matrix.GeneralLinearGroup (Fin 2) F)
        (CoefficientQuotient (F := F) m))
      (ColorPaths.diagonalExteriorColorRepresentation F m)) (TauCeti.diagGL t)
  rw [ht,ColorPaths.diagonalExteriorColorRepresentation_character]
  have htriv :
      (Representation.trivial F (Matrix.GeneralLinearGroup (Fin 2) F)
        (CoefficientQuotient (F := F) m)).character (TauCeti.diagGL t)=
      (Fintype.card (StrictWordPolynomialIndex (fun _ : Fin n ↦ 1) (canonicalWord m)) : F) := by
    change LinearMap.trace F (CoefficientQuotient (F := F) m) LinearMap.id=_
    rw [LinearMap.trace_id,Module.finrank_eq_card_basis (coefficientBoxBasis hn m)]
  rw [htriv,coefficientBoxCard hn m]
  by_cases h : Admissible m <;> simp only [h,if_true,if_false,zero_mul,mul_assoc]

/-- Character of the natural admissible direct-sum target. -/
theorem admissibleExteriorRepresentation_character (hn : 0<n) (t : Fin 2 → Fˣ) :
    Representation.character (k := F)
      (V := ⨁ m : {m : MultiplicityVector n // Admissible m}, ExteriorCoefficientBlock (F := F) m.val)
      (admissibleExteriorRepresentation (F := F) (n := n)) (TauCeti.diagGL t)=
      ∑ m : MultiplicityVector n,if Admissible m then
        ColorPaths.multiplicityBoxPolynomial (1 : F) m*
          ((t 0 : F)+(t 1 : F))^ColorPaths.singleCount m*
          ((t 0 : F)*(t 1 : F))^ColorPaths.doubleCount m else 0 := by
  letI : ∀ m : {m : MultiplicityVector n // Admissible m},
      Module.Finite F (ExteriorCoefficientBlock (F := F) m.val) :=
    fun m ↦ exteriorCoefficientBlock_finite hn m.val
  change LinearMap.trace F _ (DirectSum.lmap
    (fun m : {m : MultiplicityVector n // Admissible m} ↦
      exteriorCoefficientRepresentation m.val (TauCeti.diagGL t)))=_
  rw [trace_directSum_lmap]
  change (∑ m : {m : MultiplicityVector n // Admissible m},
    (exteriorCoefficientRepresentation m.val).character (TauCeti.diagGL t))=_
  simp only [exteriorCoefficientRepresentation_character hn,Subtype.property,if_true]
  rw [←Finset.sum_subtype
    (Finset.univ.filter (fun m : MultiplicityVector n ↦ Admissible m))
    (by intro m; simp) (fun m ↦
      ColorPaths.multiplicityBoxPolynomial (1 : F) m*
        ((t 0 : F)+(t 1 : F))^ColorPaths.singleCount m*
        ((t 0 : F)*(t 1 : F))^ColorPaths.doubleCount m),Finset.sum_filter]

/-- Both sides are the actual representations specified before comparing
their traces. No equivalence is used to define either action. -/
theorem complexColor_character_eq_admissible (hn : 0<n) (t : Fin 2 → ℂˣ) :
    Representation.character (k := ℂ) (V := ComplexStrictQuotient n)
      (complexColorRepresentation (n := n)) (TauCeti.diagGL t)=
      Representation.character (k := ℂ)
        (V := ⨁ m : {m : MultiplicityVector n // Admissible m},
          ExteriorCoefficientBlock (F := ℂ) m.val)
        (admissibleExteriorRepresentation (F := ℂ) (n := n)) (TauCeti.diagGL t) := by
  have h01 : (TauCeti.diagGL t).val 0 1=0 := by
    change (TauCeti.diagGL t : Matrix (Fin 2) (Fin 2) ℂ) 0 1=0
    simp only [TauCeti.diagGL_apply,show (0 : Fin 2)≠1 by decide,if_false]
  have h10 : (TauCeti.diagGL t).val 1 0=0 := by
    change (TauCeti.diagGL t : Matrix (Fin 2) (Fin 2) ℂ) 1 0=0
    simp only [TauCeti.diagGL_apply,show (1 : Fin 2)≠0 by decide,if_false]
  rw [admissibleExteriorRepresentation_character hn]
  have h := strict_paper_q_color_sum (F := ℂ) hn (1 : ℂ) (t 0 : ℂ) (t 1 : ℂ)
  rw [←h]
  change LinearMap.trace ℂ (ComplexStrictQuotient n)
    (ColorAction.quotientEquiv (TauCeti.diagGL t)
      (fun i : Fin n ↦ MvPolynomial.X i)).toLinearMap=_
  rw [diagonal_trace_eq_box_sum hn (TauCeti.diagGL t) h01 h10]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [diagonalMonomialWeight,one_pow,one_mul]
  change ((TauCeti.diagGL t : Matrix (Fin 2) (Fin 2) ℂ) 0 0)^z.val.1.1.card*
      ((TauCeti.diagGL t : Matrix (Fin 2) (Fin 2) ℂ) 1 1)^z.val.1.2.card=_
  simp only [TauCeti.diagGL_apply,if_true]

/-- The total-module version of the noncanonical decomposition in Section
8.2. This endpoint is distinct from the stronger polynomial-degree statement.
It has no rationality, character-equality, or semisimplicity hypothesis. -/
theorem complexColor_module_decomposition (hn : 0<n) :
    Nonempty ((complexColorRepresentation (n := n)).Equiv
      (admissibleExteriorRepresentation (F := ℂ) (n := n))) :=
  TauCeti.IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    (W := ComplexStrictQuotient n)
    (W' := ⨁ m : {m : MultiplicityVector n // Admissible m},
      ExteriorCoefficientBlock (F := ℂ) m.val)
    (ρ := complexColorRepresentation (n := n))
    (σ := admissibleExteriorRepresentation (F := ℂ) (n := n))
    (complexColorRepresentation_polynomial hn).isRationalRep
    (admissibleExteriorRepresentation_rational hn)
    (complexColor_character_eq_admissible hn)

end TypeA
end PaperVerification.Fermion
