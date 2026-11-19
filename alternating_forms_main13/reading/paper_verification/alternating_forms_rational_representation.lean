module

public import PaperVerification.AlternatingFormsSymmetricPencilAction
public import TauCeti.RepresentationTheory.ClassicalGroups.UnitaryTrick
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Rationality of the actual quotient representation

The two closure operations needed in addition to Tau Ceti's existing API
are duals and subrepresentations.  Matrix inversion is proved rational by
the ordinary adjugate formula.  Subrepresentations use extension of linear
functionals, so no invariant complement or reductivity is assumed here.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Matrix

namespace PaperVerification.AlternatingForms.RationalRepresentation

open TauCeti TauCeti.Matrix.GeneralLinearGroup

theorem adjugateEntry_polynomial (n : ℕ) (i j : Fin n) :
    (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ).adjugate i j) ∈
      polynomialFunctions ℂ n := by
  refine mem_polynomialFunctions.mpr
    ⟨(Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).adjugate i j, fun g => ?_⟩
  have h := (MvPolynomial.eval
    (fun p : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2)).map_adjugate
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)
  have he : (MvPolynomial.eval
      (fun p : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2)).mapMatrix
        (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) =
      (g : Matrix (Fin n) (Fin n) ℂ) := by
    ext a b
    simp [Matrix.mvPolynomialX]
  rw [he] at h
  exact (congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) h).symm

theorem rational_pointwise_add {n : ℕ} {f g : GL (Fin n) ℂ → ℂ}
    (hf : f∈rationalFunctions ℂ n) (hg : g∈rationalFunctions ℂ n) :
    (fun x => f x+g x)∈rationalFunctions ℂ n := by
  have he : f+g=(fun x => f x+g x) := by funext x; rfl
  rw [←he]
  exact (rationalFunctions ℂ n).add_mem hf hg

theorem rational_pointwise_mul {n : ℕ} {f g : GL (Fin n) ℂ → ℂ}
    (hf : f∈rationalFunctions ℂ n) (hg : g∈rationalFunctions ℂ n) :
    (fun x => f x*g x)∈rationalFunctions ℂ n := by
  have he : f*g=(fun x => f x*g x) := by funext x; rfl
  rw [←he]
  exact (rationalFunctions ℂ n).mul_mem hf hg

theorem inverseEntry_rational (n : ℕ) (i j : Fin n) :
    (fun g : GL (Fin n) ℂ => (g⁻¹ : Matrix (Fin n) (Fin n) ℂ) i j) ∈
      rationalFunctions ℂ n := by
  have hd : (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ).det⁻¹) ∈
      rationalFunctions ℂ n := by
    simpa only [_root_.zpow_neg_one, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.val_det_apply] using det_zpow_mem_rationalFunctions (k := ℂ) (n := n) (-1)
  have ha := polynomialFunctions_le_rationalFunctions (adjugateEntry_polynomial n i j)
  have h := rational_pointwise_mul hd ha
  simpa only [Pi.mul_apply, Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul] using h

theorem rational_comp_inverse (n : ℕ) (f : GL (Fin n) ℂ → ℂ)
    (hf : f ∈ rationalFunctions ℂ n) :
    (fun g => f g⁻¹) ∈ rationalFunctions ℂ n := by
  have hpoly (P : MvPolynomial (Fin n × Fin n) ℂ) :
      (fun g : GL (Fin n) ℂ => MvPolynomial.eval
        (fun p => (g⁻¹ : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P) ∈
          rationalFunctions ℂ n := by
    induction P using MvPolynomial.induction_on with
    | C a =>
        simp only [MvPolynomial.eval_C]
        exact (rationalFunctions ℂ n).algebraMap_mem a
    | add P Q hP hQ =>
        simpa only [map_add] using rational_pointwise_add hP hQ
    | mul_X P i hP =>
        simpa only [map_mul, MvPolynomial.eval_X] using
          rational_pointwise_mul hP (inverseEntry_rational n i.1 i.2)
  obtain ⟨P, m, hP⟩ := mem_rationalFunctions_iff_inv.mp hf
  have he : (fun g : GL (Fin n) ℂ => f g⁻¹) =
      (fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ).det^m) *
        (fun g : GL (Fin n) ℂ => MvPolynomial.eval
          (fun p => (g⁻¹ : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P) := by
    funext g
    rw [Pi.mul_apply, hP]
    congr 1
    · rw [← Matrix.GeneralLinearGroup.val_det_apply,
        map_inv, Units.val_inv_eq_inv_val, inv_pow, inv_inv,
        Matrix.GeneralLinearGroup.val_det_apply]
    · simp only [Matrix.GeneralLinearGroup.coe_inv]
  rw [he]
  exact (rationalFunctions ℂ n).mul_mem
    (polynomialFunctions_le_rationalFunctions
      ((polynomialFunctions ℂ n).pow_mem det_mem_polynomialFunctions m)) (hpoly P)

section Closure

variable {n : ℕ} {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) ℂ) V}
  {σ : Representation ℂ (GL (Fin n) ℂ) W}

theorem dual (hρ : IsRationalRep ρ) : IsRationalRep ρ.dual := by
  letI := hρ.finite
  let b := Module.finBasis ℂ V
  apply (isRationalRep_iff_forall_mem_rationalFunctions b.dualBasis).mpr
  intro i j
  have h := rational_comp_inverse n
    (fun g => b.dualBasis j (ρ g (b i))) (hρ.dual_apply_mem_rationalFunctions _ _)
  simpa only [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply] using h

theorem prod (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) :
    IsRationalRep (ρ.prod σ) := by
  letI := hρ.finite
  letI := hσ.finite
  apply isRationalRep_iff_forall_dual_apply_mem_rationalFunctions.mpr
  intro f v
  have he : (fun g => f (ρ.prod σ g v)) =
      (fun g => (f ∘ₗ LinearMap.inl ℂ V W) (ρ g v.1)) +
        (fun g => (f ∘ₗ LinearMap.inr ℂ V W) (σ g v.2)) := by
    funext g
    change f (ρ g v.1, σ g v.2) = f (ρ g v.1, 0) + f (0, σ g v.2)
    rw [← map_add]
    congr 1
    simp
  rw [he]
  exact (rationalFunctions ℂ n).add_mem
    (hρ.dual_apply_mem_rationalFunctions _ _) (hσ.dual_apply_mem_rationalFunctions _ _)

theorem subrepresentation (hρ : IsRationalRep ρ) (S : Submodule ℂ V)
    (hS : ∀ g, S ≤ S.comap (ρ g)) :
    IsRationalRep (ρ.subrepresentation S hS) := by
  letI := hρ.finite
  apply isRationalRep_iff_forall_dual_apply_mem_rationalFunctions.mpr
  intro f v
  have h := hρ.dual_apply_mem_rationalFunctions (Subspace.dualLift S f) v.val
  have he : (fun g => f (ρ.subrepresentation S hS g v)) =
      (fun g => Subspace.dualLift S f (ρ g v.val)) := by
    funext g
    exact (Subspace.dualLift_of_subtype (W := S) (φ := f)
      (ρ.subrepresentation S hS g v)).symm
  rw [he]
  exact h

theorem transport (hρ : IsRationalRep ρ) (e : ρ.Equiv σ) : IsRationalRep σ :=
  hρ.of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective

end Closure

open SymmetricPencil

theorem model_rational (t : ℕ) : IsRationalRep (modelRepresentation ℂ t) :=
  prod (dual (TauCeti.isPolynomialRep_symPowerRep 2 t).isRationalRep)
    (TauCeti.isPolynomialRep_symPowerRep 2 (t+1)).isRationalRep

theorem coordinate_rational (t : ℕ) : IsRationalRep (coordinateRepresentation ℂ t) :=
  transport (model_rational t) (coordinateRepresentationEquiv ℂ t).symm

theorem quotient_rational (t s : ℕ) : IsRationalRep (quotientRepresentation ℂ t s) := by
  let S := exteriorDegreeRelations (K := ℂ)
    (oddPathFirstQuadratic (K := ℂ) (Pi.basisFun ℂ (Fin (2*(t+1)+1))))
    (oddPathSecondQuadratic (K := ℂ) (Pi.basisFun ℂ (Fin (2*(t+1)+1)))) s
  let f : ((coordinateRepresentation ℂ t).exteriorPower s).IntertwiningMap
      (quotientRepresentation ℂ t s) :=
    .mk S.mkQ (by
      intro g
      apply LinearMap.ext
      intro x
      change S.mkQ ((coordinateRepresentation ℂ t).exteriorPower s g x) =
        quotientRepresentation ℂ t s g (S.mkQ x)
      rw [Representation.exteriorPower_apply]
      exact (quotientRepresentation_mk ℂ t s g x).symm)
  exact ((coordinate_rational t).exteriorPower s).of_surjective f S.mkQ_surjective

theorem bigraded_rational (t p q : ℕ) : IsRationalRep (bigradedRepresentation ℂ t p q) :=
  subrepresentation (quotient_rational t (p+q)) _ (bigradedPiece_invariant ℂ t p q)

end PaperVerification.AlternatingForms.RationalRepresentation
