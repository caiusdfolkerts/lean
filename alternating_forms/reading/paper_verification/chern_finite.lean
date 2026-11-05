module

public import PaperVerification.AlternatingFormsChernRelationsBasic
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Finiteness.Quotient

/-!
# Finiteness of the literal Chern quotient

The polynomial common-zero calculation over an algebraic closure is converted
by Hilbert's Nullstellensatz into nilpotence of every variable in the quotient.
Those generators are therefore integral over the coefficient field. The actual
quotient is finitely generated as an algebra, so it is finite as a module.

This argument uses no regularity or Hilbert-series assertion and keeps the
underlying quotient by the paper's original finite window of relations.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification

open MvPolynomial

/-- A finite-variable polynomial quotient with nilpotent coordinate classes
is module-finite over its coefficient ring. -/
theorem finite_polynomial_quotient_of_X_mem_radical
    {R σ : Type*} [CommRing R] [Finite σ]
    (I : Ideal (MvPolynomial σ R)) (hX : ∀ i, X i ∈ I.radical) :
    Module.Finite R (MvPolynomial σ R ⧸ I) := by
  have hXi : ∀ i, IsIntegral R (Ideal.Quotient.mk I (X i)) := by
    intro i
    obtain ⟨n,hn⟩ := hX i
    refine ⟨Polynomial.X^n, Polynomial.monic_X_pow n, ?_⟩
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hn
  letI : Algebra.IsIntegral R (MvPolynomial σ R ⧸ I) := by
    constructor
    intro z
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C r => exact isIntegral_algebraMap
    | add p q hp hq => simpa only [map_add] using hp.add hq
    | mul_X p i hp => simpa only [map_mul] using hp.mul (hXi i)
  exact Algebra.IsIntegral.finite

namespace AlternatingForms

variable {K : Type*} [Field K] [CharZero K]

/-- Every Chern coordinate lies in the radical of the actual relation ideal.
The common-zero calculation is made in an algebraic closure, while radical
membership is concluded in the original coefficient field. -/
theorem chern_X_mem_radical (s w : ℕ) (hw : 0<w) (i : Fin s) :
    (X i : MvPolynomial (Fin s) K) ∈
      (Ideal.ofList (chernRelationSequence K s w)).radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
    (K := AlgebraicClosure K)]
  intro c hc
  have hc0 : c = 0 := by
    apply chernCoefficientRelation_common_zero hw c
    intro m hwm hms
    let j : Fin s := ⟨m-w, by omega⟩
    have hj : w+j.val=m := by dsimp [j]; omega
    have hg : chernCoefficientRelation (K := K) s (w+j.val) ∈
        Ideal.ofList (chernRelationSequence K s w) :=
      Ideal.subset_span (List.mem_ofFn.mpr ⟨j,rfl⟩)
    have hz := hc _ hg
    rw [MvPolynomial.aeval_def, ← MvPolynomial.eval_map,
      map_chernCoefficientRelation, hj] at hz
    exact hz
  simp only [MvPolynomial.aeval_X, hc0, Pi.zero_apply]

/-- The Section 4 coefficient quotient is finite-dimensional for every
positive starting degree, not only for the geometric range of parameters. -/
theorem chern_relation_quotient_finite (s w : ℕ) (hw : 0<w) :
    Module.Finite K
      (MvPolynomial (Fin s) K ⧸ Ideal.ofList (chernRelationSequence K s w)) :=
  finite_polynomial_quotient_of_X_mem_radical _ (chern_X_mem_radical s w hw)

end AlternatingForms
end PaperVerification
