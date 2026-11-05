module

public import PaperVerification.FermionColorBlockExterior

/-!
# Removing exactly the zero multiplicity blocks

The coefficient ideal of every inadmissible multiplicity is the whole
polynomial ring. This file proves that its actual coefficient quotient and
its tensor with the genuine exterior powers vanish, then restricts the
actual initial-quotient decomposition to precisely the admissible indices
printed in Theorem 8.1. No dimension comparison is used.

This is a linear equivalence. Natural equivariance and multiplication are
separate obligations, not consequences of a transported definition.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped DirectSum
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.TypeA

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

abbrev ExteriorCoefficientBlock (m : MultiplicityVector n) :=
  CoefficientQuotient (F := F) m ⊗[F] ColorPaths.ExteriorColorTensor F m

instance exteriorCoefficientBlockAddCommGroup (m : MultiplicityVector n) :
    AddCommGroup (ExteriorCoefficientBlock (F := F) m) :=
  inferInstanceAs (AddCommGroup
    (CoefficientQuotient (F := F) m ⊗[F] ColorPaths.ExteriorColorTensor F m))

theorem coefficientQuotient_eq_zero_of_inadmissible (hn : 0<n)
    (m : MultiplicityVector n) (hm : ¬Admissible m)
    (c : CoefficientQuotient (F := F) m) : c=0 := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective c
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [inadmissible_coefficientIdeal_eq_top hn m hm]
  trivial

theorem exteriorCoefficientBlock_eq_zero_of_inadmissible (hn : 0<n)
    (m : MultiplicityVector n) (hm : ¬Admissible m)
    (x : ExteriorCoefficientBlock (F := F) m) : x=0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul c v =>
      rw [coefficientQuotient_eq_zero_of_inadmissible hn m hm c,
        TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx,hy,zero_add]

/-- Restriction with its explicit zero-extension inverse. The left inverse
uses vanishing of the actual tensor modules, not a declared zero dimension. -/
def restrictAdmissibleColorBlocksEquiv (hn : 0<n) :
    ((m : MultiplicityVector n) → ExteriorCoefficientBlock (F := F) m) ≃ₗ[F]
      ((m : {m : MultiplicityVector n // Admissible m}) →
        ExteriorCoefficientBlock (F := F) m.val) where
  toFun x m := x m.val
  invFun y m := if h : Admissible m then y ⟨m,h⟩ else 0
  left_inv x := by
    funext m
    by_cases h : Admissible m
    · simp only [h,dite_true]
    · simp only [h,dite_false]
      exact (exteriorCoefficientBlock_eq_zero_of_inadmissible hn m h (x m)).symm
  right_inv y := by
    funext m
    simp only [m.property,dite_true]
  map_add' x y := rfl
  map_smul' c x := rfl

/-- The exact admissible-index vector-space decomposition printed in
Theorem 8.1, with actual colon quotients and actual exterior powers. -/
def initialAdmissibleExteriorTensorEquiv (hn : 0<n) :
    StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₗ[F]
      ⨁ m : {m : MultiplicityVector n // Admissible m},
        CoefficientQuotient (F := F) m.val ⊗[F]
          ColorPaths.ExteriorColorTensor F m.val :=
  (initialSignedExteriorTensorEquiv hn).trans
    ((DirectSum.linearEquivFunOnFintype F (MultiplicityVector n)
      (fun m ↦ ExteriorCoefficientBlock (F := F) m)).trans
      ((restrictAdmissibleColorBlocksEquiv hn).trans
        (DirectSum.linearEquivFunOnFintype F
          {m : MultiplicityVector n // Admissible m}
          (fun m ↦ ExteriorCoefficientBlock (F := F) m.val)).symm))

end PaperVerification.Fermion.TypeA
