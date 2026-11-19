module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Actual homology is invariant under linear conjugacy

A linear equivalence intertwining two square-zero endomorphisms maps cycles
to cycles and boundaries to boundaries. Its induced quotient equivalence is
then transported through Mathlib's canonical `moduleCatHomologyIso`, giving
an equivalence of the actual categorical homology objects.
-/

@[expose] public section
noncomputable section

universe u v

namespace PaperVerification.SquareZeroHomologyConjugacy

open CategoryTheory

variable {R : Type u} [Ring R]
  {A B : Type v} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
  (D : A →ₗ[R] A) (E : B →ₗ[R] B)

/-- A square-zero endomorphism regarded as an ordinary short complex. -/
def complex (hD : D.comp D = 0) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk D D hD

variable (e : A ≃ₗ[R] B) (he : ∀ x, e (D x) = E (e x))

/-- The original linear equivalence restricts to an equivalence of kernels. -/
def cyclesEquiv : LinearMap.ker D ≃ₗ[R] LinearMap.ker E where
  toFun x := ⟨e x.val, by
    change E (e x.val) = 0
    exact (he x.val).symm.trans ((congrArg e x.property).trans e.map_zero)⟩
  invFun y := ⟨e.symm y.val, by
    apply e.injective
    calc
      e (D (e.symm y.val)) = E (e (e.symm y.val)) := he _
      _ = E y.val := congrArg E (e.apply_symm_apply y.val)
      _ = 0 := y.property
      _ = e 0 := e.map_zero.symm⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' r x := Subtype.ext (e.map_smul r x.val)

@[simp] theorem cyclesEquiv_apply_val (x : LinearMap.ker D) :
    (cyclesEquiv D E e he x).val = e x.val := rfl

variable (hD : D.comp D = 0) (hE : E.comp E = 0)

/-- This kernel equivalence maps the actual boundary submodule onto the
actual boundary submodule. -/
theorem map_boundaries :
    (LinearMap.range (complex D hD).moduleCatToCycles).map
      (cyclesEquiv D E e he).toLinearMap =
      LinearMap.range (complex E hE).moduleCatToCycles := by
  ext y
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨e a, Subtype.ext (he a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨(complex D hD).moduleCatToCycles (e.symm b), ⟨e.symm b, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (he (e.symm b)).trans (congrArg E (e.apply_symm_apply b))

/-- The induced equivalence of the literal kernel/image quotients. -/
def quotientHomologyEquiv :
    (LinearMap.ker D ⧸ LinearMap.range (complex D hD).moduleCatToCycles) ≃ₗ[R]
      (LinearMap.ker E ⧸ LinearMap.range (complex E hE).moduleCatToCycles) :=
  Submodule.Quotient.equiv _ _ (cyclesEquiv D E e he) (map_boundaries D E e he hD hE)

/-- The induced map sends the class of a cycle to the class of its original
image under `e`. -/
@[simp] theorem quotientHomologyEquiv_mk (x : LinearMap.ker D) :
    quotientHomologyEquiv D E e he hD hE (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cyclesEquiv D E e he x) := rfl

/-- Conjugacy preserves Mathlib's actual short-complex homology. -/
def categoricalHomologyEquiv : (complex D hD).homology ≃ₗ[R] (complex E hE).homology :=
  (complex D hD).moduleCatHomologyIso.toLinearEquiv.trans
    ((quotientHomologyEquiv D E e he hD hE).trans
      (complex E hE).moduleCatHomologyIso.symm.toLinearEquiv)

/-- Under Mathlib's canonical quotient identifications, categorical homology
conjugacy is exactly the explicit map on classes of cycles. -/
@[simp] theorem categoricalHomologyEquiv_quotient (x : LinearMap.ker D) :
    (complex E hE).moduleCatHomologyIso.toLinearEquiv
      (categoricalHomologyEquiv D E e he hD hE
        ((complex D hD).moduleCatHomologyIso.toLinearEquiv.symm (Submodule.Quotient.mk x))) =
      Submodule.Quotient.mk (cyclesEquiv D E e he x) := by
  change (complex E hE).moduleCatHomologyIso.toLinearEquiv
    ((complex E hE).moduleCatHomologyIso.toLinearEquiv.symm
      (quotientHomologyEquiv D E e he hD hE
        ((complex D hD).moduleCatHomologyIso.toLinearEquiv
          ((complex D hD).moduleCatHomologyIso.toLinearEquiv.symm
            (Submodule.Quotient.mk x))))) = _
  exact ((complex E hE).moduleCatHomologyIso.toLinearEquiv.apply_symm_apply _).trans
    ((congrArg (quotientHomologyEquiv D E e he hD hE)
      ((complex D hD).moduleCatHomologyIso.toLinearEquiv.apply_symm_apply _)).trans
        (quotientHomologyEquiv_mk D E e he hD hE x))

end PaperVerification.SquareZeroHomologyConjugacy
