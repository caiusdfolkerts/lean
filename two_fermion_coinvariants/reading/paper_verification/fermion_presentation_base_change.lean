module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Exact scalar extension of a module with its actual relation span

The comparison is constructed from the tensor/quotient isomorphism and the
first isomorphism theorem.  The hypotheses describe actual quotient kernels;
the paired application proves them from the original two-sided generators.
No flatness or injectivity of scalar extension is required.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped TensorProduct

variable {R S M N J : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

theorem baseChange_span_range (v : J → M) :
    (Submodule.span R (Set.range v)).baseChange S =
      Submodule.span S (Set.range (fun j ↦ (1 : S) ⊗ₜ[R] v j)) := by
  rw [Submodule.baseChange_eq_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨y,hy,rfl⟩
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j,rfl⟩ := hy
        exact Submodule.subset_span ⟨j,rfl⟩
    | zero =>
        change (1 : S) ⊗ₜ[R] (0 : M)∈Submodule.span S (Set.range (fun j ↦ (1 : S) ⊗ₜ[R] v j))
        rw [TensorProduct.tmul_zero]
        exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
        change (1 : S) ⊗ₜ[R] (x+y)∈Submodule.span S (Set.range (fun j ↦ (1 : S) ⊗ₜ[R] v j))
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ihx ihy
    | smul r x hx ih =>
        change (1 : S) ⊗ₜ[R] (r • x)∈_
        have he : (1 : S) ⊗ₜ[R] (r • x) = algebraMap R S r • ((1 : S) ⊗ₜ[R] x) := by
          rw [← TensorProduct.smul_tmul]
          simp [Algebra.smul_def,TensorProduct.smul_tmul',smul_eq_mul]
        rw [he]
        exact Submodule.smul_mem _ _ ih
  · apply Submodule.span_le.mpr
    rintro x ⟨j,rfl⟩
    exact Submodule.subset_span ⟨v j,Submodule.subset_span ⟨j,rfl⟩,rfl⟩

theorem map_baseChange_span_range (e : S ⊗[R] M ≃ₗ[S] N) (v : J → M) :
    ((Submodule.span R (Set.range v)).baseChange S).map e.toLinearMap =
      Submodule.span S (Set.range (fun j ↦ e ((1 : S) ⊗ₜ[R] v j))) := by
  rw [baseChange_span_range,Submodule.map_span,← Set.range_comp]
  rfl

variable {Q T : Type*} [AddCommGroup Q] [Module R Q]
  [AddCommGroup T] [Module S T]

theorem map_baseChange_kernel_of_spans
    (e : S ⊗[R] M ≃ₗ[S] N) (q : M →ₗ[R] Q) (q' : N →ₗ[S] T)
    (v : J → M) (v' : J → N)
    (hq : q.ker = Submodule.span R (Set.range v))
    (hq' : q'.ker = Submodule.span S (Set.range v'))
    (he : ∀ j, e ((1 : S) ⊗ₜ[R] v j) = v' j) :
    (q.ker.baseChange S).map e.toLinearMap = q'.ker := by
  rw [hq,hq',map_baseChange_span_range]
  congr 2
  exact funext he

/-- Scalar extension of a quotient, with no omitted relation or supplied
fiber-isomorphism assertion.  Its exact action on every quotient class is
recorded next. -/
def quotientBaseChangeEquivOfSpans
    (e : S ⊗[R] M ≃ₗ[S] N) (q : M →ₗ[R] Q) (q' : N →ₗ[S] T)
    (hs : Function.Surjective q) (hs' : Function.Surjective q')
    (v : J → M) (v' : J → N)
    (hq : q.ker = Submodule.span R (Set.range v))
    (hq' : q'.ker = Submodule.span S (Set.range v'))
    (he : ∀ j, e ((1 : S) ⊗ₜ[R] v j) = v' j) :
    S ⊗[R] Q ≃ₗ[S] T :=
  ((q.quotKerEquivOfSurjective hs).symm.baseChange R S _ _).trans
    ((TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S q.ker).trans
      ((Submodule.Quotient.equiv _ _ e
        (map_baseChange_kernel_of_spans e q q' v v' hq hq' he)).trans
          (q'.quotKerEquivOfSurjective hs')))

@[simp] theorem quotientBaseChangeEquivOfSpans_tmul
    (e : S ⊗[R] M ≃ₗ[S] N) (q : M →ₗ[R] Q) (q' : N →ₗ[S] T)
    (hs : Function.Surjective q) (hs' : Function.Surjective q')
    (v : J → M) (v' : J → N)
    (hq : q.ker = Submodule.span R (Set.range v))
    (hq' : q'.ker = Submodule.span S (Set.range v'))
    (he : ∀ j, e ((1 : S) ⊗ₜ[R] v j) = v' j) (s : S) (x : M) :
    quotientBaseChangeEquivOfSpans e q q' hs hs' v v' hq hq' he (s ⊗ₜ[R] q x) =
      q' (e (s ⊗ₜ[R] x)) := by
  simp only [quotientBaseChangeEquivOfSpans,LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul,LinearMap.quotKerEquivOfSurjective_symm_apply,
    TensorProduct.AlgebraTensorModule.tensorQuotientEquiv_apply_tmul,
    Submodule.Quotient.equiv_apply,Submodule.mapQ_apply,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end PaperVerification.Fermion
