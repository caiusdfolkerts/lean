module

public import Mathlib.Algebra.RingQuot
import all Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The actual linear relations of a noncommutative algebra presentation

The kernel of the genuine algebra quotient is exactly the linear span of
all two-sided contexts of the defining relations. This supplies the
linear-algebra interface needed to compare tensor-annihilator relations
with actual quadratic dual algebras. No kernel or presentation equality
is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.RingQuotLinearRelations

variable {K A V : Type*} [CommRing K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V]
  (r : A → A → Prop) (F : A →ₗ[K] V)
  (hF : ∀ {x y},r x y → ∀ a b,F (a*x*b)=F (a*y*b))

include hF in
theorem context_respects_closure {x y : A} (h : RingQuot.Rel r x y) :
    ∀ a b,F (a*x*b)=F (a*y*b) := by
  induction h with
  | of h => exact hF h
  | @add_left x y z h ih =>
      intro a b
      simp only [mul_add,add_mul,map_add,ih]
  | @mul_left x y z h ih =>
      intro a b
      simpa only [mul_assoc] using ih a (z*b)
  | @mul_right x y z h ih =>
      intro a b
      simpa only [mul_assoc] using ih (a*x) b

/-- A genuine linear map out of the algebra quotient, provided the
original linear functional kills every context of a defining relation. -/
def lift : RingQuot r →ₗ[K] V where
  toFun z := Quot.lift F (fun x y h ↦ by
    simpa only [one_mul,mul_one] using context_respects_closure r F hF h 1 1) z.toQuot
  map_add' := by
    rintro ⟨⟨x⟩⟩ ⟨⟨y⟩⟩
    simp only [RingQuot.add_quot,map_add]
  map_smul' := by
    rintro c ⟨⟨x⟩⟩
    simp only [RingQuot.smul_quot,map_smul,RingHom.id_apply]

@[simp] theorem lift_mk (x : A) : lift r F hF (RingQuot.mkAlgHom K r x)=F x := by
  simp only [RingQuot.mkAlgHom_def, RingQuot.mkRingHom_def]
  rfl

/-- Literal linear span of two-sided contexts, retaining the actual
noncommutative multiplication order. -/
def relationSpan : Submodule K A :=
  Submodule.span K {z | ∃ a b x y,r x y ∧ a*(x-y)*b=z}

/-- No further linear relations arise in the genuine algebra quotient. -/
theorem relationSpan_eq_kernel :
    relationSpan (K := K) r=LinearMap.ker (RingQuot.mkAlgHom K r).toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨a,b,x,y,h,rfl⟩
    change RingQuot.mkAlgHom K r (a*(x-y)*b)=0
    rw [map_mul,map_mul,map_sub,RingQuot.mkAlgHom_rel K h,sub_self,mul_zero,zero_mul]
  · intro z hz
    let S := relationSpan (K := K) r
    have hrespect : ∀ {x y},r x y → ∀ a b,S.mkQ (a*x*b)=S.mkQ (a*y*b) := by
      intro x y h a b
      apply (Submodule.Quotient.eq S).mpr
      change a*x*b-a*y*b∈S
      rw [←sub_mul,←mul_sub]
      exact Submodule.subset_span ⟨a,b,x,y,h,rfl⟩
    have he := congrArg (lift r S.mkQ hrespect)
      (show RingQuot.mkAlgHom K r z=0 from hz)
    rw [lift_mk,map_zero] at he
    exact (Submodule.Quotient.mk_eq_zero S).mp he

/-- The independently specified linear quotient and the actual algebra
quotient have the same underlying module, by a proved kernel identity. -/
def quotientEquiv : (A ⧸ relationSpan (K := K) r) ≃ₗ[K] RingQuot r :=
  (Submodule.quotEquivOfEq _ _ (relationSpan_eq_kernel (K := K) r)).trans
    ((RingQuot.mkAlgHom K r).toLinearMap.quotKerEquivOfSurjective
      (RingQuot.mkAlgHom_surjective K r))

@[simp] theorem quotientEquiv_mk (x : A) :
    quotientEquiv (K := K) r (Submodule.Quotient.mk x)=RingQuot.mkAlgHom K r x := by
  rfl

/-- The dual of the genuine algebra quotient consists precisely of the
linear functionals annihilating all actual relation contexts. -/
def dualEquiv : Module.Dual K (RingQuot r) ≃ₗ[K]
    (relationSpan (K := K) r).dualAnnihilator :=
  (quotientEquiv (K := K) r).dualMap.trans
    (Submodule.dualQuotEquivDualAnnihilator (relationSpan (K := K) r))

end PaperVerification.RingQuotLinearRelations
