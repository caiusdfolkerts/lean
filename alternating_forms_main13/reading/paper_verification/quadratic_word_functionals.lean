module

public import PaperVerification.RingQuotLinearRelations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Functionals on the genuine homogeneous pieces of a quadratic quotient

A multiplicative word basis determines the original word degree. We prove
that the dual of the actual image of its degree-n space in the algebra
quotient is exactly the space of functionals satisfying all degree-n
contexts of the quadratic relations. The relation space is independently
given and homogeneous of degree two. No assertion about Koszulness,
quadratic duality, or quotient kernels is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.QuadraticWordFunctionals

variable {K A J : Type*} [Field K] [Ring A] [Algebra K A]
  (B : Module.Basis (List J) K A)

def degreeSpace (n : ℕ) : Submodule K A :=
  Submodule.span K (B '' {L | L.length=n})

theorem basis_mem_degreeSpace (L : List J) : B L∈degreeSpace B L.length :=
  Submodule.subset_span ⟨L,rfl,rfl⟩

def projection (n : ℕ) : A →ₗ[K] A :=
  B.constr K (fun L ↦ if L.length=n then B L else 0)

@[simp] theorem projection_basis (n : ℕ) (L : List J) :
    projection B n (B L)=if L.length=n then B L else 0 :=
  B.constr_basis K _ L

theorem projection_homogeneous (n m : ℕ) (x : A) (hx : x∈degreeSpace B m) :
    projection B n x=if m=n then x else 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨L,hL,rfl⟩ := hx
      change L.length=m at hL
      rw [projection_basis,hL]
  | zero => simp only [map_zero,ite_self]
  | add x y hx hy ihx ihy =>
      rw [map_add,ihx,ihy]
      split_ifs <;> simp only [add_zero]
  | smul c x hx ih =>
      rw [map_smul,ih]
      split_ifs <;> simp only [smul_zero]

theorem projection_mem (n : ℕ) (x : A) : projection B n x∈degreeSpace B n := by
  have hr : LinearMap.range (projection B n)≤degreeSpace B n := by
    rw [projection,Module.Basis.constr_range]
    apply Submodule.span_le.mpr
    rintro _ ⟨L,rfl⟩
    change (if L.length=n then B L else 0)∈degreeSpace B n
    by_cases h : L.length=n
    · rw [if_pos h]
      exact Submodule.subset_span ⟨L,h,rfl⟩
    · rw [if_neg h]
      exact Submodule.zero_mem _
  exact hr ⟨x,rfl⟩

def projectionToPiece (n : ℕ) : A →ₗ[K] degreeSpace B n :=
  (projection B n).codRestrict _ (projection_mem B n)

@[simp] theorem projectionToPiece_val (n : ℕ) (x : A) :
    (projectionToPiece B n x).val=projection B n x := rfl

theorem projectionToPiece_retraction (n : ℕ) (x : degreeSpace B n) :
    projectionToPiece B n x.val=x := by
  apply Subtype.ext
  exact (projection_homogeneous B n n x.val x.property).trans (if_pos rfl)

variable (hmul : ∀ L M,B (L++M)=B L*B M)

include hmul in
theorem degree_mul {n m : ℕ} {x y : A}
    (hx : x∈degreeSpace B n) (hy : y∈degreeSpace B m) :
    x*y∈degreeSpace B (n+m) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨L,hL,rfl⟩ := hx
      change L.length=n at hL
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨M,hM,rfl⟩ := hy
          change M.length=m at hM
          rw [←hmul]
          exact Submodule.subset_span ⟨L++M,by
            change (L++M).length=n+m
            rw [List.length_append,hL,hM],rfl⟩
      | zero => simpa only [mul_zero] using (degreeSpace B (n+m)).zero_mem
      | add y z hy hz ihy ihz =>
          simpa only [mul_add] using (degreeSpace B (n+m)).add_mem ihy ihz
      | smul c y hy ih =>
          simpa only [mul_smul_comm] using (degreeSpace B (n+m)).smul_mem c ih
  | zero => simpa only [zero_mul] using (degreeSpace B (n+m)).zero_mem
  | add x z hx hz ihx ihz =>
      simpa only [add_mul] using (degreeSpace B (n+m)).add_mem ihx ihz
  | smul c x hx ih =>
      simpa only [smul_mul_assoc] using (degreeSpace B (n+m)).smul_mem c ih

/-- Testing contexts on a basis really tests every two-sided context. -/
theorem context_vanishes (F : A →ₗ[K] K) (q : A)
    (h : ∀ L M,F (B L*q*B M)=0) (a b : A) : F (a*q*b)=0 := by
  have hright (L : List J) : ∀ b,F (B L*q*b)=0 := by
    have he : F.comp (LinearMap.mulLeft K (B L*q))=0 := by
      apply B.ext
      intro M
      exact h L M
    intro b
    exact LinearMap.congr_fun he b
  have he : (F.comp (LinearMap.mulRight K b)).comp (LinearMap.mulRight K q)=0 := by
    apply B.ext
    intro L
    exact hright L b
  exact LinearMap.congr_fun he a

variable (S : Submodule K A)

inductive Relation : A → A → Prop
  | relation (q : A) (hq : q∈S) : Relation q 0

abbrev Quotient := RingQuot (Relation S)

def quotientMap : A →ₐ[K] Quotient S := RingQuot.mkAlgHom K (Relation S)

def quotientPiece (n : ℕ) : Submodule K (Quotient S) :=
  (degreeSpace B n).map (quotientMap S).toLinearMap

def pieceMap (n : ℕ) : degreeSpace B n →ₗ[K] quotientPiece B S n where
  toFun x := ⟨quotientMap S x,⟨x.val,x.property,rfl⟩⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul _ _ _)

theorem pieceMap_surjective (n : ℕ) : Function.Surjective (pieceMap B S n) := by
  rintro ⟨x,hx⟩
  obtain ⟨y,hy,hxy⟩ := hx
  exact ⟨⟨y,hy⟩,Subtype.ext hxy⟩

/-- The independently written linear equations imposed by all quadratic
contexts after projection to the original word degree. -/
def relationFunctionals (n : ℕ) : Submodule K (Module.Dual K (degreeSpace B n)) where
  carrier := {φ | ∀ L M q,q∈S → φ (projectionToPiece B n (B L*q*B M))=0}
  zero_mem' := by simp only [Set.mem_setOf_eq,LinearMap.zero_apply,implies_true]
  add_mem' := by
    intro φ ψ hφ hψ L M q hq
    simp only [LinearMap.add_apply,hφ L M q hq,hψ L M q hq,add_zero]
  smul_mem' := by
    intro c φ hφ L M q hq
    simp only [LinearMap.smul_apply,hφ L M q hq,smul_zero]

variable (hS : S≤degreeSpace B 2)

include hmul hS in
theorem restriction_mem (n : ℕ) (φ : Module.Dual K (quotientPiece B S n)) :
    φ.comp (pieceMap B S n)∈relationFunctionals B S n := by
  intro L M q hq
  have hc : B L*q*B M∈degreeSpace B (L.length+2+M.length) :=
    degree_mul B hmul
      (degree_mul B hmul (basis_mem_degreeSpace B L) (hS hq))
      (basis_mem_degreeSpace B M)
  have he : pieceMap B S n (projectionToPiece B n (B L*q*B M))=0 := by
    apply Subtype.ext
    change quotientMap S (projection B n (B L*q*B M))=0
    rw [projection_homogeneous B n _ _ hc]
    split_ifs
    · rw [map_mul,map_mul]
      have hq0 : quotientMap S q=0 :=
        (RingQuot.mkAlgHom_rel K (Relation.relation q hq)).trans (map_zero _)
      rw [hq0,mul_zero,zero_mul]
    · exact map_zero _
  change φ (pieceMap B S n (projectionToPiece B n (B L*q*B M)))=0
  rw [he,map_zero]

def restriction (n : ℕ) :
    Module.Dual K (quotientPiece B S n) →ₗ[K] relationFunctionals B S n where
  toFun φ := ⟨φ.comp (pieceMap B S n),restriction_mem B hmul S hS n φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    rfl
  map_smul' c φ := by
    apply Subtype.ext
    rfl

theorem functional_respects_relation (n : ℕ) (φ : relationFunctionals B S n) :
    ∀ {x y},Relation S x y → ∀ a b,
      (φ.val.comp (projectionToPiece B n)) (a*x*b)=
        (φ.val.comp (projectionToPiece B n)) (a*y*b) := by
  intro x y h a b
  cases h with
  | relation hq =>
      simp only [mul_zero,zero_mul,map_zero]
      exact context_vanishes B (φ.val.comp (projectionToPiece B n)) x
        (fun L M ↦ φ.property L M x hq) a b

/-- A solution of the relation equations extends to an actual functional
on the algebra quotient by the proved linear quotient construction. -/
def liftFunctional (n : ℕ) (φ : relationFunctionals B S n) :
    Module.Dual K (Quotient S) :=
  RingQuotLinearRelations.lift (Relation S) (φ.val.comp (projectionToPiece B n))
    (functional_respects_relation B S n φ)

@[simp] theorem liftFunctional_mk (n : ℕ) (φ : relationFunctionals B S n) (x : A) :
    liftFunctional B S n φ (quotientMap S x)=φ.val (projectionToPiece B n x) :=
  RingQuotLinearRelations.lift_mk (K := K) (Relation S)
    (φ.val.comp (projectionToPiece B n)) (functional_respects_relation B S n φ) x

include hmul hS in
theorem restriction_bijective (n : ℕ) : Function.Bijective (restriction B hmul S hS n) := by
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := pieceMap_surjective B S n x
    exact LinearMap.congr_fun (congrArg Subtype.val h) y
  · intro φ
    refine ⟨(liftFunctional B S n φ).comp (quotientPiece B S n).subtype,?_⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change liftFunctional B S n φ (quotientMap S x.val)=φ.val x
    rw [liftFunctional_mk,projectionToPiece_retraction]

/-- Actual degree-n quotient dual, with no assumed grading or kernel identity. -/
def dualPieceEquiv (n : ℕ) :
    Module.Dual K (quotientPiece B S n) ≃ₗ[K] relationFunctionals B S n :=
  LinearEquiv.ofBijective (restriction B hmul S hS n)
    (restriction_bijective B hmul S hS n)

end PaperVerification.QuadraticWordFunctionals
