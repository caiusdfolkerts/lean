module

public import PaperVerification.FermionDescendingAssociatedGraded
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# The action induced on actual successive filtration quotients

A filtration-preserving algebra map acts on F_d/F_(d+1) by mapping its
representative.  These maps give an algebra map of the actual direct sum.
Their identity and composition laws are checked on quotient representatives,
so group actions are induced by the original action without transport through
an initial-algebra identification.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped DirectSum

namespace PaperVerification.Fermion.DescendingAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Restriction of the original algebra map to an actual filtration piece. -/
def filteredMap (f : Filtration R A) (e : A →ₐ[R] A)
    (he : ∀ d x,x∈f.piece d → e x∈f.piece d) (d : ℕ) :
    f.piece d →ₗ[R] f.piece d where
  toFun x := ⟨e x,he d x x.property⟩
  map_add' x y := Subtype.ext (map_add e (x : A) (y : A))
  map_smul' c x := Subtype.ext (map_smul e c (x : A))

/-- The map on the actual quotient F_d/F_(d+1). -/
def pieceMap (f : Filtration R A) (e : A →ₐ[R] A)
    (he : ∀ d x,x∈f.piece d → e x∈f.piece d) (d : ℕ) :
    GradedPiece f d →ₗ[R] GradedPiece f d :=
  (nextRestricted f d).mapQ (nextRestricted f d) (filteredMap f e he d)
    (fun x hx ↦ he (d+1) x hx)

@[simp] theorem pieceMap_mk (f : Filtration R A) (e : A →ₐ[R] A)
    (he : ∀ d x,x∈f.piece d → e x∈f.piece d) (d : ℕ) (x : f.piece d) :
    pieceMap f e he d (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk (⟨e x,he d x x.property⟩ : f.piece d) := rfl

theorem pieceMap_one (f : Filtration R A) (e : A →ₐ[R] A)
    (he : ∀ d x,x∈f.piece d → e x∈f.piece d) :
    pieceMap f e he 0 (gradedOne f)=gradedOne f := by
  rw [gradedOne_def,pieceMap_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact map_one e

theorem pieceMap_mul (f : Filtration R A) (e : A →ₐ[R] A)
    (he : ∀ d x,x∈f.piece d → e x∈f.piece d) (i j : ℕ)
    (x : GradedPiece f i) (y : GradedPiece f j) :
    pieceMap f e he (i+j) (gradedMul f i j x y)=
      gradedMul f i j (pieceMap f e he i x) (pieceMap f e he j y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
          rw [gradedMul_apply_mk,pieceMap_mk,pieceMap_mk,pieceMap_mk,gradedMul_apply_mk]
          apply congrArg Submodule.Quotient.mk
          apply Subtype.ext
          exact map_mul e (x : A) (y : A)

/-- The induced algebra map is assembled from the original representative maps. -/
def associatedMap (f : Filtration R A) (e : A →ₐ[R] A)
    (he : ∀ d x,x∈f.piece d → e x∈f.piece d) :
    AssociatedGraded f →ₐ[R] AssociatedGraded f :=
  DirectSum.toAlgebra R _
    (fun d ↦ (DirectSum.lof R ℕ (GradedPiece f) d).comp (pieceMap f e he d))
    (by
      change DirectSum.of (GradedPiece f) 0 (pieceMap f e he 0 (gradedOne f))=1
      rw [pieceMap_one,associatedGraded_of_gradedOne])
    (by
      intro i j x y
      change DirectSum.of (GradedPiece f) (i+j)
          (pieceMap f e he (i+j) (gradedMul f i j x y))=
        DirectSum.of (GradedPiece f) i (pieceMap f e he i x)*
          DirectSum.of (GradedPiece f) j (pieceMap f e he j y)
      rw [associatedGraded_of_mul_of,pieceMap_mul])

@[simp] theorem associatedMap_of (f : Filtration R A) (e : A →ₐ[R] A)
    (he : ∀ d x,x∈f.piece d → e x∈f.piece d) (d : ℕ) (x : GradedPiece f d) :
    associatedMap f e he (DirectSum.of (GradedPiece f) d x)=
      DirectSum.of (GradedPiece f) d (pieceMap f e he d x) :=
  DirectSum.toAddMonoid_of _ d x

@[simp] theorem associatedMap_of_mk (f : Filtration R A) (e : A →ₐ[R] A)
    (he : ∀ d x,x∈f.piece d → e x∈f.piece d) (d : ℕ) (x : f.piece d) :
    associatedMap f e he (DirectSum.of (GradedPiece f) d (Submodule.Quotient.mk x))=
      DirectSum.of (GradedPiece f) d
        (Submodule.Quotient.mk (⟨e x,he d x x.property⟩ : f.piece d)) := by
  rw [associatedMap_of,pieceMap_mk]

/-- Every filtration-preserving automorphism induces its actual graded automorphism. -/
def associatedEquiv (f : Filtration R A) (e : A ≃ₐ[R] A)
    (he : ∀ d x,e x∈f.piece d ↔ x∈f.piece d) :
    AssociatedGraded f ≃ₐ[R] AssociatedGraded f :=
  let hf : ∀ d x,x∈f.piece d → e x∈f.piece d :=
    fun d x hx ↦ (he d x).mpr hx
  let hb : ∀ d x,x∈f.piece d → e.symm x∈f.piece d :=
    fun d x hx ↦ (he d (e.symm x)).mp (by simpa only [e.apply_symm_apply] using hx)
  let forward := associatedMap f e.toAlgHom hf
  let backward := associatedMap f e.symm.toAlgHom hb
  AlgEquiv.ofAlgHom forward backward
    (by
      apply DirectSum.algHom_ext
      intro d x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
          change forward (backward (DirectSum.of (GradedPiece f) d
            (Submodule.Quotient.mk x)))=
              DirectSum.of (GradedPiece f) d (Submodule.Quotient.mk x)
          let x' : f.piece d := ⟨e.symm (x : A),hb d x x.property⟩
          have hback : backward (DirectSum.of (GradedPiece f) d
              (Submodule.Quotient.mk x))=
                DirectSum.of (GradedPiece f) d (Submodule.Quotient.mk x') :=
            associatedMap_of_mk f e.symm.toAlgHom hb d x
          have hforward := associatedMap_of_mk f e.toAlgHom hf d x'
          refine (congrArg forward hback).trans (hforward.trans ?_)
          apply congrArg (fun y : f.piece d ↦
            DirectSum.of (GradedPiece f) d (Submodule.Quotient.mk y))
          apply Subtype.ext
          exact e.apply_symm_apply (x : A))
    (by
      apply DirectSum.algHom_ext
      intro d x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
          change backward (forward (DirectSum.of (GradedPiece f) d
            (Submodule.Quotient.mk x)))=
              DirectSum.of (GradedPiece f) d (Submodule.Quotient.mk x)
          let x' : f.piece d := ⟨e (x : A),hf d x x.property⟩
          have hforward : forward (DirectSum.of (GradedPiece f) d
              (Submodule.Quotient.mk x))=
                DirectSum.of (GradedPiece f) d (Submodule.Quotient.mk x') :=
            associatedMap_of_mk f e.toAlgHom hf d x
          have hback := associatedMap_of_mk f e.symm.toAlgHom hb d x'
          refine (congrArg backward hforward).trans (hback.trans ?_)
          apply congrArg (fun y : f.piece d ↦
            DirectSum.of (GradedPiece f) d (Submodule.Quotient.mk y))
          apply Subtype.ext
          exact e.symm_apply_apply (x : A))

@[simp] theorem associatedEquiv_of_mk (f : Filtration R A) (e : A ≃ₐ[R] A)
    (he : ∀ d x,e x∈f.piece d ↔ x∈f.piece d) (d : ℕ) (x : f.piece d) :
    associatedEquiv f e he (DirectSum.of (GradedPiece f) d (Submodule.Quotient.mk x))=
      DirectSum.of (GradedPiece f) d
        (Submodule.Quotient.mk (⟨e x,(he d x).mpr x.property⟩ : f.piece d)) :=
  associatedMap_of_mk f e.toAlgHom (fun d x hx ↦ (he d x).mpr hx) d x

/-- The induced action comes directly from the original action on each quotient. -/
def associatedAction {G : Type*} [Group G] (f : Filtration R A)
    (rho : G →* (A ≃ₐ[R] A))
    (hrho : ∀ g d x,rho g x∈f.piece d ↔ x∈f.piece d) :
    G →* (AssociatedGraded f ≃ₐ[R] AssociatedGraded f) where
  toFun g := associatedEquiv f (rho g) (hrho g)
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply DirectSum.algHom_ext
    intro d x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change associatedEquiv f (rho 1) (hrho 1) (DirectSum.of _ d (Submodule.Quotient.mk x))=_
        simp only [associatedEquiv_of_mk,map_one,AlgEquiv.one_apply,AlgEquiv.coe_toAlgHom]
  map_mul' g h := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply DirectSum.algHom_ext
    intro d x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change associatedEquiv f (rho (g*h)) (hrho (g*h))
          (DirectSum.of _ d (Submodule.Quotient.mk x))=
          associatedEquiv f (rho g) (hrho g)
            (associatedEquiv f (rho h) (hrho h) (DirectSum.of _ d (Submodule.Quotient.mk x)))
        simp only [associatedEquiv_of_mk,map_mul,AlgEquiv.mul_apply]

end PaperVerification.Fermion.DescendingAlgebra
