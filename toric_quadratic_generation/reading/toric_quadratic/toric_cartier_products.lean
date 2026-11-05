module

public import PaperVerification.ToricCartierPresentation
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

/-!
# Cartier products and actual section multiplication

Products and inverses are defined by multiplying and inverting genuine local
rational generators on a common open refinement. The section multiplication
map is multiplication of actual rational functions, first as a bilinear map
of actual sheaf sections and then as the induced tensor-product map.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

/-- The pushforward rational-function sections carry the actual ring
structure of the generic-point structure sheaf on the inverse image. -/
instance rationalSectionsCommRing (U : X.Opens) : CommRing Γ(rationalFunctions X,U) :=
  inferInstanceAs (CommRing Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U))

/-- Multiplication in the actual generic-point pushforward ring. -/
def rationalMul (U : X.Opens) (s t : Γ(rationalFunctions X,U)) :
    Γ(rationalFunctions X,U) :=
  (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s) *
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t)

@[simp] theorem rationalValue_mul (U : X.Opens) [Nonempty U]
    (s t : Γ(rationalFunctions X,U)) :
    rationalValue X U (rationalMul U s t) =
      rationalValue X U s * rationalValue X U t :=
  map_mul (rationalSectionValueIso X U).hom.hom
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s)
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t)

theorem rationalMul_add_left (U : X.Opens) (s t r : Γ(rationalFunctions X,U)) :
    rationalMul U (s+t) r = rationalMul U s r + rationalMul U t r := add_mul s t r

theorem rationalMul_add_right (U : X.Opens) (s t r : Γ(rationalFunctions X,U)) :
    rationalMul U s (t+r) = rationalMul U s t + rationalMul U s r := mul_add s t r

theorem rationalMul_smul_left (U : X.Opens) (a : Γ(X,U))
    (s t : Γ(rationalFunctions X,U)) :
    rationalMul U (a • s) t = a • rationalMul U s t := by
  change ((genericPointMap X).app U a *
      (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s)) *
      (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t) =
    (genericPointMap X).app U a *
      ((show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s) *
        (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t))
  exact mul_assoc _ _ _

theorem rationalMul_smul_right (U : X.Opens) (a : Γ(X,U))
    (s t : Γ(rationalFunctions X,U)) :
    rationalMul U s (a • t) = a • rationalMul U s t := by
  change (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s) *
      ((genericPointMap X).app U a *
        (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t)) =
    (genericPointMap X).app U a *
      ((show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s) *
        (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t))
  exact mul_left_comm _ _ _

theorem rationalMul_restrict {U V : X.Opens} (i : V ⟶ U)
    (s t : Γ(rationalFunctions X,U)) :
    (rationalFunctions X).presheaf.map i.op (rationalMul U s t) =
      rationalMul V ((rationalFunctions X).presheaf.map i.op s)
        ((rationalFunctions X).presheaf.map i.op t) :=
  map_mul ((Spec X.functionField).presheaf.map
    ((Opens.map (genericPointMap X).base).map i).op).hom
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s)
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t)

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- Addition of Cartier divisors multiplies their O(D) local generators. -/
def mul : RationalCartierCocycle X where
  index := C.index × D.index
  openSet i := C.openSet i.1 ⊓ D.openSet i.2
  covers x := by
    obtain ⟨i,hi⟩ := C.covers x
    obtain ⟨j,hj⟩ := D.covers x
    exact ⟨(i,j),hi,hj⟩
  generator i := C.generator i.1 * D.generator i.2
  transition i j x hi hj := by
    have hC := C.transition i.1 j.1 x hi.1 hj.1
    have hD := D.transition i.2 j.2 x hi.2 hj.2
    have h := (regularAtSubring X x).mul_mem hC hD
    simpa only [Units.val_mul,div_mul_div_comm] using h

/-- Negation of a Cartier divisor inverts its nonzero rational generators. -/
def inv : RationalCartierCocycle X where
  index := C.index
  openSet := C.openSet
  covers := C.covers
  generator i := (C.generator i)⁻¹
  transition i j x hi hj := by
    have h := C.transition j i x hj hi
    have he : ((C.generator i : X.functionField)⁻¹ /
        (C.generator j : X.functionField)⁻¹) =
        (C.generator j : X.functionField)/(C.generator i : X.functionField) := by
      field_simp [Units.ne_zero]
    simpa only [Units.val_inv_eq_inv_val,he] using h

/-- A principal fractional sheaf, with its specified rational generator. -/
def principal (q : X.functionFieldˣ) : RationalCartierCocycle X where
  index := PUnit.{u+1}
  openSet _ := ⊤
  covers x := ⟨PUnit.unit,trivial⟩
  generator _ := q
  transition _ _ _ _ _ := by simpa using (regularAtSubring X _).one_mem

theorem isSection_mul (U : X.Opens)
    (s t : Γ(rationalFunctions X,U))
    (hs : C.IsSection U s) (ht : D.IsSection U t) :
    (C.mul D).IsSection U (rationalMul U s t) := by
  intro i x hx
  letI : Nonempty U := ⟨x⟩
  have h := (regularAtSubring X x.val).mul_mem
    (hs i.1 x hx.1) (ht i.2 x hx.2)
  simpa only [rationalValueAt_eq,rationalValue_mul,mul,Units.val_mul,
    div_mul_div_comm] using h

/-- Multiplication of actual sections, before passing to the tensor product. -/
def sectionProduct (U : X.Opens) :
    Γ(C.sheaf,U) →ₗ[Γ(X,U)] Γ(D.sheaf,U) →ₗ[Γ(X,U)] Γ((C.mul D).sheaf,U) where
  toFun s :=
    { toFun := fun t=>⟨rationalMul U s.val t.val,
        C.isSection_mul D U s.val t.val s.property t.property⟩
      map_add' := fun t r=>Subtype.ext (rationalMul_add_right U s.val t.val r.val)
      map_smul' := fun a t=>Subtype.ext (rationalMul_smul_right U a s.val t.val) }
  map_add' s t := by
    ext r
    exact Subtype.ext (rationalMul_add_left U s.val t.val r.val)
  map_smul' a s := by
    ext t
    exact Subtype.ext (rationalMul_smul_left U a s.val t.val)

@[simp] theorem sectionProduct_value (U : X.Opens) [Nonempty U]
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    (C.mul D).toCartierData.sectionValue U (C.sectionProduct D U s t) =
      C.toCartierData.sectionValue U s * D.toCartierData.sectionValue U t :=
  rationalValue_mul U s.val t.val

/-- The genuine section multiplication map on tensor products. -/
def sectionMultiplication (U : X.Opens) :
    Γ(C.sheaf,U) ⊗[Γ(X,U)] Γ(D.sheaf,U) →ₗ[Γ(X,U)] Γ((C.mul D).sheaf,U) :=
  TensorProduct.lift (C.sectionProduct D U)

@[simp] theorem sectionMultiplication_tmul (U : X.Opens)
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    C.sectionMultiplication D U (s ⊗ₜ[Γ(X,U)] t) = C.sectionProduct D U s t := rfl

theorem sectionProduct_restrict {U V : X.Opens} (i : V ⟶ U)
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    (C.mul D).sheaf.presheaf.map i.op (C.sectionProduct D U s t) =
      C.sectionProduct D V (C.sheaf.presheaf.map i.op s)
        (D.sheaf.presheaf.map i.op t) := by
  apply Subtype.ext
  exact rationalMul_restrict i s.val t.val

end RationalCartierCocycle

namespace CartierData

variable (D E : CartierData X)

/-- Sum of fractional Cartier presentations, constructed from actual local
equations on the common refinement. -/
def add : CartierData X := (D.localCocycle.mul E.localCocycle).toCartierData

/-- Additive inverse, using inverse rational local generators. -/
def neg : CartierData X := D.localCocycle.inv.toCartierData

/-- Section multiplication for arbitrary actual Cartier presentations. -/
def sectionProduct (U : X.Opens) :
    Γ(D.sheaf,U) →ₗ[Γ(X,U)] Γ(E.sheaf,U) →ₗ[Γ(X,U)] Γ((D.add E).sheaf,U) :=
  ((D.localCocycle.sectionProduct E.localCocycle U).compl₂ (E.presentationMap U)).comp
    (D.presentationMap U)

/-- The tensor-product multiplication map is induced by actual rational
function multiplication. -/
def sectionMultiplication (U : X.Opens) :
    Γ(D.sheaf,U) ⊗[Γ(X,U)] Γ(E.sheaf,U) →ₗ[Γ(X,U)] Γ((D.add E).sheaf,U) :=
  TensorProduct.lift (D.sectionProduct E U)

@[simp] theorem sectionProduct_value (U : X.Opens) [Nonempty U]
    (s : Γ(D.sheaf,U)) (t : Γ(E.sheaf,U)) :
    (D.add E).sectionValue U (D.sectionProduct E U s t) =
      D.sectionValue U s * E.sectionValue U t :=
  rationalValue_mul U (D.inclusion.app U s) (E.inclusion.app U t)

@[simp] theorem sectionMultiplication_value_tmul (U : X.Opens) [Nonempty U]
    (s : Γ(D.sheaf,U)) (t : Γ(E.sheaf,U)) :
    (D.add E).sectionValue U (D.sectionMultiplication E U (s ⊗ₜ[Γ(X,U)] t)) =
      D.sectionValue U s * E.sectionValue U t :=
  D.sectionProduct_value E U s t

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProduct_restrict
#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplication_value_tmul
