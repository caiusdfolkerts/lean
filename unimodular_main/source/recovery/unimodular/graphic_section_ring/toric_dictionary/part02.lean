module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part01
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricCartierProducts



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
end
-- END PaperVerification.ToricCartierProducts
end

section
-- BEGIN PaperVerification.ToricCartierAmple



/-!
# Intrinsic nonvanishing and ampleness of actual Cartier sheaves

The nonvanishing open is computed from actual regular coordinates in local
frames. Its membership is independent of the frame, and is exactly the
condition that the local coefficient is outside the maximal ideal of the
actual local ring. Ampleness uses the standard affine nonvanishing-open
definition (EGA II, Definition 4.5.3; Stacks Project, tag 01PS).

No fan, polytope, support-function inequality, or section-space formula is
part of this definition. Powers use powers of actual local Cartier equations;
the tensor-sheaf identification is developed separately.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

/-- The usual unit condition in an actual local ring, expressed through its
injective embedding in the actual function field. -/
theorem isUnit_stalk_iff (x : X) (a : X.presheaf.stalk x) :
    IsUnit a ↔
      algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 ∧
      (algebraMap (X.presheaf.stalk x) X.functionField a)⁻¹ ∈ regularAtSubring X x := by
  constructor
  · rintro ⟨u,rfl⟩
    have hne : algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x)≠0 :=
      ((u.isUnit).map (algebraMap (X.presheaf.stalk x) X.functionField)).ne_zero
    refine ⟨hne,⟨(u⁻¹ : (X.presheaf.stalk x)ˣ),?_⟩⟩
    apply mul_left_cancel₀ hne
    rw [← map_mul,u.mul_inv,map_one,mul_inv_cancel₀ hne]
  · rintro ⟨hne,b,hb⟩
    have hab : a*b=1 := by
      apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      rw [map_mul,hb,map_one,mul_inv_cancel₀ hne]
    exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,rfl⟩

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- Natural powers of the actual local rational generators. -/
def pow (n : ℕ) : RationalCartierCocycle X where
  index := C.index
  openSet := C.openSet
  covers := C.covers
  generator i := C.generator i ^ n
  transition i j x hi hj := by
    simpa only [Units.val_pow_eq_pow_val,div_pow] using
      (regularAtSubring X x).pow_mem (C.transition i j x hi hj) n

@[simp] theorem pow_openSet (n : ℕ) (i : C.index) :
    (C.pow n).openSet i=C.openSet i := rfl

@[simp] theorem pow_generator (n : ℕ) (i : C.index) :
    ((C.pow n).generator i : X.functionField)=(C.generator i : X.functionField)^n := rfl

/-- The actual regular coefficient of a global section in a local frame. -/
def localCoefficient (i : C.index) (s : Γ(C.sheaf,⊤)) : Γ(X,C.openSet i) :=
  C.localCoordinates i (C.openSet i) le_rfl
    (C.sheaf.presheaf.map (homOfLE le_top).op s)

theorem localCoefficient_value (i : C.index) [Nonempty (C.openSet i)]
    (s : Γ(C.sheaf,⊤)) :
    X.germToFunctionField (C.openSet i) (C.localCoefficient i s) =
      C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField) := by
  rw [localCoefficient,C.localCoordinates_value]
  change rationalValue X (C.openSet i)
      ((rationalFunctions X).presheaf.map (homOfLE le_top).op s.val) /
        (C.generator i : X.functionField) =
    rationalValue X ⊤ s.val / (C.generator i : X.functionField)
  exact congrArg (fun z : X.functionField => z / (C.generator i : X.functionField))
    (rationalValue_restrict X (homOfLE (show C.openSet i≤⊤ from le_top)) s.val)

/-- The usual nonvanishing locus of a section, as an actual open set. -/
def nonvanishingOpen (s : Γ(C.sheaf,⊤)) : X.Opens :=
  ⨆ i,X.basicOpen (C.localCoefficient i s)

/-- In any chosen local frame, nonvanishing is the actual local unit test. -/
theorem mem_localNonvanishing_iff (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈X.basicOpen (C.localCoefficient i s) ↔
      C.toCartierData.sectionValue ⊤ s ≠ 0 ∧
      (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s ∈
        regularAtSubring X x := by
  letI : Nonempty (C.openSet i) := ⟨⟨x,hxi⟩⟩
  rw [X.mem_basicOpen _ x hxi,isUnit_stalk_iff,
    X.algebraMap_germ_eq_germToFunctionField hxi,C.localCoefficient_value]
  rw [div_ne_zero_iff,inv_div]
  constructor
  · rintro ⟨⟨h,-⟩,hr⟩
    exact ⟨h,hr⟩
  · rintro ⟨h,hr⟩
    exact ⟨⟨h,(C.generator i).ne_zero⟩,hr⟩

/-- The local nonvanishing condition agrees on overlaps. -/
theorem localNonvanishing_iff (i j : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) (hxj : x∈C.openSet j) :
    x∈X.basicOpen (C.localCoefficient i s) ↔
      x∈X.basicOpen (C.localCoefficient j s) := by
  rw [C.mem_localNonvanishing_iff i s x hxi,
    C.mem_localNonvanishing_iff j s x hxj]
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hratio := C.transition j i x hxj hxi
    have he : ((C.generator j : X.functionField)/(C.generator i : X.functionField))*
        ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (C.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using (regularAtSubring X x).mul_mem hratio h
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hratio := C.transition i j x hxi hxj
    have he : ((C.generator i : X.functionField)/(C.generator j : X.functionField))*
        ((C.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using (regularAtSubring X x).mul_mem hratio h

/-- A frame-independent membership test for the actual nonvanishing open. -/
theorem mem_nonvanishingOpen_iff (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      IsUnit (X.presheaf.germ (C.openSet i) x hxi (C.localCoefficient i s)) := by
  rw [← X.mem_basicOpen _ x hxi]
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hx
    exact (C.localNonvanishing_iff j i s x (X.basicOpen_le _ hj) hxi).mp hj
  · intro hx
    exact Opens.mem_iSup.mpr ⟨i,hx⟩

/-- In the actual local rank-one coordinate, the section is nonvanishing
exactly when it is outside the maximal ideal. This is the ordinary fibre
criterion, without interpreting nonvanishing as a formal support inequality. -/
theorem mem_nonvanishingOpen_iff_not_mem_maximalIdeal
    (i : C.index) (s : Γ(C.sheaf,⊤)) (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      X.presheaf.germ (C.openSet i) x hxi (C.localCoefficient i s) ∉
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  rw [C.mem_nonvanishingOpen_iff i s x hxi,IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff,not_not]

/-- A power of an actual rational section is an actual section of the
corresponding power of its Cartier sheaf. -/
def sectionPow (n : ℕ) (s : Γ(C.sheaf,⊤)) : Γ((C.pow n).sheaf,⊤) := by
  let t : Γ(rationalFunctions X,⊤) :=
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val)^n
  refine ⟨t,?_⟩
  intro i x hx
  have hs : rationalValue X ⊤ s.val / (C.generator i : X.functionField) ∈
      regularAtSubring X x.val := s.property i x hx
  have h := (regularAtSubring X x.val).pow_mem hs n
  have ht : rationalValue X ⊤ t = (rationalValue X ⊤ s.val)^n :=
    map_pow (rationalSectionValueIso X ⊤).hom.hom
      (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val) n
  change rationalValue X ⊤ t / (C.generator i : X.functionField)^n ∈ regularAtSubring X x.val
  rw [ht]
  simpa only [div_pow] using h

@[simp] theorem sectionPow_value (n : ℕ) (s : Γ(C.sheaf,⊤)) :
    (C.pow n).toCartierData.sectionValue ⊤ (C.sectionPow n s) =
      (C.toCartierData.sectionValue ⊤ s)^n :=
  map_pow (rationalSectionValueIso X ⊤).hom.hom
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val) n

theorem localCoefficient_sectionPow (n : ℕ) (i : C.index)
    (s : Γ(C.sheaf,⊤)) :
    (C.pow n).localCoefficient i (C.sectionPow n s) = (C.localCoefficient i s)^n := by
  classical
  by_cases hU : Nonempty (C.openSet i)
  · letI := hU
    letI : Nonempty ((C.pow n).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    apply X.germToFunctionField_injective (C.openSet i)
    calc
      _ = (C.pow n).toCartierData.sectionValue ⊤ (C.sectionPow n s) /
          (C.generator i : X.functionField)^n :=
        (C.pow n).localCoefficient_value i (C.sectionPow n s)
      _ = (C.toCartierData.sectionValue ⊤ s)^n / (C.generator i : X.functionField)^n :=
        congrArg (fun z : X.functionField => z / (C.generator i : X.functionField)^n)
          (C.sectionPow_value n s)
      _ = (C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField))^n :=
        (div_pow _ _ n).symm
      _ = (X.germToFunctionField (C.openSet i) (C.localCoefficient i s))^n :=
        congrArg (fun z : X.functionField => z^n) (C.localCoefficient_value i s).symm
      _ = _ := (map_pow (X.germToFunctionField (C.openSet i)).hom _ n).symm
  · have hbot : C.openSet i=⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hU ⟨⟨x,hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
    change (_ : Γ(X,C.openSet i)) = _
    exact Subsingleton.elim _ _

/-- Raising a section to a positive power preserves its actual nonvanishing
open, exactly as for regular functions. -/
theorem nonvanishingOpen_sectionPow (n : ℕ) (hn : 0<n) (s : Γ(C.sheaf,⊤)) :
    (C.pow n).nonvanishingOpen (C.sectionPow n s)=C.nonvanishingOpen s := by
  change (⨆ i : C.index,X.basicOpen ((C.pow n).localCoefficient i (C.sectionPow n s))) =
    ⨆ i : C.index,X.basicOpen (C.localCoefficient i s)
  apply iSup_congr
  intro i
  exact (congrArg (fun t : Γ(X,C.openSet i) => X.basicOpen t)
    (C.localCoefficient_sectionPow n i s)).trans (X.basicOpen_pow _ hn)

/-- The standard intrinsic definition of an ample Cartier sheaf. Compactness
here is quasi-compactness of the underlying spectral topological space. -/
def IsAmple : Prop :=
  CompactSpace X ∧ ∀ x : X,∃ n : ℕ,0<n ∧
    ∃ s : Γ((C.pow n).sheaf,⊤),
      x∈(C.pow n).nonvanishingOpen s ∧ IsAffineOpen ((C.pow n).nonvanishingOpen s)

/-- Ampleness supplies a finite affine cover by genuine nonvanishing opens
of positive tensor powers. -/
theorem IsAmple.exists_finite_cover (hC : C.IsAmple) :
    ∃ (ι : Type u) (_ : Fintype ι) (n : ι→ℕ)
      (s : ∀ i,Γ((C.pow (n i)).sheaf,⊤)),
      (∀ i,0<n i) ∧
      (∀ i,IsAffineOpen ((C.pow (n i)).nonvanishingOpen (s i))) ∧
      (⨆ i,(C.pow (n i)).nonvanishingOpen (s i))=⊤ := by
  classical
  letI := hC.1
  choose n hn s hs ha using hC.2
  have hcover : IsOpenCover (fun x:X=>(C.pow (n x)).nonvanishingOpen (s x)) := by
    apply le_antisymm le_top
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x,hs x⟩
  obtain ⟨t,ht⟩ := hcover.exists_finite_of_compactSpace
  exact ⟨t,inferInstance,fun i=>n i.val,fun i=>s i.val,
    fun i=>hn i.val,fun i=>ha i.val,ht⟩

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

/-- Multiplication of a Cartier divisor by a natural number. -/
def nsmul (n : ℕ) : CartierData X := (D.localCocycle.pow n).toCartierData

/-- Intrinsic ampleness, without any fan or polytope hypothesis. -/
def IsAmple : Prop := D.localCocycle.IsAmple

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.mem_nonvanishingOpen_iff_not_mem_maximalIdeal
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.nonvanishingOpen_sectionPow
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.IsAmple.exists_finite_cover
end
-- END PaperVerification.ToricCartierAmple
end

section
-- BEGIN PaperVerification.ToricCartierTranslate



/-!
# Principal translates and linear equivalence of actual Cartier sheaves

A nonzero rational function acts by an actual automorphism of the rational
function sheaf. Postcomposing a fractional embedding by this automorphism
changes the Cartier divisor by a principal divisor, while preserving its
actual invertible sheaf. This is linear equivalence, distinguished from the
embedding-preserving equivalence of presentations of the same divisor.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

def rationalScaleEquivNonempty (q : X.functionFieldˣ) (U : X.Opens) [Nonempty U] :
    Γ(rationalFunctions X,U) ≃ₗ[Γ(X,U)] Γ(rationalFunctions X,U) := by
  let e : X.functionField ≃ₗ[X.functionField] X.functionField :=
    LinearEquiv.smulOfUnit q
  exact (rationalValueLinearEquiv X U).trans
    ((e.restrictScalars Γ(X,U)).trans (rationalValueLinearEquiv X U).symm)

def rationalScaleEquiv (q : X.functionFieldˣ) (U : X.Opens) :
    Γ(rationalFunctions X,U) ≃ₗ[Γ(X,U)] Γ(rationalFunctions X,U) := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    exact rationalScaleEquivNonempty q U
  · exact LinearEquiv.refl _ _

@[simp] theorem rationalScaleEquiv_value (q : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] (s : Γ(rationalFunctions X,U)) :
    rationalValue X U (rationalScaleEquiv q U s) =
      (q : X.functionField)*rationalValue X U s := by
  simp only [rationalScaleEquiv,dif_pos (show Nonempty U from inferInstance)]
  change (rationalValueLinearEquiv X U)
      ((rationalValueLinearEquiv X U).symm
        ((q : X.functionField) * (rationalValueLinearEquiv X U) s)) =
    (q : X.functionField) * (rationalValueLinearEquiv X U) s
  exact (rationalValueLinearEquiv X U).apply_symm_apply _

theorem rationalScaleEquiv_restrict (q : X.functionFieldˣ)
    {U V : X.Opens} (i : V ⟶ U) (s : Γ(rationalFunctions X,U)) :
    rationalScaleEquiv q V ((rationalFunctions X).presheaf.map i.op s) =
      (rationalFunctions X).presheaf.map i.op (rationalScaleEquiv q U s) := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    letI : Nonempty U := ⟨⟨(Classical.choice hV).val,i.le (Classical.choice hV).property⟩⟩
    apply (rationalValue X V).injective
    rw [rationalScaleEquiv_value,rationalValue_restrict,rationalValue_restrict,
      rationalScaleEquiv_value]
  · have hbot : V=⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hV ⟨⟨x,hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X V hbot
    letI := Module.subsingleton Γ(X,V) Γ(rationalFunctions X,V)
    exact Subsingleton.elim _ _

/-- Multiplication by a rational unit is an actual sheaf automorphism. -/
def rationalScaleIso (q : X.functionFieldˣ) : rationalFunctions X ≅ rationalFunctions X :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun U=>(rationalScaleEquiv q U.unop).toModuleIso)
      (by
        intro U V f
        ext s
        exact rationalScaleEquiv_restrict q f.unop s)

namespace CartierData

variable (D E F : CartierData X)

/-- Linear equivalence records an isomorphism of the actual invertible
sheaves. It does not require equality of their rational embeddings. -/
def LinearlyEquivalent : Prop := Nonempty (D.sheaf ≅ E.sheaf)

theorem linearlyEquivalent_refl : D.LinearlyEquivalent D := ⟨Iso.refl _⟩

theorem linearlyEquivalent_symm (h : D.LinearlyEquivalent E) : E.LinearlyEquivalent D :=
  ⟨h.some.symm⟩

theorem linearlyEquivalent_trans (hDE : D.LinearlyEquivalent E)
    (hEF : E.LinearlyEquivalent F) : D.LinearlyEquivalent F := ⟨hDE.some ≪≫ hEF.some⟩

theorem Equivalent.linearlyEquivalent (h : D.Equivalent E) : D.LinearlyEquivalent E :=
  ⟨h.choose⟩

/-- Principal translation multiplies the actual fractional embedding by q.
The underlying actual sheaf is unchanged by construction. -/
def scale (q : X.functionFieldˣ) : CartierData X where
  sheaf := D.sheaf
  inclusion := D.inclusion ≫ (rationalScaleIso q).hom
  inclusion_injective U :=
    (rationalScaleEquiv q U).injective.comp (D.inclusion_injective U)
  locallyFree := D.locallyFree

def scaleSheafIso (q : X.functionFieldˣ) : (D.scale q).sheaf ≅ D.sheaf := Iso.refl _

theorem scale_linearlyEquivalent (q : X.functionFieldˣ) :
    (D.scale q).LinearlyEquivalent D := ⟨D.scaleSheafIso q⟩

@[simp] theorem scale_sectionValue (q : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf,U)) :
    (D.scale q).sectionValue U s = (q : X.functionField)*D.sectionValue U s :=
  rationalScaleEquiv_value q U (D.inclusion.app U s)

theorem scale_equivalent_scale (h : D.Equivalent E) (q : X.functionFieldˣ) :
    (D.scale q).Equivalent (E.scale q) := by
  obtain ⟨e,he⟩ := h
  refine ⟨e,?_⟩
  change e.hom ≫ (E.inclusion ≫ (rationalScaleIso q).hom) =
    D.inclusion ≫ (rationalScaleIso q).hom
  rw [← Category.assoc,he]

/-- The principal translation changes every local rational generator by
the same explicit factor, so no character shift is lost. -/
theorem scale_frameRationalGenerator (q : X.functionFieldˣ)
    {U : X.Opens} [Nonempty U] (e : D.Frame U) :
    (D.scale q).frameRationalGenerator e =
      (q : X.functionField)*D.frameRationalGenerator e :=
  D.scale_sectionValue q U (D.frameGenerator e U le_rfl)

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.rationalScaleIso
#print axioms PaperVerification.ToricSchemes.CartierData.scale_linearlyEquivalent
#print axioms PaperVerification.ToricSchemes.CartierData.scale_frameRationalGenerator
end
-- END PaperVerification.ToricCartierTranslate
end

section
-- BEGIN PaperVerification.ToricCartierDescent



/-!
# Descent of Cartier arithmetic through equality of presentations

Regular ratios of genuine local generators give inclusions of the actual
fractional sheaves. Ratios regular in both directions give an isomorphism
preserving the rational embedding. This proves that products, inverses and
powers descend through equality of Cartier-divisor presentations.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

namespace RationalCartierCocycle

variable (C D E F : RationalCartierCocycle X)

/-- Every local generator of C is a regular multiple of every local
generator of D wherever the two local frames overlap. -/
def GeneratorRatioRegular : Prop :=
  ∀ i j (x : X),x∈C.openSet i → x∈D.openSet j →
    (C.generator i : X.functionField)/(D.generator j : X.functionField) ∈
      regularAtSubring X x

theorem generatorRatioRegular_refl : C.GeneratorRatioRegular C := C.transition

theorem isSection_mono (h : C.GeneratorRatioRegular D)
    (U : X.Opens) (s : Γ(rationalFunctions X,U)) (hs : C.IsSection U s) :
    D.IsSection U s := by
  intro j x hxj
  obtain ⟨i,hxi⟩ := C.covers x.val
  have ht := h i j x.val hxi hxj
  have hc := hs i x hxi
  have he : (rationalValueAt X U x s/(C.generator i : X.functionField))*
      ((C.generator i : X.functionField)/(D.generator j : X.functionField)) =
      rationalValueAt X U x s/(D.generator j : X.functionField) := by
    field_simp [Units.ne_zero]
  simpa only [he] using (regularAtSubring X x.val).mul_mem hc ht

def sameGeneratorSheafLinearEquiv
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C)
    (U : X.Opens) : Γ(C.sheaf,U) ≃ₗ[Γ(X,U)] Γ(D.sheaf,U) where
  toFun s := ⟨s.val,C.isSection_mono D hCD U s.val s.property⟩
  invFun s := ⟨s.val,D.isSection_mono C hDC U s.val s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Equality of the actual fractional subsheaves, with the same rational
values under the resulting sheaf isomorphism. -/
def sameGeneratorSheafIso
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C) :
    C.sheaf ≅ D.sheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U=>(C.sameGeneratorSheafLinearEquiv D hCD hDC U.unop).toModuleIso)
      (by intros; rfl)

theorem equivalent_of_generatorRatios
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C) :
    C.toCartierData.Equivalent D.toCartierData := by
  refine ⟨C.sameGeneratorSheafIso D hCD hDC,?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rfl

theorem GeneratorRatioRegular.mul
    (hCD : C.GeneratorRatioRegular D) (hEF : E.GeneratorRatioRegular F) :
    (C.mul E).GeneratorRatioRegular (D.mul F) := by
  intro i j x hxi hxj
  have h₁ := hCD i.1 j.1 x hxi.1 hxj.1
  have h₂ := hEF i.2 j.2 x hxi.2 hxj.2
  change ((C.generator i.1 : X.functionField) * (E.generator i.2 : X.functionField)) /
    ((D.generator j.1 : X.functionField) * (F.generator j.2 : X.functionField)) ∈
      regularAtSubring X x
  simpa only [div_mul_div_comm] using
    (regularAtSubring X x).mul_mem h₁ h₂

theorem GeneratorRatioRegular.inv (hDC : D.GeneratorRatioRegular C) :
    C.inv.GeneratorRatioRegular D.inv := by
  intro i j x hxi hxj
  change (((C.generator i)⁻¹ : X.functionFieldˣ) : X.functionField) /
    (((D.generator j)⁻¹ : X.functionFieldˣ) : X.functionField) ∈ regularAtSubring X x
  simpa only [Units.val_inv_eq_inv_val,inv_div_inv] using hDC j i x hxj hxi

theorem GeneratorRatioRegular.pow (hCD : C.GeneratorRatioRegular D) (n : ℕ) :
    (C.pow n).GeneratorRatioRegular (D.pow n) := by
  intro i j x hxi hxj
  change (C.generator i : X.functionField)^n /
    (D.generator j : X.functionField)^n ∈ regularAtSubring X x
  simpa only [div_pow] using
    (regularAtSubring X x).pow_mem (hCD i j x hxi hxj) n

end RationalCartierCocycle

namespace CartierData

variable (D D' E E' : CartierData X)

set_option backward.isDefEq.respectTransparency false in
/-- Equality of actual fractional sheaves makes all cross-frame ratios
regular in the actual local rings. -/
theorem localCocycle_generatorRatios (h : D.Equivalent D') :
    D.localCocycle.GeneratorRatioRegular D'.localCocycle := by
  intro i j x hxi hxj
  let U := invertibleOpen D.locallyFree i
  let W := invertibleOpen D'.locallyFree j
  let V : X.Opens := U⊓W
  letI : Nonempty U := ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
  letI : Nonempty W := ⟨⟨j,mem_invertibleOpen D'.locallyFree j⟩⟩
  letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
  have hq : D.frameRationalGenerator (invertibleFrame D.locallyFree i) ∈
      D.sectionValueRange V :=
    ⟨D.frameGenerator (invertibleFrame D.locallyFree i) V inf_le_left,
      D.sectionValue_frameGenerator _ inf_le_left⟩
  rw [D.equivalent_sectionValueRange D' h V] at hq
  obtain ⟨a,ha⟩ :=
    (D'.mem_sectionValueRange_iff (invertibleFrame D'.locallyFree j)
      (V := V) inf_le_right _).mp hq
  have ha' : X.germToFunctionField V a =
      D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
        D'.frameRationalGenerator (invertibleFrame D'.locallyFree j) :=
    (eq_div_iff (D'.frameRationalGenerator_ne_zero _)).mpr ha
  change D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
    D'.frameRationalGenerator (invertibleFrame D'.locallyFree j) ∈ regularAtSubring X x
  rw [← ha']
  exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩

theorem add_equivalent_add (hD : D.Equivalent D') (hE : E.Equivalent E') :
    (D.add E).Equivalent (D'.add E') :=
  (D.localCocycle.mul E.localCocycle).equivalent_of_generatorRatios
    (D'.localCocycle.mul E'.localCocycle)
    (RationalCartierCocycle.GeneratorRatioRegular.mul
      D.localCocycle D'.localCocycle E.localCocycle E'.localCocycle
      (D.localCocycle_generatorRatios D' hD) (E.localCocycle_generatorRatios E' hE))
    (RationalCartierCocycle.GeneratorRatioRegular.mul
      D'.localCocycle D.localCocycle E'.localCocycle E.localCocycle
      (D'.localCocycle_generatorRatios D (D.equivalent_symm D' hD))
      (E'.localCocycle_generatorRatios E (E.equivalent_symm E' hE)))

theorem neg_equivalent_neg (hD : D.Equivalent D') :
    D.neg.Equivalent D'.neg :=
  D.localCocycle.inv.equivalent_of_generatorRatios D'.localCocycle.inv
    (RationalCartierCocycle.GeneratorRatioRegular.inv D.localCocycle D'.localCocycle
      (D'.localCocycle_generatorRatios D (D.equivalent_symm D' hD)))
    (RationalCartierCocycle.GeneratorRatioRegular.inv D'.localCocycle D.localCocycle
      (D.localCocycle_generatorRatios D' hD))

theorem nsmul_equivalent_nsmul (hD : D.Equivalent D') (n : ℕ) :
    (D.nsmul n).Equivalent (D'.nsmul n) :=
  (D.localCocycle.pow n).equivalent_of_generatorRatios (D'.localCocycle.pow n)
    (RationalCartierCocycle.GeneratorRatioRegular.pow D.localCocycle D'.localCocycle
      (D.localCocycle_generatorRatios D' hD) n)
    (RationalCartierCocycle.GeneratorRatioRegular.pow D'.localCocycle D.localCocycle
      (D'.localCocycle_generatorRatios D (D.equivalent_symm D' hD)) n)

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.equivalent_of_generatorRatios
#print axioms PaperVerification.ToricSchemes.CartierData.add_equivalent_add
#print axioms PaperVerification.ToricSchemes.CartierData.neg_equivalent_neg
#print axioms PaperVerification.ToricSchemes.CartierData.nsmul_equivalent_nsmul
end
-- END PaperVerification.ToricCartierDescent
end

section
-- BEGIN PaperVerification.ToricCartierScaleCocycle



/-!
# Principal translations preserve intrinsic ampleness

The actual sheaf isomorphism multiplies rational values by the specified
factor. Its local regular coefficients are unchanged after the local
generators are multiplied by that same factor. Hence the actual
nonvanishing opens, including those of every positive tensor power, are
unchanged. This proves invariance of intrinsic ampleness under the principal
translation used to normalize a divisor on the torus.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X) (q : X.functionFieldˣ)

def scale : RationalCartierCocycle X where
  index := C.index
  openSet := C.openSet
  covers := C.covers
  generator i := q*C.generator i
  transition i j x hi hj := by
    have he : ((q : X.functionField)*(C.generator i : X.functionField))/
        ((q : X.functionField)*(C.generator j : X.functionField)) =
        (C.generator i : X.functionField)/(C.generator j : X.functionField) := by
      field_simp [Units.ne_zero]
    simpa only [Units.val_mul,he] using C.transition i j x hi hj

theorem isSection_scale_iff (U : X.Opens) (s : Γ(rationalFunctions X,U)) :
    C.IsSection U s ↔ (C.scale q).IsSection U (rationalScaleEquiv q U s) := by
  have he (i : C.index) (x : U) :
      rationalValueAt X U x (rationalScaleEquiv q U s) /
        ((C.scale q).generator i : X.functionField) =
      rationalValueAt X U x s/(C.generator i : X.functionField) := by
    letI : Nonempty U := ⟨x⟩
    rw [rationalValueAt_eq,rationalScaleEquiv_value,rationalValueAt_eq]
    change ((q : X.functionField)*rationalValue X U s)/
      ((q : X.functionField)*(C.generator i : X.functionField)) = _
    field_simp [Units.ne_zero]
  constructor <;> intro h i x hx
  · exact (he (show C.index from i) x).symm ▸ h i x hx
  · exact he i x ▸ h i x hx

def scaleSectionEquiv (U : X.Opens) :
    Γ(C.sheaf,U) ≃ₗ[Γ(X,U)] Γ((C.scale q).sheaf,U) where
  toFun s := ⟨rationalScaleEquiv q U s.val,(C.isSection_scale_iff q U s.val).mp s.property⟩
  invFun s :=
    ⟨(rationalScaleEquiv q U).symm s.val,
      (C.isSection_scale_iff q U ((rationalScaleEquiv q U).symm s.val)).mpr
        (Eq.mpr (congrArg ((C.scale q).IsSection U)
          ((rationalScaleEquiv q U).apply_symm_apply s.val)) s.property)⟩
  left_inv s := Subtype.ext ((rationalScaleEquiv q U).symm_apply_apply s.val)
  right_inv s := Subtype.ext ((rationalScaleEquiv q U).apply_symm_apply s.val)
  map_add' s t := Subtype.ext ((rationalScaleEquiv q U).map_add s.val t.val)
  map_smul' a s := Subtype.ext ((rationalScaleEquiv q U).map_smul a s.val)

def scaleSheafIso : C.sheaf ≅ (C.scale q).sheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun U=>(C.scaleSectionEquiv q U.unop).toModuleIso)
      (by
        intro U V f
        ext s
        apply Subtype.ext
        change rationalScaleEquiv q V.unop
            ((rationalFunctions X).presheaf.map f s.val) =
          (rationalFunctions X).presheaf.map f (rationalScaleEquiv q U.unop s.val)
        exact rationalScaleEquiv_restrict q f.unop s.val)

/-- The explicit generator scaling agrees with postcomposing the actual
fractional embedding by rational multiplication. -/
theorem scale_toCartierData_equivalent :
    (C.toCartierData.scale q).Equivalent (C.scale q).toCartierData := by
  refine ⟨C.scaleSheafIso q,?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rfl

@[simp] theorem scaleSheafIso_value (U : X.Opens) [Nonempty U]
    (s : Γ(C.sheaf,U)) :
    (C.scale q).toCartierData.sectionValue U ((C.scaleSheafIso q).hom.app U s) =
      (q : X.functionField)*C.toCartierData.sectionValue U s :=
  rationalScaleEquiv_value q U s.val

theorem scale_localCoefficient (i : C.index) (s : Γ(C.sheaf,⊤)) :
    (C.scale q).localCoefficient i ((C.scaleSheafIso q).hom.app ⊤ s) =
      C.localCoefficient i s := by
  classical
  by_cases hU : Nonempty (C.openSet i)
  · letI := hU
    let j : (C.scale q).index := i
    letI : Nonempty ((C.scale q).openSet j) := hU
    apply X.germToFunctionField_injective (C.openSet i)
    calc
      _ = (C.scale q).toCartierData.sectionValue ⊤
            ((C.scaleSheafIso q).hom.app ⊤ s) /
          ((C.scale q).generator j : X.functionField) :=
        (C.scale q).localCoefficient_value j _
      _ = C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField) := by
        rw [C.scaleSheafIso_value]
        change ((q : X.functionField)*C.toCartierData.sectionValue ⊤ s)/
          ((q : X.functionField)*(C.generator i : X.functionField)) = _
        field_simp [Units.ne_zero]
      _ = _ := (C.localCoefficient_value i s).symm
  · have hbot : C.openSet i=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
    change (_ : Γ(X,C.openSet i)) = _
    exact Subsingleton.elim _ _

theorem scale_nonvanishingOpen (s : Γ(C.sheaf,⊤)) :
    (C.scale q).nonvanishingOpen ((C.scaleSheafIso q).hom.app ⊤ s) =
      C.nonvanishingOpen s := by
  apply iSup_congr
  intro i
  exact congrArg (fun a : Γ(X,C.openSet i) => X.basicOpen a)
    (C.scale_localCoefficient q (show C.index from i) s)

theorem scale_nonvanishingOpen_inv (s : Γ((C.scale q).sheaf,⊤)) :
    C.nonvanishingOpen ((C.scaleSheafIso q).inv.app ⊤ s) =
      (C.scale q).nonvanishingOpen s := by
  have h := C.scale_nonvanishingOpen q ((C.scaleSheafIso q).inv.app ⊤ s)
  have he : (C.scaleSheafIso q).hom.app ⊤ ((C.scaleSheafIso q).inv.app ⊤ s)=s := by
    simpa only [Scheme.Modules.Hom.comp_app,Scheme.Modules.Hom.id_app,
      ConcreteCategory.comp_apply,ConcreteCategory.id_apply] using
      congrArg (fun f=>f.app ⊤ s) (C.scaleSheafIso q).inv_hom_id
  rw [he] at h
  exact h.symm

@[simp] theorem pow_scale (n : ℕ) : (C.scale q).pow n = (C.pow n).scale (q^n) := by
  cases C
  simp [scale,pow,mul_pow]

theorem mul_scale (D : RationalCartierCocycle X) (r : X.functionFieldˣ) :
    (C.scale q).mul (D.scale r)=(C.mul D).scale (q*r) := by
  cases C
  cases D
  simp [scale,mul,mul_assoc,mul_left_comm,mul_comm]

/-- Principal translation preserves the standard, intrinsic notion of
ampleness, because it preserves all actual nonvanishing opens. -/
theorem isAmple_scale_iff : (C.scale q).IsAmple ↔ C.IsAmple := by
  have hpow (n : ℕ) (x : X) :
      (∃ s : Γ(((C.scale q).pow n).sheaf,⊤),
        x ∈ ((C.scale q).pow n).nonvanishingOpen s ∧
          IsAffineOpen (((C.scale q).pow n).nonvanishingOpen s)) =
      (∃ s : Γ(((C.pow n).scale (q^n)).sheaf,⊤),
        x ∈ ((C.pow n).scale (q^n)).nonvanishingOpen s ∧
          IsAffineOpen (((C.pow n).scale (q^n)).nonvanishingOpen s)) :=
    congrArg (fun B : RationalCartierCocycle X =>
      ∃ s : Γ(B.sheaf,⊤), x ∈ B.nonvanishingOpen s ∧ IsAffineOpen (B.nonvanishingOpen s))
        (C.pow_scale q n)
  constructor
  · rintro ⟨hcompact,hcover⟩
    refine ⟨hcompact,?_⟩
    intro x
    obtain ⟨n,hn,s,hx,ha⟩ := hcover x
    obtain ⟨t,ht,hAt⟩ := Eq.mp (hpow n x) ⟨s,hx,ha⟩
    refine ⟨n,hn,((C.pow n).scaleSheafIso (q^n)).inv.app ⊤ t,?_,?_⟩
    · simpa only [(C.pow n).scale_nonvanishingOpen_inv (q^n) t] using ht
    · simpa only [(C.pow n).scale_nonvanishingOpen_inv (q^n) t] using hAt
  · rintro ⟨hcompact,hcover⟩
    refine ⟨hcompact,?_⟩
    intro x
    obtain ⟨n,hn,s,hx,ha⟩ := hcover x
    refine ⟨n,hn,Eq.mpr (hpow n x) ?_⟩
    refine ⟨((C.pow n).scaleSheafIso (q^n)).hom.app ⊤ s,?_,?_⟩
    · simpa only [(C.pow n).scale_nonvanishingOpen (q^n) s] using hx
    · simpa only [(C.pow n).scale_nonvanishingOpen (q^n) s] using ha

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X) (q : X.functionFieldˣ)

theorem scale_localCocycle :
    (D.scale q).localCocycle=D.localCocycle.scale q := by
  unfold localCocycle RationalCartierCocycle.scale
  congr 1
  funext x
  apply Units.ext
  letI : Nonempty (invertibleOpen D.locallyFree x) :=
    ⟨⟨x,mem_invertibleOpen D.locallyFree x⟩⟩
  exact D.scale_frameRationalGenerator q (invertibleFrame D.locallyFree x)

theorem isAmple_scale_iff : (D.scale q).IsAmple ↔ D.IsAmple := by
  change (D.scale q).localCocycle.IsAmple ↔ D.localCocycle.IsAmple
  rw [D.scale_localCocycle]
  exact D.localCocycle.isAmple_scale_iff q

theorem scale_add_equivalent (E : CartierData X) (r : X.functionFieldˣ) :
    ((D.scale q).add (E.scale r)).Equivalent ((D.add E).scale (q*r)) := by
  have h := (D.localCocycle.mul E.localCocycle).scale_toCartierData_equivalent (q*r)
  have heq : (D.scale q).add (E.scale r) =
      ((D.localCocycle.mul E.localCocycle).scale (q*r)).toCartierData := by
    unfold add
    rw [D.scale_localCocycle,E.scale_localCocycle,
      D.localCocycle.mul_scale q E.localCocycle r]
  rw [heq]
  exact CartierData.equivalent_symm _ _ h

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.scale_nonvanishingOpen
#print axioms PaperVerification.ToricSchemes.CartierData.isAmple_scale_iff
end
-- END PaperVerification.ToricCartierScaleCocycle
end

section
-- BEGIN PaperVerification.ToricFunctionFieldBridge



/-!
# Restriction of actual rational functions to a dense open affine scheme

An open immersion between irreducible schemes identifies their generic
stalks.  The map below is the genuine stalk map of that immersion, with
the generic points identified by Mathlib's generic-point theorem.  Its
compatibility with regular sections is proved from stalk-map naturality.
For an affine source its target is identified with the ordinary fraction
field of the coordinate ring by the universal property of localization.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped nonZeroDivisors

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    [IrreducibleSpace X] [IrreducibleSpace Y]

/-- Restriction to an open subscheme is an isomorphism of the actual
generic stalks.  No identification of rational functions is assumed. -/
def openImmersionFunctionFieldIso : Y.functionField ≅ X.functionField :=
  Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint X))

def openImmersionFunctionFieldEquiv : Y.functionField ≃+* X.functionField :=
  (openImmersionFunctionFieldIso j).commRingCatIsoToRingEquiv

/-- Every nonempty open of the target meets the open source.  This proves
the nonemptiness needed for its ordinary germ-to-function-field map. -/
theorem openImmersion_preimage_nonempty (U : Y.Opens) [Nonempty U] :
    Nonempty (j ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change j (genericPoint X) ∈ U
  rw [genericPoint_eq_of_isOpenImmersion j]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using (show Nonempty U from inferInstance))

set_option backward.isDefEq.respectTransparency.types false in
/-- The generic-stalk isomorphism sends the germ of a regular section to
the germ of its actual sheaf restriction. -/
theorem openImmersionFunctionFieldIso_germ (U : Y.Opens) [Nonempty U]
    [Nonempty (j ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ (openImmersionFunctionFieldIso j).hom =
      j.app U ≫ X.germToFunctionField (j ⁻¹ᵁ U) := by
  simp only [openImmersionFunctionFieldIso, Iso.trans_hom, Scheme.germToFunctionField,
    TopCat.Presheaf.stalkCongr_hom, asIso_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact j.germ_stalkMap U (genericPoint X) _

@[simp] theorem openImmersionFunctionFieldEquiv_germ (U : Y.Opens)
    [Nonempty U] [Nonempty (j ⁻¹ᵁ U)] (a : Γ(Y,U)) :
    openImmersionFunctionFieldEquiv j (Y.germToFunctionField U a) =
      X.germToFunctionField (j ⁻¹ᵁ U) (j.app U a) := by
  exact congrArg (fun f => f a) (openImmersionFunctionFieldIso_germ j U)

set_option backward.isDefEq.respectTransparency.types false in
/-- Compatibility with a composite of actual open immersions. -/
theorem openImmersionFunctionFieldIso_comp {Z : Scheme.{u}}
    [IrreducibleSpace Z] (g : Y ⟶ Z) [IsOpenImmersion g] :
    openImmersionFunctionFieldIso (j ≫ g) =
      openImmersionFunctionFieldIso g ≪≫ openImmersionFunctionFieldIso j := by
  apply Iso.ext
  apply Z.presheaf.stalk_hom_ext
  intro U hU
  letI : Nonempty U := ⟨⟨genericPoint Z,hU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := openImmersion_preimage_nonempty g U
  letI : Nonempty (j ⁻¹ᵁ (g ⁻¹ᵁ U)) :=
    openImmersion_preimage_nonempty j (g ⁻¹ᵁ U)
  letI : Nonempty ((j ≫ g) ⁻¹ᵁ U) := openImmersion_preimage_nonempty (j ≫ g) U
  change Z.germToFunctionField U ≫ (openImmersionFunctionFieldIso (j ≫ g)).hom =
    Z.germToFunctionField U ≫
      ((openImmersionFunctionFieldIso g).hom ≫ (openImmersionFunctionFieldIso j).hom)
  rw [openImmersionFunctionFieldIso_germ (j ≫ g) U, ← Category.assoc,
    openImmersionFunctionFieldIso_germ g U, Category.assoc,
    openImmersionFunctionFieldIso_germ j (g ⁻¹ᵁ U)]
  change (g.app U ≫ j.app (g ⁻¹ᵁ U)) ≫
      X.germToFunctionField (j ⁻¹ᵁ (g ⁻¹ᵁ U)) =
    g.app U ≫ (j.app (g ⁻¹ᵁ U) ≫ X.germToFunctionField (j ⁻¹ᵁ (g ⁻¹ᵁ U)))
  exact Category.assoc _ _ _

theorem openImmersionFunctionFieldEquiv_comp {Z : Scheme.{u}}
    [IrreducibleSpace Z] (g : Y ⟶ Z) [IsOpenImmersion g] :
    openImmersionFunctionFieldEquiv (j ≫ g) =
      (openImmersionFunctionFieldEquiv g).trans (openImmersionFunctionFieldEquiv j) := by
  ext r
  exact congrArg (fun e => e.hom r) (openImmersionFunctionFieldIso_comp j g)

/-- A regular function on a genuine nonempty chart open determines a
rational function on the ambient scheme, via the inverse generic-stalk
isomorphism. -/
def openImmersionRegularToFunctionField (U : X.Opens) [Nonempty U] :
    Γ(X,U) →+* Y.functionField :=
  (openImmersionFunctionFieldEquiv j).symm.toRingHom.comp
    (X.germToFunctionField U).hom

abbrev openImmersionGlobalToFunctionField : Γ(X,⊤) →+* Y.functionField :=
  openImmersionRegularToFunctionField j ⊤

theorem openImmersionRegularToFunctionField_injective [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    Function.Injective (openImmersionRegularToFunctionField j U) :=
  (openImmersionFunctionFieldEquiv j).symm.injective.comp
    (X.germToFunctionField_injective U)

theorem openImmersionGlobalToFunctionField_injective [IsIntegral X] :
    Function.Injective (openImmersionGlobalToFunctionField j) :=
  openImmersionRegularToFunctionField_injective j ⊤

/-- Changing to a smaller open chart leaves its rational value unchanged. -/
theorem openImmersionGlobalToFunctionField_restrict {Z : Scheme.{u}}
    [IrreducibleSpace Z] (g : Y ⟶ Z) [IsOpenImmersion g] (a : Γ(Y,⊤)) :
    openImmersionGlobalToFunctionField (j ≫ g) (j.appTop a) =
      openImmersionGlobalToFunctionField g a := by
  apply (openImmersionFunctionFieldEquiv (j ≫ g)).injective
  change (openImmersionFunctionFieldEquiv (j ≫ g))
      ((openImmersionFunctionFieldEquiv (j ≫ g)).symm
        (X.germToFunctionField ⊤ (j.appTop a))) =
    (openImmersionFunctionFieldEquiv (j ≫ g))
      ((openImmersionFunctionFieldEquiv g).symm (Y.germToFunctionField ⊤ a))
  rw [RingEquiv.apply_symm_apply, openImmersionFunctionFieldEquiv_comp]
  simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  letI : Nonempty (j ⁻¹ᵁ (⊤ : Y.Opens)) := openImmersion_preimage_nonempty j ⊤
  exact (openImmersionFunctionFieldEquiv_germ j ⊤ a).symm

theorem openImmersionRegularToFunctionField_restrict
    {U V : X.Opens} [Nonempty U] [Nonempty V] (i : V ⟶ U) (a : Γ(X,U)) :
    openImmersionRegularToFunctionField j V (X.presheaf.map i.op a) =
      openImmersionRegularToFunctionField j U a := by
  change (openImmersionFunctionFieldEquiv j).symm
      (X.germToFunctionField V (X.presheaf.map i.op a)) =
    (openImmersionFunctionFieldEquiv j).symm (X.germToFunctionField U a)
  exact congrArg (openImmersionFunctionFieldEquiv j).symm
    (X.presheaf.germ_res_apply i (genericPoint X) _ a)

theorem openImmersion_image_nonempty (U : X.Opens) [Nonempty U] :
    Nonempty (j ''ᵁ U) := by
  let x : U := Classical.choice (show Nonempty U from inferInstance)
  exact ⟨⟨j x,⟨x.val,x.property,rfl⟩⟩⟩

/-- The inverse field map of a chart section agrees with its ordinary
regular section on the open image, under the open-immersion section iso. -/
theorem openImmersionRegularToFunctionField_eq_germ_image
    (U : X.Opens) [Nonempty U] [Nonempty (j ''ᵁ U)] (a : Γ(X,U)) :
    openImmersionRegularToFunctionField j U a =
      Y.germToFunctionField (j ''ᵁ U) ((j.appIso U).inv a) := by
  letI : Nonempty (j ⁻¹ᵁ (j ''ᵁ U)) :=
    openImmersion_preimage_nonempty j (j ''ᵁ U)
  apply (openImmersionFunctionFieldEquiv j).injective
  change (openImmersionFunctionFieldEquiv j)
      ((openImmersionFunctionFieldEquiv j).symm (X.germToFunctionField U a)) =
    openImmersionFunctionFieldEquiv j
      (Y.germToFunctionField (j ''ᵁ U) ((j.appIso U).inv a))
  rw [RingEquiv.apply_symm_apply, openImmersionFunctionFieldEquiv_germ]
  have h := congrArg (fun f => f a) (j.appIso_inv_app U)
  simp only [ConcreteCategory.comp_apply] at h
  change X.germToFunctionField U a =
    X.germToFunctionField (j ⁻¹ᵁ (j ''ᵁ U))
      (j.app (j ''ᵁ U) ((j.appIso U).inv a))
  rw [h]
  exact (X.presheaf.germ_res_apply
    (eqToHom (Scheme.Hom.preimage_image_eq j U))
    (genericPoint X) (((genericPoint_spec X).mem_open_set_iff
      (j ⁻¹ᵁ (j ''ᵁ U)).isOpen).mpr
        (by simpa using (show Nonempty (j ⁻¹ᵁ (j ''ᵁ U)) from inferInstance))) a).symm

/-- A chart-regular function is regular in the ambient local ring at
every point of that chart.  Both local rings and their field embeddings
are the actual scheme stalk constructions. -/
theorem openImmersionRegularToFunctionField_mem_regularAt
    [IsIntegral Y] (U : X.Opens) [Nonempty U] (a : Γ(X,U))
    (x : X) (hx : x∈U) :
    openImmersionRegularToFunctionField j U a ∈ regularAtSubring Y (j x) := by
  letI : Nonempty (j ''ᵁ U) := openImmersion_image_nonempty j U
  rw [openImmersionRegularToFunctionField_eq_germ_image]
  exact regular_germ_mem_regularAt Y (j ''ᵁ U) ((j.appIso U).inv a)
    (j x) ⟨x,hx,rfl⟩

theorem openImmersionGlobalToFunctionField_mem_regularAt
    [IsIntegral Y] (a : Γ(X,⊤)) (x : X) :
    openImmersionGlobalToFunctionField j a ∈ regularAtSubring Y (j x) :=
  openImmersionRegularToFunctionField_mem_regularAt j ⊤ a x trivial

variable (R : CommRingCat.{u}) [IsDomain R]

/-- The actual generic stalk of `Spec R` is its fraction field, by the
uniqueness of localization at the nonzero divisors. -/
def affineFunctionFieldEquiv : (Spec R).functionField ≃ₐ[R] FractionRing R :=
  IsLocalization.algEquiv R⁰ (Spec R).functionField (FractionRing R)

@[simp] theorem affineFunctionFieldEquiv_algebraMap (r : R) :
    affineFunctionFieldEquiv R (algebraMap R (Spec R).functionField r) =
      algebraMap R (FractionRing R) r :=
  (affineFunctionFieldEquiv R).commutes r

/-- The algebra map used for this localization is precisely the germ of
the corresponding global regular function, not an unrelated embedding. -/
theorem affine_germToFunctionField_top :
    (Spec R).germToFunctionField ⊤ =
      (Scheme.ΓSpecIso R).hom ≫
        CommRingCat.ofHom (algebraMap R (Spec R).functionField) := by
  calc
    (Spec R).germToFunctionField ⊤ =
        (Scheme.ΓSpecIso R).hom ≫ ((Scheme.ΓSpecIso R).inv ≫
          (Spec R).germToFunctionField ⊤) := by simp
    _ = _ := rfl

@[simp] theorem affineFunctionFieldEquiv_germ_top (a : Γ(Spec R,⊤)) :
    affineFunctionFieldEquiv R ((Spec R).germToFunctionField ⊤ a) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso R).hom a) := by
  rw [affine_germToFunctionField_top]
  exact (affineFunctionFieldEquiv R).commutes _

/-- The function field of an irreducible scheme with this actual open
affine chart is the fraction field of its actual coordinate ring. -/
def affineOpenFunctionFieldEquiv (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    Y.functionField ≃+* FractionRing R :=
  (openImmersionFunctionFieldEquiv j).trans
    (affineFunctionFieldEquiv R).toRingEquiv

@[simp] theorem affineOpenFunctionFieldEquiv_germ_top
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (a : Γ(Y,⊤)) :
    affineOpenFunctionFieldEquiv R j (Y.germToFunctionField ⊤ a) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso R).hom (j.appTop a)) := by
  change affineFunctionFieldEquiv R
    (openImmersionFunctionFieldEquiv j (Y.germToFunctionField ⊤ a)) = _
  letI : Nonempty (j ⁻¹ᵁ (⊤ : Y.Opens)) := openImmersion_preimage_nonempty j ⊤
  rw [openImmersionFunctionFieldEquiv_germ]
  exact affineFunctionFieldEquiv_germ_top R (j.appTop a)

/-- Surjectivity is part of the constructed ring equivalence; in
particular every fraction arises from an actual rational function. -/
theorem affineOpenFunctionFieldEquiv_surjective
    (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    Function.Surjective (affineOpenFunctionFieldEquiv R j) :=
  (affineOpenFunctionFieldEquiv R j).surjective

/-- The actual coordinate-ring embedding of an open affine chart into
the ambient function field, through regular sections and generic germs. -/
def affineOpenCoordinateMap (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    R →+* Y.functionField :=
  (openImmersionGlobalToFunctionField j).comp (Scheme.ΓSpecIso R).inv.hom

def affineOpenCoordinateAlgebra (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    Algebra R Y.functionField :=
  (affineOpenCoordinateMap R j).toAlgebra

@[simp] theorem affineOpenFunctionFieldEquiv_coordinateMap
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (r : R) :
    affineOpenFunctionFieldEquiv R j (affineOpenCoordinateMap R j r) =
      algebraMap R (FractionRing R) r := by
  change affineFunctionFieldEquiv R
      ((openImmersionFunctionFieldEquiv j)
        ((openImmersionFunctionFieldEquiv j).symm
          ((Spec R).germToFunctionField ⊤ ((Scheme.ΓSpecIso R).inv r)))) = _
  rw [RingEquiv.apply_symm_apply, affineFunctionFieldEquiv_germ_top]
  simp

/-- The function-field equivalence respects the actual chart coordinate
map, hence is an algebra equivalence for that explicit algebra structure. -/
def affineOpenFunctionFieldAlgEquiv (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    letI := affineOpenCoordinateAlgebra R j
    Y.functionField ≃ₐ[R] FractionRing R := by
  letI := affineOpenCoordinateAlgebra R j
  exact
    { affineOpenFunctionFieldEquiv R j with
      commutes' := affineOpenFunctionFieldEquiv_coordinateMap R j }

/-- The ambient function field is a fraction ring of an actual affine
chart, with precisely the regular-section/generic-stalk coordinate map.
This explicit structure can be used directly in Kähler localization. -/
theorem affineOpenCoordinate_isFractionRing
    (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    letI := affineOpenCoordinateAlgebra R j
    IsFractionRing R Y.functionField := by
  letI := affineOpenCoordinateAlgebra R j
  exact IsLocalization.isLocalization_of_algEquiv R⁰
    (affineOpenFunctionFieldAlgEquiv R j).symm

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.openImmersionFunctionFieldIso
#print axioms PaperVerification.ToricSchemes.openImmersionFunctionFieldIso_germ
#print axioms PaperVerification.ToricSchemes.affineOpenFunctionFieldEquiv
end
-- END PaperVerification.ToricFunctionFieldBridge
end

section
-- BEGIN PaperVerification.ToricInvertibleRestriction



/-!
# Restriction of actual rank-one sheaves

An open immersion transports actual local frames through its actual
isomorphisms on sections. The proof constructs the linear maps on every
smaller open and checks their restriction compatibility.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} (hM : IsInvertibleModule M)

theorem invertibleFrameCoordinates_restrict (x : X)
    {U V : X.Opens} (i : V ⟶ U)
    (hU : U≤ invertibleOpen hM x) (hV : V≤ invertibleOpen hM x)
    (s : Γ(M,U)) :
    invertibleFrameCoordinates hM x V hV (M.presheaf.map i.op s) =
      X.presheaf.map i.op (invertibleFrameCoordinates hM x U hU s) := by
  let f : Over.mk (homOfLE hV) ⟶ Over.mk (homOfLE hU) :=
    Over.homMk i (by subsingleton)
  exact PresheafOfModules.naturality_apply (invertibleFrame hM x).hom.val f.op s

/-- Local frame coordinates transported along the actual section
isomorphism of an open immersion. -/
def restrictFrameCoordinates (x : X) (U : Y.Opens)
    (hU : j ''ᵁ U≤ invertibleOpen hM x) :
    Γ(M.restrict j,U) ≃ₗ[Γ(Y,U)] Γ(Y,U) := by
  let eM := (M.restrictAppIso j U).addCommGroupIsoToAddEquiv
  let eX := invertibleFrameCoordinates hM x (j ''ᵁ U) hU
  let eR := (j.appIso U).commRingCatIsoToRingEquiv
  refine
    { toFun := fun s=>eR (eX (eM s))
      invFun := fun a=>eM.symm (eX.symm (eR.symm a))
      left_inv := by intro s; simp
      right_inv := by intro a; simp
      map_add' := by intro s t; simp
      map_smul' := ?_ }
  intro a s
  change eR (eX (eR.symm a • eM s)) = a * eR (eX (eM s))
  rw [eX.map_smul]
  change eR (eR.symm a * eX (eM s)) = _
  rw [map_mul,RingEquiv.apply_symm_apply]

theorem restrictFrameCoordinates_restrict (x : X)
    {U V : Y.Opens} (i : V ⟶ U)
    (hU : j ''ᵁ U≤ invertibleOpen hM x)
    (hV : j ''ᵁ V≤ invertibleOpen hM x) (s : Γ(M.restrict j,U)) :
    restrictFrameCoordinates j hM x V hV ((M.restrict j).presheaf.map i.op s) =
      Y.presheaf.map i.op (restrictFrameCoordinates j hM x U hU s) := by
  let i' : j ''ᵁ V ⟶ j ''ᵁ U := homOfLE (j.image_mono i.le)
  let t : Γ(M,j ''ᵁ U) := (M.restrictAppIso j U).hom s
  change (j.appIso V).hom
      (invertibleFrameCoordinates hM x (j ''ᵁ V) hV (M.presheaf.map i'.op t)) =
    Y.presheaf.map i.op ((j.appIso U).hom
      (invertibleFrameCoordinates hM x (j ''ᵁ U) hU t))
  have hn : X.presheaf.map i'.op ≫ (j.appIso V).hom =
      (j.appIso U).hom ≫ Y.presheaf.map i.op := by
    simp [Scheme.Hom.appIso_hom']
  calc
    _ = (j.appIso V).hom (X.presheaf.map i'.op
        (invertibleFrameCoordinates hM x (j ''ᵁ U) hU t)) :=
      congrArg (fun a : Γ(X,j ''ᵁ V) => (j.appIso V).hom a)
        (invertibleFrameCoordinates_restrict hM x i' hU hV t)
    _ = _ := congrArg (fun f : Γ(X,j ''ᵁ U) ⟶ Γ(Y,V) =>
      f (invertibleFrameCoordinates hM x (j ''ᵁ U) hU t)) hn

include hM in
/-- Restriction along an actual open immersion preserves local rank one. -/
theorem isInvertibleModule_restrict : IsInvertibleModule (M.restrict j) := by
  intro y
  let U : Y.Opens := j ⁻¹ᵁ invertibleOpen hM (j y)
  have hy : y∈U := mem_invertibleOpen hM (j y)
  refine ⟨U,hy,⟨?_⟩⟩
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun V=>?_) ?_
  · have hV : j ''ᵁ V.unop.left≤ invertibleOpen hM (j y) := by
      rintro z ⟨v,hv,rfl⟩
      exact V.unop.hom.le hv
    exact (restrictFrameCoordinates j hM (j y) V.unop.left hV).toModuleIso
  · intro V W f
    ext s
    exact restrictFrameCoordinates_restrict j hM (j y) f.unop.left _ _ s

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isInvertibleModule_restrict
end
-- END PaperVerification.ToricInvertibleRestriction
end

section
-- BEGIN PaperVerification.ToricCharacterMultiplication



/-!
# Multiplication of genuine Laurent-character submodules

For an arbitrary exponent set S, the module V(S) consists of the elements
of the actual additive monoid algebra whose finite support is contained
in S. The tensor-product multiplication map has image exactly V(S+T).
This algebraic statement imposes no finiteness on the exponent sets and
does not assume an identification with global sections of a line bundle.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped Pointwise TensorProduct

variable (k : Type*) [CommSemiring k]
variable {M : Type*} [AddCommMonoid M]

/-- The ordinary submodule of the monoid algebra with support in S. -/
abbrev characterModule (S : Set M) : Submodule k (AddMonoidAlgebra k M) :=
  AddMonoidAlgebra.supported k k S

theorem mem_characterModule_iff (S : Set M) (f : AddMonoidAlgebra k M) :
    f ∈ characterModule k S ↔ (f.coeff.support : Set M) ⊆ S :=
  AddMonoidAlgebra.mem_supported

theorem characterModule_eq_span (S : Set M) :
    characterModule k S = Submodule.span k ((fun m : M => single m (1 : k)) '' S) :=
  AddMonoidAlgebra.supported_eq_span_single k S

theorem characterModule_mono {S T : Set M} (h : S ⊆ T) :
    characterModule k S ≤ characterModule k T :=
  AddMonoidAlgebra.supported_mono h

theorem single_mem_characterModule [Nontrivial k] (S : Set M) (m : M) :
    single m (1 : k) ∈ characterModule k S ↔ m ∈ S := by
  rw [characterModule_eq_span]
  exact AddMonoidAlgebra.single_mem_span_single

/-- Multiplication on the actual monoid algebra, restricted on its two
tensor factors but initially retaining the full algebra as codomain. -/
def characterMultiplicationAmbient (S T : Set M) :
    characterModule k S ⊗[k] characterModule k T →ₗ[k] AddMonoidAlgebra k M :=
  (LinearMap.mul' k (AddMonoidAlgebra k M)).comp
    (TensorProduct.mapIncl (characterModule k S) (characterModule k T))

@[simp] theorem characterMultiplicationAmbient_tmul (S T : Set M)
    (f : characterModule k S) (g : characterModule k T) :
    characterMultiplicationAmbient k S T (f ⊗ₜ[k] g) =
      (f : AddMonoidAlgebra k M) * (g : AddMonoidAlgebra k M) := rfl

theorem character_product_set (S T : Set M) :
    Set.image2 (fun f g : AddMonoidAlgebra k M => f * g)
      ((fun m : M => single m (1 : k)) '' S)
      ((fun m : M => single m (1 : k)) '' T) =
        (fun m : M => single m (1 : k)) '' (S + T) := by
  ext f
  constructor
  · rintro ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y, Set.add_mem_add hx hy, by simp⟩
  · rintro ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨single x 1, ⟨x, hx, rfl⟩,
      single y 1, ⟨y, hy, rfl⟩, by simp⟩

/-- The image is exactly the span of all products of the original
characters; cancellation of coefficients introduces no new exponents. -/
theorem range_characterMultiplicationAmbient (S T : Set M) :
    LinearMap.range (characterMultiplicationAmbient k S T) =
      characterModule k (S + T) := by
  change LinearMap.range (TensorProduct.lift (LinearMap.mul k (AddMonoidAlgebra k M)) ∘ₗ
    TensorProduct.mapIncl (characterModule k S) (characterModule k T)) = _
  rw [← TensorProduct.map₂_eq_range_lift_comp_mapIncl]
  rw [characterModule_eq_span, characterModule_eq_span,
    Submodule.map₂_span_span, characterModule_eq_span]
  congr 1
  exact character_product_set k S T

/-- Multiplication with codomain restricted to any genuine support
module containing the pointwise sum of the two exponent sets. -/
def characterMultiplication (S T U : Set M) (hST : S + T ⊆ U) :
    characterModule k S ⊗[k] characterModule k T →ₗ[k] characterModule k U :=
  (characterMultiplicationAmbient k S T).codRestrict (characterModule k U) (by
    intro x
    apply characterModule_mono k hST
    rw [← range_characterMultiplicationAmbient k S T]
    exact ⟨x, rfl⟩)

@[simp] theorem characterMultiplication_coe (S T U : Set M) (hST : S + T ⊆ U)
    (x : characterModule k S ⊗[k] characterModule k T) :
    ((characterMultiplication k S T U hST x : characterModule k U) :
      AddMonoidAlgebra k M) = characterMultiplicationAmbient k S T x := rfl

@[simp] theorem characterMultiplication_tmul (S T U : Set M) (hST : S + T ⊆ U)
    (f : characterModule k S) (g : characterModule k T) :
    ((characterMultiplication k S T U hST (f ⊗ₜ[k] g) : characterModule k U) :
      AddMonoidAlgebra k M) = (f : AddMonoidAlgebra k M) * g := rfl

theorem range_characterMultiplication (S T U : Set M) (hST : S + T ⊆ U) :
    LinearMap.range (characterMultiplication k S T U hST) =
      (characterModule k (S + T)).comap (characterModule k U).subtype := by
  rw [characterMultiplication, LinearMap.range_codRestrict,
    range_characterMultiplicationAmbient]

/-- Surjectivity is exactly the full lattice-point sum assertion. The
nonzero coefficient hypothesis is necessary to recover an exponent from
its character; it holds over every field, in every characteristic. -/
theorem characterMultiplication_surjective_iff [Nontrivial k]
    (S T U : Set M) (hST : S + T ⊆ U) :
    Function.Surjective (characterMultiplication k S T U hST) ↔ U = S + T := by
  constructor
  · intro hsurj
    apply Set.Subset.antisymm _ hST
    intro m hm
    let χ : characterModule k U :=
      ⟨single m (1 : k), (single_mem_characterModule k U m).mpr hm⟩
    obtain ⟨x, hx⟩ := hsurj χ
    have hχ : single m (1 : k) ∈ LinearMap.range
        (characterMultiplicationAmbient k S T) := by
      refine ⟨x, ?_⟩
      exact congrArg (fun y : characterModule k U => (y : AddMonoidAlgebra k M)) hx
    rw [range_characterMultiplicationAmbient] at hχ
    exact (single_mem_characterModule k (S + T) m).mp hχ
  · intro hU f
    have hf : (f : AddMonoidAlgebra k M) ∈ characterModule k (S + T) := by
      rw [← hU]
      exact f.property
    rw [← range_characterMultiplicationAmbient k S T] at hf
    obtain ⟨x, hx⟩ := hf
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.range_characterMultiplicationAmbient
#print axioms PaperVerification.ToricCharacters.characterMultiplication_surjective_iff
end
-- END PaperVerification.ToricCharacterMultiplication
end

section
-- BEGIN PaperVerification.ToricCharacterSubrepresentations



/-!
# Character bases of algebraic torus subrepresentations

Stability here is under the actual coalgebra comultiplication, with values
in the tensor product containing the submodule. It is not stability under
the action of rational points. Thus the argument works over finite fields
as well. Taking one coefficient in the first tensor factor isolates one
character in the second; this proves the character basis assertion.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct

variable (k : Type*) [Field k]
variable {M : Type*} [AddCommGroup M]

/-- Extract the coefficient of one character from the first tensor
factor, retaining the actual second module. -/
def characterCoefficient {V : Type*} [AddCommGroup V] [Module k V] (m : M) :
    AddMonoidAlgebra k M ⊗[k] V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap.comp
    (((AddMonoidAlgebra.basis M k).coord m).rTensor V)

@[simp] theorem characterCoefficient_tmul {V : Type*}
    [AddCommGroup V] [Module k V]
    (m : M) (f : AddMonoidAlgebra k M) (v : V) :
    characterCoefficient k m (f ⊗ₜ[k] v) = f.coeff m • v := by
  simp only [characterCoefficient, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul]
  rfl

/-- Comultiplication followed by one coefficient projection is exactly
the corresponding individual character term. -/
theorem characterCoefficient_comul (m : M) (f : AddMonoidAlgebra k M) :
    characterCoefficient k m (Coalgebra.comul (R := k) f) = single m (f.coeff m) := by
  have h : (characterCoefficient k m).comp
        (Coalgebra.comul (R := k) (A := AddMonoidAlgebra k M)) =
      (AddMonoidAlgebra.lsingle (R := k) m).comp
        ((AddMonoidAlgebra.basis M k).coord m) := by
    apply (AddMonoidAlgebra.basis M k).ext
    intro i
    change characterCoefficient k m
        (Coalgebra.comul (R := k) (AddMonoidAlgebra.single i (1 : k))) =
      AddMonoidAlgebra.single m ((AddMonoidAlgebra.single i (1 : k)).coeff m)
    by_cases hi : i = m
    · subst i
      simp [AddMonoidAlgebra.comul_single]
    · simp [AddMonoidAlgebra.comul_single, hi, Ne.symm hi]
  exact congrArg (fun g => g f) h

/-- Algebraic stability of a Laurent-polynomial submodule under the
split torus: the genuine coaction factors through `k[M] ⊗ S`. -/
def IsCharacterStable (S : Submodule k (AddMonoidAlgebra k M)) : Prop :=
  ∀ f ∈ S, Coalgebra.comul (R := k) f ∈ LinearMap.range
    (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
      S.subtype)

theorem characterCoefficient_map_subtype
    (S : Submodule k (AddMonoidAlgebra k M)) (m : M)
    (z : AddMonoidAlgebra k M ⊗[k] S) :
    characterCoefficient k m
      (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
        S.subtype z) ∈ S := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simpa only [TensorProduct.map_tmul, LinearMap.id_apply,
        Submodule.subtype_apply, characterCoefficient_tmul] using
        S.smul_mem (f.coeff m) g.property
  | add z w hz hw => simpa only [map_add] using S.add_mem hz hw

/-- Algebraic coaction stability is equivalent to closure under the
literal Laurent character components. The reverse implication builds
the required tensor preimage from the finite support of the element. -/
theorem isCharacterStable_iff_components
    (S : Submodule k (AddMonoidAlgebra k M)) :
    IsCharacterStable k S ↔
      ∀ f∈S,∀ m : M,single m (f.coeff m)∈S := by
  constructor
  · intro hS f hf m
    obtain ⟨z,hz⟩ := hS f hf
    have h := characterCoefficient_map_subtype k S m z
    rw [hz,characterCoefficient_comul] at h
    exact h
  · intro hS f hf
    classical
    let z : AddMonoidAlgebra k M ⊗[k] S :=
      ∑ m∈f.coeff.support,
        (single m 1) ⊗ₜ[k] (⟨single m (f.coeff m),hS f hf m⟩ : S)
    refine ⟨z,?_⟩
    have hsum : (∑ m∈f.coeff.support,single m (f.coeff m))=f :=
      AddMonoidAlgebra.sum_coeff_single f
    conv_rhs => rw [← hsum]
    simp only [z,map_sum,TensorProduct.map_tmul,LinearMap.id_apply,
      Submodule.subtype_apply,AddMonoidAlgebra.comul_single,
      CommSemiring.comul_apply,AddMonoidAlgebra.lsingle_apply]

/-- Each nonzero coefficient of a stable element supplies its entire
one-dimensional character line in the same submodule. -/
theorem single_mem_of_stable (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) (f : AddMonoidAlgebra k M) (hf : f ∈ S)
    (m : M) (hm : f.coeff m ≠ 0) : single m (1 : k) ∈ S := by
  obtain ⟨z, hz⟩ := hS f hf
  have hterm := characterCoefficient_map_subtype k S m z
  rw [hz, characterCoefficient_comul] at hterm
  have hmul := S.smul_mem (f.coeff m)⁻¹ hterm
  simpa only [smul_single, smul_eq_mul, inv_mul_cancel₀ hm] using hmul

/-- The exponent set of the characters actually contained in the
submodule, without a chosen spanning family or a weight decomposition. -/
def characterExponents (S : Submodule k (AddMonoidAlgebra k M)) : Set M :=
  {m | single m (1 : k) ∈ S}

/-- A subrepresentation of the regular representation of a split torus
has precisely its contained characters as a basis. This equality first
states the spanning assertion at the level of actual submodules. -/
theorem stable_eq_characterModule (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) :
    S = characterModule k (characterExponents k S) := by
  apply le_antisymm
  · intro f hf
    rw [mem_characterModule_iff]
    intro m hm
    exact single_mem_of_stable k S hS f hf m
      (Finsupp.mem_support_iff.mp hm)
  · rw [characterModule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact hm

/-- The actual coordinate equivalence of a stable module with finitely
supported functions on its character exponents. -/
def stableCharacterCoordinates (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) : S ≃ₗ[k] characterExponents k S →₀ k :=
  (LinearEquiv.ofEq S (characterModule k (characterExponents k S))
    (stable_eq_characterModule k S hS)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
        (characterExponents k S))

def stableCharacterBasis (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) :
    Module.Basis (characterExponents k S) k S where
  repr := stableCharacterCoordinates k S hS

/-- Finite-dimensionality supplies a finite exponent set, with no
assumption on the cardinality or characteristic of the ground field. -/
theorem finite_characterExponents
    (S : Submodule k (AddMonoidAlgebra k M)) [FiniteDimensional k S]
    (hS : IsCharacterStable k S) : (characterExponents k S).Finite := by
  letI := FiniteDimensional.fintypeBasisIndex (stableCharacterBasis k S hS)
  exact Set.toFinite _

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.stable_eq_characterModule
#print axioms PaperVerification.ToricCharacters.finite_characterExponents
end
-- END PaperVerification.ToricCharacterSubrepresentations
end

#eval "TORIC_DICTIONARY_PART_02_EOF"
