module

public import PaperVerification.ToricCartierTensor
public import PaperVerification.ToricCartierAmple
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Cartier powers are actual tensor powers

The power of the rational local equations is identified with the
recursively formed genuine tensor power of the sheaf. The transition
between the common cover for a tensor product and the original cover
is justified by the regular-unit transition equations.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X : Scheme.{u}}

/-- Actual iterated tensor powers, with the structure sheaf in degree zero. -/
def tensorSheafPower (F : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n+1 => tensorSheaf (tensorSheafPower F n) F

def tensorSheafPowerIso {F G : X.Modules} (e : F ≅ G) :
    ∀ n, tensorSheafPower F n ≅ tensorSheafPower G n
  | 0 => Iso.refl _
  | n+1 => tensorSheafIso (tensorSheafPowerIso e n) e

variable [IsIntegral X]

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- Equal actual fractional-section predicates give the identity
isomorphism on their rational values. -/
def sectionEquivOfIff (h : ∀ U s, C.IsSection U s ↔ D.IsSection U s)
    (U : X.Opens) : Γ(C.sheaf,U) ≃ₗ[Γ(X,U)] Γ(D.sheaf,U) where
  toFun s := ⟨s.val,(h U s.val).mp s.property⟩
  invFun s := ⟨s.val,(h U s.val).mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sheafIsoOfIsSectionIff (h : ∀ U s, C.IsSection U s ↔ D.IsSection U s) :
    C.sheaf ≅ D.sheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => (C.sectionEquivOfIff D h U.unop).toModuleIso)
      (by intro U V f; ext s; rfl)

@[simp] theorem sheafIsoOfIsSectionIff_value
    (h : ∀ U s, C.IsSection U s ↔ D.IsSection U s)
    (U : X.Opens) (s : Γ(C.sheaf,U)) :
    ((C.sheafIsoOfIsSectionIff D h).hom.app U s).val = s.val := rfl

/-- A globally principal fractional sheaf is the actual rank-one
structure module. The frame coordinates supply the natural isomorphism. -/
def principalSheafIsoUnit (q : X.functionFieldˣ) :
    (principal (X := X) q).sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => ((principal (X := X) q).localCoordinates PUnit.unit U.unop le_top).toModuleIso)
      (by
        intro U V f
        ext s
        exact (principal (X := X) q).localCoordinates_restrict PUnit.unit
          f.unop le_top le_top s)

theorem pow_zero_isSection_iff (U : X.Opens) (s : Γ(rationalFunctions X,U)) :
    (C.pow 0).IsSection U s ↔ (principal (X := X) 1).IsSection U s := by
  constructor
  · intro hs i x hx
    obtain ⟨j,hj⟩ := C.covers x.val
    simpa only [pow, principal, Units.val_pow_eq_pow_val, pow_zero, Units.val_one] using hs j x hj
  · intro hs i x hx
    simpa only [pow, principal, Units.val_pow_eq_pow_val, pow_zero, Units.val_one] using
      hs PUnit.unit x trivial

/-- Passing to the common product cover preserves the power sheaf. -/
theorem pow_succ_isSection_iff (n : ℕ) (U : X.Opens)
    (s : Γ(rationalFunctions X,U)) :
    (C.pow (n+1)).IsSection U s ↔ ((C.pow n).mul C).IsSection U s := by
  constructor
  · intro hs ij x hx
    have hpow := hs ij.1 x hx.1
    have htransition := C.transition ij.1 ij.2 x.val hx.1 hx.2
    have h := (regularAtSubring X x.val).mul_mem hpow htransition
    change rationalValueAt X U x s /
      ((C.generator ij.1 : X.functionField)^n*(C.generator ij.2 : X.functionField)) ∈ _
    have he : (rationalValueAt X U x s /
        (C.generator ij.1 : X.functionField)^(n+1)) *
        ((C.generator ij.1 : X.functionField)/(C.generator ij.2 : X.functionField)) =
      rationalValueAt X U x s /
        ((C.generator ij.1 : X.functionField)^n*(C.generator ij.2 : X.functionField)) := by
      rw [pow_succ]
      field_simp [Units.ne_zero]
      <;> ring
    simpa only [pow, Units.val_pow_eq_pow_val, he] using h
  · intro hs i x hx
    have h := hs (i,i) x ⟨hx,hx⟩
    simpa only [pow, mul, Units.val_mul, Units.val_pow_eq_pow_val, pow_succ] using h

def powZeroSheafIso : (C.pow 0).sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  (C.pow 0).sheafIsoOfIsSectionIff (principal (X := X) 1) C.pow_zero_isSection_iff ≪≫
    principalSheafIsoUnit (X := X) 1

def powSuccSheafIso (n : ℕ) :
    (C.pow (n+1)).sheaf ≅ ((C.pow n).mul C).sheaf :=
  (C.pow (n+1)).sheafIsoOfIsSectionIff ((C.pow n).mul C) (C.pow_succ_isSection_iff n)

/-- Every natural Cartier power is the full ordinary tensor power of
the actual sheaf, including degree zero. -/
def tensorSheafPowerIso : ∀ n, tensorSheafPower C.sheaf n ≅ (C.pow n).sheaf := by
  intro n
  induction n with
  | zero => exact C.powZeroSheafIso.symm
  | succ n ih =>
    exact tensorSheafIso ih (Iso.refl C.sheaf) ≪≫
      (C.pow n).tensorSheafMulIso C ≪≫ (C.powSuccSheafIso n).symm

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

/-- The n-fold Cartier sum represents the genuine n-fold tensor power,
even when the initial fractional presentation uses arbitrary local frames. -/
def tensorSheafNsmulIso (n : ℕ) :
    tensorSheafPower D.sheaf n ≅ (D.nsmul n).sheaf :=
  tensorSheafPowerIso D.presentationIso n ≪≫
    D.localCocycle.tensorSheafPowerIso n

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.tensorSheafPowerIso
#print axioms PaperVerification.ToricSchemes.CartierData.tensorSheafNsmulIso
