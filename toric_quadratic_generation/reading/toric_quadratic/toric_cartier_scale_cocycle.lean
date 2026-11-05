module

public import PaperVerification.ToricCartierDescent

@[expose] public section

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
