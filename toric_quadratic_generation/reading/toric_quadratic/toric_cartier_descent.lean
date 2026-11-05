module

public import PaperVerification.ToricCartierTranslate

@[expose] public section

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
