module

public import ToricPower.TensorInverseMates
public import ToricPower.CartierExtSourceNaturality
public import ToricPower.DivisorWeightTensorNaturality

/-!
# Rational multiplication and the actual Cartier evaluation pairing

If a map between Cartier sheaves and the reverse map between their
inverse sheaves multiply rational sections by the same rational function,
they preserve the actual tensor evaluation pairing. Consequently the
second map is the conjugate map of the exact tensor adjunctions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

namespace ToricPower

universe u
variable {X : Scheme.{u}} [IsIntegral X]

/-- Undoing the structure-sheaf identification leaves the genuine
Cartier multiplication and transport to the zero divisor. -/
theorem cartierTensorNegIsoUnit_comp_zero (D : CartierDivisor X) :
    (cartierTensorNegIsoUnit D).hom ≫ (unitIsoSheafZero X).hom =
      (tensorSheafIso D (-D)).hom ≫
        (eqToIso (congrArg (fun E : CartierDivisor X => E.sheaf)
          (add_neg_cancel D))).hom := by
  simp only [cartierTensorNegIsoUnit, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual evaluation pairing is rational multiplication on every
inserted pure tensor of sections. -/
theorem cartierTensorNegIsoUnit_rationalValue (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf, U)) (t : Γ((-D).sheaf, U)) :
    rationalFunctionsEquiv U
      (Scheme.Modules.Hom.app (0 : CartierDivisor X).sheafι U
        (Scheme.Modules.Hom.app
          ((cartierTensorNegIsoUnit D).hom ≫ (unitIsoSheafZero X).hom) U
          (schemeTensorSection D.sheaf (-D).sheaf U s t))) =
      rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U s) *
        rationalFunctionsEquiv U (Scheme.Modules.Hom.app (-D).sheafι U t) := by
  rw [cartierTensorNegIsoUnit_comp_zero, schemeHom_comp_apply,
    cartierEqToIso_value (add_neg_cancel D)]
  exact cartierTensorSheafIso_value D (-D) U s t

/-- Equal rational multipliers commute with the actual evaluation
pairings. The equality includes all tensor and zero-divisor transports. -/
theorem cartierPairing_of_rationalMultiplier
    {D E : CartierDivisor X} (f : D.sheaf ⟶ E.sheaf)
    (g : (-E).sheaf ⟶ (-D).sheaf) (r : X.functionField)
    (hf : ∀ (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf, U)),
      rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app E.sheafι U (Scheme.Modules.Hom.app f U s)) =
      r * rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U s))
    (hg : ∀ (U : X.Opens) [Nonempty U] (t : Γ((-E).sheaf, U)),
      rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app (-D).sheafι U (Scheme.Modules.Hom.app g U t)) =
      r * rationalFunctionsEquiv U (Scheme.Modules.Hom.app (-E).sheafι U t)) :
    D.sheaf ◁ g ≫ (cartierTensorNegIsoUnit D).hom =
      f ▷ (-E).sheaf ≫ (cartierTensorNegIsoUnit E).hom := by
  apply (cancel_mono (unitIsoSheafZero X).hom).mp
  apply cartierTensorHom_ext_nonempty (0 : CartierDivisor X)
  intro U hU s t
  have leftTensor :
      Scheme.Modules.Hom.app (D.sheaf ◁ g) U
        (schemeTensorSection D.sheaf (-E).sheaf U s t) =
      schemeTensorSection D.sheaf (-D).sheaf U s (Scheme.Modules.Hom.app g U t) := by
    simpa only [id_tensorHom, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using
      schemeTensorSection_naturality (𝟙 D.sheaf) g U s t
  have rightTensor :
      Scheme.Modules.Hom.app (f ▷ (-E).sheaf) U
        (schemeTensorSection D.sheaf (-E).sheaf U s t) =
      schemeTensorSection E.sheaf (-E).sheaf U (Scheme.Modules.Hom.app f U s) t := by
    simpa only [tensorHom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using
      schemeTensorSection_naturality f (𝟙 (-E).sheaf) U s t
  have leftSection :=
    (schemeHom_comp_apply (D.sheaf ◁ g)
      ((cartierTensorNegIsoUnit D).hom ≫ (unitIsoSheafZero X).hom) U
      (schemeTensorSection D.sheaf (-E).sheaf U s t)).trans
      (congrArg (fun z => Scheme.Modules.Hom.app
        ((cartierTensorNegIsoUnit D).hom ≫ (unitIsoSheafZero X).hom) U z) leftTensor)
  have rightSection :=
    (schemeHom_comp_apply (f ▷ (-E).sheaf)
      ((cartierTensorNegIsoUnit E).hom ≫ (unitIsoSheafZero X).hom) U
      (schemeTensorSection D.sheaf (-E).sheaf U s t)).trans
      (congrArg (fun z => Scheme.Modules.Hom.app
        ((cartierTensorNegIsoUnit E).hom ≫ (unitIsoSheafZero X).hom) U z) rightTensor)
  let value := fun z => rationalFunctionsEquiv U
    (Scheme.Modules.Hom.app (0 : CartierDivisor X).sheafι U z)
  have leftValue := (congrArg value leftSection).trans
    (cartierTensorNegIsoUnit_rationalValue D U s (Scheme.Modules.Hom.app g U t))
  have rightValue := (congrArg value rightSection).trans
    (cartierTensorNegIsoUnit_rationalValue E U (Scheme.Modules.Hom.app f U s) t)
  have products :
      rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U s) *
          rationalFunctionsEquiv U
            (Scheme.Modules.Hom.app (-D).sheafι U (Scheme.Modules.Hom.app g U t)) =
        rationalFunctionsEquiv U
            (Scheme.Modules.Hom.app E.sheafι U (Scheme.Modules.Hom.app f U s)) *
          rationalFunctionsEquiv U (Scheme.Modules.Hom.app (-E).sheafι U t) := by
    calc
      _ = rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U s) *
          (r * rationalFunctionsEquiv U (Scheme.Modules.Hom.app (-E).sheafι U t)) :=
        congrArg (fun z => rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U s) * z)
          (hg U t)
      _ = (r * rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U s)) *
          rationalFunctionsEquiv U (Scheme.Modules.Hom.app (-E).sheafι U t) := by ring
      _ = _ := congrArg
        (fun z => z * rationalFunctionsEquiv U (Scheme.Modules.Hom.app (-E).sheafι U t))
          (hf U s).symm
  exact leftValue.trans (products.trans rightValue.symm)

/-- Equal actual rational multipliers identify the dual-twist map on
every coefficient sheaf with tensoring the actual reverse map. -/
theorem cartierDualTwistMap_eq_of_rationalMultiplier
    {D E : CartierDivisor X} (f : D.sheaf ⟶ E.sheaf)
    (g : (-E).sheaf ⟶ (-D).sheaf) (r : X.functionField)
    (hf : ∀ (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf, U)),
      rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app E.sheafι U (Scheme.Modules.Hom.app f U s)) =
      r * rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U s))
    (hg : ∀ (U : X.Opens) [Nonempty U] (t : Γ((-E).sheaf, U)),
      rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app (-D).sheafι U (Scheme.Modules.Hom.app g U t)) =
      r * rationalFunctionsEquiv U (Scheme.Modules.Hom.app (-E).sheafι U t)) :
    cartierDualTwistMap X f = (tensoringLeft X.Modules).map g := by
  exact tensorEquivalenceOfInverse_conjugate
    (cartierNegTensorIsoUnit E) (cartierTensorNegIsoUnit E)
    (cartierNegTensorIsoUnit D) (cartierTensorNegIsoUnit D) f g
    (cartierPairing_of_rationalMultiplier f g r hf hg)

end ToricPower
