module

public import ToricPower.AffineSplitting
public import ToricPower.SchemeAffineLinear

/-!
# Actual affine coefficient maps and the scheme adjunction

The module map `r ↦ φ(r)b`, sheafified by the actual tilde functor and
identified with the actual direct image, is the adjunct of multiplication
by the actual global section corresponding to `b`. This verifies the
normalization of the affine direct-image comparison used in the diagonal
augmentation, including its scalar action.

Candidate source pending compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

universe u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- A literal coefficient in the affine target ring gives the actual
base-linear map to that ring with scalars restricted along `φ`. -/
def affineCoefficientHom (b : S) : ModuleCat.of R R ⟶ affineRestrictedRing φ :=
  ModuleCat.ofHom (X := ModuleCat.of R R) (Y := affineRestrictedRing φ)
    { toFun := fun r => φ r * b
      map_add' := fun r t => by simp only [map_add, add_mul]
      map_smul' := fun r t => by
        change φ (r * t) * b = φ r * (φ t * b)
        rw [map_mul, mul_assoc] }

@[simp]
theorem affineCoefficientHom_apply (b : S) (r : R) :
    affineCoefficientHom φ b r = φ r * b := rfl

/-- The actual sheaf morphism obtained from the displayed coefficient
module map and the actual affine direct-image isomorphism. -/
def affineCoefficientSheafMap (b : S) :
    SheafOfModules.unit (Spec R).ringCatSheaf ⟶
      (Scheme.Modules.pushforward (Spec.map φ)).obj
        (SheafOfModules.unit (Spec S).ringCatSheaf) :=
  (tildeSelf (R := R)).inv ≫ tilde.map (affineCoefficientHom φ b) ≫
    (affinePushforwardStructureIso φ).inv

/-- The affine direct-image comparison has exactly the global-sections
adjunct dictated by its actual descent construction. -/
theorem affinePushforwardTildeIso_inv_homEquiv (M : ModuleCat.{u} S) :
    (tilde.adjunction (R := R)).homEquiv _ _
        (affinePushforwardTildeIso φ M).inv =
      (ModuleCat.restrictScalars φ.hom).map (tilde.isoTop M).hom ≫
        (affinePushforwardSectionsIso φ).inv.app (tilde M) := by
  let e := (affinePushforwardSectionsIso φ).app (tilde M) ≪≫
    (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop M).symm
  change (tilde.adjunction (R := R)).homEquiv _ _
      (tilde.map e.inv ≫
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)).fromTildeΓ) = e.inv
  have counit := (tilde.adjunction (R := R)).homEquiv_counit (g := e.inv)
  exact (congrArg ((tilde.adjunction (R := R)).homEquiv _ _) counit.symm).trans
    (Equiv.apply_symm_apply _ e.inv)

/-- In particular, the coefficient `b` becomes the literal affine global
function `(ΓSpecIso S).inv b` in the actual direct image of the unit sheaf. -/
theorem affinePushforwardStructureIso_inv_homEquiv_apply (b : S) :
    ((tilde.adjunction (R := R)).homEquiv _ _
      (affinePushforwardStructureIso φ).inv) b = (Scheme.ΓSpecIso S).inv b := by
  have h := congrArg (fun f => f b)
    (affinePushforwardTildeIso_inv_homEquiv φ (ModuleCat.of S S))
  have maps : (Scheme.Modules.pushforward (Spec.map φ)).map
      (tildeSelf (R := S)).hom = 𝟙 _ :=
    (Scheme.Modules.pushforward (Spec.map φ)).map_id _
  have comparison : (affinePushforwardStructureIso φ).inv =
      (affinePushforwardTildeIso φ (ModuleCat.of S S)).inv := by
    change (affinePushforwardTildeIso φ (ModuleCat.of S S)).inv ≫
      (Scheme.Modules.pushforward (Spec.map φ)).map (tildeSelf (R := S)).hom = _
    rw [maps, Category.comp_id]
  rw [comparison]
  exact h.trans rfl

/-- The sheafified literal coefficient is the actual adjunct of
multiplication by that coefficient on the affine source. -/
theorem affineCoefficientSheafMap_eq_adjunct (b : S) :
    affineCoefficientSheafMap φ b =
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _
        ((Scheme.Modules.pullbackObjUnitIso (Spec.map φ)).hom ≫
          Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec S).ringCatSheaf)
            ((Scheme.ΓSpecIso S).inv b)) := by
  rw [Adjunction.homEquiv_naturality_right,
    Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
  apply ((tilde.adjunction (R := R)).homEquiv (ModuleCat.of R R) _).injective
  change (tilde.adjunction (R := R)).homEquiv _ _
      (tilde.map (affineCoefficientHom φ b) ≫ (affinePushforwardStructureIso φ).inv) = _
  have natural := (tilde.adjunction (R := R)).homEquiv_naturality_left
    (affineCoefficientHom φ b) (affinePushforwardStructureIso φ).inv
  refine natural.trans ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  rw [ConcreteCategory.comp_apply,affineCoefficientHom_apply,
    affinePushforwardStructureIso_inv_homEquiv_apply]
  change (Scheme.ΓSpecIso S).inv (φ r * b) =
    (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec S).ringCatSheaf)
      ((Scheme.ΓSpecIso S).inv b)).app ((Spec.map φ) ⁻¹ᵁ ⊤)
        ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r))
  rw [Scheme.Modules.globalSectionsSmul_app]
  change (Scheme.ΓSpecIso S).inv (φ r * b) =
    (Spec S).presheaf.map (𝟙 (⊤ : (Spec S).Opens)).op
      ((Scheme.ΓSpecIso S).inv b) * (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)
  rw [CategoryTheory.op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  rw [map_mul]
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) r
  change (Scheme.ΓSpecIso S).inv (φ r) =
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) at h
  rw [← h,mul_comm]

end ToricPower
