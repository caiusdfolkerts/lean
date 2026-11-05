module

public import PaperVerification.LineExteriorSquareZero

/-!
# The actual coordinate maps of the Proj tautological line

A homogeneous coordinate of degree one multiplies a section of O(-1)
to a section of O(0), which is then identified with a regular function.
These are morphisms of sheaves, defined before any vanishing assertion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite

namespace PaperVerification.ProjTautologicalLineCoordinates

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

local instance (U : (Proj 𝒜).Opensᵒᵖ) :
    CommRing ((Proj 𝒜).ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(Proj 𝒜, U.unop))

local instance (U : (Proj 𝒜).Opensᵒᵖ) :
    CommRing ((SheafOfModules.unit (Proj 𝒜).ringCatSheaf).val.obj U) :=
  inferInstanceAs (CommRing Γ(Proj 𝒜, U.unop))

/-- Multiplication by the actual degree-one section, on the actual Proj twists. -/
def multiplyByCoordinate (a : A) (ha : a ∈ 𝒜 1) :
    Proj.twistingSheaf 𝒜 (-1) ⟶ Proj.twistingSheaf 𝒜 0 where
  val :=
    { app := fun U => by
        let M := (Proj.twistingSheaf 𝒜 (-1)).val.obj U
        let N := (Proj.twistingSheaf 𝒜 0).val.obj U
        exact ModuleCat.ofHom (X := M) (Y := N)
          ((Proj.twistingSheaf.mul 𝒜 U.unop (-1) 1).flip
            (Proj.toTwistingSheaf 𝒜 rfl U.unop ⟨a, ha⟩))
      naturality := by
        intro U V i
        ext s
        rfl }

/-- The corresponding coordinate of the tautological inclusion O(-1) → Oⁿ. -/
def coordinate (a : A) (ha : a ∈ 𝒜 1) :
    Proj.twistingSheaf 𝒜 (-1) ⟶ SheafOfModules.unit (Proj 𝒜).ringCatSheaf :=
  multiplyByCoordinate 𝒜 a ha ≫ (Proj.unitIsoTwistingSheafZero 𝒜).inv

/-- Its value in every stalk localization is the literal product with a/1. -/
theorem coordinate_value (a : A) (ha : a ∈ 𝒜 1) (U : (Proj 𝒜).Opens)
    (s : Γ(Proj.twistingSheaf 𝒜 (-1), U)) (x : U) :
    (((coordinate 𝒜 a ha).val.app (op U) s).1 x).val =
      s.1 x * Localization.mk a 1 := by
  change (((Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U).symm
    (Proj.twistingSheaf.mul 𝒜 U (-1) 1 s
      (Proj.toTwistingSheaf 𝒜 rfl U ⟨a, ha⟩))).1 x).val = _
  rw [Proj.sectionsLinearEquivTwistingSheafZero_symm_apply_val,
    Proj.twistingSheaf.mul_apply, Proj.toTwistingSheaf_apply_apply]

/-- On its own standard chart the coordinate sends the genuine line frame to one. -/
theorem coordinate_chartGenerator (a : A) (ha : a ∈ 𝒜 1)
    (U : (Proj 𝒜).Opens) (hU : U ≤ Proj.basicOpen 𝒜 a) :
    (coordinate 𝒜 a ha).val.app (op U)
      (Proj.twistingSheaf.chartGenerator (-1) a ha U hU) = 1 := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  rw [coordinate_value]
  have hpos : Localization.mk a (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
      (Proj.twistingSheaf.chartGenerator 1 a ha U hU).1 x := by
    simp [Proj.twistingSheaf.chartGenerator_apply]
    apply congrArg (Localization.mk a)
    apply Subtype.ext
    rfl
  rw [hpos]
  simpa [Proj.twistingSheaf.chartGenerator_apply, Localization.mk_mul,
    Proj.one_apply, HomogeneousLocalization.val_one] using
    Localization.mk_self
      (⟨a, fun h ↦ hU x.2 h⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)

/-- The same coordinate recovers the coefficient in the local line frame. -/
theorem coordinate_chartSectionsLinearEquiv (a : A) (ha : a ∈ 𝒜 1)
    (U : (Proj 𝒜).Opens) (hU : U ≤ Proj.basicOpen 𝒜 a) (r : Γ(Proj 𝒜, U)) :
    (coordinate 𝒜 a ha).val.app (op U)
      (Proj.twistingSheaf.chartSectionsLinearEquiv (-1) a ha U hU r) = r := by
  rw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply, map_smul,
    coordinate_chartGenerator]
  exact mul_one r

end PaperVerification.ProjTautologicalLineCoordinates
