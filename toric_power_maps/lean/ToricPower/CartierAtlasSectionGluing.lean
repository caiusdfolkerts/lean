module

public import ToricPower.CartierAtlasFrameTransitions
public import ToricPower.SheafOverlapRestriction
public import ToricPower.QuasicoherentPoleClearing

/-!
# Gluing sections as maps from an actual Cartier line bundle

Sections in local Cartier frames define a global morphism exactly when
they obey the actual frame transition functions. This is ordinary sheaf
descent, with the value in each frame retained as an explicit equation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace ToricPower

universe u v

variable {X : Scheme.{u}}

/-- A section on an open gives its compatible family on the slice site. -/
def overModuleSection (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    (M.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun V => M.presheaf.map V.unop.hom.op s) (by
      intro V W f
      change M.presheaf.map f.unop.left.op (M.presheaf.map V.unop.hom.op s) =
        M.presheaf.map W.unop.hom.op s
      rw [← CategoryTheory.Functor.map_comp_apply, ← op_comp, Over.w])

/-- The linear morphism whose value on one is the supplied section. -/
def overSectionHom (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    (SheafOfModules.unit X.ringCatSheaf).over U ⟶ M.over U :=
  (M.over U).unitHomEquiv.symm (overModuleSection M U s)

@[simp]
theorem overSectionHom_apply (M : X.Modules) (U : X.Opens) (s : Γ(M, U))
    (V : (Over U)ᵒᵖ) (a : Γ(X, V.unop.left)) :
    (overSectionHom M U s).val.app V a = a • M.presheaf.map V.unop.hom.op s := rfl

@[simp]
theorem overSectionHom_one (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    (overSectionHom M U s).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)) = s := by
  rw [overSectionHom_apply, one_smul]
  change M.presheaf.map (𝟙 (op U)) s = s
  exact ConcreteCategory.congr_hom (M.presheaf.map_id (op U)) s

theorem restrictOverHom_comp {M N P : X.Modules} {U W : X.Opens}
    (included : W ≤ U) (f : M.over U ⟶ N.over U) (g : N.over U ⟶ P.over U) :
    restrictOverHom X.ringCatSheaf (homOfLE included) (f ≫ g) =
      restrictOverHom X.ringCatSheaf (homOfLE included) f ≫
        restrictOverHom X.ringCatSheaf (homOfLE included) g := by
  simp [restrictOverHom, Category.assoc]

theorem restrictOverHom_section (M : X.Modules) {U W : X.Opens}
    (included : W ≤ U) (s : Γ(M, U)) :
    restrictOverHom X.ringCatSheaf (homOfLE included) (overSectionHom M U s) =
      overSectionHom M W (PoleClearing.restrict M included s) := by
  apply overUnitHom_ext_top
  rw [restrictOverHom_app, overSectionHom_apply, overSectionHom_one, one_smul]
  rfl

namespace CartierEquationAtlas

variable [IsIntegral X] (atlas : CartierEquationAtlas.{u,v} X)
  (M : X.Modules) (sections : ∀ j, Γ(M, atlas.chart j))

/-- A prescribed image of the Cartier generator gives the actual local map. -/
def localSectionMap (j : atlas.Index) :
    atlas.cartierDivisor.sheaf.over (atlas.chart j) ⟶ M.over (atlas.chart j) :=
  (atlas.chartTrivialization j).inv ≫ overSectionHom M (atlas.chart j) (sections j)

theorem localSectionMap_restrict (j : atlas.Index) (W : X.Opens)
    (included : W ≤ atlas.chart j) :
    restrictOverHom X.ringCatSheaf (homOfLE included)
        (atlas.localSectionMap M sections j) =
      (atlas.frameOn j W included).inv ≫
        overSectionHom M W (PoleClearing.restrict M included (sections j)) := by
  rw [localSectionMap, restrictOverHom_comp, restrictOverHom_section]
  rfl

variable (transition : ∀ j k, Γ(X, atlas.chart j ⊓ atlas.chart k)ˣ)
  (ratio : ∀ j k,
    letI := atlas.nonempty_chart j
    letI := atlas.nonempty_chart k
    letI := nonempty_integral_open_intersection (atlas.chart j) (atlas.chart k)
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField X
      (atlas.chart j ⊓ atlas.chart k) (transition j k) * atlas.equation j =
        atlas.equation k)
  (compatible : ∀ j k,
    PoleClearing.restrict M (inf_le_left : atlas.chart j ⊓ atlas.chart k ≤ atlas.chart j)
        (sections j) =
      (transition j k : Γ(X, atlas.chart j ⊓ atlas.chart k)) •
        PoleClearing.restrict M
          (inf_le_right : atlas.chart j ⊓ atlas.chart k ≤ atlas.chart k) (sections k))

include transition ratio compatible in
theorem localSectionMap_compatible :
    SheafModuleGluing.Compatible atlas.chart (atlas.localSectionMap M sections) := by
  apply SheafModuleGluing.compatible_of_overlap_restrictions
  intro j k
  letI := atlas.nonempty_chart j
  letI := atlas.nonempty_chart k
  letI := nonempty_integral_open_intersection (atlas.chart j) (atlas.chart k)
  rw [atlas.localSectionMap_restrict, atlas.localSectionMap_restrict]
  apply (cancel_epi (atlas.frameOn j (atlas.chart j ⊓ atlas.chart k) inf_le_left).hom).mp
  rw [Iso.hom_inv_id_assoc,
    atlas.frameOn_transition j k _ inf_le_left inf_le_right (transition j k) (ratio j k)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply overUnitHom_ext_top
  change (overSectionHom M _ _).val.app (op (Over.mk (𝟙 _))) (1 : Γ(X, _)) =
    (overSectionHom M _ _).val.app (op (Over.mk (𝟙 _)))
      ((overScalarHom _ _).val.app (op (Over.mk (𝟙 _))) (1 : Γ(X, _)))
  rw [overSectionHom_one, overScalarHom_apply, overSectionHom_apply]
  change PoleClearing.restrict M inf_le_left (sections j) =
    ((1 : Γ(X, atlas.chart j ⊓ atlas.chart k)) *
      X.presheaf.map (𝟙 (op (atlas.chart j ⊓ atlas.chart k))) (transition j k)) •
      M.presheaf.map (𝟙 (op (atlas.chart j ⊓ atlas.chart k)))
        (PoleClearing.restrict M inf_le_right (sections k))
  simp only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, one_mul]
  exact compatible j k

/-- The global map obtained by gluing the prescribed local images. -/
def sectionMap : atlas.cartierDivisor.sheaf ⟶ M :=
  SheafModuleGluing.glueHom atlas.chart atlas.covers (atlas.localSectionMap M sections)
    (atlas.localSectionMap_compatible M sections transition ratio compatible)

/-- In each actual Cartier frame, the glued map has exactly the prescribed
section as its image of the generator. -/
theorem sectionMap_frame (j : atlas.Index) :
    (atlas.chartTrivialization j).hom ≫
        (atlas.sectionMap M sections transition ratio compatible).over (atlas.chart j) =
      overSectionHom M (atlas.chart j) (sections j) := by
  rw [sectionMap, SheafModuleGluing.glueHom_over, localSectionMap, Iso.hom_inv_id_assoc]

end CartierEquationAtlas

end ToricPower

end
