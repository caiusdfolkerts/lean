module

public import ToricPower.AffineFiniteGenerators

/-!
# Epimorphisms detected by actual local generating sections

The criterion below uses genuine epimorphisms from free sheaves on every
member of an open cover. A factorization of every local generator through
one sheaf morphism therefore makes that morphism an epimorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace ToricPower

universe u v

variable {X : Scheme.{u}}

/-- Composition of a section map is the section map of its actual image. -/
theorem overSectionHom_comp {M N : X.Modules} (p : M ⟶ N)
    (U : X.Opens) (s : Γ(M, U)) :
    overSectionHom M U s ≫ p.over U = overSectionHom N U (p.app U s) := by
  apply overUnitHom_ext_top
  change p.app U ((overSectionHom M U s).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) = _
  rw [overSectionHom_one, overSectionHom_one]

/-- Local generators that factor through `p` prove the categorical
epimorphism property, against arbitrary module-sheaf targets. -/
theorem epi_of_local_generator_factorizations {Index : Type v}
    (opens : Index → X.Opens) (covers : IsOpenCover opens)
    {Q M : X.Modules} (p : Q ⟶ M)
    (G : ∀ j, (M.over (opens j)).GeneratingSections)
    (source : ∀ j, (G j).I → X.Modules)
    (lift : ∀ j a, source j a ⟶ Q)
    (frame : ∀ j a, (SheafOfModules.unit X.ringCatSheaf).over (opens j) ⟶
      (source j a).over (opens j))
    (factor : ∀ j a,
      (frame j a ≫ (lift j a).over (opens j)) ≫ p.over (opens j) =
        overSectionHom M (opens j) (((G j).s a).val (op (Over.mk (𝟙 (opens j)))))) :
    Epi p := by
  constructor
  intro T f g equality
  apply SheafModuleGluing.hom_ext_of_cover opens covers
  intro j
  apply (cancel_epi (G j).π).mp
  apply (T.over (opens j)).freeHomEquiv.injective
  funext a
  change (T.over (opens j)).unitHomEquiv
      (SheafOfModules.ιFree a ≫ (G j).π ≫ f.over (opens j)) =
    (T.over (opens j)).unitHomEquiv
      (SheafOfModules.ιFree a ≫ (G j).π ≫ g.over (opens j))
  apply congrArg (T.over (opens j)).unitHomEquiv
  rw [← Category.assoc, ← Category.assoc, generatingSections_ι_π,
    ← factor j a]
  simp only [Category.assoc]
  have localEquality := congrArg (fun mapping : Q ⟶ T => mapping.over (opens j)) equality
  simp only [SheafOfModules.Hom.over, CategoryTheory.Functor.map_comp] at localEquality
  rw [localEquality]

end ToricPower

end
