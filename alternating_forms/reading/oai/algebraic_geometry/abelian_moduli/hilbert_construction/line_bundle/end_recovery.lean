import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality

/-! Canonical pullback/restriction comparison for arbitrary module-sheaf maps.
The two generic lemmas are retained verbatim from the pinned upstream file;
line-bundle scalar-transfer applications are not needed by map gluing. -/
namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
noncomputable section
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

theorem LineBundle.EndRecovery.pullbackModuleRestrictionMap_injective (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) : Function.Injective (OpenPullback.ModuleValues.pullbackModuleRestrictionMap f (M := M) (N := N)) := by
  intro φ ψ h
  unfold OpenPullback.ModuleValues.pullbackModuleRestrictionMap at h
  exact (cancel_epi ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M)).mp
    ((cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app N)).mp
      (by simpa only [Category.assoc] using h))

theorem LineBundle.EndRecovery.pullbackModuleRestrictionMap_global (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (φ : M ⟶ N) :
    OpenPullback.ModuleValues.pullbackModuleRestrictionMap f ((Scheme.Modules.pullback f).map φ) =
      (Scheme.Modules.restrictFunctor f).map φ := by
  unfold OpenPullback.ModuleValues.pullbackModuleRestrictionMap
  rw [← Category.assoc, ← (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality φ,
    Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback f).hom_inv_id_app, Category.comp_id]

end
end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
