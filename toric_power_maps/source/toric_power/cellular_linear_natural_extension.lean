module

public import ToricPower.CellularLinearDensityExtension
public import ToricPower.CellularRealizationLinear

/-!
# Extending the specified comparison to any linear target functor

A colimit-preserving linear source functor is determined by its values
on free representables. This construction extends the original natural
comparison to any linear target functor and retains its exact value on
every representable. In particular the target may be the ordinary
coend placed in the genuine top cellular degree.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace ToricPower.Cellular

universe u v
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasColimitsOfSize.{u,u} B]
  (Ψ : (C ⥤ ModuleCat.{u} k) ⥤ B) [Ψ.Additive] [Ψ.Linear k]

@[reassoc]
theorem fromValue_precompose (M : C ⥤ ModuleCat.{u} k)
    {c d : C} (f : c ⟶ d) (x : M.obj c) :
    representablePrecompose k f ≫ fromValue k M c x =
      fromValue k M d (M.map f x) := by
  apply (representableHomEquiv k M d).injective
  exact (evaluate_representablePrecompose k M f (fromValue k M c x)).trans
    ((congrArg (M.map f) (evaluate_fromValue k M c x)).trans
      (evaluate_fromValue k M d (M.map f x)).symm)

/-- Every vector maps by its original Yoneda arrow under the given
linear functor. -/
def densityFunctorHom (M : C ⥤ ModuleCat.{u} k) :
    M ⟶ (homDiagram k (representableFunctor k ⋙ Ψ)).obj (Ψ.obj M) where
  app c := ModuleCat.ofHom ((Ψ.mapLinearMap k).comp (fromValueLinear k M c))
  naturality {c d} f := by
    ext x
    change Ψ.map (fromValue k M d (M.map f x)) =
      Ψ.map (representablePrecompose k f) ≫ Ψ.map (fromValue k M c x)
    rw [← Ψ.map_comp,fromValue_precompose]

def densityToFunctorComponent (M : C ⥤ ModuleCat.{u} k) :
    (realization k (representableFunctor k ⋙ Ψ)).obj M ⟶ Ψ.obj M :=
  realizationDesc k (representableFunctor k ⋙ Ψ) (densityFunctorHom k Ψ M)

@[reassoc]
theorem densityToFunctor_generator (M : C ⥤ ModuleCat.{u} k) (c : C) (x : M.obj c) :
    realizationInclusion k (representableFunctor k ⋙ Ψ) M c x ≫
      densityToFunctorComponent k Ψ M = Ψ.map (fromValue k M c x) := by
  rw [densityToFunctorComponent,realizationInclusion_desc]
  rfl

/-- The coend descent is natural in the entire original diagram. -/
def densityToFunctor : realization k (representableFunctor k ⋙ Ψ) ⟶ Ψ where
  app := densityToFunctorComponent k Ψ
  naturality {M N} f := by
    apply realization_hom_ext k (representableFunctor k ⋙ Ψ)
    intro c x
    rw [realizationInclusion_map_assoc,densityToFunctor_generator]
    have actual := congrArg Ψ.map (fromValue_comp k f c x)
    simp only [CategoryTheory.Functor.map_comp] at actual
    exact actual.symm.trans
      (densityToFunctor_generator_assoc k Ψ M c x (Ψ.map f)).symm

variable (Φ : (C ⥤ ModuleCat.{u} k) ⥤ B) [Φ.Additive] [Φ.Linear k]
  [PreservesColimitsOfSize.{u,u} Φ]
  (β : representableFunctor k ⋙ Φ ⟶ representableFunctor k ⋙ Ψ)

/-- Extension of the specified original source-natural maps. -/
def densityExtensionToFunctor : Φ ⟶ Ψ :=
  densityExtension k Φ (representableFunctor k ⋙ Ψ) β ≫ densityToFunctor k Ψ

@[reassoc]
theorem densityExtensionToFunctor_generator
    (M : C ⥤ ModuleCat.{u} k) (c : C) (x : M.obj c) :
    Φ.map (fromValue k M c x) ≫ (densityExtensionToFunctor k Ψ Φ β).app M =
      β.app (op c) ≫ Ψ.map (fromValue k M c x) := by
  change Φ.map (fromValue k M c x) ≫
    densityExtensionComponent k Φ (representableFunctor k ⋙ Ψ) β M ≫
      densityToFunctorComponent k Ψ M = _
  rw [densityExtension_generator_assoc,densityToFunctor_generator]

/-- The extension is exactly the given comparison on every original
representable, rather than an unspecified quasi-isomorphic map. -/
theorem densityExtensionToFunctor_representable (c : C) :
    (densityExtensionToFunctor k Ψ Φ β).app (representable k c) = β.app (op c) := by
  have equality := densityExtensionToFunctor_generator k Ψ Φ β
    (representable k c) c (ModuleCat.freeMk (𝟙 c))
  have identity : fromValue k (representable k c) c (ModuleCat.freeMk (𝟙 c)) = 𝟙 _ :=
    fromValue_evaluate k (representable k c) c (𝟙 _)
  simp only [identity,CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id] at equality
  exact equality.trans ((congrArg
    (fun f => β.app (op c) ≫ f) (Ψ.map_id (representable k c))).trans
      (Category.comp_id (β.app (op c))))

end ToricPower.Cellular

end
