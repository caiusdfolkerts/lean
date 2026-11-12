module

public import ToricPower.InverseSerreFullyFaithful

/-!
# Full faithfulness of an ambient inverse-Serre functor

The representing functor takes bounded objects into the full unbounded
ambient category. It need not be lifted back to the bounded category.
Two natural pairings recover its actual morphism map. Finiteness is
required only for the original bounded Hom spaces; the two intervening
Hom spaces are proved finite from the pairings and separation by duals.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower.SerrePairing

universe r u v u' v'
variable (k : Type r) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]
variable (i T : C ⥤ D) [i.Additive] [i.Linear k] [i.Full] [i.Faithful]
variable (pairing : ∀ (G : C) (E : D),
  (E ⟶ i.obj G) ≃ₗ[k] Module.Dual k (T.obj G ⟶ E))
variable [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- Full faithfulness of the ordinary inclusion identifies bounded Hom
spaces with their actual ambient Hom spaces. -/
def inclusionHomEquiv (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] (i.obj X ⟶ i.obj Y) :=
  LinearEquiv.ofBijective (i.mapLinearMap k) ⟨i.map_injective, i.map_surjective⟩

include i pairing in
theorem ambientInverseSerre_hom_finite (X Y : C) :
    FiniteDimensional k (T.obj X ⟶ T.obj Y) := by
  letI : FiniteDimensional k (i.obj X ⟶ i.obj Y) :=
    (inclusionHomEquiv k i X Y).finiteDimensional
  letI : FiniteDimensional k (Module.Dual k (T.obj Y ⟶ i.obj X)) :=
    (pairing Y (i.obj X)).finiteDimensional
  letI : FiniteDimensional k (T.obj Y ⟶ i.obj X) :=
    (Module.finite_dual_iff k).mp inferInstance
  letI : FiniteDimensional k (Module.Dual k (T.obj X ⟶ T.obj Y)) :=
    (pairing X (T.obj Y)).finiteDimensional
  exact (Module.finite_dual_iff k).mp inferInstance

/-- An actual inverse to the ambient functor's map on morphisms. -/
def recoverAmbientHomEquiv (X Y : C) :
    (T.obj X ⟶ T.obj Y) ≃ₗ[k] (X ⟶ Y) :=
  letI := ambientInverseSerre_hom_finite k i T pairing X Y
  (((Module.evalEquiv k (T.obj X ⟶ T.obj Y)).trans
    (pairing X (T.obj Y)).dualMap).trans
    (pairing Y (i.obj X)).symm).trans (inclusionHomEquiv k i X Y).symm

variable
  (sourceNaturality : ∀ (G : C) {E F : D} (a : E ⟶ F)
    (f : F ⟶ i.obj G) (g : T.obj G ⟶ E),
    pairing G E (a ≫ f) g = pairing G F f (g ≫ a))
  (targetNaturality : ∀ {G H : C} (a : G ⟶ H) (E : D)
    (f : E ⟶ i.obj G) (g : T.obj H ⟶ E),
    pairing H E (f ≫ i.map a) g = pairing G E f (T.map a ≫ g))

include sourceNaturality targetNaturality

theorem recoverAmbientHomEquiv_map {X Y : C} (f : X ⟶ Y) :
    recoverAmbientHomEquiv k i T pairing X Y (T.map f) = f := by
  apply (inclusionHomEquiv k i X Y).injective
  apply (pairing Y (i.obj X)).injective
  apply LinearMap.ext
  intro g
  simp only [recoverAmbientHomEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply,
    Module.evalEquiv_apply, Module.Dual.eval_apply]
  change pairing X (T.obj Y) g (T.map f) = pairing Y (i.obj X) (i.map f) g
  calc
    pairing X (T.obj Y) g (T.map f) =
        pairing Y (T.obj Y) (g ≫ i.map f) (𝟙 _) := by
      simpa only [Category.comp_id] using
        (targetNaturality f (T.obj Y) g (𝟙 _)).symm
    _ = pairing Y (i.obj X) (i.map f) g := by
      simpa only [Category.id_comp] using
        sourceNaturality Y g (i.map f) (𝟙 _)

/-- Full faithfulness holds in the entire ambient category, without
assuming that the representing objects belong to the inclusion's image. -/
def ambientRepresentingFunctorFullyFaithful : T.FullyFaithful where
  preimage {X Y} f := recoverAmbientHomEquiv k i T pairing X Y f
  map_preimage {X Y} f := by
    apply (recoverAmbientHomEquiv k i T pairing X Y).injective
    exact recoverAmbientHomEquiv_map k i T pairing sourceNaturality targetNaturality _
  preimage_map f :=
    recoverAmbientHomEquiv_map k i T pairing sourceNaturality targetNaturality f

end ToricPower.SerrePairing

end
