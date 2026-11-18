module

public import ToricPower.InverseSerreLinear
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Full faithfulness from two natural inverse-Serre pairings

The map on morphisms is identified explicitly: composing two pairings
sends the functor's actual image of a morphism to its evaluation in the
double dual. Finite-dimensionality is used only in this bounded category,
where every indicated Hom space is finite-dimensional. No reflexivity
of an arbitrary unbounded object is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower.SerrePairing

universe r u v
variable (k : Type r) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable (T : C ⥤ C)
variable (pairing : ∀ (G E : C),
  (E ⟶ G) ≃ₗ[k] Module.Dual k (T.obj G ⟶ E))
variable [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- The inverse to the actual morphism map, constructed from the two
pairings and the finite-dimensional evaluation isomorphism. -/
def recoverHomEquiv (X Y : C) :
    (T.obj X ⟶ T.obj Y) ≃ₗ[k] (X ⟶ Y) :=
  ((Module.evalEquiv k (T.obj X ⟶ T.obj Y)).trans
    (pairing X (T.obj Y)).dualMap).trans (pairing Y X).symm

variable
  (sourceNaturality : ∀ (G : C) {E F : C} (a : E ⟶ F)
    (f : F ⟶ G) (g : T.obj G ⟶ E),
    pairing G E (a ≫ f) g = pairing G F f (g ≫ a))
  (targetNaturality : ∀ {G H : C} (a : G ⟶ H) (E : C)
    (f : E ⟶ G) (g : T.obj H ⟶ E),
    pairing H E (f ≫ a) g = pairing G E f (T.map a ≫ g))

include sourceNaturality targetNaturality

/-- Naturality identifies the constructed equivalence with the actual
functor map, rather than merely proving an equality of dimensions. -/
theorem recoverHomEquiv_map {X Y : C} (f : X ⟶ Y) :
    recoverHomEquiv k T pairing X Y (T.map f) = f := by
  apply (pairing Y X).injective
  apply LinearMap.ext
  intro g
  simp only [recoverHomEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply,
    Module.evalEquiv_apply, Module.Dual.eval_apply]
  calc
    pairing X (T.obj Y) g (T.map f) =
        pairing Y (T.obj Y) (g ≫ f) (𝟙 _) := by
      simpa only [Category.comp_id] using
        (targetNaturality f (T.obj Y) g (𝟙 _)).symm
    _ = pairing Y X f g := by
      simpa only [Category.id_comp] using
        sourceNaturality Y g f (𝟙 _)

/-- The actual representing functor is fully faithful. -/
def representingFunctorFullyFaithful : T.FullyFaithful where
  preimage {X Y} f := recoverHomEquiv k T pairing X Y f
  map_preimage {X Y} f := by
    apply (recoverHomEquiv k T pairing X Y).injective
    exact recoverHomEquiv_map k T pairing sourceNaturality targetNaturality _
  preimage_map f := recoverHomEquiv_map k T pairing sourceNaturality targetNaturality f

end ToricPower.SerrePairing

end
