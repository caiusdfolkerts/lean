module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Linearity forced by an actual inverse-Serre pairing

The target of the representing functor may be an unbounded category.
Naturality and separation by scalar-linear functionals prove linearity;
no reflexivity or finite-dimensionality of its arbitrary argument is used.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower.SerrePairing

universe r u v u' v'
variable (k : Type r) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]
variable (i T : C ⥤ D) [i.Linear k]

/-- A scalar-linear pairing, natural in the finite argument, forces the
representing functor's actual morphism map to preserve scalars. -/
theorem representingFunctor_linear
    (pairing : ∀ (G : C) (E : D),
      (E ⟶ i.obj G) ≃ₗ[k] Module.Dual k (T.obj G ⟶ E))
    (naturality : ∀ {G H : C} (a : G ⟶ H) (E : D)
      (f : E ⟶ i.obj G) (g : T.obj H ⟶ E),
      pairing H E (f ≫ i.map a) g =
        pairing G E f (T.map a ≫ g)) : T.Linear k := by
  constructor
  intro G H a r
  apply Module.eval_apply_injective k
  apply LinearMap.ext
  intro functional
  obtain ⟨f, hf⟩ := (pairing G (T.obj H)).surjective functional
  subst functional
  change pairing G (T.obj H) f (T.map (r • a)) =
    pairing G (T.obj H) f (r • T.map a)
  calc
    pairing G (T.obj H) f (T.map (r • a)) =
        pairing H (T.obj H) (f ≫ i.map (r • a)) (𝟙 _) := by
      simpa only [Category.comp_id] using
        (naturality (r • a) (T.obj H) f (𝟙 _)).symm
    _ = r • pairing H (T.obj H) (f ≫ i.map a) (𝟙 _) := by
      simp only [CategoryTheory.Functor.map_smul, Linear.comp_smul, map_smul,
        LinearMap.smul_apply]
    _ = pairing G (T.obj H) f (r • T.map a) := by
      rw [naturality, Category.comp_id, map_smul]

end ToricPower.SerrePairing

end
