module

public import ToricPower.CellularCochainVectorGenerator

/-! # Composing the actual cellular generator comparisons

The statements keep the specified composite map opaque while composing
the two original generator identities. This permits the same literal
maps to be specialized without re-expanding their coefficient objects.
-/

@[expose] public section

open CategoryTheory

namespace ToricPower

universe v u

variable {B : Type u} [Category.{v} B]
  {W X Y Z T : B}

/-- Two consecutive generator identities give the specified three-step map. -/
theorem reconstruction_generator_chain
    (a : W ⟶ X) (u : X ⟶ Y) (v : Y ⟶ Z) (w : Z ⟶ T)
    (f : X ⟶ T) (b : W ⟶ Y) (c : W ⟶ Z)
    (factor : f = u ≫ v ≫ w) (first : a ≫ u = b) (second : b ≫ v = c) :
    a ≫ f = c ≫ w := by
  rw [factor, ← Category.assoc a u, first, ← Category.assoc b v, second]

/-- Postcomposition preserves the displayed generator and specified map. -/
theorem reconstruction_generator_postcompose
    (a : W ⟶ X) (f : X ⟶ Y) (c : W ⟶ Z) (w : Z ⟶ Y)
    (same : a ≫ f = c ≫ w) (post : Y ⟶ T) :
    a ≫ f ≫ post = c ≫ w ≫ post := by
  simpa only [Category.assoc] using congrArg (fun z => z ≫ post) same

/-- The specified comparison fixes the intermediate objects before the
two already proved generator identities are inserted. -/
theorem reconstruction_generator_chain_of_components
    {u : X ⟶ Y} {v : Y ⟶ Z} {w : Z ⟶ T} {f : X ⟶ T}
    (factor : f = u ≫ v ≫ w)
    {a : W ⟶ X} {b : W ⟶ Y} {c : W ⟶ Z}
    (first : a ≫ u = b) (second : b ≫ v = c) :
    a ≫ f = c ≫ w :=
  reconstruction_generator_chain a u v w f b c factor first second

end ToricPower

end
