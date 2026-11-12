module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-! # A nonzero map from a genuine whole coproduct detects a component -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {A D : Type*} [Category* A] [Category* D] [HasZeroMorphisms D]
  {I : Type*} (family : I → A) [HasColimit (Discrete.functor family)]
  (F : A ⥤ D) [PreservesColimit (Discrete.functor family) F]

/-- This follows from the actual colimit universal property, so it
allows an infinite family and an arbitrary derived target. -/
theorem exists_nonzero_coproduct_component {S : A} (frame : colimit (Discrete.functor family) ≅ S)
    {T : D} (f : F.obj S ⟶ T) (nonzero : f ≠ 0) :
    ∃ i : I, F.map (colimit.ι (Discrete.functor family) ⟨i⟩ ≫ frame.hom) ≫ f ≠ 0 := by
  by_contra! zero
  have vanishes : F.map frame.hom ≫ f = 0 :=
    (isColimitOfPreserves F (colimit.isColimit (Discrete.functor family))).hom_ext (fun i => by
      change F.map (colimit.ι (Discrete.functor family) i) ≫ (F.map frame.hom ≫ f) =
        F.map (colimit.ι (Discrete.functor family) i) ≫ 0
      simpa only [F.map_comp,Category.assoc,comp_zero] using zero i.as)
  apply nonzero
  rw [← cancel_epi (F.map frame.hom),comp_zero]
  exact vanishes

end ToricPower

end
