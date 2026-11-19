module

public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Naturality of the ordinary singular augmentation

The augmentation on zeroth homology sends every point class to the
identity of the coefficient object.  This gives its naturality for every
continuous map, without any connectedness assumption.  The computation
is made on the actual zero-simplex coproduct and its quotient to homology.

Candidate until the pinned Lean compiler has checked this source.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace ToricPower

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  [Preadditive C] [CategoryWithHomology C]

/-- The ordinary simplicial augmentation is natural, as an equality of
maps from the actual homology objects. -/
theorem simplicialHomologyZeroAugmentation_naturality {X Y : SSet.{w}}
    (f : X ⟶ Y) (M : C) :
    SSet.homologyMap f M 0 ≫ Y.homology₀ε M = X.homology₀ε M := by
  apply (cancel_epi ((X.chainComplex M).homologyπ 0)).mp
  apply (cancel_epi (X.chainComplex M).cycles₀Iso.inv).mp
  apply SSet.chainComplex_hom_ext
  intro x
  have hx : X.ιChainComplex x ≫ (X.chainComplex M).cycles₀Iso.inv =
      (X.chainComplex M).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (cancel_mono ((X.chainComplex M).iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.iCyclesIso_inv_hom_id,
      Category.comp_id, HomologicalComplex.liftCycles_i]
  simp only [← Category.assoc]
  rw [hx]
  simp only [Category.assoc]
  change (X.chainComplex M).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      (X.chainComplex M).homologyπ 0 ≫
        HomologicalComplex.homologyMap (SSet.chainComplexMap f M) 0 ≫
          Y.homology₀ε M = _
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  simp only [
    SSet.ι_chainComplexMap_f,
    SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε,
    SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε]

/-- The ordinary singular augmentation commutes with every actual
continuous map.  In particular it commutes with the translations of
convex strips used for chart monomial multiplication. -/
theorem singularHomologyZeroAugmentation_naturality {X Y : TopCat.{w}}
    (f : X ⟶ Y) (M : C) :
    ((singularHomologyFunctor C 0).obj M).map f ≫ Y.singularHomology₀ε M =
      X.singularHomology₀ε M :=
  simplicialHomologyZeroAugmentation_naturality (TopCat.toSSet.map f) M

end ToricPower
