module

public import ToricPower.CategoricalFoundations
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Actual shifted detection through full faithfulness and adjunction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  (B : C ⥤ D) [B.Additive] [B.CommShift ℤ]
  (F G : C ⥤ C) [F.Additive] [G.Additive] [G.CommShift ℤ]
  (P : D ⥤ D) (adj : F ⊣ G) (fullyFaithful : B.FullyFaithful)
  (comparison : F ⋙ B ≅ B ⋙ P)

include adj fullyFaithful comparison in
/-- The resulting map has the original right-adjoint target. The
comparison and both adjunction directions retain their specified maps. -/
theorem exists_nonzero_rightAdjoint_of_diagram
    (M L : C) (q : ℤ) (f : P.obj (B.obj M) ⟶ (B.obj L)⟦q⟧) (nonzero : f ≠ 0) :
    ∃ g : M ⟶ (G.obj L)⟦q⟧, g ≠ 0 := by
  let source := comparison.app M
  let target := (B.commShiftIso q).app L
  let a := fullyFaithful.preimage (source.hom ≫ f ≫ target.inv)
  have nonzeroA : a ≠ 0 := by
    intro zero
    have mapped := congrArg B.map zero
    rw [fullyFaithful.map_preimage,B.map_zero] at mapped
    apply nonzero
    rw [← cancel_epi source.hom,← cancel_mono target.inv,Category.assoc,comp_zero,zero_comp]
    exact mapped
  let b := adj.homEquiv M (L⟦q⟧) a
  have nonzeroB : b ≠ 0 := by
    intro zero
    apply nonzeroA
    apply (adj.homEquiv M (L⟦q⟧)).injective
    exact zero.trans (adj.homAddEquiv_zero M (L⟦q⟧)).symm
  let rightShift := (G.commShiftIso q).app L
  refine ⟨b ≫ rightShift.hom,?_⟩
  intro zero
  apply nonzeroB
  rw [← cancel_mono rightShift.hom,zero_comp]
  exact zero

end ToricPower

end
