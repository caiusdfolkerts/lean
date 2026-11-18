module

public import TauCeti.AlgebraicTopology.Cellular.Map
public import TauCeti.AlgebraicTopology.Cellular.Comparison

/-!
# Naturality of cellular–singular homology comparison

The comparison is defined through the actual skeletal inclusions. This
file proves that it intertwines an arbitrary cellular map with the actual
map on relative singular homology. Consequently it can be used to compare
costalk restriction and translation maps, not just isolated groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex TauCeti

namespace ToricPower

universe w v u

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] {D : Set X} {E : Set Y}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
  [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]
  [∀ m, HasExactColimitsOfShape (Discrete (cell C' m)) A]
  (M : A)

/-- The skeletal description of cycles commutes with every cellular map. -/
theorem cellularCyclesIso_inv_natural (q : ℕ) :
    (TauCeti.cellularCyclesIso C M q).inv ≫
        HomologicalComplex.cyclesMap (TauCeti.cellularChainComplexMap C C' hf M) q =
      TopPair.singularHomologyMap (TauCeti.skeletonBasePairMap C C' hf q) M q ≫
        (TauCeti.cellularCyclesIso C' M q).inv := by
  apply (cancel_mono ((TauCeti.cellularChainComplex C' M).iCycles q)).mp
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    TauCeti.cellularCyclesIso_inv_comp_iCycles,
    TauCeti.cellularCyclesIso_inv_comp_iCycles_assoc,
    TauCeti.cellularChainComplexMap_f, TauCeti.cellularChainGroupMap_def]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rw [← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp,
    TauCeti.skeletonBasePairMap_comp_toSkeletonPair]

/-- The forward cycle comparison is natural as well. -/
theorem cellularCyclesIso_natural (q : ℕ) :
    HomologicalComplex.cyclesMap (TauCeti.cellularChainComplexMap C C' hf M) q ≫
        (TauCeti.cellularCyclesIso C' M q).hom =
      (TauCeti.cellularCyclesIso C M q).hom ≫
        TopPair.singularHomologyMap (TauCeti.skeletonBasePairMap C C' hf q) M q := by
  apply (cancel_epi (TauCeti.cellularCyclesIso C M q).inv).mp
  rw [← Category.assoc, cellularCyclesIso_inv_natural]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Naturality of the actual cellular–singular isomorphism. The only
comparison hypotheses assert the standard skeletal inclusion isomorphisms;
these are automatic for module coefficients or finite-dimensional CW pairs. -/
theorem cellularSingularHomologyIso_natural (q : ℕ)
    [IsIso (TopPair.singularHomologyMap
      (TauCeti.skeletonBasePairToComplex C (q + 1)) M q)]
    [IsIso (TopPair.singularHomologyMap
      (TauCeti.skeletonBasePairToComplex C' (q + 1)) M q)] :
    HomologicalComplex.homologyMap (TauCeti.cellularChainComplexMap C C' hf M) q ≫
        (TauCeti.cellularSingularHomologyIso C' M q).hom =
      (TauCeti.cellularSingularHomologyIso C M q).hom ≫
        TopPair.singularHomologyMap (TauCeti.complexBasePairMap C C' hf) M q := by
  apply (cancel_epi ((TauCeti.cellularChainComplex C M).homologyπ q)).mp
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    TauCeti.homologyπ_comp_cellularSingularHomologyIso_hom,
    ← Category.assoc, cellularCyclesIso_natural,
    Category.assoc, ← TopPair.singularHomologyMap_comp,
    TauCeti.skeletonBasePairMap_comp_toComplex,
    TopPair.singularHomologyMap_comp,
    ← Category.assoc, ← TauCeti.homologyπ_comp_cellularSingularHomologyIso_hom,
    Category.assoc]

end ToricPower
