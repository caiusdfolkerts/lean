module

public import ToricPower.ArrangementOpenSupport
public import ToricPower.ArrangementCostalkTranslation
public import ToricPower.ArrangementCostalkCells
public import ToricPower.ConvexComplementTranslatedRestriction

/-!
# Translation and extension for actual arrangement cochains

If translating an open cell support by an integral vector puts it inside
a second support, inverse translation is a genuine map of complementary
relative CW pairs. Its scalar dual is the desired translated extension
of cochains. The fixed ambient top classes commute with these actual
maps for nonempty bounded convex supports.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  {U V : OpenCellSupport A} (z : Fin n → ℤ)
  (h : translatedRegion (U.val : Set (Fin n → ℝ)) (latticeLift z) ⊆ V.val)

local instance : CWComplex (arrangementCarrier A) := periodicArrangementCWComplex A

include h

/-- Inverse translation sends the complement of the larger support into
the complement of the smaller support. -/
theorem openSupportChainTranslation_base (p : arrangementCarrier A)
    (outside : p.val ∈ (V.val : Set (Fin n → ℝ))ᶜ) :
    (arrangementTranslation A (-z) p).val ∈ (U.val : Set (Fin n → ℝ))ᶜ := by
  intro inside
  apply outside
  apply h
  refine ⟨p.val + latticeLift (-z), inside, ?_⟩
  rw [latticeLift_neg]
  abel

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)

/-- The genuine chain map is induced by inverse ambient translation. -/
def openSupportChainTranslation :
    openSupportChainComplex A M V ⟶ openSupportChainComplex A M U :=
  relativeCWChainMap (openSupportComplement A V) (openSupportComplement A U)
    (arrangementTranslation A (-z)) M (arrangementTranslation_cellular A (-z))
    (openSupportChainTranslation_base A z h)

/-- The same literal translation on complementary topological pairs. -/
def openSupportPairTranslation :
    TopPair.ofSubset ((V.val : Set (Fin n → ℝ))ᶜ : Set (TopCat.of (Fin n → ℝ))) ⟶
      TopPair.ofSubset ((U.val : Set (Fin n → ℝ))ᶜ :
        Set (TopCat.of (Fin n → ℝ))) :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨fun p => p + latticeLift (-z), by fun_prop⟩)
    (fun p outside inside => outside (h
      ⟨p + latticeLift (-z), inside, by rw [latticeLift_neg]; abel⟩))

/-- The actual relative CW map and the actual singular map agree under
the cellular comparison. -/
theorem openSupportCellularSingularIso_translation (q : ℕ) :
    HomologicalComplex.homologyMap (openSupportChainTranslation A z h M) q ≫
        (openSupportCellularSingularIso A M U q).hom =
      (openSupportCellularSingularIso A M V q).hom ≫
        TopPair.singularHomologyMap (openSupportPairTranslation A z h) M q := by
  let B := openSupportComplement A V
  let D := openSupportComplement A U
  let C₁ := relativeCWCarrier B
  let C₂ := relativeCWCarrier D
  let hf := relativeCWMap_cellular B D (arrangementTranslation A (-z))
    (arrangementTranslation_cellular A (-z)) (openSupportChainTranslation_base A z h)
  have comparison :
      TauCeti.complexBasePairMap C₁ C₂ hf ≫ (openSupportPairIso A U).hom =
        (openSupportPairIso A V).hom ≫ openSupportPairTranslation A z h := by
    apply TopPair.hom_ext_of_fst
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp,
      TauCeti.complexBasePairMap_fst, openSupportPairIso_hom_fst,
      openSupportPairIso_hom_fst]
    dsimp only [relativeCWMap, openSupportPairTranslation]
    erw [TopPair.ofSubsetMap_fst]
    ext p
    rfl
  change HomologicalComplex.homologyMap
      (TauCeti.cellularChainComplexMap C₁ C₂ hf M) q ≫
        (TauCeti.cellularSingularHomologyIso C₂ M q).hom ≫
          TopPair.singularHomologyMap (openSupportPairIso A U).hom M q =
    (TauCeti.cellularSingularHomologyIso C₁ M q).hom ≫
      TopPair.singularHomologyMap (openSupportPairIso A V).hom M q ≫
        TopPair.singularHomologyMap (openSupportPairTranslation A z h) M q
  rw [← Category.assoc, cellularSingularHomologyIso_natural, Category.assoc,
    ← TopPair.singularHomologyMap_comp, comparison, TopPair.singularHomologyMap_comp]

/-- The genuine inverse-translation map preserves the ambient chain
class. No orientation is chosen separately on a translated support. -/
theorem openSupportChainTopClassIso_translation
    (convexU : Convex ℝ (U.val : Set (Fin n → ℝ)))
    (convexV : Convex ℝ (V.val : Set (Fin n → ℝ)))
    (nonemptyU : (U.val : Set (Fin n → ℝ)).Nonempty)
    (nonemptyV : (V.val : Set (Fin n → ℝ)).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))
    (boundedV : Bornology.IsBounded (V.val : Set (Fin n → ℝ))) :
    HomologicalComplex.homologyMap (openSupportChainTranslation A z h M) n ≫
        (openSupportChainTopClassIso A M U convexU nonemptyU boundedU).hom =
      (openSupportChainTopClassIso A M V convexV nonemptyV boundedV).hom := by
  simp only [openSupportChainTopClassIso, Iso.trans_hom]
  rw [← Category.assoc, openSupportCellularSingularIso_translation, Category.assoc]
  congr 1
  apply convexComplementTopClassIso_translatedRestriction M
    (V.val : Set (Fin n → ℝ)) (U.val : Set (Fin n → ℝ)) (latticeLift (-z))
    convexV convexU nonemptyV nonemptyU boundedV boundedU
  · intro p hp
    refine ⟨p + latticeLift z, h ⟨p, hp, rfl⟩, ?_⟩
    rw [latticeLift_neg]
    abel
  · exact TopPair.ofSubsetMap_fst _ _

section Field

variable (k : Type) [Field k]

/-- Actual translation followed by extension of scalar cochains. -/
def openSupportCochainTranslation :
    openSupportCochainComplex A k U ⟶ openSupportCochainComplex A k V :=
  scalarDualMap k (openSupportChainTranslation A z h (ModuleCat.of k k))

/-- The coefficient on the coherent top class is exactly one. -/
theorem openSupportCochainTopClassIso_translation
    (convexU : Convex ℝ (U.val : Set (Fin n → ℝ)))
    (convexV : Convex ℝ (V.val : Set (Fin n → ℝ)))
    (nonemptyU : (U.val : Set (Fin n → ℝ)).Nonempty)
    (nonemptyV : (V.val : Set (Fin n → ℝ)).Nonempty)
    (boundedU : Bornology.IsBounded (U.val : Set (Fin n → ℝ)))
    (boundedV : Bornology.IsBounded (V.val : Set (Fin n → ℝ))) :
    HomologicalComplex.homologyMap (openSupportCochainTranslation A z h k) n ≫
        (openSupportCochainTopClassIso A k V convexV nonemptyV boundedV).hom =
      (openSupportCochainTopClassIso A k U convexU nonemptyU boundedU).hom :=
  scalarDualHomologyClassIso_natural k _ n _ _
    (openSupportChainTopClassIso_translation A z h (ModuleCat.of k k)
      convexU convexV nonemptyU nonemptyV boundedU boundedV)

end Field
end ToricPower.IntegralArrangement
