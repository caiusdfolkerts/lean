module

public import ToricPower.ArrangementLaurentTopInclusion

/-!
# Quasi-isomorphism of the original complete Laurent top summand

The original top-cell summand is the unrestricted coproduct of its
character maps. Every permitted character uses the actual top-class
preserving support extension; every omitted source coefficient has an
acyclic target. Exactness of module coproducts therefore proves the
quasi-isomorphism of the original map, without truncating any weights.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (k : Type) [Field k]
  (strictDirection : ∃ v : Fin n → ℝ, ∀ i ∈ Sum.inl '' S,
    0 < augmentedForms A i v)
  (minimal : Fin n → ℤ)
  (minimal_eq : ∀ i ∈ S, rayPairing A minimal i = c.2.val.val.1 (.inl i) - 1)
  (p : RepresentableCostalkIndex A c S minimal n)

local notation "singleTop" => HomologicalComplex.single (ModuleCat k) (ComplexShape.up ℕ) n
local notation "L" => fun m => PLift (RepresentableSupportedWeight A S c m)
local notation "e" => representedMinimalCofaceProofEquiv A S c strictDirection minimal minimal_eq p
local notation "topMap" => representedLaurentTopCofaceInclusion A S c k (Sigma.fst (Subtype.val p)) (Sigma.snd (Subtype.val p))
local notation "K" => fun m => representedWeightCellularComplex A S c m k

/-- The original Laurent inclusion and the specified fixed-character
support map agree as whole maps of complexes. -/
@[reassoc]
theorem representedTopCofaceFamilyCompatibility (m : Fin n → ℤ) :
    (singleTop).map (freePartitionInclusion k L e m) ≫ topMap =
      representedTopCofaceFiberMap A S c k strictDirection minimal minimal_eq p m ≫
        representedLaurentWeightInclusion A S c k m := by
  apply HomologicalComplex.from_single_hom_ext
  apply (cancel_epi (HomologicalComplex.singleObjXSelf (.up ℕ) n
    (representedSupportedWeightCoefficient A S c k m)).inv).mp
  simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
    representedSupportedWeightCoefficient, Category.assoc, Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro h a
  change (topMap).f n
      ((HomologicalComplex.singleObjXSelf (.up ℕ) n
        ((reflectedLaurentDiagram A S k).obj ⟨n,p.val.1⟩)).inv
          (Finsupp.mapDomain (fun h : PLift (RepresentableSupportedWeight A S c m) =>
            (e).symm ⟨m,h⟩) (Finsupp.single h a))) =
    (representedLaurentWeightInclusion A S c k m).f n
      ((representedTopCofaceFiberMap A S c k strictDirection minimal minimal_eq p m).f n
        ((HomologicalComplex.singleObjXSelf (.up ℕ) n
          (representedSupportedWeightCoefficient A S c k m)).inv (Finsupp.single h a)))
  rw [representedTopCofaceFiberMap_generator, representedLaurentWeightInclusion_generator]
  rw [Finsupp.mapDomain_single, representedLaurentTopCofaceInclusion_generator]
  rfl

include strictDirection minimal_eq in
/-- The original full Laurent top-summand inclusion is a
quasi-isomorphism, with no restriction on the character family. -/
theorem representedLaurentTopCofaceInclusion_quasiIso : QuasiIso topMap := by
  let sourceIso := freePartitionSingleColimitIso k L e n
  let β := representedTopCofaceFamilyMap A S c k strictDirection minimal minimal_eq p
  haveI fiberQuasiIso (m : Discrete (Fin n → ℤ)) : QuasiIso (β.app m) :=
    representedTopCofaceFiberMap_quasiIso A S c k strictDirection minimal minimal_eq p m.as
  haveI colimitQuasiIso : QuasiIso (colim.map β) :=
    ToricPower.complex_colimitMap_quasiIso β
  have assembled : sourceIso.inv ≫ topMap =
      colim.map β ≫ (ModuleDirectSum.complexColimitIso k K).inv ≫
        (representableCellularWeightSumIso A S c k).inv := by
    apply colimit.hom_ext
    intro m
    simp only [sourceIso, Category.assoc,
      colimit.ι_map_assoc]
    erw [freePartitionSingleColimitIso_inclusion_assoc k L e n m.as]
    change (singleTop).map (freePartitionInclusion k L e m.as) ≫ topMap =
      representedTopCofaceFiberMap A S c k strictDirection minimal minimal_eq p m.as ≫
        colimit.ι (Discrete.functor K) m ≫
          (ModuleDirectSum.complexColimitIso k K).inv ≫
            (representableCellularWeightSumIso A S c k).inv
    rw [← ModuleDirectSum.complexColimitIso_inclusion k K m.as]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact representedTopCofaceFamilyCompatibility A S c k strictDirection minimal minimal_eq p m.as
  haveI compositeQuasiIso : QuasiIso (sourceIso.inv ≫ topMap) := by
    rw [assembled]
    infer_instance
  exact quasiIso_of_comp_left sourceIso.inv topMap

end ToricPower.IntegralArrangement

end

