module

public import ToricPower.ArrangementStrictRegion
public import ToricPower.ArrangementLocalStrictRegion
public import ToricPower.ArrangementFaceNerve
public import ToricPower.ArrangementLocalMorse
public import ToricPower.CellularOpenRegionSections
public import ToricPower.CellularLocalMorseVanishing
public import ToricPower.CellularConstantMorse

/-! # The actual local Morse complex of strict arrangement support

The coefficient functor consists of the genuine open scalar submodules,
with all face maps. Contractibility of the cut and its true closed
complement proves vanishing of its particular derived-section mapping
fiber at an excluded central cell.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open BondalThomsen.ConvexNerveReducedCochainAcyclicity

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]

local notation "U" => UniversalIncidenceObject A
local notation "E" => Fin n → ℝ
local notation "J" => Fin s ⊕ Fin n

variable (lower : (Fin s ⊕ Fin n) → ℤ) (selected : Set (Fin s ⊕ Fin n))

/-- The actual face diagram of strict integral support. -/
def universalStrictCoefficientDiagram : U ⥤ ModuleCat k :=
  Cellular.openScalarDiagram k (universalStrictClosedPredicate A lower selected)
    (universalStrictClosedPredicate_downward A lower selected)

theorem universalStrictCoefficient_isZero (c : U)
    (outside : universalStrictClosedPredicate A lower selected c) :
    IsZero ((universalStrictCoefficientDiagram A k lower selected).obj c) := by
  letI : Subsingleton (MorseCoefficients.openScalar k
      (universalStrictClosedPredicate A lower selected c)) := ⟨fun a b => by
    apply Subtype.ext
    exact (a.property outside).trans (b.property outside).symm⟩
  change IsZero (ModuleCat.of k (MorseCoefficients.openScalar k
    (universalStrictClosedPredicate A lower selected c)))
  exact ModuleCat.isZero_of_subsingleton _

/-- Outside the weak support, the actual local Morse complex vanishes
for every cut region: every coefficient on the full face star is zero. -/
theorem universalStrict_outside_localMorse_acyclic
    (c : U) (region : Set E)
    (outside : ¬ ∀ j ∈ selected, (lower j : ℝ) ≤
      augmentedForms A j (cellCenter (augmentedForms A) c.2)) :
    ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (U ⥤ ModuleCat k) 0).obj
        (universalStrictCoefficientDiagram A k lower selected))).Acyclic := by
  apply Cellular.localMorse_single_acyclic_of_coefficients k
    (universalRegionInclusion A c region) c (universalRegionInitialArrows A c region)
    (universalStrictCoefficientDiagram A k lower selected)
  · exact universalStrictCoefficient_isZero A k lower selected c
      (universalStrictSupport_absent_above A lower selected c outside le_rfl)
  · intro d
    exact universalStrictCoefficient_isZero A k lower selected d.val.val
      (universalStrictSupport_absent_above A lower selected c outside d.val.property)

/-- On a supported central cell, the canonical inclusion into constant
coefficients is an isomorphism on its entire face star. -/
theorem universalStrict_interior_localMorse_acyclic
    (c : U) (region : Set E) (supported : universalStrictSupport A lower selected c)
    (contractible : ContractibleSpace (incidenceRealization
      (fun d e : UniversalFaceStar A c => d ≤ e)
      (universalFaceStarMeets A c region))) :
    ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (U ⥤ ModuleCat k) 0).obj
        (universalStrictCoefficientDiagram A k lower selected))).Acyclic := by
  letI := contractible
  let j := universalRegionInclusion A c region
  let arrows := universalRegionInitialArrows A c region
  let f := Cellular.openScalarInclusion k
    (universalStrictClosedPredicate A lower selected)
    (universalStrictClosedPredicate_downward A lower selected)
  haveI : IsIso (f.app c) :=
    Cellular.openScalarInclusion_app_isIso k
      (universalStrictClosedPredicate A lower selected)
      (universalStrictClosedPredicate_downward A lower selected) c
      (fun absent => absent supported)
  haveI : IsIso ((Cellular.localDiagramRestriction k j).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro d
    exact Cellular.openScalarInclusion_app_isIso k
      (universalStrictClosedPredicate A lower selected)
      (universalStrictClosedPredicate_downward A lower selected) d.val.val
      (fun absent => absent (universalStrictSupport_upward A lower selected d.val.property supported))
  haveI := FiniteCech.constant_localSectionComparison_single_quasiIso k
    (universalFaceStarMeets A c region)
    (fun _ _ h => universalFaceStarMeets_upward A c region h) j c arrows
  haveI : QuasiIso ((Cellular.localSectionComparison k j c arrows).app
      ((CochainComplex.singleFunctor (U ⥤ ModuleCat k) 0).obj
        (universalStrictCoefficientDiagram A k lower selected))) :=
    Cellular.localSectionComparison_single_quasiIso_of_map k j c arrows f
  exact Cellular.localMorse_acyclic_of_comparison_quasiIso k j c arrows _

/-- This is a vanishing theorem for the actual local Morse functor,
not a definition of microsupport through an assumed vanishing property. -/
theorem universalStrict_localMorse_acyclic_of_nerves (c : U) (region : Set E)
    (outside : universalStrictClosedPredicate A lower selected c)
    (wholeContractible : ContractibleSpace (incidenceRealization
      (fun d e : UniversalFaceStar A c => d ≤ e)
      (universalFaceStarMeets A c region)))
    (closedContractible : ContractibleSpace (incidenceRealization
      (fun d e : {d : UniversalFaceStar A c // faceStarStrictClosedPredicate A lower selected c d}
        => d ≤ e)
      (fun d => universalFaceStarMeets A c region d.val))) :
    ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (U ⥤ ModuleCat k) 0).obj
        (universalStrictCoefficientDiagram A k lower selected))).Acyclic := by
  apply Cellular.localMorse_single_acyclic_of_stalk_and_restrictedSections k
    (universalRegionInclusion A c region) c (universalRegionInitialArrows A c region)
    (universalStrictCoefficientDiagram A k lower selected)
    (universalStrictCoefficient_isZero A k lower selected c outside)
  exact Cellular.openCutProjectiveSection_acyclic k
    (universalFaceStarMeets A c region) (faceStarStrictClosedPredicate A lower selected c)
    (fun _ _ h => universalFaceStarMeets_upward A c region h)
    (faceStarStrictClosedPredicate_downward A lower selected c)
    (Cellular.localSectionResolution k (H := UniversalRegionStar A c region))
    wholeContractible closedContractible

/-- A convex local cut with a nonempty star-convex excluded complement
has vanishing actual strict-support Morse complex at an excluded cell. -/
theorem universalStrict_localMorse_acyclic_of_starConvex_complement
    (c : U) (region : Set E)
    (outside : universalStrictClosedPredicate A lower selected c)
    (convex : Convex ℝ region) (nonempty : region.Nonempty)
    (inside : region ⊆ localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2))
    (center : E)
    (star : StarConvex ℝ center
      (region ∩ (strictCellRegion (augmentedForms A) lower selected)ᶜ))
    (excludedNonempty :
      (region ∩ (strictCellRegion (augmentedForms A) lower selected)ᶜ).Nonempty) :
    ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (U ⥤ ModuleCat k) 0).obj
        (universalStrictCoefficientDiagram A k lower selected))).Acyclic := by
  apply universalStrict_localMorse_acyclic_of_nerves A k lower selected c region outside
  · exact universalFaceStarMeets_incidence_contractible A c region convex nonempty inside
  · exact closedUniversalFaceStarMeets_incidence_contractible A c region
      (region ∩ (strictCellRegion (augmentedForms A) lower selected)ᶜ)
      (faceStarStrictClosedPredicate A lower selected c)
      (faceStarStrictClosedPredicate_downward A lower selected c) convex
      inter_subset_left center star excludedNonempty
      (faceStarStrictClosedPatch_cover A lower selected c region inside)

/-- At a boundary cell, every covector outside the negative cone of
the actual active inequalities has zero literal local Morse complex. -/
theorem universalStrict_boundary_localMorse_acyclic
    (c : U) (neighborhood : Set E) (ξ : Module.Dual ℝ E)
    (convex : Convex ℝ neighborhood) (openNeighborhood : IsOpen neighborhood)
    (center : cellCenter (augmentedForms A) c.2 ∈ neighborhood)
    (inside : neighborhood ⊆
      localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2))
    (weak : ∀ j ∈ selected, (lower j : ℝ) ≤
      augmentedForms A j (cellCenter (augmentedForms A) c.2))
    (activeNonempty : (strictActive (augmentedForms A) lower selected
      (cellCenter (augmentedForms A) c.2)).Nonempty)
    (feasible : ∃ w : E, ∀ j : strictActive (augmentedForms A) lower selected
      (cellCenter (augmentedForms A) c.2), 0 < augmentedForms A j.val w)
    (outsideCone : -ξ ∉ PointedCone.hull ℝ (Set.range
      (fun j : strictActive (augmentedForms A) lower selected
        (cellCenter (augmentedForms A) c.2) => augmentedForms A j.val))) :
    ((universalLocalMorse A k c (universalNegativeHalf A c neighborhood ξ)).obj
      ((CochainComplex.singleFunctor (U ⥤ ModuleCat k) 0).obj
        (universalStrictCoefficientDiagram A k lower selected))).Acyclic := by
  obtain ⟨p,star,hp⟩ := shiftedNegativeHalf_excluded_starConvex
    (augmentedForms A) lower selected (cellCenter (augmentedForms A) c.2) ξ
    convex openNeighborhood center inside weak activeNonempty feasible outsideCone
  have outside : universalStrictClosedPredicate A lower selected c := by
    intro supported
    have strict := (mem_strictCellRegion_iff_of_mem_cell (augmentedForms A)
      lower selected _ _ (cellCenter_mem (augmentedForms A) c.2)).mpr supported
    obtain ⟨j,hj,equal⟩ := activeNonempty
    have impossible := strict j hj
    rw [equal] at impossible
    exact lt_irrefl _ impossible
  exact universalStrict_localMorse_acyclic_of_starConvex_complement
    A k lower selected c (universalNegativeHalf A c neighborhood ξ) outside
    (shiftedNegativeHalf_convex convex (cellCenter (augmentedForms A) c.2) ξ)
    ⟨p,hp.1⟩ (fun _ hy => inside hy.1) p star ⟨p,hp⟩

/-- The complete strict-support calculation: interior, boundary and
exterior cells all use the same literal local Morse functor and the
negative cone of the inequalities active at the actual center. -/
theorem universalStrict_localMorse_acyclic_outside_activeCone
    (c : U) (neighborhood : Set E) (ξ : Module.Dual ℝ E)
    (convex : Convex ℝ neighborhood) (openNeighborhood : IsOpen neighborhood)
    (center : cellCenter (augmentedForms A) c.2 ∈ neighborhood)
    (inside : neighborhood ⊆
      localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2))
    (feasible : ∃ w : E, ∀ j : strictActive (augmentedForms A) lower selected
      (cellCenter (augmentedForms A) c.2), 0 < augmentedForms A j.val w)
    (outsideCone : -ξ ∉ PointedCone.hull ℝ (Set.range
      (fun j : strictActive (augmentedForms A) lower selected
        (cellCenter (augmentedForms A) c.2) => augmentedForms A j.val))) :
    ((universalLocalMorse A k c (universalNegativeHalf A c neighborhood ξ)).obj
      ((CochainComplex.singleFunctor (U ⥤ ModuleCat k) 0).obj
        (universalStrictCoefficientDiagram A k lower selected))).Acyclic := by
  classical
  by_cases weak : ∀ j ∈ selected, (lower j : ℝ) ≤
      augmentedForms A j (cellCenter (augmentedForms A) c.2)
  · by_cases active : (strictActive (augmentedForms A) lower selected
        (cellCenter (augmentedForms A) c.2)).Nonempty
    · exact universalStrict_boundary_localMorse_acyclic A k lower selected c
        neighborhood ξ convex openNeighborhood center inside weak active feasible outsideCone
    · have supported : universalStrictSupport A lower selected c := by
        apply (mem_strictCellRegion_iff_of_mem_cell (augmentedForms A) lower selected
          _ _ (cellCenter_mem (augmentedForms A) c.2)).mp
        intro j hj
        by_contra notStrict
        exact active ⟨j,hj,le_antisymm (le_of_not_gt notStrict) (weak j hj)⟩
      apply universalStrict_interior_localMorse_acyclic A k lower selected c
        (universalNegativeHalf A c neighborhood ξ) supported
      exact universalFaceStarMeets_incidence_contractible A c
        (universalNegativeHalf A c neighborhood ξ)
        (shiftedNegativeHalf_convex convex (cellCenter (augmentedForms A) c.2) ξ)
        (shiftedNegativeHalf_nonempty_of_outsideActiveCone (augmentedForms A) lower selected
          (cellCenter (augmentedForms A) c.2) ξ openNeighborhood center feasible outsideCone)
        (fun _ h => inside h.1)
  · exact universalStrict_outside_localMorse_acyclic A k lower selected c
      (universalNegativeHalf A c neighborhood ξ) weak

end ToricPower.IntegralArrangement

end
