module

public import ToricPower.ArrangementFaceIntersections
public import ToricPower.CechPosetResolution

/-!
# The literal half-neighborhood and its cut face strata

An open region is intersected with every actual arrangement cell. A cell
is retained precisely when this intersection is nonempty; this agrees
with the closed-cell test by the proved closure formula. In particular
the negative half-ball is not replaced by a union of uncut cells.
Closed-cell intersections identify the finite cover nerve with the
actual meet condition in the local face star.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local notation "U" => UniversalIncidenceObject A
local notation "E" => Fin n → ℝ

/-- The genuine closed-cell patch in the chosen ambient region. -/
def universalFaceStarPatch (c : U) (region : Set E) (d : UniversalFaceStar A c) : Set E :=
  universalIncidenceClosedCell A d.val ∩ region

/-- Exactly the cells met by the region, with all lattice translates
present through the actual universal face star. -/
def universalFaceStarMeets (c : U) (region : Set E) (d : UniversalFaceStar A c) : Prop :=
  (universalFaceStarPatch A c region d).Nonempty

theorem universalFaceStarMeets_upward (c : U) (region : Set E)
    {d e : UniversalFaceStar A c} (h : d ≤ e)
    (hd : universalFaceStarMeets A c region d) : universalFaceStarMeets A c region e := by
  obtain ⟨x,hx,hr⟩ := hd
  exact ⟨x,h hx,hr⟩

/-- For an open cut, the closed-cell criterion retains exactly the
nonempty cut relative interiors. No boundary-only cells are inserted. -/
theorem universalFaceStarMeets_iff_openCell (c : U) (region : Set E)
    (openRegion : IsOpen region) (d : UniversalFaceStar A c) :
    universalFaceStarMeets A c region d ↔
      (cell (augmentedForms A) d.val.2.val.1 d.val.2.val.2 ∩ region).Nonempty := by
  constructor
  · rintro ⟨x,hx,hr⟩
    have closure : x ∈ closure (cell (augmentedForms A) d.val.2.val.1 d.val.2.val.2) := by
      rw [closure_cell _ (fun i => (augmentedForms A i).continuous_of_finiteDimensional)
        _ _ d.val.2.property.1]
      exact hx
    obtain ⟨y,hy,hcell⟩ := mem_closure_iff.mp closure region openRegion hr
    exact ⟨y,hcell,hy⟩
  · rintro ⟨x,hx,hr⟩
    exact ⟨x,cell_subset_closedCell _ _ _ hx,hr⟩

/-- The face category of the genuine intersections with an open region. -/
def UniversalRegionStar (c : U) (region : Set E) :=
  {d : UniversalFaceStar A c // universalFaceStarMeets A c region d}

instance universalRegionStar_finite (c : U) (region : Set E) :
    Finite (UniversalRegionStar A c region) :=
  inferInstanceAs (Finite {d : UniversalFaceStar A c // universalFaceStarMeets A c region d})

instance universalRegionStar_partialOrder (c : U) (region : Set E) :
    PartialOrder (UniversalRegionStar A c region) :=
  inferInstanceAs (PartialOrder {d : UniversalFaceStar A c // universalFaceStarMeets A c region d})

def universalRegionStarInclusion (c : U) (region : Set E) :
    UniversalRegionStar A c region ⥤ UniversalFaceStar A c where
  obj d := d.val
  map f := homOfLE f.le

/-- The cell containing a point in the open star is an actual coface. -/
theorem universalIncidenceOfPoint_mem_faceStar (c : U) {x : E}
    (inside : x ∈ localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) :
    c ≤ universalIncidenceOfPoint A x := by
  have center := localStar_point_mem_closedCell (augmentedForms A)
    (cellCenter (augmentedForms A) c.2) inside
  have contain := closedCell_of_point_subset (augmentedForms A)
    (ceilingVector (augmentedForms A) x) (integralIndices (augmentedForms A) x) center
  change closedCell (augmentedForms A) c.2.val.1 c.2.val.2 ⊆
    closedCell (augmentedForms A) (ceilingVector (augmentedForms A) x)
      (integralIndices (augmentedForms A) x)
  simpa only [cellCenter_ceilingVector,cellCenter_integralIndices] using contain

/-- These are actual relatively closed convex patches of the region. -/
theorem universalFaceStarPatch_convex (c : U) (region : Set E)
    (convex : Convex ℝ region) (d : UniversalFaceStar A c) :
    Convex ℝ (universalFaceStarPatch A c region d) :=
  (closedCell_convex _ _ _).inter convex

theorem universalFaceStarPatch_relativelyClosed (c : U) (region : Set E)
    (d : UniversalFaceStar A c) :
    IsClosed {x : region | x.val ∈ universalFaceStarPatch A c region d} := by
  have equal : {x : region | x.val ∈ universalFaceStarPatch A c region d} =
      {x : region | x.val ∈ universalIncidenceClosedCell A d.val} := by
    ext x
    exact and_iff_left x.property
  rw [equal]
  exact (closedCell_isClosed (augmentedForms A)
    (fun i => (augmentedForms A i).continuous_of_finiteDimensional) _ _).preimage
      continuous_subtype_val

/-- Every point in a local region is covered by its own genuine cell. -/
theorem universalFaceStarPatch_cover (c : U) (region : Set E)
    (inside : region ⊆ localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) :
    (⋃ d : UniversalFaceStar A c, universalFaceStarPatch A c region d) = region := by
  apply Subset.antisymm
  · exact iUnion_subset fun _ => inter_subset_right
  · intro x hx
    let d : UniversalFaceStar A c :=
      ⟨universalIncidenceOfPoint A x,universalIncidenceOfPoint_mem_faceStar A c (inside hx)⟩
    exact mem_iUnion.mpr ⟨d,cell_subset_closedCell _ _ _ (mem_cell_self _ x),hx⟩

/-- Closed cells preserve the actual meet, as subsets of the ambient space. -/
def universalFaceStarClosedInfHom (c : U) : InfHom (UniversalFaceStar A c) (Set E) where
  toFun d := universalIncidenceClosedCell A d.val
  map_inf' d e := universalFaceStarInf_closedCell A c d e

/-- Ordered tuple intersections retain all repetitions and all degrees. -/
theorem universalFaceStar_tupleMeet_mem (c : U) {q : ℕ}
    (tuple : Fin (q+1) → UniversalFaceStar A c) (x : E) :
    x ∈ universalIncidenceClosedCell A (FiniteCech.tupleMeet tuple).val ↔
      ∀ j, x ∈ universalIncidenceClosedCell A (tuple j).val := by
  change x ∈ universalFaceStarClosedInfHom A c
    (Finset.univ.inf' Finset.univ_nonempty tuple) ↔ _
  rw [map_finset_inf']
  have h : ({x} : Set E) ⊆ Finset.univ.inf' Finset.univ_nonempty
      (universalFaceStarClosedInfHom A c ∘ tuple) ↔
      ∀ j ∈ (Finset.univ : Finset (Fin (q+1))),
        ({x} : Set E) ⊆ universalFaceStarClosedInfHom A c (tuple j) :=
    Finset.le_inf'_iff Finset.univ_nonempty _
  simpa only [Set.singleton_subset_iff,Finset.mem_univ,forall_const,
    universalFaceStarClosedInfHom,InfHom.coe_mk] using h

/-- The geometric nerve condition is exactly the actual meet retained
by the cut region; it is not a center-based approximation. -/
theorem universalFaceStar_tuple_intersection_nonempty (c : U) (region : Set E) {q : ℕ}
    (tuple : Fin (q+1) → UniversalFaceStar A c) :
    (∃ x, ∀ j, x ∈ universalFaceStarPatch A c region (tuple j)) ↔
      universalFaceStarMeets A c region (FiniteCech.tupleMeet tuple) := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,(universalFaceStar_tupleMeet_mem A c tuple x).mpr (fun j => (hx j).1),
      (hx 0).2⟩
  · rintro ⟨x,hx,hr⟩
    exact ⟨x,fun j => ⟨(universalFaceStar_tupleMeet_mem A c tuple x).mp hx j,hr⟩⟩

/-- The exact negative half of an arbitrary local neighborhood. -/
def universalNegativeHalf (c : U) (neighborhood : Set E) (ξ : Module.Dual ℝ E) : Set E :=
  neighborhood ∩ {x | ξ (x-cellCenter (augmentedForms A) c.2) < 0}

theorem universalNegativeHalf_open (c : U) (neighborhood : Set E)
    (hopen : IsOpen neighborhood) (ξ : Module.Dual ℝ E) :
    IsOpen (universalNegativeHalf A c neighborhood ξ) :=
  hopen.inter (isOpen_lt
    (ξ.continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)) continuous_const)

/-- Every actual normal covector misses the whole base cell in its
negative half-neighborhood, including all boundary points of that cell. -/
theorem universalNegativeHalf_misses_base (c : U) (neighborhood : Set E)
    (ξ : Module.Dual ℝ E)
    (normal : ξ ∈ cellNormal (augmentedForms A) c.2.val.2) :
    ¬ universalFaceStarMeets A c (universalNegativeHalf A c neighborhood ξ)
      (universalFaceStarPoint A c) := by
  rintro ⟨x,hx,_,negative⟩
  have tangent := sub_mem_cellDirection (augmentedForms A) c.2.val.1 c.2.val.2
    (cell_subset_closedCell _ _ _ (cellCenter_mem _ c.2)) hx
  have annihilates : ξ ∈ (cellDirection (augmentedForms A) c.2.val.2).dualAnnihilator := by
    rwa [cellDirection_dualAnnihilator]
  have zero := (Submodule.mem_dualAnnihilator ξ).mp annihilates _ tangent
  exact (ne_of_lt negative) zero

end ToricPower.IntegralArrangement

end
