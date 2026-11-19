module

public import ToricPower.ArrangementHalfStar
public import ToricPower.CechSingular.FaceNerveContractible

/-! # Actual nerves of cut arrangement face stars

Convexity is required of the cut cells. The closed-complement union is
allowed to be star-convex. In both cases the conclusion concerns the
literal incidence realization used by the projective section complex.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open BondalThomsen.ConvexNerveReducedCochainAcyclicity

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local notation "U" => UniversalIncidenceObject A
local notation "E" => Fin n → ℝ

/-- The nerve of the genuine cell intersections with a nonempty convex
local region is contractible. -/
theorem universalFaceStarMeets_incidence_contractible (c : U) (region : Set E)
    (convex : Convex ℝ region) (nonempty : region.Nonempty)
    (inside : region ⊆ localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) :
    ContractibleSpace (incidenceRealization
      (fun d e : UniversalFaceStar A c => d ≤ e)
      (universalFaceStarMeets A c region)) := by
  obtain ⟨center,hcenter⟩ := nonempty
  exact FaceNerve.incidence_contractible_of_starConvex
    (universalFaceStarClosedInfHom A c) region region center
    (convex.starConvex hcenter) ⟨center,hcenter⟩
    (universalFaceStarPatch_convex A c region convex)
    (universalFaceStarPatch_relativelyClosed A c region)
    (universalFaceStarPatch_cover A c region inside)

/-- Relative closedness is retained when the ambient region is replaced
by a subset, including the nonconvex union of excluded half-spaces. -/
theorem universalFaceStarPatch_relativelyClosedWithin (c : U)
    (region subset : Set E) (contained : subset ⊆ region)
    (d : UniversalFaceStar A c) :
    IsClosed {x : subset | x.val ∈ universalFaceStarPatch A c region d} := by
  have equal : {x : subset | x.val ∈ universalFaceStarPatch A c region d} =
      {x : subset | x.val ∈ universalIncidenceClosedCell A d.val} := by
    ext x
    exact and_iff_left (contained x.property)
  rw [equal]
  exact (closedCell_isClosed (augmentedForms A)
    (fun i => (augmentedForms A i).continuous_of_finiteDimensional) _ _).preimage
      continuous_subtype_val

/-- A true downward-closed family of cells has its own actual face
nerve. Contractibility of its star-convex cut union gives contractibility
of that nerve, with no boundary-touching replacement of the family. -/
theorem closedUniversalFaceStarMeets_incidence_contractible (c : U)
    (region excluded : Set E) (Q : UniversalFaceStar A c → Prop)
    (downward : Antitone Q) (convex : Convex ℝ region)
    (contained : excluded ⊆ region) (center : E)
    (star : StarConvex ℝ center excluded) (nonempty : excluded.Nonempty)
    (cover : (⋃ d : {d : UniversalFaceStar A c // Q d},
      universalFaceStarPatch A c region d.val) = excluded) :
    ContractibleSpace (incidenceRealization
      (fun d e : {d : UniversalFaceStar A c // Q d} => d ≤ e)
      (fun d => universalFaceStarMeets A c region d.val)) := by
  letI : SemilatticeInf {d : UniversalFaceStar A c // Q d} :=
    Subtype.semilatticeInf (fun _ _ hd _ => downward inf_le_left hd)
  let cells : InfHom {d : UniversalFaceStar A c // Q d} (Set E) := {
    toFun := fun d => universalIncidenceClosedCell A d.val.val
    map_inf' := fun d e => universalFaceStarInf_closedCell A c d.val e.val }
  exact FaceNerve.incidence_contractible_of_starConvex cells region excluded center
    star nonempty
    (fun d => universalFaceStarPatch_convex A c region convex d.val)
    (fun d => universalFaceStarPatch_relativelyClosedWithin A c region excluded contained d.val)
    cover

end ToricPower.IntegralArrangement

end
