module
public import Papers.TenVertexSmallFacetBudgets
public import Papers.TenVertexLargeFacetReduction
public import Papers.PolygonDiagonalCounting
public import ActualFacetInducedGraph
public import TenGraphMask
public import EncodedNonedgeFacetCoverage
public import GraphGrowthConstraints
public import ActualGrowthTarget
public import GraphCandidateCoverage
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Basic

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: AllSixFacetBudgets.lean -/






@[expose] public section

/-!
# The complete numerical reduction when every facet has at most six vertices

The counts in this file belong to an actual convex four-polytope. In particular,
pentagonal ridges and triangular-prism facets are retained. A six-vertex facet
has one redundant polygon relation precisely when its polygon excess is three;
this assertion follows directly from relation-space dimension and diagonal
counting, without assuming a combinatorial catalogue.

The exact identities are `c = E - q - 2p + t` and `W = E + L - p`, where `L`
counts six-vertex facets and `t` counts those with polygon excess three. They
give all the inequalities used by the finite all-six-facet budget enumeration.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Finset
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeRelationBudget
open Papers.PolytopeFacetSurplus Papers.PolytopeMasterBudget
open Papers.PolytopeNonedgeAllocation Papers.PolytopeFaceNonedges
open Papers.PolytopeFaceRestriction

/-- Polygons of a prescribed size, as genuine two-faces. -/
def polygonSizeFaces {d : ℕ} (P : ConvexPolytope d) (k : ℕ) : Finset (Face P 2) :=
  Finset.univ.filter fun R => Nat.card (VerticesOn P R.val.carrier) = k

def pentagonalFaces {d : ℕ} (P : ConvexPolytope d) : Finset (Face P 2) :=
  polygonSizeFaces P 5

/-- The local count uses the actual two-faces contained in the facet. -/
def facetPolygonSizeCount {d : ℕ} (P : ConvexPolytope d) (F : Face P 3)
    (k : ℕ) : ℕ :=
  (Finset.univ.filter fun R : FaceBelow P F.val.carrier 2 =>
    Nat.card (VerticesOn P R.val.val.carrier) = k).card

/-- In the at-most-six regime this intrinsic condition characterizes the
triangular-prism facets. The numerical argument only needs the condition. -/
def threeExcessFacets {d : ℕ} (P : ConvexPolytope d) : Finset (Face P 3) :=
  Finset.univ.filter fun F => facetPolygonExcess P F = 3

theorem twice_facet_polygon_excess_le_diagonal_count {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3) :
    2 * facetPolygonExcess P F ≤ (facetDiagonalCount P F : ℤ) := by
  rw [facetDiagonalCount_eq_sum_polygon_diagonals,
    facetPolygonExcess_eq_sum_faceBelow, Finset.mul_sum]
  exact Finset.sum_le_sum fun R _ => polygon_diagonal_excess_bound P R.val

theorem actualPolygonRelationRank_add_four_le_facet_card {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3) :
    actualPolygonRelationRank P e F + 4 ≤ facetVertexCount P F := by
  have hle := Submodule.finrank_mono (actualPolygonRelationSpan_le P e F)
  have hdim := globalRelationSpace_finrank (vertexCoordinates P e)
    (actualFaceLabels P e F.val)
  rw [actualFaceLabels_rank, F.property, actualFaceLabels_card] at hdim
  change actualPolygonRelationRank P e F ≤ _ at hle
  change _ + (3 + 1) = facetVertexCount P F at hdim
  omega

/-- A rank-one polygon relation span has exactly one unit of polygon excess,
even when pentagons have not been excluded. -/
theorem actual_polygon_rank_one_excess_one {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (hPcard : 3 ≤ P.vertices.card) (F : Face P 3)
    (hone : actualPolygonRelationRank P e F = 1) :
    facetPolygonExcess P F = 1 := by
  have hdiagonal := twice_facet_polygon_excess_le_diagonal_count P F
  have htwo := actualPolygonRelationRank_one P e hPcard F hone
  have hbelow := actualPolygonRelationRank_le P e F
  rw [htwo] at hdiagonal
  rw [hone] at hbelow
  omega

/-- The complete six-vertex rank correction, including prism and pentagonal
pyramid cases. -/
theorem actual_rank_correction_of_card_le_six {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (hPcard : 3 ≤ P.vertices.card) (F : Face P 3)
    (hF : facetVertexCount P F ≤ 6) :
    (actualPolygonRelationRank P e F : ℤ) = facetPolygonExcess P F -
      if facetPolygonExcess P F = 3 then 1 else 0 := by
  by_cases hsmall : facetVertexCount P F ≤ 5
  · have hmax := facetPolygonExcess_le_one_of_card_le_five P F hsmall
    rw [if_neg (by omega)]
    simpa only [sub_zero] using
      actualPolygonRelationRank_eq_excess_of_card_le_five P e F hsmall
  have hcard : facetVertexCount P F = 6 := by omega
  have hmax := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  rw [hcard] at hmax
  have hrmax := actualPolygonRelationRank_add_four_le_facet_card P e F
  rw [hcard] at hrmax
  have hbelow := actualPolygonRelationRank_le P e F
  by_cases hz : actualPolygonRelationRank P e F = 0
  · rw [hz, (actualPolygonRelationRank_eq_zero_iff P e F).mp hz]
    norm_num
  by_cases ho : actualPolygonRelationRank P e F = 1
  · rw [ho, actual_polygon_rank_one_excess_one P e hPcard F ho]
    norm_num
  have hr : actualPolygonRelationRank P e F = 2 := by omega
  rw [hr] at hbelow ⊢
  split_ifs <;> omega

theorem threeExcessFacets_subset_six {d : ℕ} (P : ConvexPolytope d)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6) :
    threeExcessFacets P ⊆ sixVertexFacets P := by
  intro F hF
  have hg := (Finset.mem_filter.mp hF).2
  have hlo := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  have hhi := hfacets F
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by omega⟩

theorem actual_shared_count_of_card_le_six {d n : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4) (e : Fin n ≃ P.vertices)
    (hPcard : 3 ≤ P.vertices.card)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6) :
    sharedRelationCount P (actualPolygonRelationRank P e) =
      facetExcess P - polygonExcess P + (threeExcessFacets P).card := by
  have hsum : (∑ F : Face P 3, (actualPolygonRelationRank P e F : ℤ)) =
      2 * polygonExcess P - (threeExcessFacets P).card := by
    simp_rw [actual_rank_correction_of_card_le_six P e hPcard _ (hfacets _)]
    rw [Finset.sum_sub_distrib, sum_facet_polygon_excess P hP]
    simp [threeExcessFacets]
  unfold sharedRelationCount
  rw [hsum]
  ring

theorem facetExcess_eq_nonsimplicial_add_six {d : ℕ}
    (P : ConvexPolytope d)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6) :
    facetExcess P = ((nonsimplicialFacets P).card : ℤ) + (sixVertexFacets P).card := by
  have hpoint (F : Face P 3) : (facetVertexCount P F : ℤ) - 4 =
      (if F ∈ nonsimplicialFacets P then 1 else 0) +
        (if F ∈ sixVertexFacets P then 1 else 0) := by
    have hlo : 4 ≤ facetVertexCount P F := face_vertices_card_ge_dim_add_one P 3 F
    have hhi := hfacets F
    have hN : F ∈ nonsimplicialFacets P ↔ 4 < facetVertexCount P F :=
      mem_nonsimplicialFacets P F
    have hL : F ∈ sixVertexFacets P ↔ facetVertexCount P F = 6 := by
      simp [sixVertexFacets]
    simp only [hN, hL]
    split_ifs <;> omega
  change (∑ F : Face P 3, ((facetVertexCount P F : ℤ) - 4)) = _
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem polygon_card_le_five_of_facet_card_le_six {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6)
    (R : Face P 2) : Nat.card (VerticesOn P R.val.carrier) ≤ 5 := by
  have hcofaces := ridge_coface_card P 2 hP R
  change Nat.card (Coface P R.val.carrier 3) = 2 at hcofaces
  have hex : Nonempty (Coface P R.val.carrier 3) :=
    (Nat.card_pos_iff.mp (show 0 < Nat.card (Coface P R.val.carrier 3) by omega)).1
  obtain ⟨F⟩ := hex
  have hlt := polygon_card_lt_containing_facet P R F.val F.property
  have hbound := hfacets F.val
  omega

theorem polygonExcess_eq_quadrilaterals_add_twice_pentagons {d : ℕ}
    (P : ConvexPolytope d)
    (hpolygons : ∀ R : Face P 2, Nat.card (VerticesOn P R.val.carrier) ≤ 5) :
    polygonExcess P = ((quadrilateralFaces P).card : ℤ) +
      2 * (pentagonalFaces P).card := by
  have hpoint (R : Face P 2) : (Nat.card (VerticesOn P R.val.carrier) : ℤ) - 3 =
      (if R ∈ quadrilateralFaces P then 1 else 0) +
        2 * (if R ∈ pentagonalFaces P then 1 else 0) := by
    have hlo := face_vertices_card_ge_dim_add_one P 2 R
    have hhi := hpolygons R
    have hQ : R ∈ quadrilateralFaces P ↔ Nat.card (VerticesOn P R.val.carrier) = 4 := by
      simp [quadrilateralFaces]
    have hH : R ∈ pentagonalFaces P ↔ Nat.card (VerticesOn P R.val.carrier) = 5 := by
      simp [pentagonalFaces, polygonSizeFaces]
    simp only [hQ, hH]
    split_ifs <;> omega
  unfold polygonExcess
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Weighted ridge incidence counting. Every actual polygon has exactly two
facet cofaces, so an arbitrary integer weight is counted twice. -/
theorem sum_facet_polygon_weights {d : ℕ} (P : ConvexPolytope d)
    (hP : P.dim = 4) (w : Face P 2 → ℤ) :
    (∑ F : Face P 3, ∑ R : FaceBelow P F.val.carrier 2, w R.val) =
      2 * ∑ R : Face P 2, w R := by
  have hbelow (F : Face P 3) :
      (∑ R : FaceBelow P F.val.carrier 2, w R.val) =
        ∑ R : Face P 2, if R.val.carrier ⊆ F.val.carrier then w R else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (fun R => by simp) w).symm
  have habove (R : Face P 2) :
      (∑ F : Face P 3, if R.val.carrier ⊆ F.val.carrier then w R else 0) =
        2 * w R := by
    calc
      _ = ∑ _F : Coface P R.val.carrier 3, w R := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (fun F => by simp) (fun _ => w R)
      _ = 2 * w R := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card, ridge_coface_card P 2 hP R, Nat.cast_ofNat]
  simp_rw [hbelow]
  rw [Finset.sum_comm]
  simp_rw [habove]
  rw [Finset.mul_sum]

theorem sum_facet_polygon_size_counts {d : ℕ} (P : ConvexPolytope d)
    (hP : P.dim = 4) (k : ℕ) :
    (∑ F : Face P 3, (facetPolygonSizeCount P F k : ℤ)) =
      2 * (polygonSizeFaces P k).card := by
  have h := sum_facet_polygon_weights P hP
    (fun R => if Nat.card (VerticesOn P R.val.carrier) = k then 1 else 0)
  simpa only [Finset.sum_boole, facetPolygonSizeCount, polygonSizeFaces] using h

theorem facet_diagonal_count_of_polygon_card_le_five {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 5) :
    (facetDiagonalCount P F : ℤ) = 2 * facetPolygonExcess P F +
      facetPolygonSizeCount P F 5 := by
  have hlocal (R : FaceBelow P F.val.carrier 2) :
      (Nat.card (NonedgesOn P R.val.val.carrier) : ℤ) =
        2 * ((Nat.card (VerticesOn P R.val.val.carrier) : ℤ) - 3) +
          if Nat.card (VerticesOn P R.val.val.carrier) = 5 then 1 else 0 := by
    have hmin := face_vertices_card_ge_dim_add_one P 2 R.val
    have hmax := hpolygons R
    have hc := polygon_nonedge_count P R.val
    have hr : Nat.card (VerticesOn P R.val.val.carrier) = 3 ∨
        Nat.card (VerticesOn P R.val.val.carrier) = 4 ∨
          Nat.card (VerticesOn P R.val.val.carrier) = 5 := by omega
    rcases hr with hr | hr | hr <;> rw [hr] at hc ⊢ <;>
      norm_num [Nat.choose] at hc ⊢ <;> omega
  rw [facetDiagonalCount_eq_sum_polygon_diagonals,
    facetPolygonExcess_eq_sum_faceBelow]
  simp_rw [hlocal]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, facetPolygonSizeCount]

theorem allocatedFacetWeight_of_polygon_card_le_five {d : ℕ}
    (P : ConvexPolytope d) (F : Face P 3)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 5) :
    allocatedFacetWeight P F =
      ((facetVertexCount P F : ℚ) - 4) * ((facetVertexCount P F : ℚ) - 3) / 2 -
        (facetPolygonSizeCount P F 5 : ℚ) / 2 := by
  have hid := facet_weight_surplus_identity P F 0
  have hd := facet_diagonal_count_of_polygon_card_le_five P F hpolygons
  have hdQ : (facetDiagonalCount P F : ℚ) =
      2 * (facetPolygonExcess P F : ℚ) + facetPolygonSizeCount P F 5 := by
    exact_mod_cast hd
  unfold rankSurplus at hid
  norm_num only [Nat.cast_zero, add_zero, sub_zero] at hid
  nlinarith only [hid, hdQ]

/-- The exact total allocated nonedge weight for the whole all-six regime. -/
theorem allocated_weight_sum_of_card_le_six {d : ℕ}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6) :
    (∑ F : Face P 3, allocatedFacetWeight P F) =
      (facetExcess P : ℚ) + (sixVertexFacets P).card - (pentagonalFaces P).card := by
  have hpolygons := polygon_card_le_five_of_facet_card_le_six P hP hfacets
  have hpoint (F : Face P 3) : allocatedFacetWeight P F =
      ((facetVertexCount P F : ℚ) - 4) +
        (if F ∈ sixVertexFacets P then 1 else 0) -
          (facetPolygonSizeCount P F 5 : ℚ) / 2 := by
    rw [allocatedFacetWeight_of_polygon_card_le_five P F (fun R => hpolygons R.val)]
    have hmin : 4 ≤ facetVertexCount P F := face_vertices_card_ge_dim_add_one P 3 F
    have hmax := hfacets F
    have hmem : F ∈ sixVertexFacets P ↔ facetVertexCount P F = 6 := by
      simp [sixVertexFacets]
    have hc : facetVertexCount P F = 4 ∨ facetVertexCount P F = 5 ∨
        facetVertexCount P F = 6 := by omega
    rcases hc with hc | hc | hc <;> simp [hmem, hc] <;> ring
  have hE : (∑ F : Face P 3, ((facetVertexCount P F : ℚ) - 4)) =
      (facetExcess P : ℚ) := by
    unfold facetExcess facetVertexCount
    push_cast
    rfl
  have hpZ := sum_facet_polygon_size_counts P hP 5
  have hpQ : (∑ F : Face P 3, (facetPolygonSizeCount P F 5 : ℚ)) =
      2 * (pentagonalFaces P).card := by exact_mod_cast hpZ
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hE, ← Finset.sum_div, hpQ]
  simp

/-- All intrinsic parameters of the six-vertex residual. `E` is a natural
number because it is the nonsimplicial count plus the six-vertex count. -/
structure AllSixFacetBudget where
  m : ℕ
  E : ℕ
  q : ℕ
  p : ℕ
  L : ℕ
  t : ℕ
  deriving DecidableEq

def AllSixFacetBudget.Admissible (B : AllSixFacetBudget) : Prop :=
  10 ≤ B.m ∧ 1 ≤ B.L ∧ B.L + 10 ≤ B.E ∧ B.E ≤ B.m + B.L ∧
    B.m + B.E ≤ 26 ∧ B.t ≤ B.L ∧ B.q + 2 * B.p + 9 ≤ B.E + B.t ∧
      2 * B.E + B.m + B.L ≤ 35 + B.q + 3 * B.p

instance (B : AllSixFacetBudget) : Decidable B.Admissible := by
  unfold AllSixFacetBudget.Admissible
  infer_instance

def actualAllSixFacetBudget {d : ℕ} (P : ConvexPolytope d) : AllSixFacetBudget where
  m := Nat.card (Face P 3)
  E := (nonsimplicialFacets P).card + (sixVertexFacets P).card
  q := (quadrilateralFaces P).card
  p := (pentagonalFaces P).card
  L := (sixVertexFacets P).card
  t := (threeExcessFacets P).card

/-- Every actual residual with a six-vertex facet and no larger facet satisfies
the complete numerical predicate. No prism or pentagon branch is omitted. -/
theorem actual_all_six_budget_admissible {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6)
    (hsix : (sixVertexFacets P).Nonempty) :
    (actualAllSixFacetBudget P).Admissible := by
  have hE := facetExcess_eq_nonsimplicial_add_six P hfacets
  have hpolygons := polygon_card_le_five_of_facet_card_le_six P hP hfacets
  have hg := polygonExcess_eq_quadrilaterals_add_twice_pentagons P hpolygons
  have hcount := sparseSharedRowIndex_card P e
  rw [actual_shared_count_of_card_le_six P hP e (by omega) hfacets, hE, hg] at hcount
  have hbound := actualSharedRowIndex_count_bound P hP e
  rw [← sparseSharedRowIndex_card_eq, hn, hE] at hbound
  norm_num only [show Nat.choose 10 2 = 45 by decide, Nat.cast_ofNat] at hbound
  have hweights := allocated_weights_le_nonedge_card P hP
  rw [allocated_weight_sum_of_card_le_six P hP hfacets] at hweights
  have hweightsZ : facetExcess P + (sixVertexFacets P).card - (pentagonalFaces P).card ≤
      (Nat.card (Nonedge P) : ℤ) := by exact_mod_cast hweights
  have heuler := actual_excess_identity P hP
  rw [hn, hE, hg] at heuler
  rw [hE] at hweightsZ
  norm_num only [show Nat.choose 10 2 = 45 by decide, Nat.cast_ofNat] at heuler
  have hcard := Finset.card_le_card (Finset.subset_univ (nonsimplicialFacets P))
  simp only [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcard
  have hL := Finset.card_pos.mpr hsix
  have ht := Finset.card_le_card (threeExcessFacets_subset_six P hfacets)
  unfold AllSixFacetBudget.Admissible actualAllSixFacetBudget
  dsimp only
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart0

section BundlePart1
/- Source: ActualComplementGraph.lean -/





@[expose] public section

/-!
# Actual complement graphs in the exhaustive graph catalogue

The forty-five graph slots are exactly the unordered pairs of the ten
vertex labels. Their two-bit masks agree with the facet universe. The
complement of an actual nonsimple four-polytope therefore gives a valid
degree-at-most-four input to the complete graph catalogue.
-/

noncomputable section
namespace Papers.RationalityTen.ActualComplementGraph

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeNonedgeAllocation
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry ActualFacetInducedGraph
open TenGraphEdges

theorem edgeMask_set (e : Fin 45) : maskSet (edgeMask e) = {first e, second e} := by
  have h : ∀ e : Fin 45, maskSet (edgeMask e) = {first e, second e} := by decide +kernel
  exact h e

theorem edgeMask_membership (e : Fin 45) (v : Fin 10) :
    (edgeMask e).testBit v.val = true ↔ incidence e v = true := by
  rw [← mem_maskSet, edgeMask_set]
  simp only [Finset.mem_insert, Finset.mem_singleton, incidence, decide_eq_true_eq]

theorem edgeMask_card (e : Fin 45) : (maskSet (edgeMask e)).card = 2 := by
  rw [edgeMask_set]
  exact Finset.card_pair (endpoints_distinct e)

theorem edgeMask_injective : Function.Injective edgeMask := by
  intro a b hab
  apply incidence_ext
  intro v
  apply Bool.eq_iff_iff.mpr
  rw [← edgeMask_membership, ← edgeMask_membership, hab]

theorem exists_edgeMask {m : ℕ} (hm : m < 1024) (hcard : (maskSet m).card = 2) :
    ∃ e : Fin 45, edgeMask e = m := by
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hcard
  refine ⟨encode a b, maskSet_injective (edgeMask_lt _) hm ?_⟩
  ext v
  rw [mem_maskSet, edgeMask_membership, encode_incidence a b v hab, hset]
  simp only [decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]

theorem total_degree (v : Fin 10) :
    ((Finset.univ : Finset (Fin 45)).filter fun e => incidence e v = true).card = 9 := by
  have h : ∀ v : Fin 10,
      ((Finset.univ : Finset (Fin 45)).filter fun e => incidence e v = true).card = 9 := by
    decide +kernel
  exact h v

def presentEdges (G : Finset ℕ) : Finset (Fin 45) :=
  Finset.univ.filter fun e => edgeMask e ∈ G

def complementEdges (G : Finset ℕ) : Finset (Fin 45) := Finset.univ \ presentEdges G

@[simp] theorem mem_presentEdges (G : Finset ℕ) (e : Fin 45) :
    e ∈ presentEdges G ↔ edgeMask e ∈ G := by
  simp only [presentEdges, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_complementEdges (G : Finset ℕ) (e : Fin 45) :
    e ∈ complementEdges G ↔ edgeMask e ∉ G := by
  simp only [complementEdges, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_presentEdges]

theorem presentEdges_image (G : Finset ℕ)
    (hbound : ∀ e ∈ G, e < 1024) (hcard : ∀ e ∈ G, (maskSet e).card = 2) :
    (presentEdges G).image edgeMask = G := by
  ext m
  constructor
  · intro hm
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm
    exact (mem_presentEdges G e).mp he
  · intro hm
    obtain ⟨e, rfl⟩ := exists_edgeMask (hbound m hm) (hcard m hm)
    exact Finset.mem_image.mpr ⟨e, (mem_presentEdges G e).mpr hm, rfl⟩

theorem presentEdges_card (G : Finset ℕ)
    (hbound : ∀ e ∈ G, e < 1024) (hcard : ∀ e ∈ G, (maskSet e).card = 2) :
    (presentEdges G).card = G.card := by
  calc
    _ = ((presentEdges G).image edgeMask).card :=
      (Finset.card_image_of_injective _ edgeMask_injective).symm
    _ = _ := congrArg Finset.card (presentEdges_image G hbound hcard)

theorem complementEdges_card (G : Finset ℕ)
    (hbound : ∀ e ∈ G, e < 1024) (hcard : ∀ e ∈ G, (maskSet e).card = 2) :
    (complementEdges G).card = 45 - G.card := by
  rw [complementEdges, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, presentEdges_card G hbound hcard]

theorem present_incidence_image (G : Finset ℕ)
    (hbound : ∀ e ∈ G, e < 1024) (hcard : ∀ e ∈ G, (maskSet e).card = 2)
    (v : Fin 10) :
    ((presentEdges G).filter fun e => incidence e v = true).image edgeMask =
      G.filter fun m => m.testBit v.val = true := by
  ext m
  constructor
  · intro hm
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨heG, heV⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr
      ⟨(mem_presentEdges G e).mp heG, (edgeMask_membership e v).mpr heV⟩
  · intro hm
    obtain ⟨hmG, hmV⟩ := Finset.mem_filter.mp hm
    obtain ⟨e, rfl⟩ := exists_edgeMask (hbound m hmG) (hcard m hmG)
    exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr
      ⟨(mem_presentEdges G e).mpr hmG, (edgeMask_membership e v).mp hmV⟩, rfl⟩

theorem present_incidence_card (G : Finset ℕ)
    (hbound : ∀ e ∈ G, e < 1024) (hcard : ∀ e ∈ G, (maskSet e).card = 2)
    (v : Fin 10) :
    ((presentEdges G).filter fun e => incidence e v = true).card =
      (G.filter fun m => m.testBit v.val = true).card := by
  calc
    _ = (((presentEdges G).filter fun e => incidence e v = true).image edgeMask).card :=
      (Finset.card_image_of_injective _ edgeMask_injective).symm
    _ = _ := congrArg Finset.card (present_incidence_image G hbound hcard v)

theorem complement_present_degree (G : Finset ℕ) (v : Fin 10) :
    ((complementEdges G).filter fun e => incidence e v = true).card +
      ((presentEdges G).filter fun e => incidence e v = true).card = 9 := by
  have hpart : ((complementEdges G).filter fun e => incidence e v = true) =
      (Finset.univ.filter fun e => incidence e v = true) \
        ((presentEdges G).filter fun e => incidence e v = true) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      mem_complementEdges, mem_presentEdges]
    tauto
  rw [hpart]
  have hsub : (presentEdges G).filter (fun e => incidence e v = true) ⊆
      Finset.univ.filter (fun e => incidence e v = true) :=
    Finset.filter_subset_filter _ (Finset.subset_univ _)
  rw [Finset.card_sdiff_of_subset hsub]
  have hle := Finset.card_le_card hsub
  rw [total_degree] at hle ⊢
  omega

theorem degree_toList (S : Finset (Fin 45)) (v : Fin 10) :
    GraphCatalogueCore.degree incidence S.toList v =
      (S.filter fun e => incidence e v = true).card := by
  rw [GraphCatalogueCore.degree, ← List.toFinset_card_of_nodup (S.nodup_toList.filter _)]
  congr 1
  ext e
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_toList, Finset.mem_filter]

/-- The actual complement graph satisfies the graph catalogue's complete
target predicate, with no preselected graph or enumeration assumption. -/
theorem actual_complement_valid {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v) :
    GraphCatalogueCore.Valid incidence 4
      (complementEdges (literalGraphEdges cells E.family)).toList := by
  refine ⟨Finset.nodup_toList _, ?_⟩
  intro v
  rw [degree_toList]
  have hsum := complement_present_degree (literalGraphEdges cells E.family) v
  rw [present_incidence_card _
    (fun e he => literalGraphEdges_bound cells E.family hwell he)
    (fun e he => literalGraphEdges_two_vertices cells E hP he) v] at hsum
  have hmin := literal_nonsimple_degree_ge_five cells hwell E hP hnonsimple v
  omega

theorem actual_complement_length {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4) :
    (complementEdges (literalGraphEdges cells E.family)).toList.length =
      45 - Nat.card (Face P 1) := by
  rw [Finset.length_toList, complementEdges_card _
    (fun e he => literalGraphEdges_bound cells E.family hwell he)
    (fun e he => literalGraphEdges_two_vertices cells E hP he),
    literalGraphEdges_card cells hwell E hP]

theorem actual_complement_length_nonedges {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4) :
    (complementEdges (literalGraphEdges cells E.family)).toList.length =
      Nat.card (Nonedge P) := by
  have hn : P.vertices.card = 10 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr lab
  rw [actual_complement_length cells hwell E hP, nonedge_card_eq, hn]
  norm_num [Nat.choose]

end Papers.RationalityTen.ActualComplementGraph

end
end
end BundlePart1

section BundlePart2
/- Source: ActualComplementNonedgeCoverage.lean -/





@[expose] public section

/-!
# Internal missing pairs inside the actual complement graph

This connects the exact internal-nonedge cardinality to the graph catalogue's
forty-five pair slots. Equality of the two counts makes every complement
edge a mandatory covered pair in the finite growth search.
-/

noncomputable section
namespace Papers.RationalityTen.ActualComplementGraph

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry ActualFacetInducedGraph
open ChirotopeDensity EncodedNonedgeFacetCoverage TenGraphEdges

theorem internalNonedgeMasks_subset_complement {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4) :
    internalNonedgeMasks cells E.family ⊆
      (complementEdges (literalGraphEdges cells E.family)).image edgeMask := by
  intro m hm
  obtain ⟨i, hi, hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨hbound, hcard, hsub, hnot⟩ := Finset.mem_filter.mp hm
  have hglobal : m ∉ literalGraphEdges cells E.family := by
    intro hmem
    have hlocal : m ∈ (cells i).edges.toFinset := by
      rw [literal_facet_edges_induced cells hwell E hP i hi]
      exact Finset.mem_filter.mpr ⟨hmem, hsub⟩
    exact hnot (List.mem_toFinset.mp hlocal)
  obtain ⟨e, rfl⟩ := exists_edgeMask (Finset.mem_range.mp hbound) hcard
  exact Finset.mem_image.mpr ⟨e, (mem_complementEdges _ e).mpr hglobal, rfl⟩

/-- In particular, the `D=E` graph rows require every missing global pair
to occur inside at least one selected nonsimplicial facet. -/
theorem all_complement_edges_covered_of_equal_count {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (hcount : (complementEdges (literalGraphEdges cells E.family)).toList.length =
      (nonsimplicialFacets P).card) :
    internalNonedgeMasks cells E.family =
      (complementEdges (literalGraphEdges cells E.family)).image edgeMask := by
  apply Finset.eq_of_subset_of_card_le
    (internalNonedgeMasks_subset_complement cells hwell E hP)
  rw [Finset.card_image_of_injective _ edgeMask_injective,
    literal_internal_nonedge_card cells hwell E hP hfacets]
  have hc : (complementEdges (literalGraphEdges cells E.family)).card =
      (nonsimplicialFacets P).card := by
    simpa only [Finset.length_toList] using hcount
  exact hc.le

end Papers.RationalityTen.ActualComplementGraph

end
end
end BundlePart2

section BundlePart3
/- Source: SixFacetNonedgeCoverage.lean -/





@[expose] public section

/-!
# Exact internal nonedge coverage for all six-vertex facet budgets

The union of facet-internal nonedges has cardinal `E + L - p`: `E` is
the total facet excess, `L` counts six-vertex facets, and `p` counts
pentagonal ridges. This includes every six-vertex facet type. In particular,
the graph-conditioned row with `E = 11`, `L = 1`, and `p = 0` covers
exactly twelve missing global pairs.
-/

noncomputable section
namespace Papers.RationalityTen.SixFacetNonedgeCoverage

open Finset Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus Papers.PolytopeNonedgeAllocation
open ChirotopeDensity EncodedNonedgeFacetCoverage ActualComplementGraph
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry ActualFacetInducedGraph
open TenGraphEdges

/-- The shifted equality avoids any truncated subtraction in the budget. -/
theorem covered_nonedge_card_add_pentagons {d : ℕ} (P : ConvexPolytope d)
    (hP : P.dim = 4) (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6) :
    (coveredNonedges P).card + (actualAllSixFacetBudget P).p =
      (actualAllSixFacetBudget P).E + (actualAllSixFacetBudget P).L := by
  have h := (allocated_weight_sum_eq_covered_nonedge_card P hP).symm.trans
    (allocated_weight_sum_of_card_le_six P hP hfacets)
  rw [facetExcess_eq_nonsimplicial_add_six P hfacets] at h
  push_cast at h
  have hQ : ((coveredNonedges P).card : ℚ) + (pentagonalFaces P).card =
      (nonsimplicialFacets P).card + (sixVertexFacets P).card +
        (sixVertexFacets P).card := by linarith
  change (coveredNonedges P).card + (pentagonalFaces P).card =
    (nonsimplicialFacets P).card + (sixVertexFacets P).card + (sixVertexFacets P).card
  exact_mod_cast hQ

theorem literal_internal_nonedge_card_add_pentagons {d c : ℕ}
    {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (cells : Fin c → ConcreteGrowth.Cell) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6) :
    (internalNonedgeMasks cells E.family).card + (actualAllSixFacetBudget P).p =
      (actualAllSixFacetBudget P).E + (actualAllSixFacetBudget P).L := by
  rw [literal_internal_nonedge_card_eq_covered cells hwell E]
  exact covered_nonedge_card_add_pentagons P hP hfacets

theorem literal_internal_nonedge_card_six {d c : ℕ}
    {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (cells : Fin c → ConcreteGrowth.Cell) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6) :
    (internalNonedgeMasks cells E.family).card =
      (actualAllSixFacetBudget P).E + (actualAllSixFacetBudget P).L -
        (actualAllSixFacetBudget P).p := by
  have h := literal_internal_nonedge_card_add_pentagons cells hwell E hP hfacets
  omega

/-- Equality with the global complement count forces every missing global
pair into a facet, for all six-vertex types and all admissible budgets. -/
theorem all_six_complement_edges_covered_of_equal_count {d c : ℕ}
    {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (cells : Fin c → ConcreteGrowth.Cell) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6)
    (hcount : (complementEdges (literalGraphEdges cells E.family)).toList.length =
      (actualAllSixFacetBudget P).E + (actualAllSixFacetBudget P).L -
        (actualAllSixFacetBudget P).p) :
    internalNonedgeMasks cells E.family =
      (complementEdges (literalGraphEdges cells E.family)).image edgeMask := by
  apply Finset.eq_of_subset_of_card_le
    (internalNonedgeMasks_subset_complement cells hwell E hP)
  rw [Finset.card_image_of_injective _ edgeMask_injective,
    literal_internal_nonedge_card_six cells hwell E hP hfacets]
  have hc : (complementEdges (literalGraphEdges cells E.family)).card =
      (actualAllSixFacetBudget P).E + (actualAllSixFacetBudget P).L -
        (actualAllSixFacetBudget P).p := by
    simpa only [Finset.length_toList] using hcount
  exact hc.le

end Papers.RationalityTen.SixFacetNonedgeCoverage

end
end
end BundlePart3

section BundlePart4
/- Source: ActualGraphGrowthTarget.lean -/






@[expose] public section

/-!
# Actual convex boundaries satisfy the graph-conditioned target predicate

`LiteralData` describes exact finite encodings of cell incidences. The
target theorem then derives all geometric search premises from one actual
boundary encoding. In particular, the required edges are the complete
actual graph, and missing features count the union of actual facet-internal
nonedges. Finite producer output is not assumed to cover actual facets.
-/

noncomputable section
namespace Papers.RationalityTen.ActualGraphGrowthTarget

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus
open ChirotopeDensity
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualFacetInducedGraph ActualComplementGraph EncodedNonedgeFacetCoverage
open GraphGrowthConstraints GrowthBitsets TenGraphEdges

variable {c k d : ℕ}

/-- Field-by-field semantics for the finite masks used by the graph checker.
These are equalities of finite data, with no convexity or catalogue premise. -/
structure LiteralData (D : Problem c 1024 45 10 k)
    (cells : Fin c → ConcreteGrowth.Cell) : Prop where
  ridges : ∀ i, D.ridgeList i = ConcreteGrowth.ridgeList cells i
  compatible : ∀ i j, D.compatible i j = ConcreteGrowth.compatible (cells i) (cells j)
  kind : ∀ i, D.kind i = (cells i).kind
  vertices : ∀ a i, (D.vertexRows a).testBit i.val = (cells i).vertices.testBit a.val
  edges : ∀ i q, (D.edges i).testBit q.val = true ↔ edgeMask q ∈ (cells i).edges
  missing : ∀ i q, (D.missing i).testBit q.val = true ↔
    edgeMask q ∈ cellInternalNonedgeMasks (cells i)

theorem LiteralData.edgeUnion_iff {D : Problem c 1024 45 10 k}
    {cells : Fin c → ConcreteGrowth.Cell} (H : LiteralData D cells)
    (S : Finset (Fin c)) (q : Fin 45) :
    (edgeUnion D S.toList).testBit q.val = true ↔ edgeMask q ∈ literalGraphEdges cells S := by
  rw [edgeUnion, ← bitAt_eq_testBit, bitAt_unionValues]
  simp only [bitAt_eq_testBit, H.edges, Finset.mem_toList,
    literalGraphEdges, Finset.mem_biUnion, List.mem_toFinset]

theorem LiteralData.missingUnion_iff {D : Problem c 1024 45 10 k}
    {cells : Fin c → ConcreteGrowth.Cell} (H : LiteralData D cells)
    (S : Finset (Fin c)) (q : Fin 45) :
    (missingUnion D S.toList).testBit q.val = true ↔
      edgeMask q ∈ internalNonedgeMasks cells S := by
  rw [missingUnion, ← bitAt_eq_testBit, bitAt_unionValues]
  simp only [bitAt_eq_testBit, H.missing, Finset.mem_toList,
    internalNonedgeMasks, Finset.mem_biUnion]

theorem mask_card_eq_pair_card (bits : ℕ) (pairs : Finset ℕ)
    (hbit : ∀ q : Fin 45, bits.testBit q.val = true ↔ edgeMask q ∈ pairs)
    (hbound : ∀ m ∈ pairs, m < 1024)
    (htwo : ∀ m ∈ pairs, (maskSet m).card = 2) :
    FiniteMaskSets.card 45 bits = pairs.card := by
  have hset : (FiniteMaskSets.elements 45 bits).toFinset = presentEdges pairs := by
    ext q
    simp only [List.mem_toFinset, FiniteMaskSets.mem_elements, mem_presentEdges, hbit]
  rw [FiniteMaskSets.card, ← List.toFinset_card_of_nodup
    (FiniteMaskSets.elements_nodup 45 bits), hset]
  exact presentEdges_card pairs hbound htwo

theorem LiteralData.missingUnion_card {D : Problem c 1024 45 10 k}
    {cells : Fin c → ConcreteGrowth.Cell} (H : LiteralData D cells)
    (S : Finset (Fin c)) :
    FiniteMaskSets.card 45 (missingUnion D S.toList) =
      (internalNonedgeMasks cells S).card := by
  apply mask_card_eq_pair_card _ _ (H.missingUnion_iff S)
  · intro m hm
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  · intro m hm
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hm
    exact (Finset.mem_filter.mp hi).2.1

theorem LiteralData.vertexCount_eq {D : Problem c 1024 45 10 k}
    {cells : Fin c → ConcreteGrowth.Cell} (H : LiteralData D cells)
    (S : Finset (Fin c)) (a : Fin 10) :
    vertexCount D S.toList a =
      (S.filter fun i => a ∈ (decodeCell (cells i)).vertices).card := by
  rw [vertexCount, ← List.toFinset_card_of_nodup (S.nodup_toList.filter _)]
  congr 1
  ext i
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_toList,
    Finset.mem_filter, decodeCell, mem_maskSet, H.vertices]

/-- Assemble the exact target used by graph-conditioned exhaustive growth.
The only numerical inputs are actual kind counts and the independently
proved cardinality of the internal-nonedge union. -/
theorem actual_target {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (D : Problem c 1024 45 10 k) (cells : Fin c → ConcreteGrowth.Cell)
    (H : LiteralData D cells) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hnonsimple : ∀ a : P.vertices, ¬ IsSimpleVertex P a)
    (hquota : ∀ j : Fin k, (E.family.filter fun i => D.kind i = j.val).card = D.quota j.val)
    (hminimum : D.minimumIncidence = 5)
    (hgraph : ∀ q : Fin 45, D.requiredEdges.testBit q.val = true ↔
      edgeMask q ∈ literalGraphEdges cells E.family)
    (hmissing : (internalNonedgeMasks cells E.family).card = D.missingCount) :
    GraphGrowthConstraints.Target D E.family.toList := by
  have hbudget (j : ℕ) : (E.family.filter fun i => D.kind i = j).card ≤ D.quota j := by
    by_cases hj : j < k
    · exact (hquota ⟨j, hj⟩).le
    · have hempty : E.family.filter (fun i => D.kind i = j) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i _ heq
        exact hj (heq ▸ D.kind_lt i)
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
  refine ⟨?_, E.family.nodup_toList, ?_, ?_, ?_, ?_⟩
  · have hr := funext H.ridges
    have hc := funext fun i => funext (H.compatible i)
    have hk := funext H.kind
    change GrowthRenaming.Target (fun i => SparseGrowthDAG.has (D.ridgeList i))
      D.compatible D.kind D.quota E.family.toList
    rw [hr, hc, hk]
    apply LiteralMaskGeometry.actual_literal_target cells hwell E hP
    intro j
    simpa only [H.kind] using hbudget j
  · intro j
    rw [ActualGrowthTarget.kindCount_toList]
    exact hquota j
  · intro a
    rw [hminimum, H.vertexCount_eq]
    exact ActualGrowthTarget.actual_nonsimple_incidence E hP hnonsimple a
  · intro q hq
    exact (H.edgeUnion_iff E.family q).mpr ((hgraph q).mp hq)
  · rw [H.missingUnion_card, hmissing]

/-- For the all-small branch the union cardinality is exactly the number
of nonsimplicial facets, already proved from actual nonedge allocation. -/
theorem actual_small_target {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (D : Problem c 1024 45 10 k) (cells : Fin c → ConcreteGrowth.Cell)
    (H : LiteralData D cells) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hnonsimple : ∀ a : P.vertices, ¬ IsSimpleVertex P a)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (hquota : ∀ j : Fin k, (E.family.filter fun i => D.kind i = j.val).card = D.quota j.val)
    (hminimum : D.minimumIncidence = 5)
    (hgraph : ∀ q : Fin 45, D.requiredEdges.testBit q.val = true ↔
      edgeMask q ∈ literalGraphEdges cells E.family)
    (hmissing : D.missingCount = (nonsimplicialFacets P).card) :
    GraphGrowthConstraints.Target D E.family.toList := by
  apply actual_target D cells H hwell E hP hnonsimple hquota hminimum hgraph
  rw [hmissing]
  exact literal_internal_nonedge_card cells hwell E hP hfacets

/-- The corresponding all-six target uses the complete nonedge-allocation
identity, including the pentagonal correction. -/
theorem actual_six_target {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (D : Problem c 1024 45 10 k) (cells : Fin c → ConcreteGrowth.Cell)
    (H : LiteralData D cells) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hnonsimple : ∀ a : P.vertices, ¬ IsSimpleVertex P a)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6)
    (hquota : ∀ j : Fin k, (E.family.filter fun i => D.kind i = j.val).card = D.quota j.val)
    (hminimum : D.minimumIncidence = 5)
    (hgraph : ∀ q : Fin 45, D.requiredEdges.testBit q.val = true ↔
      edgeMask q ∈ literalGraphEdges cells E.family)
    (hmissing : D.missingCount = (actualAllSixFacetBudget P).E +
      (actualAllSixFacetBudget P).L - (actualAllSixFacetBudget P).p) :
    GraphGrowthConstraints.Target D E.family.toList := by
  apply actual_target D cells H hwell E hP hnonsimple hquota hminimum hgraph
  rw [hmissing]
  exact SixFacetNonedgeCoverage.literal_internal_nonedge_card_six cells hwell E hP hfacets

end Papers.RationalityTen.ActualGraphGrowthTarget

end
end
end BundlePart4

section BundlePart5
/- Source: ActualGraphNormalization.lean -/




@[expose] public section

/-!
# Graph-catalogue renamings are actual relabelings of the vertices

The graph catalogue supplies incidence-preserving bijections of its forty-five
edge slots and ten vertex slots. Their vertex maps act on an actual vertex
labeling. The resulting complement graph is exactly the recorded renamed
edge list. Thus graph isomorphism witnesses normalize genuine polytopes,
without assuming a geometric interpretation of an arbitrary permutation.
-/

noncomputable section
namespace Papers.RationalityTen.ActualGraphNormalization

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry ActualFacetInducedGraph
open ActualComplementGraph TenGraphEdges GrowthRenaming GraphCatalogueCore

def bijectionEquiv {α : Type} (p : Bijection α) : Equiv.Perm α where
  toFun := p.forward
  invFun := p.inverse
  left_inv := p.left_inverse
  right_inv := p.right_inverse

theorem faceLabels_relabel {d n k : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (σ : Equiv.Perm (Fin n)) (F : Face P k) :
    faceLabels P (lab.trans σ) F = (faceLabels P lab F).image σ := by
  simp only [faceLabels, Finset.image_image]
  rfl

theorem actualGraphEdges_relabel {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (σ : Equiv.Perm (Fin n)) :
    actualGraphEdges P (lab.trans σ) =
      (actualGraphEdges P lab).image (fun S => S.image σ) := by
  unfold actualGraphEdges
  rw [Finset.image_image]
  apply Finset.image_congr
  intro F _
  exact faceLabels_relabel P lab σ F

theorem edgeMask_relabel (p : IncidenceRenaming incidence) (e : Fin 45) :
    maskSet (edgeMask (p.cells.forward e)) =
      (maskSet (edgeMask e)).image (bijectionEquiv p.ridgeMap) := by
  ext v
  have hi := p.incidence e (p.ridgeMap.inverse v)
  rw [p.ridgeMap.right_inverse] at hi
  constructor
  · intro hv
    have he : incidence e (p.ridgeMap.inverse v) = true := by
      rw [← hi]
      exact (edgeMask_membership _ v).mp ((mem_maskSet _ v).mp hv)
    exact Finset.mem_image.mpr ⟨p.ridgeMap.inverse v,
      (mem_maskSet _ _).mpr ((edgeMask_membership e _).mpr he), p.ridgeMap.right_inverse v⟩
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    change p.ridgeMap.forward w = v at hwv
    subst v
    apply (mem_maskSet _ _).mpr
    apply (edgeMask_membership _ _).mpr
    rw [p.incidence]
    exact (edgeMask_membership e w).mp ((mem_maskSet _ w).mp hw)

/-- The actual complement on the fixed forty-five slots, independent of
which finite facet universe is used to encode the boundary. -/
def intrinsicComplement {d : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin 10) : Finset (Fin 45) :=
  Finset.univ.filter fun e => maskSet (edgeMask e) ∉ actualGraphEdges P lab

@[simp] theorem mem_intrinsicComplement {d : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin 10) (e : Fin 45) :
    e ∈ intrinsicComplement P lab ↔ maskSet (edgeMask e) ∉ actualGraphEdges P lab := by
  simp only [intrinsicComplement, Finset.mem_filter, Finset.mem_univ, true_and]

theorem intrinsicComplement_relabel_membership {d : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin 10) (p : IncidenceRenaming incidence) (e : Fin 45) :
    p.cells.forward e ∈ intrinsicComplement P (lab.trans (bijectionEquiv p.ridgeMap)) ↔
      e ∈ intrinsicComplement P lab := by
  rw [mem_intrinsicComplement, mem_intrinsicComplement, actualGraphEdges_relabel,
    edgeMask_relabel]
  exact not_congr (CellRelabelGeometry.mem_image_family_iff
    (bijectionEquiv p.ridgeMap) (actualGraphEdges P lab) (maskSet (edgeMask e)))

theorem intrinsicComplement_relabel {d : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin 10) (p : IncidenceRenaming incidence) :
    intrinsicComplement P (lab.trans (bijectionEquiv p.ridgeMap)) =
      (intrinsicComplement P lab).image p.cells.forward := by
  ext a
  obtain ⟨e, rfl⟩ := (bijectionEquiv p.cells).surjective a
  change p.cells.forward e ∈ intrinsicComplement P (lab.trans (bijectionEquiv p.ridgeMap)) ↔
    p.cells.forward e ∈ (intrinsicComplement P lab).image p.cells.forward
  rw [intrinsicComplement_relabel_membership]
  constructor
  · exact Finset.mem_image_of_mem _
  · intro h
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp h
    exact p.cells.injective hbe ▸ hb

theorem intrinsicComplement_relabel_perm {d : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin 10) (p : IncidenceRenaming incidence) :
    (intrinsicComplement P (lab.trans (bijectionEquiv p.ridgeMap))).toList.Perm
      ((intrinsicComplement P lab).toList.map p.cells.forward) := by
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
    (List.pairwise_map.mpr ((Finset.nodup_toList _).imp
      (fun hne heq => hne (p.cells.injective heq))))).mpr
  intro e
  rw [Finset.mem_toList, intrinsicComplement_relabel]
  simp only [Finset.mem_image, List.mem_map, Finset.mem_toList]

theorem applyWord_perm {g : ℕ} (renamings : Fin g → IncidenceRenaming incidence)
    (word : List (Fin g)) {A B : List (Fin 45)} (h : A.Perm B) :
    (OrbitGrowthDAG.applyWord renamings word A).Perm
      (OrbitGrowthDAG.applyWord renamings word B) := by
  induction word generalizing A B with
  | nil => exact h
  | cons p rest ih => exact ih (h.map (renamings p).cells.forward)

/-- Every word of verified graph frames is realized by a genuine change
of the ten vertex labels. -/
theorem normalize_intrinsic_graph_word {d g : ℕ} (P : ConvexPolytope d)
    (renamings : Fin g → IncidenceRenaming incidence) (word : List (Fin g))
    (lab : P.vertices ≃ Fin 10) :
    ∃ lab' : P.vertices ≃ Fin 10,
      (intrinsicComplement P lab').toList.Perm
        (OrbitGrowthDAG.applyWord renamings word (intrinsicComplement P lab).toList) := by
  induction word generalizing lab with
  | nil => exact ⟨lab, List.Perm.refl _⟩
  | cons p rest ih =>
      let lab₁ := lab.trans (bijectionEquiv (renamings p).ridgeMap)
      obtain ⟨lab₂, h₂⟩ := ih lab₁
      have h₁ := intrinsicComplement_relabel_perm P lab (renamings p)
      exact ⟨lab₂, h₂.trans (applyWord_perm renamings rest h₁)⟩

theorem actual_graph_mask_membership {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (m : ℕ) (hm : m < 1024) :
    m ∈ literalGraphEdges cells E.family ↔ maskSet m ∈ actualGraphEdges P lab := by
  have himage : (literalGraphEdges cells E.family).image maskSet = actualGraphEdges P lab := by
    rw [literalGraphEdges_image]
    exact E.edges_eq_actual hP
  rw [← himage]
  constructor
  · exact Finset.mem_image_of_mem _
  · intro h
    obtain ⟨k, hk, hkm⟩ := Finset.mem_image.mp h
    exact maskSet_injective (literalGraphEdges_bound cells E.family hwell hk) hm hkm ▸ hk

theorem encoded_complement_eq_intrinsic {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4) :
    complementEdges (literalGraphEdges cells E.family) = intrinsicComplement P lab := by
  ext e
  rw [mem_complementEdges, mem_intrinsicComplement,
    actual_graph_mask_membership cells hwell E hP (edgeMask e) (edgeMask_lt e)]

/-- The graph catalogue's exhaustive coverage produces an actual vertex
labeling with the literal catalogued complement, rather than only an
abstract graph isomorphism unrelated to the polytope. -/
theorem exists_graph_model_labeling {d c g count size : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (renamings : Fin g → IncidenceRenaming incidence) (models : Fin count → List (Fin 45))
    (hcoverage : Covers incidence 4 renamings models size)
    (hsize : (complementEdges (literalGraphEdges cells E.family)).toList.length = size) :
    ∃ model : Fin count, ∃ lab' : P.vertices ≃ Fin 10,
      (intrinsicComplement P lab').toList.Perm (models model) := by
  obtain ⟨model, word, hmodel⟩ := hcoverage _
    (actual_complement_valid cells hwell E hP hnonsimple) hsize
  rw [encoded_complement_eq_intrinsic cells hwell E hP] at hmodel
  obtain ⟨lab', hlabel⟩ := normalize_intrinsic_graph_word P renamings word lab
  exact ⟨model, lab', hlabel.trans hmodel.symm⟩

end Papers.RationalityTen.ActualGraphNormalization

end
end
end BundlePart5

section BundlePart6
/- Source: EncodedBoundaryRestriction.lean -/




@[expose] public section

/-!
# Restricting an actual encoding to a checked candidate subuniverse

A finite graph filter may discard most full-universe cells. If every
selected actual cell has a retained index, the entire actual boundary
reindexes into the smaller universe. This preserves every cell field and
all kind counts; no fresh geometric coverage assumption is introduced.
-/

noncomputable section
namespace Papers.RationalityTen.MatroidChecked.FacetBoundaryEncoding.Encoding

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting

variable {d n c l : ℕ} {P : ConvexPolytope d} {lab : P.vertices ≃ Fin n}
  {fullCells : Fin c → Cell n} {localCells : Fin l → Cell n}

theorem restrict_to_subuniverse (E : Encoding P lab fullCells)
    (embedding : Fin l ↪ Fin c)
    (hcell : ∀ i, localCells i = fullCells (embedding i))
    (hcoverage : ∀ i ∈ E.family, ∃ j, embedding j = i) :
    ∃ E' : Encoding P lab localCells, ∀ F, embedding (E'.index F) = E.index F := by
  have h (F : Face P 3) : ∃ j, embedding j = E.index F :=
    hcoverage _ ((E.mem_family _).mpr ⟨F, rfl⟩)
  choose index hindex using h
  let E' : Encoding P lab localCells :=
    { index := index
      index_spec := by
        intro F
        rw [hcell, hindex, E.index_spec] }
  exact ⟨E', hindex⟩

theorem restricted_family_image (E : Encoding P lab fullCells)
    (E' : Encoding P lab localCells) (embedding : Fin l ↪ Fin c)
    (hindex : ∀ F, embedding (E'.index F) = E.index F) :
    E'.family.image embedding = E.family := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨F, rfl⟩ := (E'.mem_family j).mp hj
    rw [hindex]
    exact (E.mem_family _).mpr ⟨F, rfl⟩
  · intro hi
    obtain ⟨F, rfl⟩ := (E.mem_family i).mp hi
    exact Finset.mem_image.mpr
      ⟨E'.index F, (E'.mem_family _).mpr ⟨F, rfl⟩, hindex F⟩

theorem restricted_kind_card (E : Encoding P lab fullCells)
    (E' : Encoding P lab localCells) (embedding : Fin l ↪ Fin c)
    (hindex : ∀ F, embedding (E'.index F) = E.index F)
    (fullKind : Fin c → ℕ) (localKind : Fin l → ℕ)
    (hkind : ∀ i, localKind i = fullKind (embedding i)) (j : ℕ) :
    (E'.family.filter fun i => localKind i = j).card =
      (E.family.filter fun i => fullKind i = j).card := by
  rw [ActualGrowthTarget.encoded_kind_card, ActualGrowthTarget.encoded_kind_card]
  simp only [hkind, hindex]

theorem selected_kind_quota_pos (E : Encoding P lab fullCells)
    (kind : Fin c → ℕ) (quota : ℕ → ℕ)
    (hquota : ∀ j, (E.family.filter fun i => kind i = j).card ≤ quota j)
    (i : Fin c) (hi : i ∈ E.family) : 0 < quota (kind i) := by
  have hpos : 0 < (E.family.filter fun a => kind a = kind i).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  exact hpos.trans_le (hquota (kind i))

end Papers.RationalityTen.MatroidChecked.FacetBoundaryEncoding.Encoding

end
end
end BundlePart6

section BundlePart7
/- Source: ActualGraphCandidateRestriction.lean -/







@[expose] public section

/-!
# Checked graph filters retain every actual facet

The graph producer supplies a list of full-universe indices and one exact
eligible-mask equality. This module proves that every actual facet occurs
in that list. The proof uses the actual induced-edge theorem and positivity
of the selected facet's kind quota, and then reindexes the entire boundary.
No producer-local list is assumed complete.
-/

noncomputable section
namespace Papers.RationalityTen.ActualGraphCandidateRestriction

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualFacetInducedGraph ActualComplementGraph ActualGraphNormalization
open TenGraphEdges GraphCandidateCoverage

variable {d c : ℕ}

/-- These are exact finite-data equalities for the candidate filter's rows. -/
structure RowsForCells (R : IncidenceRows c 10 45)
    (cells : Fin c → ConcreteGrowth.Cell) : Prop where
  first : ∀ q, R.first q = TenGraphEdges.first q
  second : ∀ q, R.second q = TenGraphEdges.second q
  vertices : ∀ i, R.vertices i = (cells i).vertices
  edges : ∀ i q, (R.edges i).testBit q.val = true ↔ edgeMask q ∈ (cells i).edges

theorem pair_within_iff (q : Fin 45) (vertices : ℕ) :
    Nat.land (edgeMask q) vertices = edgeMask q ↔
      vertices.testBit (first q).val = true ∧ vertices.testBit (second q).val = true := by
  rw [← maskSet_subset_iff (edgeMask_lt q), edgeMask_set,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]
  simp only [mem_maskSet]

theorem actual_edge_membership {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (cells : Fin c → ConcreteGrowth.Cell) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (i : Fin c) (hi : i ∈ E.family) (q : Fin 45) :
    edgeMask q ∈ (cells i).edges ↔
      edgeMask q ∈ literalGraphEdges cells E.family ∧
        (cells i).vertices.testBit (first q).val = true ∧
        (cells i).vertices.testBit (second q).val = true := by
  rw [← List.mem_toFinset, literal_facet_edges_induced cells hwell E hP i hi,
    Finset.mem_filter, pair_within_iff]

/-- Every selected actual facet has exactly the edges induced by the
specified complete graph. -/
theorem selected_induced {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (R : IncidenceRows c 10 45) (cells : Fin c → ConcreteGrowth.Cell)
    (H : RowsForCells R cells) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (complement : ℕ)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      edgeMask q ∉ literalGraphEdges cells E.family)
    (i : Fin c) (hi : i ∈ E.family) : Induced R complement i := by
  intro q
  apply Bool.eq_iff_iff.mpr
  rw [H.edges, actual_edge_membership cells hwell E hP i hi q]
  simp only [Bool.and_eq_true_iff, Bool.not_eq_true', Bool.eq_false_iff,
    H.vertices, H.first, H.second, ne_eq, hcomplement, not_not]
  exact and_comm

/-- Matching a catalogue graph after an actual vertex relabeling supplies
the complement-mask premise needed by the finite candidate filter. -/
theorem complement_from_model {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (cells : Fin c → ConcreteGrowth.Cell) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (model : List (Fin 45)) (complement : ℕ)
    (hmodel : (intrinsicComplement P lab).toList.Perm model)
    (hbits : ∀ q : Fin 45, complement.testBit q.val = true ↔ q ∈ model)
    (q : Fin 45) :
    complement.testBit q.val = true ↔ edgeMask q ∉ literalGraphEdges cells E.family := by
  calc
    _ ↔ q ∈ model := hbits q
    _ ↔ q ∈ (intrinsicComplement P lab).toList := hmodel.mem_iff.symm
    _ ↔ maskSet (edgeMask q) ∉ actualGraphEdges P lab := by
      rw [Finset.mem_toList, mem_intrinsicComplement]
    _ ↔ edgeMask q ∉ literalGraphEdges cells E.family :=
      (not_congr (actual_graph_mask_membership cells hwell E hP
        (edgeMask q) (edgeMask_lt q))).symm

/-- The bitset equality certifies full coverage of actual selected cells.
Only selected cells need the edge-endpoint fact, which follows here from
the induced actual graph. -/
theorem selected_mem_candidates {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (R : IncidenceRows c 10 45) (cells : Fin c → ConcreteGrowth.Cell)
    (H : RowsForCells R cells) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (quota : ℕ → ℕ) (allowed complement : ℕ) (candidates : List (Fin c))
    (hquota : ∀ j, (E.family.filter fun i => (cells i).kind = j).card ≤ quota j)
    (hallowed : ∀ i, allowed.testBit i.val = true ↔ 0 < quota (cells i).kind)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      edgeMask q ∉ literalGraphEdges cells E.family)
    (hmask : eligibleMask R allowed complement = GrowthBitsets.ofList candidates)
    (i : Fin c) (hi : i ∈ E.family) : i ∈ candidates := by
  have hinduced := selected_induced R cells H hwell E hP complement hcomplement i hi
  have hedges (q : Fin 45) (hq : (R.edges i).testBit q.val = true) :
      (R.vertices i).testBit (R.first q).val = true ∧
        (R.vertices i).testBit (R.second q).val = true := by
    rw [hinduced q, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at hq
    exact hq.1
  apply (mem_embedding_iff R allowed complement candidates hmask i hedges).mpr
  exact ⟨(hallowed i).mpr
    (E.selected_kind_quota_pos (fun a => (cells a).kind) quota hquota i hi), hinduced⟩

/-- Reindex the complete actual boundary into the exact candidate list.
The returned equality also transports every kind count by the generic
`Encoding.restricted_kind_card` theorem. -/
theorem encoding_in_checked_candidates {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10}
    (R : IncidenceRows c 10 45) (cells : Fin c → ConcreteGrowth.Cell)
    (H : RowsForCells R cells) (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (quota : ℕ → ℕ) (allowed complement : ℕ) (candidates : List (Fin c))
    (hnodup : candidates.Nodup)
    (localCells : Fin candidates.length → ConcreteGrowth.Cell)
    (hlocal : ∀ i, localCells i = cells (candidates.get i))
    (hquota : ∀ j, (E.family.filter fun i => (cells i).kind = j).card ≤ quota j)
    (hallowed : ∀ i, allowed.testBit i.val = true ↔ 0 < quota (cells i).kind)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      edgeMask q ∉ literalGraphEdges cells E.family)
    (hmask : eligibleMask R allowed complement = GrowthBitsets.ofList candidates) :
    ∃ E' : Encoding P lab (fun i => decodeCell (localCells i)),
      (∀ F, candidates.get (E'.index F) = E.index F) ∧
      ∀ j, (E'.family.filter fun i => (localCells i).kind = j).card =
        (E.family.filter fun i => (cells i).kind = j).card := by
  let embedding : Fin candidates.length ↪ Fin c :=
    ⟨candidates.get, hnodup.injective_get⟩
  have hcoverage : ∀ i ∈ E.family, ∃ j, embedding j = i := by
    intro i hi
    exact List.mem_iff_get.mp (selected_mem_candidates R cells H hwell E hP quota
      allowed complement candidates hquota hallowed hcomplement hmask i hi)
  obtain ⟨E', hindex⟩ := E.restrict_to_subuniverse embedding
    (fun i => congrArg decodeCell (hlocal i)) hcoverage
  refine ⟨E', hindex, ?_⟩
  intro j
  exact E.restricted_kind_card E' embedding hindex (fun i => (cells i).kind)
    (fun i => (localCells i).kind) (fun i => congrArg ConcreteGrowth.Cell.kind (hlocal i)) j

end Papers.RationalityTen.ActualGraphCandidateRestriction

end
end
end BundlePart7

section BundlePart8
/- Source: LiteralGraphPairSemantics.lean -/






@[expose] public section

/-!
# Exact pair-bit semantics for literal cells

These lemmas connect compact 45-bit edge and missing-pair masks with the
ten-bit vertex masks stored in facet cells. The map from pair slots to
two-bit masks is injective; consequently a list equality supplies complete
edge semantics, and finite complementation inside the vertex set supplies
complete internal-nonedge semantics.
-/

noncomputable section
namespace Papers.RationalityTen.LiteralGraphPairSemantics

open Finset LiteralMaskGeometry TenGraphEdges ActualComplementGraph
open ActualGraphCandidateRestriction EncodedNonedgeFacetCoverage
open GrowthBitsets PrimitiveBitsetGrowth

theorem edge_mask_bit_iff (indices : List (Fin 45)) (q : Fin 45) :
    (PrimitiveBitsetGrowth.mask indices).testBit q.val = true ↔
      edgeMask q ∈ indices.map edgeMask := by
  rw [PrimitiveBitsetGrowth.mask_eq, ← bitAt_eq_testBit, bitAt_ofList]
  exact (List.mem_map_of_injective edgeMask_injective).symm

theorem edge_mask_bit_of_map (C : ConcreteGrowth.Cell) (indices : List (Fin 45))
    (hmap : indices.map edgeMask = C.edges) (q : Fin 45) :
    (PrimitiveBitsetGrowth.mask indices).testBit q.val = true ↔
      edgeMask q ∈ C.edges := by
  rw [edge_mask_bit_iff, hmap]

theorem internal_pair_iff (C : ConcreteGrowth.Cell) (q : Fin 45) :
    edgeMask q ∈ cellInternalNonedgeMasks C ↔
      C.vertices.testBit (first q).val = true ∧
        C.vertices.testBit (second q).val = true ∧ edgeMask q ∉ C.edges := by
  simp only [cellInternalNonedgeMasks, Finset.mem_filter, Finset.mem_range,
    edgeMask_lt q, edgeMask_card q, true_and, pair_within_iff, and_assoc]

/-- The missing-pair mask is exactly the complete within-cell pair mask
minus the cell's edge mask. Only explicit bit equalities are used. -/
theorem missing_mask_bit (C : ConcreteGrowth.Cell) (edges within missing : ℕ)
    (hedges : ∀ q : Fin 45, edges.testBit q.val = true ↔ edgeMask q ∈ C.edges)
    (hwithin : ∀ q : Fin 45, within.testBit q.val =
      (C.vertices.testBit (first q).val && C.vertices.testBit (second q).val))
    (hmissing : missing = Nat.land within (Nat.xor (FiniteMaskSets.allMask 45) edges))
    (q : Fin 45) :
    missing.testBit q.val = true ↔ edgeMask q ∈ cellInternalNonedgeMasks C := by
  have hxor : (Nat.xor (FiniteMaskSets.allMask 45) edges).testBit q.val =
      ((FiniteMaskSets.allMask 45).testBit q.val ^^ edges.testBit q.val) :=
    Nat.testBit_xor _ _ _
  rw [hmissing, FiniteMaskSets.testBit_land, hxor,
    FiniteMaskSets.allMask_bit q, hwithin, Bool.true_xor, internal_pair_iff]
  simp only [Bool.and_eq_true_iff, Bool.not_eq_true', Bool.eq_false_iff,
    ne_eq, hedges, and_assoc]

end Papers.RationalityTen.LiteralGraphPairSemantics

end
end
end BundlePart8

section BundlePart9
/- Source: LiteralGraphGrowthRenaming.lean -/




@[expose] public section

/-!
# Vertex permutations give sound graph-growth frames

A frame is checked by its vertex permutation and exact cell images.
Compatibility then follows from geometric relabeling, without a quadratic
table of cell pairs. The same permutation transports every ridge, actual
edge feature and internal missing pair.
-/

noncomputable section
namespace Papers.RationalityTen.LiteralGraphGrowthRenaming

open Finset Set
open scoped Classical
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
open LiteralMaskGeometry CellRelabelGeometry
open EncodedNonedgeFacetCoverage ActualGraphGrowthTarget
open GraphGrowthConstraints TenGraphEdges

variable {c k : ℕ}

def vertexBijection (σ : Equiv.Perm (Fin 10)) : GrowthRenaming.Bijection (Fin 10) where
  forward := σ
  inverse := σ.symm
  left_inverse := σ.symm_apply_apply
  right_inverse := σ.apply_symm_apply

theorem internalNonedges_map_iff (σ : Equiv.Perm (Fin 10))
    (C : Cell 10) (S : Finset (Fin 10)) :
    S.image σ ∈ cellInternalNonedges (mapCell σ.toEmbedding C) ↔
      S ∈ cellInternalNonedges C := by
  simp only [cellInternalNonedges, Finset.mem_sdiff, Finset.mem_powersetCard,
    mapCell, Equiv.toEmbedding_apply, Equiv.coe_toEmbedding]
  rw [Finset.image_subset_image_iff σ.injective,
    Finset.card_image_of_injective _ σ.injective, mem_image_family_iff]

theorem internal_mask_iff (C : ConcreteGrowth.Cell) (hC : WellFormed C)
    (m : ℕ) (hm : m < 1024) :
    m ∈ cellInternalNonedgeMasks C ↔ maskSet m ∈ cellInternalNonedges (decodeCell C) := by
  rw [← cellInternalNonedgeMasks_image C hC]
  constructor
  · exact Finset.mem_image_of_mem _
  · intro h
    obtain ⟨a, ha, ham⟩ := Finset.mem_image.mp h
    have haBound : a < 1024 := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    exact maskSet_injective haBound hm ham ▸ ha

/-- Finite frame data retain one and the same vertex permutation for all
cell, ridge and pair features. -/
structure Frame (D : Problem c 1024 45 10 k) (cells : Fin c → ConcreteGrowth.Cell) where
  vertices : Equiv.Perm (Fin 10)
  cellMap : GrowthRenaming.Bijection (Fin c)
  ridgeMap : GrowthRenaming.Bijection (Fin 1024)
  featureMap : GrowthRenaming.Bijection (Fin 45)
  cell_geometry : ∀ i, decodeCell (cells (cellMap.forward i)) =
    mapCell vertices.toEmbedding (decodeCell (cells i))
  ridge_geometry : ∀ q, maskSet (ridgeMap.forward q).val = (maskSet q.val).image vertices
  feature_geometry : ∀ q, maskSet (edgeMask (featureMap.forward q)) =
    (maskSet (edgeMask q)).image vertices
  kind_preserved : ∀ i, (cells (cellMap.forward i)).kind = (cells i).kind
  graph_preserved : ∀ q, D.requiredEdges.testBit (featureMap.forward q).val =
    D.requiredEdges.testBit q.val

theorem Frame.vertex_incidence {D : Problem c 1024 45 10 k}
    {cells : Fin c → ConcreteGrowth.Cell} (F : Frame D cells)
    (H : LiteralData D cells) (a : Fin 10) (i : Fin c) :
    (D.vertexRows (F.vertices a)).testBit (F.cellMap.forward i).val =
      (D.vertexRows a).testBit i.val := by
  rw [H.vertices, H.vertices]
  apply Bool.eq_iff_iff.mpr
  rw [← mem_maskSet, ← mem_maskSet]
  change F.vertices a ∈ (decodeCell (cells (F.cellMap.forward i))).vertices ↔
    a ∈ (decodeCell (cells i)).vertices
  rw [F.cell_geometry]
  change F.vertices a ∈ (decodeCell (cells i)).vertices.image F.vertices ↔ _
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
    exact F.vertices.injective hba ▸ hb
  · exact Finset.mem_image_of_mem _

theorem Frame.edge_incidence {D : Problem c 1024 45 10 k}
    {cells : Fin c → ConcreteGrowth.Cell} (F : Frame D cells)
    (H : LiteralData D cells) (hwell : ∀ i, WellFormed (cells i))
    (i : Fin c) (q : Fin 45) :
    (D.edges (F.cellMap.forward i)).testBit (F.featureMap.forward q).val =
      (D.edges i).testBit q.val := by
  apply Bool.eq_iff_iff.mpr
  rw [H.edges, H.edges,
    ← mask_mem_image_iff _ (hwell (F.cellMap.forward i)).edges_bound (edgeMask_lt _),
    ← mask_mem_image_iff _ (hwell i).edges_bound (edgeMask_lt _)]
  change maskSet (edgeMask (F.featureMap.forward q)) ∈
      (decodeCell (cells (F.cellMap.forward i))).edges ↔
    maskSet (edgeMask q) ∈ (decodeCell (cells i)).edges
  rw [F.cell_geometry, F.feature_geometry]
  exact mem_image_family_iff F.vertices _ _

theorem Frame.missing_incidence {D : Problem c 1024 45 10 k}
    {cells : Fin c → ConcreteGrowth.Cell} (F : Frame D cells)
    (H : LiteralData D cells) (hwell : ∀ i, WellFormed (cells i))
    (i : Fin c) (q : Fin 45) :
    (D.missing (F.cellMap.forward i)).testBit (F.featureMap.forward q).val =
      (D.missing i).testBit q.val := by
  apply Bool.eq_iff_iff.mpr
  rw [H.missing, H.missing,
    internal_mask_iff _ (hwell (F.cellMap.forward i)) _ (edgeMask_lt _),
    internal_mask_iff _ (hwell i) _ (edgeMask_lt _),
    F.cell_geometry, F.feature_geometry]
  exact internalNonedges_map_iff F.vertices _ _

/-- A verified literal frame supplies the complete semantic renaming used
by the generic graph-conditioned search theorem. -/
def Frame.toRenaming {D : Problem c 1024 45 10 k}
    {cells : Fin c → ConcreteGrowth.Cell} (F : Frame D cells)
    (H : LiteralData D cells) (hwell : ∀ i, WellFormed (cells i)) :
    GraphGrowthConstraints.Renaming D where
  boundary :=
    { cells := F.cellMap
      ridgeMap := F.ridgeMap
      incidence := by
        intro i q
        rw [H.ridges, H.ridges]
        exact literal_ridges_relabel cells hwell F.vertices F.cellMap.forward
          F.ridgeMap.forward F.cell_geometry F.ridge_geometry i q
      compatibility := by
        intro i j
        rw [H.compatible, H.compatible]
        exact literal_compatibility_relabel cells hwell F.vertices F.cellMap.forward
          F.cell_geometry i j
      kind_preserved := by
        intro i
        rw [H.kind, H.kind]
        exact F.kind_preserved i }
  vertices := vertexBijection F.vertices
  features := F.featureMap
  vertex_incidence := F.vertex_incidence H
  edge_incidence := F.edge_incidence H hwell
  missing_incidence := F.missing_incidence H hwell
  required_preserved := F.graph_preserved

end Papers.RationalityTen.LiteralGraphGrowthRenaming

end
end
end BundlePart9
