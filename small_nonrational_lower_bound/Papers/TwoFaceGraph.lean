module
public import Papers.ActualPlaneEdgeBound
public import Papers.ActualNeighborBound
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# The actual graph of a two-face

This module depends only on the original polytope foundation, actual
edge supports, the tangent-span degree bound, and elementary linear
algebra. It does not import the homothety-cover or lower-bound theory.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ}

def actualFaceNeighbors (P : ConvexPolytope d) (F : Set (E d)) (v : E d) :
    Finset (E d) :=
  P.vertices.filter (fun w => w ∈ F ∧ GeneralVertexStep P v w)

theorem actualFaceNeighbors_card_le_two_of_dim_le_two
    (P : ConvexPolytope d) (F : Set (E d)) (hdim : faceDim F ≤ 2)
    {w : E d} (hw : w ∈ P.vertices) (hwF : w ∈ F) :
    (actualFaceNeighbors P F w).card ≤ 2 := by
  let N := actualFaceNeighbors P F w
  by_contra hn
  change ¬ N.card ≤ 2 at hn
  have hbig : 3 ≤ N.card := Nat.succ_le_of_lt (lt_of_not_ge hn)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 3) hbig)
  have hcarderase : 1 < (N.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y,hy,z,hz,hyz⟩ := Finset.one_lt_card.mp hcarderase
  have hyN := Finset.mem_of_mem_erase hy
  have hzN := Finset.mem_of_mem_erase hz
  have hxy : x ≠ y := (Finset.ne_of_mem_erase hy).symm
  have hxz : x ≠ z := (Finset.ne_of_mem_erase hz).symm
  obtain ⟨hxP,hxF,hwx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyP,hyF,hwy⟩ := Finset.mem_filter.mp hyN
  obtain ⟨hzP,hzF,hwz⟩ := Finset.mem_filter.mp hzN
  have hsub : ({w,x,y,z} : Set (E d)) ⊆ F := by
    intro v hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hplane : finrank ℝ (vectorSpan ℝ ({w,x,y,z} : Set (E d))) ≤ 2 :=
    (Submodule.finrank_mono (vectorSpan_mono ℝ hsub)).trans hdim
  exact no_three_actual_edges_in_plane P hw hxP hyP hzP hxy hxz hyz hwx hwy hwz hplane

theorem actualStep_of_facePolytope
    (P : ConvexPolytope d) (F : Set (E d)) (hF : P.IsFace F)
    {x y : E d} (hxy : GeneralVertexStep (facePolytope P hF) x y) :
    GeneralVertexStep P x y := by
  obtain ⟨hy,hne,G,hG,hdim,hxG,hyG⟩ := hxy
  have hyP : y ∈ P.vertices := (Finset.mem_filter.mp hy).1
  exact ⟨hyP,hne,G,isFace_of_facePolytope P hF hG,hdim,hxG,hyG⟩

theorem faceDim_le_actualFaceNeighbors_card
    (P : ConvexPolytope d) (F : Set (E d)) (hF : P.IsFace F)
    {v : E d} (hv : v ∈ P.vertices) (hvF : v ∈ F) :
    faceDim F ≤ (actualFaceNeighbors P F v).card := by
  let Q := facePolytope P hF
  have hvQ : v ∈ Q.vertices := Finset.mem_filter.mpr ⟨hv,hvF⟩
  let f : Papers.PolytopeVertexCone.actualNeighbors Q v → actualFaceNeighbors P F v :=
    fun w => by
      have hwQ : w.val ∈ Q.vertices := (Finset.mem_filter.mp w.property).1
      have hwP : w.val ∈ P.vertices := (Finset.mem_filter.mp hwQ).1
      have hwF : w.val ∈ F := (Finset.mem_filter.mp hwQ).2
      have hstep : GeneralVertexStep Q v w.val := (Finset.mem_filter.mp w.property).2
      exact ⟨w.val,Finset.mem_filter.mpr
        ⟨hwP,hwF,actualStep_of_facePolytope P F hF hstep⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : actualFaceNeighbors P F v => z.val) h
    exact Subtype.ext hh
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hc
  have hd := actual_neighbor_card_ge_dim Q hvQ
  have hdim : Q.dim = faceDim F := by
    change faceDim Q.toSet = faceDim F
    rw [facePolytope_toSet P hF]
  omega

abbrev TwoFaceVertexType (P : ConvexPolytope d) (F : Set (E d)) :=
  {v : P.vertices // v.val ∈ F}

def twoFaceVertexGraph (P : ConvexPolytope d) (F : Set (E d)) :
    SimpleGraph (TwoFaceVertexType P F) where
  Adj x y := GeneralVertexStep P x.val.val y.val.val
  symm := ⟨by intro x y hxy; exact actualStep_symm x.val.property hxy⟩
  loopless := ⟨by intro x hxx; exact hxx.2.1 rfl⟩

def twoFaceGraphNeighborEquiv
    (P : ConvexPolytope d) (F : Set (E d)) (x : TwoFaceVertexType P F) :
    (twoFaceVertexGraph P F).neighborSet x ≃ actualFaceNeighbors P F x.val.val where
  toFun y := ⟨y.val.val.val,Finset.mem_filter.mpr
    ⟨y.val.val.property,y.val.property,y.property⟩⟩
  invFun y := ⟨⟨⟨y.val,(Finset.mem_filter.mp y.property).1⟩,
    (Finset.mem_filter.mp y.property).2.1⟩,
    (Finset.mem_filter.mp y.property).2.2⟩
  left_inv := by rintro ⟨⟨⟨y,hyP⟩,hyF⟩,hxy⟩; rfl
  right_inv := by rintro ⟨y,hy⟩; rfl

theorem twoFaceVertexGraph_degree_eq_actualFaceNeighbors
    (P : ConvexPolytope d) (F : Set (E d)) (x : TwoFaceVertexType P F) :
    (twoFaceVertexGraph P F).degree x = (actualFaceNeighbors P F x.val.val).card := by
  simpa only [SimpleGraph.card_neighborSet_eq_degree,Fintype.card_coe] using
    Fintype.card_congr (twoFaceGraphNeighborEquiv P F x)

theorem twoFaceVertexGraph_degree_two
    (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 2)
    (x : TwoFaceVertexType P F) :
    (twoFaceVertexGraph P F).degree x = 2 := by
  rw [twoFaceVertexGraph_degree_eq_actualFaceNeighbors]
  have hlow := faceDim_le_actualFaceNeighbors_card P F hF x.val.property x.property
  have hupp := actualFaceNeighbors_card_le_two_of_dim_le_two
    P F (by omega) x.val.property x.property
  omega

end Papers.Polytopes

