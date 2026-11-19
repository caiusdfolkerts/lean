module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.SplitIfs
public import Lean.Elab.Tactic.Omega
public import Papers.PolytopeIncidenceCounting
public import Papers.PolytopeEulerFour
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Powerset
public import Papers.ActualNeighborBound
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/RationalityTenBoundarySearch.lean -/








@[expose] public section

/-!
A finite boundary-search checker and its coverage theorem.

The search is exhaustive for a target boundary when its ridges lie in exactly
two cells, its cell-adjacency graph is connected, and every target extension
passes the explicitly supplied admissibility predicate.  No catalogue or
geometric assertion is assumed by the checker.  Geometric applications must
separately establish these hypotheses for their actual face families.

DRAFT: this source was written during an executor outage and has not compiled.
-/
namespace Papers.RationalityTen.BoundarySearch

open Finset

variable {C R : Type*} [DecidableEq C] [DecidableEq R]

def incidence (ridges : C → Finset R) (S : Finset C) (r : R) : Finset C :=
  S.filter fun c => r ∈ ridges c

def firstOpen (ridges : C → Finset R) (S : Finset C) : List R → Option R
  | [] => none
  | r :: rs =>
      if (incidence ridges S r).card = 1 then some r
      else firstOpen ridges S rs

theorem firstOpen_some (ridges : C → Finset R) (S : Finset C)
    (rs : List R) (r : R) (h : firstOpen ridges S rs = some r) :
    (incidence ridges S r).card = 1 := by
  induction rs with
  | nil => simp [firstOpen] at h
  | cons a rs ih =>
      unfold firstOpen at h
      split_ifs at h with ha
      · cases h
        exact ha
      · exact ih h

theorem firstOpen_none (ridges : C → Finset R) (S : Finset C)
    (rs : List R) (h : firstOpen ridges S rs = none) :
    ∀ r ∈ rs, (incidence ridges S r).card ≠ 1 := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
      by_cases ha : (incidence ridges S a).card = 1
      · simp [firstOpen,ha] at h
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ha
        · exact ih (by simpa only [firstOpen,if_neg ha] using h) r hr

/-- Every nontrivial partition has a ridge crossing from the selected side. -/
def RidgeConnected (ridges : C → Finset R) (B : Finset C) : Prop :=
  ∀ S ⊆ B, S.Nonempty → S ≠ B →
    ∃ a ∈ S, ∃ b ∈ B, b ∉ S ∧
      ∃ r, r ∈ ridges a ∧ r ∈ ridges b

theorem incidence_mono (ridges : C → Finset R) {S B : Finset C}
    (h : S ⊆ B) (r : R) :
    incidence ridges S r ⊆ incidence ridges B r := by
  intro c hc
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hc).1,
    (Finset.mem_filter.mp hc).2⟩

theorem open_ridge_exists (ridges : C → Finset R) (B S : Finset C)
    (hsub : S ⊆ B) (hne : S.Nonempty) (hneq : S ≠ B)
    (htwo : ∀ r, (incidence ridges B r).card ≤ 2)
    (hconn : RidgeConnected ridges B) :
    ∃ r, (incidence ridges S r).card = 1 := by
  obtain ⟨a, ha, b, hb, hbS, r, har, hbr⟩ :=
    hconn S hsub hne hneq
  have haS : a ∈ incidence ridges S r := Finset.mem_filter.mpr ⟨ha, har⟩
  have hbB : b ∈ incidence ridges B r := Finset.mem_filter.mpr ⟨hb, hbr⟩
  have hmono := incidence_mono ridges hsub r
  have hpos : 0 < (incidence ridges S r).card :=
    Finset.card_pos.mpr ⟨a, haS⟩
  have hstrict : (incidence ridges S r).card < (incidence ridges B r).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hmono, ?_⟩
    intro heq
    have : b ∈ incidence ridges S r := heq.symm ▸ hbB
    exact hbS (Finset.mem_filter.mp this).1
  exact ⟨r, by have := htwo r; omega⟩

theorem missing_cell_at_open_ridge
    (ridges : C → Finset R) (B S : Finset C) (r : R)
    (hsub : S ⊆ B) (hopen : (incidence ridges S r).card = 1)
    (htwo : (incidence ridges B r).card = 0 ∨
      (incidence ridges B r).card = 2) :
    ∃ c ∈ B, c ∉ S ∧ r ∈ ridges c := by
  have hcard := Finset.card_le_card (incidence_mono ridges hsub r)
  have hB : (incidence ridges B r).card = 2 := by omega
  by_contra h
  push_neg at h
  have hback : incidence ridges B r ⊆ incidence ridges S r := by
    intro c hc
    obtain ⟨hcB, hcr⟩ := Finset.mem_filter.mp hc
    have hcS : c ∈ S := by
      by_contra hcS
      exact h c hcB hcS hcr
    exact Finset.mem_filter.mpr ⟨hcS, hcr⟩
  have := Finset.card_le_card hback
  omega

variable [Fintype C]

/-- The allowed predicate is an explicit, computable pruning rule.
A proposed final target must be proved to pass it at every subfamily. -/
def growCheck (U : Finset C) (ridges : C → Finset R)
    (ridgeList : List R) (allowed : Finset C → C → Bool)
    (accept : Finset C → Bool) : Nat → Finset C → Bool
  | 0, S => accept S
  | fuel + 1, S =>
      match firstOpen ridges S ridgeList with
      | none => accept S
      | some r =>
          decide (∀ c : C, c ∈ U → c ∉ S → r ∈ ridges c →
            allowed S c = true →
            growCheck U ridges ridgeList allowed accept fuel (insert c S) = true)

/-- Soundness of a finite exhaustive search with a cardinality bound.
This proves the actual target is accepted, not merely that searched leaves are
internally consistent.  The only admissibility hypothesis is stated explicitly. -/
theorem growCheck_complete
    (U : Finset C) (ridges : C → Finset R) (ridgeList : List R)
    (allowed : Finset C → C → Bool) (accept : Finset C → Bool)
    (B : Finset C)
    (hU : B ⊆ U)
    (hridges : ∀ r, r ∈ ridgeList)
    (htwo : ∀ r, (incidence ridges B r).card = 0 ∨
      (incidence ridges B r).card = 2)
    (hconn : RidgeConnected ridges B)
    (hallowed : ∀ S ⊆ B, ∀ c ∈ B, c ∉ S → allowed S c = true)
    (fuel : Nat) :
    ∀ S, S ⊆ B → S.Nonempty → B.card ≤ S.card + fuel →
      growCheck U ridges ridgeList allowed accept fuel S = true →
      accept B = true := by
  induction fuel with
  | zero =>
      intro S hsub hne hcard hcheck
      have heq : S = B := by
        apply Finset.eq_of_subset_of_card_le hsub
        simpa using hcard
      simpa [growCheck, heq] using hcheck
  | succ fuel ih =>
      intro S hsub hne hcard hcheck
      cases hf : firstOpen ridges S ridgeList with
      | none =>
          have heq : S = B := by
            by_contra hneq
            obtain ⟨r, hr⟩ := open_ridge_exists ridges B S hsub hne hneq
              (fun r => by rcases htwo r with h | h <;> omega) hconn
            exact firstOpen_none ridges S ridgeList hf r (hridges r) hr
          subst S
          simpa only [growCheck, hf] using hcheck
      | some r =>
          have hopen := firstOpen_some ridges S ridgeList r hf
          obtain ⟨c, hcB, hcS, hcr⟩ :=
            missing_cell_at_open_ridge ridges B S r hsub hopen (htwo r)
          have hbranch :
              ∀ c : C, c ∈ U → c ∉ S → r ∈ ridges c →
                allowed S c = true →
                growCheck U ridges ridgeList allowed accept fuel (insert c S) = true := by
            exact of_decide_eq_true (by simpa [growCheck, hf] using hcheck)
          have hnext := hbranch c (hU hcB) hcS hcr (hallowed S hsub c hcB hcS)
          apply ih (insert c S) _ _ _ hnext
          · intro a ha
            rcases Finset.mem_insert.mp ha with rfl | ha
            · exact hcB
            · exact hsub ha
          · exact ⟨c, Finset.mem_insert_self c S⟩
          · rw [Finset.card_insert_of_notMem hcS]
            omega

end Papers.RationalityTen.BoundarySearch

end
end BundlePart0

section BundlePart1
/- Source: Papers/PolytopeBoundaryIncidence.lean -/





@[expose] public section

/-!
# Ridge pairing and connectivity of the actual facet boundary

The finite search receives these properties from
the actual convex-polytope face lattice, not as an assumed manifold
certificate. The construction works in every intrinsic dimension at
least two.
-/

noncomputable section

namespace Papers.PolytopeBoundaryIncidence

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.RationalityTen.BoundarySearch
open scoped Classical

variable {n : ℕ}

local instance faceFintype (P : ConvexPolytope n) (k : ℕ) :
    Fintype (Face P k) := Fintype.ofFinite _

def actualRidges (P : ConvexPolytope n) (k : ℕ)
    (F : Face P (k + 1)) : Finset (Face P k) :=
  Finset.univ.filter fun R => R.val.carrier ⊆ F.val.carrier

@[simp] theorem mem_actualRidges (P : ConvexPolytope n) (k : ℕ)
    (F : Face P (k + 1)) (R : Face P k) :
    R ∈ actualRidges P k F ↔ R.val.carrier ⊆ F.val.carrier := by
  simp [actualRidges]

theorem actual_ridge_incidence_card (P : ConvexPolytope n) (k : ℕ)
    (hdim : P.dim = k + 2) (R : Face P k) :
    (incidence (actualRidges P k) Finset.univ R).card = 2 := by
  have h := ridge_coface_card P k hdim R
  have heq : incidence (actualRidges P k) Finset.univ R =
      Finset.univ.filter fun F : Face P (k + 1) =>
        R.val.carrier ⊆ F.val.carrier := by
    ext F
    simp [incidence]
  rw [heq]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at h
  exact h

theorem reflTransGen_crossing {X : Type*} {r : X → X → Prop}
    {a b : X} (hpath : Relation.ReflTransGen r a b)
    (S : Set X) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x ∈ S, ∃ y, y ∉ S ∧ r x y := by
  induction hpath with
  | refl => exact (hb ha).elim
  | @tail c b hprev hstep ih =>
      by_cases hc : c ∈ S
      · exact ⟨c,hc,b,hb,hstep⟩
      · exact ih hc

theorem proper_facet (P : ConvexPolytope n) (k : ℕ)
    (hdim : P.dim = k + 1) (F : Face P k) :
    F.val.carrier ⊂ P.toSet := by
  refine (face_subset_toSet P F.val.isFace).ssubset_of_ne ?_
  intro h
  have hd := congrArg faceDim h
  change faceDim F.val.carrier = P.dim at hd
  rw [F.property,hdim] at hd
  omega

theorem actual_boundary_ridge_connected (P : ConvexPolytope n)
    (k : ℕ) (hdim : P.dim = k + 2) :
    RidgeConnected (actualRidges P k) Finset.univ := by
  intro S hS hSne hSneAll
  obtain ⟨a,ha⟩ := hSne
  have hout : ∃ b : Face P (k + 1), b ∉ S := by
    by_contra h
    push_neg at h
    apply hSneAll
    ext b
    simp [h b]
  obtain ⟨b,hb⟩ := hout
  have haT := proper_facet P (k + 1) (by omega) a
  have hbT := proper_facet P (k + 1) (by omega) b
  have hpath : Relation.ReflTransGen (RidgeStepIn P P.toSet)
      a.val.carrier b.val.carrier :=
    ridgeConnectedAboveOne_sempre P P.toSet (toSet_isFace P)
      (by change 2 ≤ P.dim; omega)
      a.val.carrier b.val.carrier a.val.isFace b.val.isFace haT hbT
      (by change faceDim a.val.carrier + 1 = P.dim; rw [a.property]; omega)
      (by change faceDim b.val.carrier + 1 = P.dim; rw [b.property]; omega)
  let U : Set (Set (E n)) :=
    {A | ∃ F : Face P (k + 1), F ∈ S ∧ F.val.carrier = A}
  have haU : a.val.carrier ∈ U := ⟨a,ha,rfl⟩
  have hbU : b.val.carrier ∉ U := by
    rintro ⟨F,hF,hFb⟩
    have heq : F = b := Subtype.ext (PolytopeFace.ext hFb)
    exact hb (heq ▸ hF)
  obtain ⟨X,hX,Y,hY,hstep⟩ := reflTransGen_crossing hpath U haU hbU
  obtain ⟨hXF,hYF,hXT,hYT,hXd,hYd,R,hRF,hRX,hRY,hRd⟩ := hstep
  have hXd' : faceDim X = k + 1 := by
    change faceDim X + 1 = P.dim at hXd
    omega
  have hYd' : faceDim Y = k + 1 := by
    change faceDim Y + 1 = P.dim at hYd
    omega
  have hRd' : faceDim R = k := by
    change faceDim R + 2 = P.dim at hRd
    omega
  let x : Face P (k + 1) := ⟨⟨X,hXF⟩,hXd'⟩
  let y : Face P (k + 1) := ⟨⟨Y,hYF⟩,hYd'⟩
  let r : Face P k := ⟨⟨R,hRF⟩,hRd'⟩
  have hxS : x ∈ S := by
    obtain ⟨F,hFS,hFX⟩ := hX
    have heq : F = x := Subtype.ext (PolytopeFace.ext hFX)
    exact heq ▸ hFS
  have hyS : y ∉ S := by
    intro hy
    exact hY ⟨y,hy,rfl⟩
  refine ⟨x,hxS,y,Finset.mem_univ _,hyS,r,?_,?_⟩
  · exact (mem_actualRidges P k x r).mpr hRX.1
  · exact (mem_actualRidges P k y r).mpr hRY.1

end Papers.PolytopeBoundaryIncidence

end
end
end BundlePart1

section BundlePart2
/- Source: ActualEdgeLinkConnectivity.lean -/





@[expose] public section

/-!
# Connectivity of the actual link of an edge

Two genuine vertex figures turn an edge of a four-polytope into a polygon.
The maps below retain the full face incidence, rather than only the equality
of incidence counts. Connectivity of the polygon boundary therefore gives
connectivity of all facets containing the fixed original edge.
-/

noncomputable section
namespace Papers.RationalityTen.ActualEdgeLinkConnectivity

open Set Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeEulerFour Papers.PolytopeBoundaryIncidence
open BoundarySearch

variable {n : ℕ}

theorem incident_figure_inclusion {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v) {i j : ℕ}
    (F : IncidentFace P v (i + 1)) (G : IncidentFace P v (j + 1)) :
    F.val.val.carrier ⊆ G.val.val.carrier ↔
      ((incidentFigureEquiv D i) F).val.carrier ⊆
        ((incidentFigureEquiv D j) G).val.carrier :=
  D.map_subset_iff (incidentStar P v i F) (incidentStar P v j G)

theorem coface_figure_inclusion {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v)
    (A : PositiveVertexStarFace P P.toSet v) {i j : ℕ}
    (F : Coface P A.carrier (i + 1)) (G : Coface P A.carrier (j + 1)) :
    F.val.val.carrier ⊆ G.val.val.carrier ↔
      ((cofaceFigureEquiv D A i) F).val.val.carrier ⊆
        ((cofaceFigureEquiv D A j) G).val.val.carrier :=
  D.map_subset_iff
    (incidentStar P v i ⟨F.val, F.property A.mem_vertex⟩)
    (incidentStar P v j ⟨G.val, G.property A.mem_vertex⟩)

/-- The first figure turns the edge into a vertex; the second removes that
vertex. The remaining cofaces retain their exact inclusion relation. -/
def doubleFigureEquiv {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v)
    (A : PositiveVertexStarFace P P.toSet v) (q : E n)
    (hAq : (D.faceEquiv A).carrier = {q})
    (D' : VertexFigureGaloisData D.figure D.figure.toSet q) (k : ℕ) :
    Coface P A.carrier (k + 2) ≃ Face D'.figure k :=
  (cofaceFigureEquiv D A (k + 1)).trans
    ((Equiv.subtypeEquivRight (fun G : Face D.figure (k + 1) => by
      change (D.faceEquiv A).carrier ⊆ G.val.carrier ↔ q ∈ G.val.carrier
      rw [hAq]
      exact Set.singleton_subset_iff)).trans (incidentFigureEquiv D' k))

theorem double_figure_inclusion {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v)
    (A : PositiveVertexStarFace P P.toSet v) (q : E n)
    (hAq : (D.faceEquiv A).carrier = {q})
    (D' : VertexFigureGaloisData D.figure D.figure.toSet q) {i j : ℕ}
    (F : Coface P A.carrier (i + 2)) (G : Coface P A.carrier (j + 2)) :
    F.val.val.carrier ⊆ G.val.val.carrier ↔
      ((doubleFigureEquiv D A q hAq D' i) F).val.carrier ⊆
        ((doubleFigureEquiv D A q hAq D' j) G).val.carrier := by
  change _ ↔ ((incidentFigureEquiv D' i) _).val.carrier ⊆
    ((incidentFigureEquiv D' j) _).val.carrier
  rw [← incident_figure_inclusion]
  change _ ↔ ((cofaceFigureEquiv D A (i + 1)) F).val.val.carrier ⊆
    ((cofaceFigureEquiv D A (j + 1)) G).val.val.carrier
  exact coface_figure_inclusion D A F G

structure EdgeFigureData (P : ConvexPolytope n) (e : Face P 1) where
  figure : ConvexPolytope n
  dimension : figure.dim = 2
  ridges : Coface P e.val.carrier 2 ≃ Face figure 0
  facets : Coface P e.val.carrier 3 ≃ Face figure 1
  incidence : ∀ R F, R.val.val.carrier ⊆ F.val.val.carrier ↔
    (ridges R).val.carrier ⊆ (facets F).val.carrier

/-- The polygon figure is constructed from the actual polytope; its
existence and its incidence maps are not assumptions of the search. -/
theorem edge_figure_exists (P : ConvexPolytope n) (hP : P.dim = 4)
    (e : Face P 1) : Nonempty (EdgeFigureData P e) := by
  obtain ⟨v, hv, hve⟩ := face_has_vertex P e.val.isFace
  obtain ⟨D⟩ := exists_figure P hv (by omega)
  have hD : D.figure.dim = 3 := figure_dim D hv 3 hP
  let A : PositiveVertexStarFace P P.toSet v :=
    { carrier := e.val.carrier
      isFace := e.val.isFace
      subset_base := face_subset_toSet P e.val.isFace
      mem_vertex := hve
      dim_pos := by rw [e.property] }
  have hAd : faceDim (D.faceEquiv A).carrier = 0 := by
    have h := D.map_dim A
    change faceDim (D.faceEquiv A).carrier + 1 = faceDim e.val.carrier at h
    rw [e.property] at h
    omega
  obtain ⟨q, hq, hAq⟩ := actual_zeroFace_is_vertex D.figure
    (D.faceEquiv A).carrier (D.faceEquiv A).isFace hAd
  obtain ⟨D'⟩ := exists_figure D.figure hq (by omega)
  have hD' : D'.figure.dim = 2 := figure_dim D' hq 2 hD
  exact ⟨{ figure := D'.figure
           dimension := hD'
           ridges := doubleFigureEquiv D A q hAq D' 0
           facets := doubleFigureEquiv D A q hAq D' 1
           incidence := fun R F => double_figure_inclusion D A q hAq D' R F }⟩

/-- Connectivity transports along separate bijections of facets and
ridges, provided their actual incidence relation is preserved. -/
theorem ridgeConnected_equiv {C D R T : Type*}
    [Fintype C] [Fintype D] [Fintype R] [Fintype T]
    [DecidableEq C] [DecidableEq D] [DecidableEq R] [DecidableEq T]
    (f : C ≃ D) (g : R ≃ T) (ridges : C → Finset R) (other : D → Finset T)
    (hinc : ∀ c r, r ∈ ridges c ↔ g r ∈ other (f c))
    (hconn : RidgeConnected other Finset.univ) :
    RidgeConnected ridges Finset.univ := by
  intro S _ hS hproper
  have himproper : S.image f ≠ Finset.univ := by
    intro hall
    apply hproper
    apply Finset.eq_univ_of_forall
    intro c
    have hc : f c ∈ S.image f := by rw [hall]; exact Finset.mem_univ _
    obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hc
    exact f.injective hac ▸ ha
  obtain ⟨a, ha, b, _, hb, r, hra, hrb⟩ :=
    hconn (S.image f) (Finset.subset_univ _) (hS.image f) himproper
  obtain ⟨a₀, ha₀, heq⟩ := Finset.mem_image.mp ha
  refine ⟨a₀, ha₀, f.symm b, Finset.mem_univ _, ?_, g.symm r, ?_, ?_⟩
  · intro h
    exact hb (Finset.mem_image.mpr ⟨f.symm b, h, f.apply_symm_apply b⟩)
  · exact (hinc a₀ (g.symm r)).mpr (by simpa only [g.apply_symm_apply, heq] using hra)
  · exact (hinc (f.symm b) (g.symm r)).mpr
      (by simpa only [g.apply_symm_apply, f.apply_symm_apply] using hrb)

def cofaceRidges (P : ConvexPolytope n) (e : Face P 1)
    (F : Coface P e.val.carrier 3) : Finset (Coface P e.val.carrier 2) :=
  Finset.univ.filter fun R => R.val.val.carrier ⊆ F.val.val.carrier

@[simp] theorem mem_cofaceRidges (P : ConvexPolytope n) (e : Face P 1)
    (F : Coface P e.val.carrier 3) (R : Coface P e.val.carrier 2) :
    R ∈ cofaceRidges P e F ↔ R.val.val.carrier ⊆ F.val.val.carrier := by
  simp only [cofaceRidges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- All cofacets containing the fixed edge are connected through ridges
that also contain that same edge. -/
theorem actual_edge_link_connected (P : ConvexPolytope n) (hP : P.dim = 4)
    (e : Face P 1) : RidgeConnected (cofaceRidges P e) Finset.univ := by
  obtain ⟨D⟩ := edge_figure_exists P hP e
  apply ridgeConnected_equiv D.facets D.ridges (cofaceRidges P e)
    (actualRidges D.figure 0)
  · intro F R
    simpa only [mem_cofaceRidges, mem_actualRidges] using D.incidence R F
  · exact actual_boundary_ridge_connected D.figure 0 D.dimension

def edgeFacets (P : ConvexPolytope n) (e : Face P 1) : Finset (Face P 3) :=
  Finset.univ.filter fun F => e.val.carrier ⊆ F.val.carrier

def edgeRidges (P : ConvexPolytope n) (e : Face P 1) (F : Face P 3) :
    Finset (Face P 2) :=
  Finset.univ.filter fun R => e.val.carrier ⊆ R.val.carrier ∧
    R.val.carrier ⊆ F.val.carrier

/-- The same link-connectivity theorem expressed on the ambient facet and
ridge types, suitable for transport to literal candidate indices. -/
theorem actual_edge_facets_connected (P : ConvexPolytope n) (hP : P.dim = 4)
    (e : Face P 1) : RidgeConnected (edgeRidges P e) (edgeFacets P e) := by
  intro S hsub hSne hSproper
  let T : Finset (Coface P e.val.carrier 3) := Finset.univ.filter fun F => F.val ∈ S
  have hTne : T.Nonempty := by
    obtain ⟨F, hF⟩ := hSne
    have heF := (Finset.mem_filter.mp (hsub hF)).2
    exact ⟨⟨F, heF⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF⟩⟩
  have hTproper : T ≠ Finset.univ := by
    intro hall
    apply hSproper
    apply Finset.Subset.antisymm hsub
    intro F hF
    let a : Coface P e.val.carrier 3 := ⟨F, (Finset.mem_filter.mp hF).2⟩
    have ha : a ∈ T := by rw [hall]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp ha).2
  obtain ⟨F, hF, G, _, hG, R, hRF, hRG⟩ :=
    actual_edge_link_connected P hP e T (Finset.subset_univ _) hTne hTproper
  refine ⟨F.val, (Finset.mem_filter.mp hF).2, G.val,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.property⟩, ?_, R.val, ?_, ?_⟩
  · intro hGS
    exact hG (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGS⟩)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, R.property,
      (mem_cofaceRidges P e F R).mp hRF⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, R.property,
      (mem_cofaceRidges P e G R).mp hRG⟩

end Papers.RationalityTen.ActualEdgeLinkConnectivity

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/RationalityTenPolygonCatalogue.lean -/










@[expose] public section

/-!
Small three-dimensional boundary catalogues, with explicit polygon edge cycles.

The hash tree is only a source of witnesses: every returned permutation and
every claimed relabelling is checked. No injectivity or collision resistance
of the hash is assumed in any theorem.

DRAFT: not compiled; prepared during the execution environment outage.
-/
namespace Papers.RationalityTen.PolygonBoundaryCatalogue

open Finset
open scoped BigOperators
open BoundarySearch

structure Polygon (n : Nat) where
  vertices : Finset (Fin n)
  edges : Finset (Fin n × Fin n)

instance {n : Nat} : DecidableEq (Polygon n) := fun A B =>
  decidable_of_iff (A.vertices = B.vertices ∧ A.edges = B.edges) (by
    constructor
    · intro h
      cases A with
      | mk av ae =>
        cases B with
        | mk bv be =>
          obtain ⟨rfl,rfl⟩ := h
          rfl
    · rintro rfl
      exact ⟨rfl,rfl⟩)

def orderedEdge {n : Nat} (a b : Fin n) : Fin n × Fin n :=
  if a ≤ b then (a,b) else (b,a)

def polygonOfCycle {n : Nat} (cy : List (Fin n)) : Polygon n :=
  ⟨cy.toFinset,
    ((cy.zip (cy.drop 1 ++ cy.take 1)).map fun e => orderedEdge e.1 e.2).toFinset⟩

def compatible {n : Nat} (A B : Polygon n) : Prop :=
  (A.vertices ∩ B.vertices).card ≤ 1 ∨
    ∃ e ∈ A.edges, e ∈ B.edges ∧
      A.vertices ∩ B.vertices = {e.1, e.2}

instance {n : Nat} (A B : Polygon n) : Decidable (compatible A B) := by
  unfold compatible
  infer_instance

def ridges {n k : Nat} (cells : Fin k → Polygon n) (c : Fin k) :=
  (cells c).edges

def edges {n k : Nat} (cells : Fin k → Polygon n) (S : Finset (Fin k)) :=
  S.biUnion fun c => (cells c).edges

def vertexDegree {n k : Nat} (cells : Fin k → Polygon n)
    (S : Finset (Fin k)) (v : Fin n) : Nat :=
  ((edges cells S).filter fun e => e.1 = v ∨ e.2 = v).card

def valid {n k : Nat} (cells : Fin k → Polygon n) (S : Finset (Fin k)) : Prop :=
  (∀ r : Fin n × Fin n,
    (incidence (ridges cells) S r).card = 0 ∨
      (incidence (ridges cells) S r).card = 2) ∧
  (∀ v : Fin n, 3 ≤ vertexDegree cells S v) ∧
  n + S.card = (edges cells S).card + 2

instance {n k : Nat} (cells : Fin k → Polygon n) (S : Finset (Fin k)) :
    Decidable (valid cells S) := by
  unfold valid
  infer_instance

def allowed {n k : Nat} (cells : Fin k → Polygon n)
    (S : Finset (Fin k)) (c : Fin k) : Bool :=
  decide ((∀ a ∈ S, compatible (cells a) (cells c)) ∧
    ∀ r : Fin n × Fin n, (incidence (ridges cells) (insert c S) r).card ≤ 2)

def ridgeList (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a => (List.finRange n).map fun b => (a,b)

theorem mem_ridgeList {n : Nat} (r : Fin n × Fin n) : r ∈ ridgeList n := by
  rcases r with ⟨a,b⟩
  simp [ridgeList]

def relabelPolygon {n : Nat} (f : Fin n → Fin n) (A : Polygon n) : Polygon n :=
  ⟨A.vertices.image f, A.edges.image fun e => orderedEdge (f e.1) (f e.2)⟩

def relabelBoundary {n k : Nat} (cells : Fin k → Polygon n)
    (f : Fin n → Fin n) (S : Finset (Fin k)) : Finset (Polygon n) :=
  S.image fun c => relabelPolygon f (cells c)

inductive WitnessTree where
  | nil
  | node (key : Nat) (value : Nat × Nat) (left right : WitnessTree)

def lookup : WitnessTree → Nat → Option (Nat × Nat)
  | .nil, _ => none
  | .node a v l r, k =>
      if k = a then some v else if k < a then lookup l k else lookup r k

/-- This is a computational index, not a cryptographic or injective encoding. -/
def familyKey {k : Nat} (S : Finset (Fin k)) : Nat :=
  (∑ c ∈ S, (c.val + 1) ^ 7) % 4294967291

def decode {n : Nat} (hn : 0 < n) (code : Nat) (i : Fin n) : Fin n :=
  ⟨(code / n ^ i.val) % n, Nat.mod_lt _ hn⟩

def accept {n k t : Nat} (hn : 0 < n) (cells : Fin k → Polygon n)
    (templates : Fin t → Finset (Polygon n)) (tree : WitnessTree)
    (S : Finset (Fin k)) : Bool :=
  if valid cells S then
    match lookup tree (familyKey S) with
    | none => false
    | some (j,code) =>
        if hj : j < t then
          decide (Function.Injective (decode hn code) ∧
            relabelBoundary cells (decode hn code) S = templates ⟨j,hj⟩)
        else false
  else true

theorem accept_has_relabeling {n k t : Nat} (hn : 0 < n)
    (cells : Fin k → Polygon n) (templates : Fin t → Finset (Polygon n))
    (tree : WitnessTree) (S : Finset (Fin k))
    (hv : valid cells S) (ha : accept hn cells templates tree S = true) :
    ∃ (p : Equiv.Perm (Fin n)) (j : Fin t),
      relabelBoundary cells p S = templates j := by
  unfold accept at ha
  simp only [if_pos hv] at ha
  cases hl : lookup tree (familyKey S) with
  | none => simp [hl] at ha
  | some w =>
      rcases w with ⟨j,code⟩
      simp only [hl] at ha
      split_ifs at ha with hj
      · have hh := of_decide_eq_true ha
        let f := decode hn code
        let p : Equiv.Perm (Fin n) :=
          Equiv.ofBijective f ⟨hh.1, Finite.surjective_of_injective hh.1⟩
        exact ⟨p, ⟨j,hj⟩, hh.2⟩

theorem allowed_of_subset {n k : Nat} (cells : Fin k → Polygon n)
    (B S : Finset (Fin k))
    (hpair : (B : Set _).Pairwise fun a b => compatible (cells a) (cells b))
    (hv : valid cells B) (hsub : S ⊆ B) (c : Fin k)
    (hcB : c ∈ B) (hcS : c ∉ S) : allowed cells S c = true := by
  unfold allowed
  apply decide_eq_true
  constructor
  · intro a ha
    apply hpair (hsub ha) hcB
    intro heq
    exact hcS (heq ▸ ha)
  · intro r
    have hins : insert c S ⊆ B := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hcB
      · exact hsub ha
    have hcard := Finset.card_le_card (incidence_mono (ridges cells) hins r)
    rcases hv.1 r with h | h <;> omega

/-- The bridge from a checked finite search to a complete boundary catalogue.
The hypotheses describe the candidate boundary itself; no assumed catalogue
membership, geometric genericity, or realization oracle occurs here. -/
theorem catalogue_of_checked_search {n k t : Nat} (hn : 0 < n)
    (cells : Fin k → Polygon n) (templates : Fin t → Finset (Polygon n))
    (tree : WitnessTree) (B seed : Finset (Fin k)) (fuel : Nat)
    (hseed : seed ⊆ B) (hne : seed.Nonempty)
    (hcard : B.card ≤ seed.card + fuel)
    (hpair : (B : Set _).Pairwise fun a b => compatible (cells a) (cells b))
    (hv : valid cells B)
    (hconn : RidgeConnected (ridges cells) B)
    (hcheck : growCheck Finset.univ (ridges cells) (ridgeList n)
      (allowed cells) (accept hn cells templates tree) fuel seed = true) :
    ∃ (p : Equiv.Perm (Fin n)) (j : Fin t),
      relabelBoundary cells p B = templates j := by
  apply accept_has_relabeling hn cells templates tree B hv
  apply growCheck_complete Finset.univ (ridges cells) (ridgeList n)
    (allowed cells) (accept hn cells templates tree) B
    (fun _ _ => Finset.mem_univ _) mem_ridgeList hv.1 hconn
    (fun S hS c hc hcS => allowed_of_subset cells B S hpair hv hS c hc hcS)
    fuel seed hseed hne hcard hcheck

end Papers.RationalityTen.PolygonBoundaryCatalogue

end
end BundlePart3

section BundlePart4
/- Source: FiniteFacetCells.lean -/





@[expose] public section

/-!
# Complete finite facet cells, independent of convex geometry

A cell retains its vertex set and its full edge and ridge families. These
same definitions are used by actual-polytope encoding and by the executable
finite certificates. Relabeling maps every part of the cell together.
-/

namespace Papers.RationalityTen.MatroidChecked.FacetBoundaryEncoding
open Finset

structure Cell (n : ℕ) where
  vertices : Finset (Fin n)
  edges : Finset (Finset (Fin n))
  ridges : Finset (Finset (Fin n))
  deriving DecidableEq

def Cell.properFaces {n : ℕ} (C : Cell n) : Finset (Finset (Fin n)) :=
  {∅} ∪ C.vertices.image (fun v => {v}) ∪ C.edges ∪ C.ridges

def Cell.Compatible {n : ℕ} (C D : Cell n) : Prop :=
  C.vertices ∩ D.vertices ∈ C.properFaces ∧
  C.vertices ∩ D.vertices ∈ D.properFaces ∧
  ∀ e : Finset (Fin n), e ⊆ C.vertices ∩ D.vertices →
    (e ∈ C.edges ↔ e ∈ D.edges)

instance {n : ℕ} (C D : Cell n) : Decidable (C.Compatible D) := by
  unfold Cell.Compatible
  infer_instance

end Papers.RationalityTen.MatroidChecked.FacetBoundaryEncoding

namespace Papers.RationalityTen.ActualFacetCatalogueTransport
open Finset PolygonBoundaryCatalogue MatroidChecked.FacetBoundaryEncoding
variable {m n : ℕ}

/-- The exact three-dimensional cell determined by a polygon template.
Every polygon contributes its actual edge pairs, not just a vertex mask. -/
def cellOfBoundary (B : Finset (Polygon n)) : Cell n where
  vertices := Finset.univ
  edges := B.biUnion fun C => C.edges.image (fun e => ({e.1, e.2} : Finset (Fin n)))
  ridges := B.image Polygon.vertices

/-- Transport a complete cell along an injective labeling map. -/
def mapCell (f : Fin m ↪ Fin n) (C : Cell m) : Cell n where
  vertices := C.vertices.image f
  edges := C.edges.image (fun S => S.image f)
  ridges := C.ridges.image (fun S => S.image f)

theorem cell_ext (A B : Cell n) (hv : A.vertices = B.vertices)
    (he : A.edges = B.edges) (hr : A.ridges = B.ridges) : A = B := by
  cases A
  cases B
  cases hv
  cases he
  cases hr
  rfl

end Papers.RationalityTen.ActualFacetCatalogueTransport

end
end BundlePart4

section BundlePart5
/- Source: MatroidChecked/IncidentFacetSimplicity.lean -/






@[expose] public section
noncomputable section

/-!
# Four incident facets are equivalent to simplicity in dimension four

The proof uses the genuine vertex figure. Its vertex count is the number
of edges at the original vertex, and its facet count is the number of
incident facets. Euler's formula and the minimum-degree bound imply
`degree + 4 ≤ 2 * incident facets`. Conversely a figure with four vertices
has exactly six edges and four facets. No polar realization is assumed.
-/

namespace Papers.RationalityTen.MatroidChecked.IncidentFacetSimplicity

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeVertexCone Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeEulerThree Papers.PolytopeEulerFour
open scoped Classical BigOperators

variable {d : ℕ}

def graphNeighborEquiv (P : ConvexPolytope d) (v : P.vertices) :
    (vertexGraph P).neighborSet v ≃ actualNeighbors P v.val where
  toFun w := ⟨w.val.val,Finset.mem_filter.mpr ⟨w.val.property,w.property⟩⟩
  invFun w := ⟨⟨w.val,(Finset.mem_filter.mp w.property).1⟩,
    (Finset.mem_filter.mp w.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem degree_eq_actual_neighbors (P : ConvexPolytope d) (v : P.vertices) :
    (vertexGraph P).degree v = (actualNeighbors P v.val).card := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (graphNeighborEquiv P v)).trans (Fintype.card_coe _)

theorem edge_count_eq (P : ConvexPolytope d) :
    (vertexGraph P).edgeFinset.card = Nat.card (Face P 1) := by
  rw [← SimpleGraph.card_edgeSet,← Nat.card_eq_fintype_card]
  exact graph_edge_card_eq_one_face_card P

theorem three_vertex_edge_bound (P : ConvexPolytope d) (hdim : P.dim = 3) :
    3 * P.vertices.card ≤ 2 * Nat.card (Face P 1) := by
  have hdeg : ∀ v : P.vertices, 3 ≤ (vertexGraph P).degree v := by
    intro v
    rw [degree_eq_actual_neighbors]
    simpa only [hdim] using actual_neighbor_card_ge_dim P v.property
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hdeg v)
  have hhand := (vertexGraph P).sum_degrees_eq_twice_card_edges
  rw [hhand,edge_count_eq] at hs
  simpa [mul_comm] using hs

theorem four_vertex_three_polytope_has_four_facets
    (P : ConvexPolytope d) (hdim : P.dim = 3) (hvertices : P.vertices.card = 4) :
    Nat.card (Face P 2) = 4 := by
  have heuler := euler_three P hdim
  have hlo := three_vertex_edge_bound P hdim
  have hup := (vertexGraph P).card_edgeFinset_le_card_choose_two
  rw [edge_count_eq] at hup
  simp only [Fintype.card_coe,hvertices] at hup
  rw [show Nat.choose 4 2 = 6 by decide] at hup
  rw [hvertices] at heuler hlo
  omega

theorem neighbor_facet_count_bound (P : ConvexPolytope d)
    (hdim : P.dim = 4) (v : P.vertices) :
    (actualNeighbors P v.val).card + 4 ≤ 2 * Nat.card (IncidentFace P v.val 3) := by
  obtain ⟨D⟩ := exists_figure P v.property (by omega)
  have hD : D.figure.dim = 3 := figure_dim D v.property 3 hdim
  have hV : D.figure.vertices.card = (actualNeighbors P v.val).card := by
    have h := Nat.card_congr (neighborEquiv D v.property)
    simpa using h.symm
  have hF : Nat.card (IncidentFace P v.val 3) = Nat.card (Face D.figure 2) :=
    Nat.card_congr (incidentFigureEquiv D 2)
  have he := euler_three D.figure hD
  have hdeg := three_vertex_edge_bound D.figure hD
  rw [hV] at he hdeg
  rw [hF]
  omega

/-- Euler's equation for the genuine vertex figure, expressed solely by
the incident faces of the original four-polytope. -/
theorem incident_face_euler (P : ConvexPolytope d)
    (hdim : P.dim = 4) (v : P.vertices) :
    Nat.card (IncidentFace P v.val 1) + Nat.card (IncidentFace P v.val 3) =
      Nat.card (IncidentFace P v.val 2) + 2 := by
  obtain ⟨D⟩ := exists_figure P v.property (by omega)
  have hD : D.figure.dim = 3 := figure_dim D v.property 3 hdim
  have h0 := Nat.card_congr (zeroFaceEquiv D.figure)
  have h1 := Nat.card_congr (incidentFigureEquiv D 0)
  have h2 := Nat.card_congr (incidentFigureEquiv D 1)
  have h3 := Nat.card_congr (incidentFigureEquiv D 2)
  have he := euler_three D.figure hD
  have hv : Nat.card D.figure.vertices = D.figure.vertices.card := by simp
  rw [h1, h2, h3, ← h0, hv]
  omega

theorem incident_edges_eq_neighbors (P : ConvexPolytope d)
    (hdim : P.dim = 4) (v : P.vertices) :
    Nat.card (IncidentFace P v.val 1) = (actualNeighbors P v.val).card := by
  obtain ⟨D⟩ := exists_figure P v.property (by omega)
  have h0 := Nat.card_congr (zeroFaceEquiv D.figure)
  have h1 := Nat.card_congr (incidentFigureEquiv D 0)
  have hn := Nat.card_congr (neighborEquiv D v.property)
  simpa using h1.trans (h0.symm.trans hn.symm)

theorem incident_edges_facet_bound (P : ConvexPolytope d)
    (hdim : P.dim = 4) (v : P.vertices) :
    Nat.card (IncidentFace P v.val 1) + 4 ≤ 2 * Nat.card (IncidentFace P v.val 3) := by
  rw [incident_edges_eq_neighbors P hdim v]
  exact neighbor_facet_count_bound P hdim v

theorem nonsimple_incident_edges_ge_five (P : ConvexPolytope d)
    (hdim : P.dim = 4) (v : P.vertices)
    (hnonsimple : (actualNeighbors P v.val).card ≠ 4) :
    5 ≤ Nat.card (IncidentFace P v.val 1) := by
  rw [incident_edges_eq_neighbors P hdim v]
  have h := actual_neighbor_card_ge_dim P v.property
  rw [hdim] at h
  omega

/-- This is the exact simplicity equivalence used by the finite search.
Both counts refer to the original polytope's actual faces. -/
theorem four_incident_facets_iff_simple (P : ConvexPolytope d)
    (hdim : P.dim = 4) (v : P.vertices) :
    Nat.card (IncidentFace P v.val 3) = 4 ↔ (actualNeighbors P v.val).card = 4 := by
  constructor
  · intro hfacets
    have hmin := actual_neighbor_card_ge_dim P v.property
    have hmax := neighbor_facet_count_bound P hdim v
    rw [hdim] at hmin
    omega
  · intro hs
    obtain ⟨D⟩ := exists_figure P v.property (by omega)
    have hD : D.figure.dim = 3 := figure_dim D v.property 3 hdim
    have hV : D.figure.vertices.card = 4 := by
      have h := Nat.card_congr (neighborEquiv D v.property)
      simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,hs] using h.symm
    rw [Nat.card_congr (incidentFigureEquiv D 2)]
    exact four_vertex_three_polytope_has_four_facets D.figure hD hV

theorem nonsimple_vertex_has_five_facets (P : ConvexPolytope d)
    (hdim : P.dim = 4) (v : P.vertices)
    (hnonsimple : (actualNeighbors P v.val).card ≠ 4) :
    5 ≤ Nat.card (IncidentFace P v.val 3) := by
  have hmin := actual_neighbor_card_ge_dim P v.property
  have hcount := neighbor_facet_count_bound P hdim v
  rw [hdim] at hmin
  omega

end Papers.RationalityTen.MatroidChecked.IncidentFacetSimplicity

end
end
end BundlePart5

section BundlePart6
/- Source: MatroidChecked/FacetBoundaryEncoding.lean -/






@[expose] public section
noncomputable section

/-!
# Actual four-polytope boundaries as finite search inputs

The cells in a boundary search record actual vertex, edge and ridge
labels. Ridge pairing and connectedness are derived from convex geometry.
They are not separate assumptions on the input polytope. A finite cell
universe must still prove that it contains every actual facet.
-/

namespace Papers.RationalityTen.MatroidChecked.FacetBoundaryEncoding

open Set Module Finset
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeBoundaryIncidence
open Papers.RationalityTen.BoundarySearch
open scoped Classical

def faceLabels {d n k : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P k) : Finset (Fin n) :=
  (faceCode P k F).image lab

theorem faceLabels_injective {d n k : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) : Function.Injective (faceLabels (k:=k) P lab) := by
  intro F G h
  exact faceCode_injective P k ((Finset.image_injective lab.injective) h)

theorem mem_faceLabels_iff {d n k : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P k) (v : Fin n) :
    v ∈ faceLabels P lab F ↔ (lab.symm v).val ∈ F.val.carrier := by
  constructor
  · intro hv
    obtain ⟨w,hw,hwv⟩ := Finset.mem_image.mp hv
    have hw' : w = lab.symm v := by simpa using congrArg lab.symm hwv
    subst w
    exact (Finset.mem_filter.mp hw).2
  · intro hv
    exact Finset.mem_image.mpr ⟨lab.symm v,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,lab.apply_symm_apply v⟩

def actualCell {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3) : Cell n where
  vertices := faceLabels P lab F
  edges := ((Finset.univ : Finset (Face P 1)).filter
    (fun e => e.val.carrier ⊆ F.val.carrier)).image (faceLabels P lab)
  ridges := (actualRidges P 2 F).image (faceLabels P lab)

theorem actualCell_injective {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) : Function.Injective (actualCell P lab) := by
  intro F G h
  exact faceLabels_injective P lab (congrArg Cell.vertices h)

structure Encoding {d n c : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (cells : Fin c → Cell n) where
  index : Face P 3 → Fin c
  index_spec : ∀ F, cells (index F) = actualCell P lab F

theorem encoding_of_coverage {d n c : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (cells : Fin c → Cell n)
    (h : ∀ F : Face P 3, ∃ i, cells i = actualCell P lab F) :
    Nonempty (Encoding P lab cells) := by
  choose f hf using h
  exact ⟨⟨f,hf⟩⟩

namespace Encoding

variable {d n c : ℕ} {P : ConvexPolytope d}
  {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n}

theorem index_injective (E : Encoding P lab cells) : Function.Injective E.index := by
  intro F G h
  apply actualCell_injective P lab
  rw [← E.index_spec,← E.index_spec,h]

def family (E : Encoding P lab cells) : Finset (Fin c) :=
  Finset.univ.image E.index

@[simp] theorem mem_family (E : Encoding P lab cells) (i : Fin c) :
    i ∈ E.family ↔ ∃ F : Face P 3, E.index F = i := by
  simp [family]

/-- Different actual facets have different vertex sets, even if the
ambient finite candidate universe contains redundant records. -/
theorem vertices_injective_on_family (E : Encoding P lab cells) :
    Set.InjOn (fun i => (cells i).vertices) E.family := by
  intro i hi j hj heq
  obtain ⟨F,rfl⟩ := (E.mem_family i).mp hi
  obtain ⟨G,rfl⟩ := (E.mem_family j).mp hj
  have hFG : F = G := by
    apply faceLabels_injective P lab
    simpa only [E.index_spec,actualCell] using heq
  exact congrArg E.index hFG

theorem family_card (E : Encoding P lab cells) :
    E.family.card = Nat.card (Face P 3) := by
  rw [family,Finset.card_image_of_injective _ E.index_injective,Finset.card_univ]
  exact Nat.card_eq_fintype_card.symm

theorem exact_family (E : Encoding P lab cells) :
    E.family.image cells =
      (Finset.univ : Finset (Face P 3)).image (actualCell P lab) := by
  simp only [family,Finset.image_image]
  congr 1
  funext F
  exact E.index_spec F

def vertexIncidence (E : Encoding P lab cells) (v : Fin n) : Finset (Fin c) :=
  E.family.filter fun i => v ∈ (cells i).vertices

theorem vertex_incidence_image (E : Encoding P lab cells) (v : Fin n) :
    E.vertexIncidence v =
      ((Finset.univ : Finset (Face P 3)).filter
        fun F => (lab.symm v).val ∈ F.val.carrier).image E.index := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiB,hiv⟩ := Finset.mem_filter.mp hi
    obtain ⟨F,hFi⟩ := (E.mem_family i).mp hiB
    rw [← hFi,E.index_spec] at hiv
    exact Finset.mem_image.mpr ⟨F,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_faceLabels_iff P lab F v).mp hiv⟩,hFi⟩
  · intro hi
    obtain ⟨F,hF,hFi⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨(E.mem_family i).mpr ⟨F,hFi⟩,?_⟩
    rw [← hFi,E.index_spec]
    exact (mem_faceLabels_iff P lab F v).mpr (Finset.mem_filter.mp hF).2

theorem vertex_incidence_card (E : Encoding P lab cells) (v : Fin n) :
    (E.vertexIncidence v).card =
      Nat.card (Papers.PolytopeIncidenceCounting.IncidentFace P (lab.symm v).val 3) := by
  rw [E.vertex_incidence_image,Finset.card_image_of_injective _ E.index_injective,
    Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- The search's minimum facet-degree constraint follows from intrinsic
nonsimplicity. No equality between graph degree and facet-degree is used. -/
theorem vertex_incidence_ge_five (E : Encoding P lab cells) (hdim : P.dim = 4)
    (hnonsimple : ∀ v : P.vertices,
      (Papers.PolytopeVertexCone.actualNeighbors P v.val).card ≠ 4) (v : Fin n) :
    5 ≤ (E.vertexIncidence v).card := by
  rw [E.vertex_incidence_card]
  exact IncidentFacetSimplicity.nonsimple_vertex_has_five_facets
    P hdim (lab.symm v) (hnonsimple _)

theorem ridge_incidence_image (E : Encoding P lab cells) (R : Face P 2) :
    incidence (fun i => (cells i).ridges) E.family (faceLabels P lab R) =
      (incidence (actualRidges P 2) Finset.univ R).image E.index := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiB,hiR⟩ := Finset.mem_filter.mp hi
    change faceLabels P lab R ∈ (cells i).ridges at hiR
    obtain ⟨F,hFi⟩ := (E.mem_family i).mp hiB
    rw [← hFi,E.index_spec] at hiR
    obtain ⟨R',hR'F,hR'R⟩ := Finset.mem_image.mp hiR
    have heq : R' = R := faceLabels_injective P lab hR'R
    subst R'
    exact Finset.mem_image.mpr ⟨F,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR'F⟩,hFi⟩
  · intro hi
    obtain ⟨F,hF,hFi⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨(E.mem_family i).mpr ⟨F,hFi⟩,?_⟩
    change faceLabels P lab R ∈ (cells i).ridges
    rw [← hFi,E.index_spec]
    exact Finset.mem_image.mpr ⟨R,(Finset.mem_filter.mp hF).2,rfl⟩

/-- Every encoded ridge has exactly two incident actual facets; a label
set which is not an actual ridge has no incidences. -/
theorem ridge_pairing (E : Encoding P lab cells) (hdim : P.dim = 4) :
    ∀ r : Finset (Fin n),
      (incidence (fun i => (cells i).ridges) E.family r).card = 0 ∨
      (incidence (fun i => (cells i).ridges) E.family r).card = 2 := by
  intro r
  by_cases hex : ∃ R : Face P 2, faceLabels P lab R = r
  · obtain ⟨R,rfl⟩ := hex
    right
    rw [E.ridge_incidence_image,Finset.card_image_of_injective _ E.index_injective]
    exact actual_ridge_incidence_card P 2 hdim R
  · left
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hiB,hir⟩ := Finset.mem_filter.mp hi
    change r ∈ (cells i).ridges at hir
    obtain ⟨F,hFi⟩ := (E.mem_family i).mp hiB
    rw [← hFi,E.index_spec] at hir
    obtain ⟨R,_,hR⟩ := Finset.mem_image.mp hir
    exact hex ⟨R,hR⟩

/-- The graph used by rooted growth is connected because the actual
facet adjacency graph of a convex four-polytope is connected. -/
theorem ridge_connected (E : Encoding P lab cells) (hdim : P.dim = 4) :
    RidgeConnected (fun i => (cells i).ridges) E.family := by
  intro S hSB hSne hSneq
  let T : Finset (Face P 3) := Finset.univ.filter fun F => E.index F ∈ S
  have hTne : T.Nonempty := by
    obtain ⟨i,hi⟩ := hSne
    obtain ⟨F,hFi⟩ := (E.mem_family i).mp (hSB hi)
    exact ⟨F,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hFi] using hi⟩⟩
  have hTneq : T ≠ Finset.univ := by
    intro hT
    apply hSneq
    apply Finset.Subset.antisymm hSB
    intro i hi
    obtain ⟨F,hFi⟩ := (E.mem_family i).mp hi
    have hF : F ∈ T := by rw [hT]; exact Finset.mem_univ _
    exact hFi ▸ (Finset.mem_filter.mp hF).2
  obtain ⟨A,hA,B,_,hBT,R,hRA,hRB⟩ :=
    actual_boundary_ridge_connected P 2 hdim T (Finset.filter_subset _ _) hTne hTneq
  have hiA : E.index A ∈ S := (Finset.mem_filter.mp hA).2
  have hiB : E.index B ∉ S := by
    intro h
    exact hBT (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  refine ⟨E.index A,hiA,E.index B,(E.mem_family _).mpr ⟨B,rfl⟩,hiB,
    faceLabels P lab R,?_,?_⟩
  · change faceLabels P lab R ∈ (cells (E.index A)).ridges
    rw [E.index_spec]
    exact Finset.mem_image.mpr ⟨R,hRA,rfl⟩
  · change faceLabels P lab R ∈ (cells (E.index B)).ridges
    rw [E.index_spec]
    exact Finset.mem_image.mpr ⟨R,hRB,rfl⟩

/-- End-to-end application of a finite rooted-growth check to the actual
boundary family. The computable pruning rules must be justified on every
subfamily of that boundary; nothing about a searched catalogue is assumed. -/
theorem accepted_of_growth (E : Encoding P lab cells) (hdim : P.dim = 4)
    (allowed : Finset (Fin c) → Fin c → Bool) (accept : Finset (Fin c) → Bool)
    (hallowed : ∀ S ⊆ E.family, ∀ i ∈ E.family, i ∉ S → allowed S i = true)
    (fuel : ℕ) (S : Finset (Fin c)) (hS : S ⊆ E.family) (hne : S.Nonempty)
    (hcard : Nat.card (Face P 3) ≤ S.card + fuel)
    (hcheck : growCheck Finset.univ (fun i => (cells i).ridges)
      (Finset.univ : Finset (Finset (Fin n))).toList allowed accept fuel S = true) :
    accept E.family = true := by
  apply growCheck_complete Finset.univ (fun i => (cells i).ridges)
    (Finset.univ : Finset (Finset (Fin n))).toList allowed accept E.family
    (Finset.subset_univ _) (fun r => by simp) (E.ridge_pairing hdim)
    (E.ridge_connected hdim) hallowed fuel S hS hne
  · simpa only [E.family_card] using hcard
  · exact hcheck

end Encoding
end Papers.RationalityTen.MatroidChecked.FacetBoundaryEncoding

end
end
end BundlePart6

section BundlePart7
/- Source: MatroidChecked/FacetBoundaryCompatibility.lean -/



@[expose] public section
noncomputable section

/-!
# Face-intersection constraints for actual facet cells

The literal SAT universe uses vertex, edge and ridge labels. Compatibility
is justified here by intersections of actual exposed faces. In particular
the cycle of a shared quadrilateral is fixed by its actual edges, so two
facets cannot silently give different cycles to the same four vertices.
-/

namespace Papers.RationalityTen.MatroidChecked.FacetBoundaryEncoding

open Set Module Finset
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeBoundaryIncidence
open Papers.Polytopes
open scoped Classical

theorem faceLabels_subset_iff {d n k l : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (A : Face P k) (B : Face P l) :
    faceLabels P lab A ⊆ faceLabels P lab B ↔ A.val.carrier ⊆ B.val.carrier := by
  constructor
  · intro h
    rw [face_eq_hull_vertices P A.val.isFace]
    apply convexHull_min
    · intro x hx
      change x ∈ P.vertices.filter (· ∈ A.val.carrier) at hx
      obtain ⟨hxP,hxA⟩ := Finset.mem_filter.mp hx
      let v : P.vertices := ⟨x,hxP⟩
      have hvA : lab v ∈ faceLabels P lab A := by
        rw [mem_faceLabels_iff,lab.symm_apply_apply]
        exact hxA
      have hvB := (mem_faceLabels_iff P lab B (lab v)).mp (h hvA)
      simpa only [lab.symm_apply_apply] using hvB
    · exact B.val.isFace.1.convex (convex_convexHull ℝ _)
  · intro h v hv
    exact (mem_faceLabels_iff P lab B v).mpr
      (h ((mem_faceLabels_iff P lab A v).mp hv))

theorem actualCell_edge_iff {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3) (e : Finset (Fin n)) :
    e ∈ (actualCell P lab F).edges ↔ ∃ E : Face P 1,
      E.val.carrier ⊆ F.val.carrier ∧ faceLabels P lab E = e := by
  simp [actualCell]

theorem actualCell_ridge_iff {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3) (r : Finset (Fin n)) :
    r ∈ (actualCell P lab F).ridges ↔ ∃ R : Face P 2,
      R.val.carrier ⊆ F.val.carrier ∧ faceLabels P lab R = r := by
  simp [actualCell]

theorem actualCell_inter_mem_properFaces {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (A B : Face P 3) (hne : A ≠ B) :
    (actualCell P lab A).vertices ∩ (actualCell P lab B).vertices ∈
      (actualCell P lab A).properFaces := by
  let I := faceLabels P lab A ∩ faceLabels P lab B
  change I ∈ (actualCell P lab A).properFaces
  by_cases hI : I = ∅
  · simp [hI,Cell.properFaces]
  obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr hI
  have hvAB : (lab.symm v).val ∈ A.val.carrier ∩ B.val.carrier :=
    ⟨(mem_faceLabels_iff P lab A v).mp (Finset.mem_inter.mp hv).1,
     (mem_faceLabels_iff P lab B v).mp (Finset.mem_inter.mp hv).2⟩
  have hface : P.IsFace (A.val.carrier ∩ B.val.carrier) :=
    ⟨A.val.isFace.1.inter B.val.isFace.1,⟨_,hvAB⟩⟩
  have hproper : A.val.carrier ∩ B.val.carrier ⊂ A.val.carrier := by
    refine ⟨Set.inter_subset_left,?_⟩
    intro hback
    have hAB : A.val.carrier ⊆ B.val.carrier := fun x hx => (hback hx).2
    have hABproper : A.val.carrier ⊂ B.val.carrier := by
      refine ⟨hAB,?_⟩
      intro hBA
      apply hne
      exact Subtype.ext (PolytopeFace.ext (Set.Subset.antisymm hAB hBA))
    have hlt := faceDim_lt_of_ssubset P A.val.isFace B.val.isFace hABproper
    rw [A.property,B.property] at hlt
    omega
  have hlt := faceDim_lt_of_ssubset P hface A.val.isFace hproper
  rw [A.property] at hlt
  have casesdim : faceDim (A.val.carrier ∩ B.val.carrier) = 0 ∨
      faceDim (A.val.carrier ∩ B.val.carrier) = 1 ∨
      faceDim (A.val.carrier ∩ B.val.carrier) = 2 := by omega
  rcases casesdim with hzero | hedge | hridge
  · obtain ⟨x,hx,hIx⟩ := actual_zeroFace_is_vertex P
      (A.val.carrier ∩ B.val.carrier) hface hzero
    let xx : P.vertices := ⟨x,hx⟩
    have hIxx : I = {lab xx} := by
      ext z
      simp only [I,Finset.mem_inter,mem_faceLabels_iff,Finset.mem_singleton]
      constructor
      · intro hz
        have hzI : (lab.symm z).val ∈ A.val.carrier ∩ B.val.carrier := hz
        have he : (lab.symm z).val = x := by
          simpa only [hIx,Set.mem_singleton_iff] using hzI
        have hvx : lab.symm z = xx := Subtype.ext he
        simpa only [lab.apply_symm_apply] using congrArg lab hvx
      · intro hz
        subst z
        rw [lab.symm_apply_apply]
        have hxI : x ∈ A.val.carrier ∩ B.val.carrier := by rw [hIx]; exact Set.mem_singleton x
        exact hxI
    have hxxA : lab xx ∈ (actualCell P lab A).vertices := by
      apply (mem_faceLabels_iff P lab A _).mpr
      rw [lab.symm_apply_apply]
      have hxI : x ∈ A.val.carrier ∩ B.val.carrier := by rw [hIx]; exact Set.mem_singleton x
      exact hxI.1
    rw [hIxx]
    simp [Cell.properFaces,hxxA]
  · let E : Face P 1 := ⟨⟨A.val.carrier ∩ B.val.carrier,hface⟩,hedge⟩
    have hlabels : faceLabels P lab E = I := by
      ext z
      simp only [I,Finset.mem_inter,mem_faceLabels_iff]
      rfl
    have hE : I ∈ (actualCell P lab A).edges :=
      (actualCell_edge_iff P lab A I).mpr ⟨E,Set.inter_subset_left,hlabels⟩
    simp [Cell.properFaces,hE]
  · let R : Face P 2 := ⟨⟨A.val.carrier ∩ B.val.carrier,hface⟩,hridge⟩
    have hlabels : faceLabels P lab R = I := by
      ext z
      simp only [I,Finset.mem_inter,mem_faceLabels_iff]
      rfl
    have hR : I ∈ (actualCell P lab A).ridges :=
      (actualCell_ridge_iff P lab A I).mpr ⟨R,Set.inter_subset_left,hlabels⟩
    simp [Cell.properFaces,hR]

theorem actualCell_compatible {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (A B : Face P 3) (hne : A ≠ B) :
    (actualCell P lab A).Compatible (actualCell P lab B) := by
  refine ⟨actualCell_inter_mem_properFaces P lab A B hne,?_,?_⟩
  · simpa only [Finset.inter_comm] using
      actualCell_inter_mem_properFaces P lab B A hne.symm
  · intro e he
    constructor
    · intro hA
      obtain ⟨E,_,hE⟩ := (actualCell_edge_iff P lab A e).mp hA
      apply (actualCell_edge_iff P lab B e).mpr
      refine ⟨E,?_,hE⟩
      apply (faceLabels_subset_iff P lab E B).mp
      rw [hE]
      exact fun v hv => (Finset.mem_inter.mp (he hv)).2
    · intro hB
      obtain ⟨E,_,hE⟩ := (actualCell_edge_iff P lab B e).mp hB
      apply (actualCell_edge_iff P lab A e).mpr
      refine ⟨E,?_,hE⟩
      apply (faceLabels_subset_iff P lab E A).mp
      rw [hE]
      exact fun v hv => (Finset.mem_inter.mp (he hv)).1

theorem Encoding.pairwise_compatible {d n c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n} (E : Encoding P lab cells) :
    (E.family : Set (Fin c)).Pairwise fun i j => (cells i).Compatible (cells j) := by
  intro i hi j hj hij
  obtain ⟨A,hAi⟩ := (E.mem_family i).mp hi
  obtain ⟨B,hBj⟩ := (E.mem_family j).mp hj
  have hAB : A ≠ B := by intro h; exact hij (hAi.symm.trans ((congrArg E.index h).trans hBj))
  rw [← hAi,← hBj,E.index_spec,E.index_spec]
  exact actualCell_compatible P lab A B hAB

theorem lower_face_in_some_facet {d k : ℕ} (P : ConvexPolytope d)
    (hdim : P.dim = 4) (hk : k < 4) (A : Face P k) :
    ∃ F : Face P 3, A.val.carrier ⊆ F.val.carrier := by
  have hproper : A.val.carrier ⊂ P.toSet := by
    refine (face_subset_toSet P A.val.isFace).ssubset_of_ne ?_
    intro h
    have he := congrArg faceDim h
    change faceDim A.val.carrier = P.dim at he
    rw [A.property,hdim] at he
    omega
  obtain ⟨F,hF,hAF,_,hdF⟩ := facet_above_proper_face P A.val.isFace hproper
  have hdimF : faceDim F = 3 := by
    change faceDim F + 1 = P.dim at hdF
    omega
  exact ⟨⟨⟨F,hF⟩,hdimF⟩,hAF⟩

theorem Encoding.edges_eq_actual {d n c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n} (E : Encoding P lab cells)
    (hdim : P.dim = 4) :
    E.family.biUnion (fun i => (cells i).edges) =
      (Finset.univ : Finset (Face P 1)).image (faceLabels P lab) := by
  ext e
  constructor
  · intro he
    obtain ⟨i,hi,hei⟩ := Finset.mem_biUnion.mp he
    obtain ⟨F,hFi⟩ := (E.mem_family i).mp hi
    rw [← hFi,E.index_spec] at hei
    obtain ⟨A,_,hAe⟩ := (actualCell_edge_iff P lab F e).mp hei
    exact Finset.mem_image.mpr ⟨A,Finset.mem_univ _,hAe⟩
  · intro he
    obtain ⟨A,_,hAe⟩ := Finset.mem_image.mp he
    obtain ⟨F,hAF⟩ := lower_face_in_some_facet P hdim (by decide : 1 < 4) A
    apply Finset.mem_biUnion.mpr
    refine ⟨E.index F,(E.mem_family _).mpr ⟨F,rfl⟩,?_⟩
    rw [E.index_spec]
    exact (actualCell_edge_iff P lab F e).mpr ⟨A,hAF,hAe⟩

theorem Encoding.edge_card {d n c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n} (E : Encoding P lab cells)
    (hdim : P.dim = 4) :
    (E.family.biUnion (fun i => (cells i).edges)).card = Nat.card (Face P 1) := by
  rw [E.edges_eq_actual hdim,Finset.card_image_of_injective _ (faceLabels_injective P lab),
    Finset.card_univ]
  exact Nat.card_eq_fintype_card.symm

theorem Encoding.ridges_eq_actual {d n c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n} (E : Encoding P lab cells)
    (hdim : P.dim = 4) :
    E.family.biUnion (fun i => (cells i).ridges) =
      (Finset.univ : Finset (Face P 2)).image (faceLabels P lab) := by
  ext r
  constructor
  · intro hr
    obtain ⟨i,hi,hri⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨F,hFi⟩ := (E.mem_family i).mp hi
    rw [← hFi,E.index_spec] at hri
    obtain ⟨A,_,hAr⟩ := (actualCell_ridge_iff P lab F r).mp hri
    exact Finset.mem_image.mpr ⟨A,Finset.mem_univ _,hAr⟩
  · intro hr
    obtain ⟨A,_,hAr⟩ := Finset.mem_image.mp hr
    obtain ⟨F,hAF⟩ := lower_face_in_some_facet P hdim (by decide : 2 < 4) A
    apply Finset.mem_biUnion.mpr
    refine ⟨E.index F,(E.mem_family _).mpr ⟨F,rfl⟩,?_⟩
    rw [E.index_spec]
    exact (actualCell_ridge_iff P lab F r).mpr ⟨A,hAF,hAr⟩

theorem labelled_incident_card {d n k : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (v : Fin n) :
    (((Finset.univ : Finset (Face P k)).image (faceLabels P lab)).filter
      (fun A => v ∈ A)).card =
      Nat.card (Papers.PolytopeIncidenceCounting.IncidentFace P (lab.symm v).val k) := by
  have heq : ((Finset.univ : Finset (Face P k)).image (faceLabels P lab)).filter
      (fun A => v ∈ A) =
      ((Finset.univ : Finset (Face P k)).filter
        (fun F => (lab.symm v).val ∈ F.val.carrier)).image (faceLabels P lab) := by
    ext A
    constructor
    · intro h
      obtain ⟨hA,hv⟩ := Finset.mem_filter.mp h
      obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hA
      exact Finset.mem_image.mpr ⟨F,Finset.mem_filter.mpr ⟨hF,
        (mem_faceLabels_iff P lab F v).mp hv⟩,rfl⟩
    · intro h
      obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨F,Finset.mem_univ _,rfl⟩,
        (mem_faceLabels_iff P lab F v).mpr (Finset.mem_filter.mp hF).2⟩
  rw [heq,Finset.card_image_of_injective _ (faceLabels_injective P lab),
    Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- The per-vertex equation rules out abstract boundary candidates whose
vertex links fail the Euler equation of an actual convex vertex figure. -/
theorem Encoding.vertex_link_euler {d n c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n} (E : Encoding P lab cells)
    (hdim : P.dim = 4) (v : Fin n) :
    ((E.family.biUnion (fun i => (cells i).edges)).filter (fun A => v ∈ A)).card +
        (E.vertexIncidence v).card =
      ((E.family.biUnion (fun i => (cells i).ridges)).filter (fun A => v ∈ A)).card + 2 := by
  rw [E.edges_eq_actual hdim,E.ridges_eq_actual hdim,E.vertex_incidence_card,
    labelled_incident_card,labelled_incident_card]
  exact IncidentFacetSimplicity.incident_face_euler P hdim (lab.symm v)

theorem Encoding.vertex_link_bound {d n c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n} (E : Encoding P lab cells)
    (hdim : P.dim = 4) (v : Fin n) :
    ((E.family.biUnion (fun i => (cells i).edges)).filter (fun A => v ∈ A)).card + 4 ≤
      2 * (E.vertexIncidence v).card := by
  rw [E.edges_eq_actual hdim,E.vertex_incidence_card,labelled_incident_card]
  exact IncidentFacetSimplicity.incident_edges_facet_bound P hdim (lab.symm v)

theorem Encoding.vertex_edge_incidence_ge_five {d n c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n} (E : Encoding P lab cells)
    (hdim : P.dim = 4)
    (hnonsimple : ∀ v : P.vertices,
      (Papers.PolytopeVertexCone.actualNeighbors P v.val).card ≠ 4) (v : Fin n) :
    5 ≤ ((E.family.biUnion (fun i => (cells i).edges)).filter (fun A => v ∈ A)).card := by
  rw [E.edges_eq_actual hdim,labelled_incident_card]
  exact IncidentFacetSimplicity.nonsimple_incident_edges_ge_five
    P hdim (lab.symm v) (hnonsimple _)

end Papers.RationalityTen.MatroidChecked.FacetBoundaryEncoding

end
end
end BundlePart7

section BundlePart8
/- Source: MatroidChecked/BoundaryTriangleCount.lean -/



@[expose] public section
noncomputable section

/-!
# Graph triangles forced by a small-facet boundary

Every triangular ridge is a graph triangle. A triangular bipyramid also
contributes its equatorial three-cycle. That cycle is contained in no
proper face of the bipyramid. Consequently compatibility makes these
extra cycles pairwise distinct and disjoint from all actual ridges.

The hypotheses concerning the shape of a cell are finite propositions
about its vertex, edge and ridge masks. For a tetrahedron, triangular
bipyramid or square pyramid they can be checked on the literal template.
Pairing and compatibility are supplied by the actual convex boundary.
No catalogue completeness or graph-realizability assumption is used here.
-/

namespace Papers.RationalityTen.MatroidChecked.BoundaryTriangleCount

open Finset Set
open FacetBoundaryEncoding
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators

private theorem double_count_filters {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset A) (t : Finset B) (r : A → B → Prop)
    [∀ a b, Decidable (r a b)] :
    (∑ a ∈ s, (t.filter (r a)).card) = ∑ b ∈ t, (s.filter fun a => r a b).card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

private theorem actual_ridge_subset_vertices {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {cells : Fin c → Cell 10}
    (E : Encoding P lab cells) (i : Fin c) (hi : i ∈ E.family)
    (r : Finset (Fin 10)) (hr : r ∈ (cells i).ridges) :
    r ⊆ (cells i).vertices := by
  obtain ⟨F,hFi⟩ := (E.mem_family i).mp hi
  rw [← hFi,E.index_spec] at hr ⊢
  obtain ⟨R,hRF,hR⟩ := (actualCell_ridge_iff P lab F r).mp hr
  rw [← hR]
  exact (faceLabels_subset_iff P lab R F).mpr hRF

def graphTriangles {n : ℕ} (edges : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 3).filter fun T => T.powersetCard 2 ⊆ edges

theorem mem_graphTriangles {n : ℕ} (edges : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) :
    T ∈ graphTriangles edges ↔ T.card = 3 ∧ T.powersetCard 2 ⊆ edges := by
  simp [graphTriangles,Finset.mem_powersetCard]

def triangularRidges {n c : ℕ} (cells : Fin c → Cell n) (S : Finset (Fin c)) :
    Finset (Finset (Fin n)) :=
  (S.biUnion fun i => (cells i).ridges).filter fun T => T.card = 3

/-- The equatorial triangle of a triangular bipyramid satisfies these
literal rules. The last rule is stronger than merely being a non-ridge:
no proper face contains the full triangle. -/
structure BaseRules {n : ℕ} (C : Cell n) (T : Finset (Fin n)) : Prop where
  card : T.card = 3
  vertices : T ⊆ C.vertices
  edges : T.powersetCard 2 ⊆ C.edges
  nonfacial : ∀ F ∈ C.properFaces, ¬T ⊆ F

theorem bases_injective {n c : ℕ} (cells : Fin c → Cell n)
    (S B : Finset (Fin c)) (hBS : B ⊆ S)
    (hcompat : (S : Set (Fin c)).Pairwise fun i j => (cells i).Compatible (cells j))
    (base : Fin c → Finset (Fin n)) (hrules : ∀ i ∈ B, BaseRules (cells i) (base i)) :
    Set.InjOn base B := by
  intro i hi j hj heq
  by_contra hij
  have hc := hcompat (hBS hi) (hBS hj) hij
  apply (hrules i hi).nonfacial _ hc.1
  intro v hv
  exact Finset.mem_inter.mpr ⟨(hrules i hi).vertices hv,
    (hrules j hj).vertices (heq ▸ hv)⟩

theorem bases_disjoint_ridges {n c : ℕ} (cells : Fin c → Cell n)
    (S B : Finset (Fin c)) (hBS : B ⊆ S)
    (hcompat : (S : Set (Fin c)).Pairwise fun i j => (cells i).Compatible (cells j))
    (hridge : ∀ i ∈ S, ∀ R ∈ (cells i).ridges, R ⊆ (cells i).vertices)
    (base : Fin c → Finset (Fin n)) (hrules : ∀ i ∈ B, BaseRules (cells i) (base i)) :
    Disjoint (B.image base) (S.biUnion fun i => (cells i).ridges) := by
  apply Finset.disjoint_left.mpr
  intro T hT hR
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨j,hj,hbasej⟩ := Finset.mem_biUnion.mp hR
  by_cases hij : i = j
  · subst j
    exact (hrules i hi).nonfacial _ (by simp [Cell.properFaces,hbasej])
      (Finset.Subset.refl _)
  · have hc := hcompat (hBS hi) hj hij
    apply (hrules i hi).nonfacial _ hc.1
    intro v hv
    exact Finset.mem_inter.mpr ⟨(hrules i hi).vertices hv,hridge j hj _ hbasej hv⟩

theorem triangles_include_ridges_and_bases {n c : ℕ} (cells : Fin c → Cell n)
    (S B : Finset (Fin c)) (hBS : B ⊆ S)
    (hcompat : (S : Set (Fin c)).Pairwise fun i j => (cells i).Compatible (cells j))
    (hridge : ∀ i ∈ S, ∀ R ∈ (cells i).ridges, R ⊆ (cells i).vertices)
    (htriangle : ∀ i ∈ S, ∀ R ∈ (cells i).ridges,
      R.card = 3 → R.powersetCard 2 ⊆ (cells i).edges)
    (base : Fin c → Finset (Fin n)) (hrules : ∀ i ∈ B, BaseRules (cells i) (base i)) :
    (triangularRidges cells S).card + B.card ≤
      (graphTriangles (S.biUnion fun i => (cells i).edges)).card := by
  have hdis : Disjoint (triangularRidges cells S) (B.image base) := by
    apply Disjoint.symm
    exact (bases_disjoint_ridges cells S B hBS hcompat hridge base hrules).mono_right
      (Finset.filter_subset _ _)
  have hsub : triangularRidges cells S ∪ B.image base ⊆
      graphTriangles (S.biUnion fun i => (cells i).edges) := by
    intro T hT
    apply (mem_graphTriangles _ T).mpr
    rcases Finset.mem_union.mp hT with hR | hB
    · obtain ⟨hR,hcard⟩ := Finset.mem_filter.mp hR
      obtain ⟨i,hi,hRi⟩ := Finset.mem_biUnion.mp hR
      refine ⟨hcard,?_⟩
      intro e he
      exact Finset.mem_biUnion.mpr ⟨i,hi,htriangle i hi T hRi hcard he⟩
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
      refine ⟨(hrules i hi).card,?_⟩
      intro e he
      exact Finset.mem_biUnion.mpr ⟨i,hBS hi,(hrules i hi).edges he⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injOn (bases_injective cells S B hBS hcompat base hrules)] at hcard
  exact hcard

theorem double_triangular_ridges {n c : ℕ} (cells : Fin c → Cell n)
    (S : Finset (Fin c))
    (hpair : ∀ R : Finset (Fin n),
      (S.filter fun i => R ∈ (cells i).ridges).card = 0 ∨
      (S.filter fun i => R ∈ (cells i).ridges).card = 2) :
    (∑ i ∈ S, ((cells i).ridges.filter fun R => R.card = 3).card) =
      2 * (triangularRidges cells S).card := by
  let T := triangularRidges cells S
  have hfilter (i : Fin c) (hi : i ∈ S) :
      T.filter (fun R => R ∈ (cells i).ridges) =
        (cells i).ridges.filter (fun R => R.card = 3) := by
    ext R
    simp only [T,triangularRidges,Finset.mem_filter,Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨_,hcard⟩,hRi⟩
      exact ⟨hRi,hcard⟩
    · rintro ⟨hRi,hcard⟩
      exact ⟨⟨⟨i,hi,hRi⟩,hcard⟩,hRi⟩
  have htwo (R : Finset (Fin n)) (hR : R ∈ T) :
      (S.filter fun i => R ∈ (cells i).ridges).card = 2 := by
    obtain ⟨i,hi,hRi⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hR).1
    have hpos : 0 < (S.filter fun j => R ∈ (cells j).ridges).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hRi⟩⟩
    have h := hpair R
    omega
  calc
    (∑ i ∈ S, ((cells i).ridges.filter fun R => R.card = 3).card) =
        ∑ i ∈ S, (T.filter fun R => R ∈ (cells i).ridges).card := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfilter i hi]
    _ = ∑ R ∈ T, (S.filter fun i => R ∈ (cells i).ridges).card :=
      double_count_filters S T (fun i R => R ∈ (cells i).ridges)
    _ = ∑ R ∈ T, (2:ℕ) := Finset.sum_congr rfl htwo
    _ = 2 * T.card := by simp [mul_comm]

/-- Each tetrahedron or square pyramid has four triangular ridges; each
triangular bipyramid has six. Ridge pairing counts each ridge twice. -/
theorem triangular_ridge_card {n c : ℕ} (cells : Fin c → Cell n)
    (S B : Finset (Fin c)) (hBS : B ⊆ S)
    (hpair : ∀ R : Finset (Fin n),
      (S.filter fun i => R ∈ (cells i).ridges).card = 0 ∨
      (S.filter fun i => R ∈ (cells i).ridges).card = 2)
    (hshape : ∀ i ∈ S, ((cells i).ridges.filter fun R => R.card = 3).card =
      4 + if i ∈ B then 2 else 0) :
    (triangularRidges cells S).card = 2 * S.card + B.card := by
  have hfilter : S.filter (fun i => i ∈ B) = B := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hBS h,h⟩⟩
  have hsum : (∑ i ∈ S, ((cells i).ridges.filter fun R => R.card = 3).card) =
      4 * S.card + 2 * B.card := by
    calc
      (∑ i ∈ S, ((cells i).ridges.filter fun R => R.card = 3).card) =
          ∑ i ∈ S, (4 + if i ∈ B then 2 else 0) :=
        Finset.sum_congr rfl hshape
      _ = 4 * S.card + 2 * B.card := by
        simp only [Finset.sum_add_distrib]
        rw [← Finset.sum_filter,hfilter]
        simp [mul_comm]
  have h := double_triangular_ridges cells S hpair
  omega

theorem actual_graph_triangle_lower_bound {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {cells : Fin c → Cell 10}
    (E : Encoding P lab cells) (hdim : P.dim = 4)
    (B : Finset (Fin c)) (hBS : B ⊆ E.family)
    (htriangle : ∀ i ∈ E.family, ∀ R ∈ (cells i).ridges,
      R.card = 3 → R.powersetCard 2 ⊆ (cells i).edges)
    (hshape : ∀ i ∈ E.family, ((cells i).ridges.filter fun R => R.card = 3).card =
      4 + if i ∈ B then 2 else 0)
    (base : Fin c → Finset (Fin 10)) (hrules : ∀ i ∈ B, BaseRules (cells i) (base i)) :
    2 * E.family.card + 2 * B.card ≤
      (graphTriangles (E.family.biUnion fun i => (cells i).edges)).card := by
  have h := triangles_include_ridges_and_bases cells E.family B hBS E.pairwise_compatible
    (actual_ridge_subset_vertices E) htriangle base hrules
  have hpair := E.ridge_pairing hdim
  change ∀ R : Finset (Fin 10),
    (E.family.filter fun i => R ∈ (cells i).ridges).card = 0 ∨
    (E.family.filter fun i => R ∈ (cells i).ridges).card = 2 at hpair
  rw [triangular_ridge_card cells E.family B hBS hpair hshape] at h
  omega

end Papers.RationalityTen.MatroidChecked.BoundaryTriangleCount

end
end
end BundlePart8
