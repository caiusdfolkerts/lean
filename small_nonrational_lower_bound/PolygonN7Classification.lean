module

public import PolygonN7ClassificationPart017
meta import Lean.Meta.Tactic.Delta

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem ridgeData_exact (a : Fin 290) :
    (PolygonGrowth.N7.ridgeList a).toFinset = (FiniteCycleCandidates.N7.cells a).edges.image edgeCode := by
  exact of_decide_eq_true (FiniteChecks.fin_of_interval
    (fun a : Fin 290 => decide ((PolygonGrowth.N7.ridgeList a).toFinset =
      (FiniteCycleCandidates.N7.cells a).edges.image edgeCode)) ridge_data_join_00000_00290 a)

theorem ridge_encoding : ∀ a q,
    has (PolygonGrowth.N7.ridgeList a) (edgeCode q) = true ↔ q ∈ (FiniteCycleCandidates.N7.cells a).edges :=
  ridge_code_of_lists FiniteCycleCandidates.N7.cells PolygonGrowth.N7.ridgeList edgeCode ridgeData_exact

theorem compatibility_sound (a b : Fin 290)
    (h : PolygonBoundaryCatalogue.compatible (FiniteCycleCandidates.N7.cells a) (FiniteCycleCandidates.N7.cells b)) :
    PolygonGrowth.N7.compatible a b = true := by
  -- Reuse the decision instance already stored in the checked Boolean row.
  -- Transport its resulting proposition, avoiding a second large instance.
  have ha : compatibilityTest a.val = true := compatibility_data_join_00000_00290 a.val (Nat.zero_le _) a.isLt
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ha ← Lean.Meta.getLocalDeclFromUserName `ha
      let equation ← Lean.instantiateMVars (← Lean.Meta.inferType ha.toExpr)
      unless equation.isAppOfArity ``Eq 3 do
        throwError "Expected the checked row's Boolean equality: {equation}"
      let #[_, lhs, _] := equation.getAppArgs
        | throwError "Expected three equality arguments"
      let expanded ← Lean.Meta.deltaExpand lhs
        (fun name => name == ``compatibilityTest)
      let mut decision := expanded
      for _ in [:256] do
        match decision with
        | .letE _ _ value body _ => decision := body.instantiate1 value
        | .mdata _ body => decision := body
        | _ => break
      unless decision.isAppOfArity ``decide 2 do
        throwError "Expected decide after unfolding the test and its leading lets"
      let #[proposition, inst] := decision.getAppArgs
        | throwError "Expected the proposition and its decision instance"
      let proof := Lean.mkApp3 (Lean.mkConst ``of_decide_eq_true)
        proposition inst ha.toExpr
      let (_, g) ← g.note `hrow proof (some proposition)
      Lean.Elab.Tactic.replaceMainGoal [g]
  have hindex : Fin.ofNat 290 a.val = a := Fin.ofNat_val_eq_self a
  have htransport := congrArg (fun x : Fin 290 => ∀ c : Fin 290,
    PolygonBoundaryCatalogue.compatible
      (FiniteCycleCandidates.N7.cells x) (FiniteCycleCandidates.N7.cells c) →
      PolygonGrowth.N7.compatible x c = true) hindex
  exact (Eq.mp htransport hrow) b h

theorem terminal_checked (j : Fin 3796) :
    terminalCheck FiniteCycleCandidates.N7.cells FiniteCycleCandidates.N7.templates (PolygonGrowth.N7.terminals j)
      (PolygonGrowth.N7.targetTemplate j) (decode (by decide : 0 < 7) (PolygonGrowth.N7.permutationCode j)) = true :=
  FiniteChecks.fin_of_interval (fun j : Fin 3796 =>
    terminalCheck FiniteCycleCandidates.N7.cells FiniteCycleCandidates.N7.templates (PolygonGrowth.N7.terminals j)
      (PolygonGrowth.N7.targetTemplate j) (decode (by decide : 0 < 7) (PolygonGrowth.N7.permutationCode j)))
    terminal_data_join_00000_03796 j

theorem neighbor_coverage : ∀ i ∈ FiniteCycleCandidates.N7.neighbors,
    ∃ seed : Fin 4, PolygonGrowth.N7.neighbors seed = i := by decide +kernel

/-- Complete classification of every paired, compatible, connected polygon
boundary in the normalized universe, with all minimum-degree and Euler
conditions. Every finite certificate premise has been checked above. -/
theorem normalized_classification (S : Finset (Fin 290))
    (hcard : S.card ≤ 2 * 7 - 4)
    (hpair : (S : Set _).Pairwise (fun a b =>
      PolygonBoundaryCatalogue.compatible (FiniteCycleCandidates.N7.cells a) (FiniteCycleCandidates.N7.cells b)))
    (hvalid : valid FiniteCycleCandidates.N7.cells S) (hconn : RidgeConnected (ridges FiniteCycleCandidates.N7.cells) S)
    (hroot : (0 : Fin 290) ∈ S) (hneighbor : (S ∩ FiniteCycleCandidates.N7.neighbors).Nonempty) :
    ∃ (σ : Equiv.Perm (Fin 7)) (i : Fin 34),
      relabelBoundary FiniteCycleCandidates.N7.cells σ S = FiniteCycleCandidates.N7.templates i := by
  obtain ⟨neighbor, hneighbor⟩ := hneighbor
  obtain ⟨hneighborS, hneighborN⟩ := Finset.mem_inter.mp hneighbor
  obtain ⟨seed, hseed⟩ := neighbor_coverage neighbor hneighborN
  have hquota : ∀ j, kindCount PolygonGrowth.N7.kind S.toList j ≤ PolygonGrowth.N7.quota j := by
    change ∀ j, kindCount (fun _ : Fin 290 => 0) S.toList j ≤ if j = 0 then 10 else 0
    exact constant_kind_budget S 10 hcard
  have hcompatible : ∀ a b, a ∈ S.toList → b ∈ S.toList → a ≠ b →
      PolygonGrowth.N7.compatible a b = true := by
    intro a b ha hb hab
    exact compatibility_sound a b (hpair (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb) hab)
  obtain ⟨j, hj⟩ := PolygonGrowth.N7.boundary_classification S.toList hquota hcompatible
    (hasMate_of_valid FiniteCycleCandidates.N7.cells S PolygonGrowth.N7.ridgeList edgeCode ridge_encoding hvalid)
    (noThree_of_valid FiniteCycleCandidates.N7.cells S PolygonGrowth.N7.ridgeList edgeCode ridge_encoding hvalid)
    (connected_of_ridgeConnected FiniteCycleCandidates.N7.cells S PolygonGrowth.N7.ridgeList edgeCode ridge_encoding hconn)
    seed (Finset.mem_toList.mpr hroot) (by rw [hseed]; exact Finset.mem_toList.mpr hneighborS)
  exact terminalCheck_sound FiniteCycleCandidates.N7.cells FiniteCycleCandidates.N7.templates (PolygonGrowth.N7.terminals j)
    (PolygonGrowth.N7.targetTemplate j) (decode (by decide : 0 < 7) (PolygonGrowth.N7.permutationCode j))
    (terminal_checked j) S (finset_eq_of_same _ S hj) hvalid

#print axioms normalized_classification
end Papers.RationalityTen.ConcretePolygonClassification.N7
