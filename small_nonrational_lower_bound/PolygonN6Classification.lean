module

public meta import LowerSchemas.FinitePolygonN
public import FinitePolygonTemplates
public import PolygonN6DAG
public import PolygonDAGSemantics
public import FiniteChecks
meta import Lean.Meta.Tactic.Delta

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N6
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

noncomputable def edgeCode : (Fin 6 × Fin 6) ≃ Fin 36 := finProdFinEquiv

noncomputable def ridgeDataTest (index : ℕ) : Bool :=
  let a := Fin.ofNat 65 index
  decide ((PolygonGrowth.N6.ridgeList a).toFinset = (FiniteCycleCandidates.N6.cells a).edges.image edgeCode)

noncomputable def compatibilityTest (index : ℕ) : Bool :=
  let a := Fin.ofNat 65 index
  decide (∀ b : Fin 65, PolygonBoundaryCatalogue.compatible (FiniteCycleCandidates.N6.cells a) (FiniteCycleCandidates.N6.cells b) →
    PolygonGrowth.N6.compatible a b = true)

noncomputable def terminalTest (index : ℕ) : Bool :=
  let j := Fin.ofNat 110 index
  terminalCheck FiniteCycleCandidates.N6.cells FiniteCycleCandidates.N6.templates (PolygonGrowth.N6.terminals j)
    (PolygonGrowth.N6.targetTemplate j) (decode (by decide : 0 < 6) (PolygonGrowth.N6.permutationCode j))

cert_ridge_data 00000 0 8 8
cert_ridge_data 00008 8 16 8
cert_ridge_data 00016 16 24 8
cert_ridge_data 00024 24 32 8
cert_ridge_data 00032 32 40 8
cert_ridge_data 00040 40 48 8
cert_ridge_data 00048 48 56 8
cert_ridge_data 00056 56 64 8
cert_ridge_data 00064 64 65 1
cert_ridge_data_join 00000 00016 0 16 8 00008
cert_ridge_data_join 00016 00032 16 32 24 00024
cert_ridge_data_join_2 00000 00032 0 32 16 00016
cert_ridge_data_join 00032 00048 32 48 40 00040
cert_ridge_data_join 00056 00065 56 65 64 00064
theorem ridge_data_join_00048_00065 : FiniteChecks.Interval ridgeDataTest 48 65 :=
  FiniteChecks.interval_append ridgeDataTest 48 56 65 ridge_data_00048 ridge_data_join_00056_00065

cert_ridge_data_join_2 00032 00065 32 65 48 00048
cert_ridge_data_join_2 00000 00065 0 65 32 00032
cert_compatibility_data 00000 0 8 8
cert_compatibility_data 00008 8 16 8
cert_compatibility_data 00016 16 24 8
cert_compatibility_data 00024 24 32 8
cert_compatibility_data 00032 32 40 8
cert_compatibility_data 00040 40 48 8
cert_compatibility_data 00048 48 56 8
cert_compatibility_data 00056 56 64 8
cert_compatibility_data 00064 64 65 1
cert_compatibility_data_join_2 00000 00016 0 16 8 00008
cert_compatibility_data_join_2 00016 00032 16 32 24 00024
cert_compatibility_data_join 00000 00032 0 32 16 00016
cert_compatibility_data_join_2 00032 00048 32 48 40 00040
cert_compatibility_data_join_2 00056 00065 56 65 64 00064
theorem compatibility_data_join_00048_00065 : FiniteChecks.Interval compatibilityTest 48 65 :=
  FiniteChecks.interval_append compatibilityTest 48 56 65 compatibility_data_00048 compatibility_data_join_00056_00065

cert_compatibility_data_join 00032 00065 32 65 48 00048
cert_compatibility_data_join 00000 00065 0 65 32 00032
cert_terminal_data 00000 0 8 8
cert_terminal_data 00008 8 16 8
cert_terminal_data 00016 16 24 8
cert_terminal_data 00024 24 32 8
cert_terminal_data 00032 32 40 8
cert_terminal_data 00040 40 48 8
cert_terminal_data 00048 48 56 8
cert_terminal_data 00056 56 64 8
cert_terminal_data 00064 64 72 8
cert_terminal_data 00072 72 80 8
cert_terminal_data 00080 80 88 8
cert_terminal_data 00088 88 96 8
cert_terminal_data 00096 96 104 8
cert_terminal_data 00104 104 110 6
cert_terminal_data_join_2 00008 00024 8 24 16 00016
cert_terminal_data_join_3 00000 00024 0 24 8 00008
cert_terminal_data_join_2 00024 00040 24 40 32 00032
cert_terminal_data_join_2 00040 00056 40 56 48 00048
cert_terminal_data_join 00024 00056 24 56 40 00040
cert_terminal_data_join 00000 00056 0 56 24 00024
cert_terminal_data_join_2 00064 00080 64 80 72 00072
cert_terminal_data_join_3 00056 00080 56 80 64 00064
cert_terminal_data_join_2 00080 00096 80 96 88 00088
cert_terminal_data_join_2 00096 00110 96 110 104 00104
cert_terminal_data_join 00080 00110 80 110 96 00096
cert_terminal_data_join 00056 00110 56 110 80 00080
cert_terminal_data_join 00000 00110 0 110 56 00056
theorem ridgeData_exact (a : Fin 65) :
    (PolygonGrowth.N6.ridgeList a).toFinset = (FiniteCycleCandidates.N6.cells a).edges.image edgeCode := by
  exact of_decide_eq_true (FiniteChecks.fin_of_interval
    (fun a : Fin 65 => decide ((PolygonGrowth.N6.ridgeList a).toFinset =
      (FiniteCycleCandidates.N6.cells a).edges.image edgeCode)) ridge_data_join_00000_00065 a)

theorem ridge_encoding : ∀ a q,
    has (PolygonGrowth.N6.ridgeList a) (edgeCode q) = true ↔ q ∈ (FiniteCycleCandidates.N6.cells a).edges :=
  ridge_code_of_lists FiniteCycleCandidates.N6.cells PolygonGrowth.N6.ridgeList edgeCode ridgeData_exact

theorem compatibility_sound (a b : Fin 65)
    (h : PolygonBoundaryCatalogue.compatible (FiniteCycleCandidates.N6.cells a) (FiniteCycleCandidates.N6.cells b)) :
    PolygonGrowth.N6.compatible a b = true := by
  -- Reuse the decision instance already stored in the checked Boolean row.
  -- Transport its resulting proposition, avoiding a second large instance.
  have ha : compatibilityTest a.val = true := compatibility_data_join_00000_00065 a.val (Nat.zero_le _) a.isLt
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
  have hindex : Fin.ofNat 65 a.val = a := Fin.ofNat_val_eq_self a
  have htransport := congrArg (fun x : Fin 65 => ∀ c : Fin 65,
    PolygonBoundaryCatalogue.compatible
      (FiniteCycleCandidates.N6.cells x) (FiniteCycleCandidates.N6.cells c) →
      PolygonGrowth.N6.compatible x c = true) hindex
  exact (Eq.mp htransport hrow) b h

theorem terminal_checked (j : Fin 110) :
    terminalCheck FiniteCycleCandidates.N6.cells FiniteCycleCandidates.N6.templates (PolygonGrowth.N6.terminals j)
      (PolygonGrowth.N6.targetTemplate j) (decode (by decide : 0 < 6) (PolygonGrowth.N6.permutationCode j)) = true :=
  FiniteChecks.fin_of_interval (fun j : Fin 110 =>
    terminalCheck FiniteCycleCandidates.N6.cells FiniteCycleCandidates.N6.templates (PolygonGrowth.N6.terminals j)
      (PolygonGrowth.N6.targetTemplate j) (decode (by decide : 0 < 6) (PolygonGrowth.N6.permutationCode j)))
    terminal_data_join_00000_00110 j

theorem neighbor_coverage : ∀ i ∈ FiniteCycleCandidates.N6.neighbors,
    ∃ seed : Fin 3, PolygonGrowth.N6.neighbors seed = i := by decide +kernel

/-- Complete classification of every paired, compatible, connected polygon
boundary in the normalized universe, with all minimum-degree and Euler
conditions. Every finite certificate premise has been checked above. -/
theorem normalized_classification (S : Finset (Fin 65))
    (hcard : S.card ≤ 2 * 6 - 4)
    (hpair : (S : Set _).Pairwise (fun a b =>
      PolygonBoundaryCatalogue.compatible (FiniteCycleCandidates.N6.cells a) (FiniteCycleCandidates.N6.cells b)))
    (hvalid : valid FiniteCycleCandidates.N6.cells S) (hconn : RidgeConnected (ridges FiniteCycleCandidates.N6.cells) S)
    (hroot : (0 : Fin 65) ∈ S) (hneighbor : (S ∩ FiniteCycleCandidates.N6.neighbors).Nonempty) :
    ∃ (σ : Equiv.Perm (Fin 6)) (i : Fin 7),
      relabelBoundary FiniteCycleCandidates.N6.cells σ S = FiniteCycleCandidates.N6.templates i := by
  obtain ⟨neighbor, hneighbor⟩ := hneighbor
  obtain ⟨hneighborS, hneighborN⟩ := Finset.mem_inter.mp hneighbor
  obtain ⟨seed, hseed⟩ := neighbor_coverage neighbor hneighborN
  have hquota : ∀ j, kindCount PolygonGrowth.N6.kind S.toList j ≤ PolygonGrowth.N6.quota j := by
    change ∀ j, kindCount (fun _ : Fin 65 => 0) S.toList j ≤ if j = 0 then 8 else 0
    exact constant_kind_budget S 8 hcard
  have hcompatible : ∀ a b, a ∈ S.toList → b ∈ S.toList → a ≠ b →
      PolygonGrowth.N6.compatible a b = true := by
    intro a b ha hb hab
    exact compatibility_sound a b (hpair (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb) hab)
  obtain ⟨j, hj⟩ := PolygonGrowth.N6.boundary_classification S.toList hquota hcompatible
    (hasMate_of_valid FiniteCycleCandidates.N6.cells S PolygonGrowth.N6.ridgeList edgeCode ridge_encoding hvalid)
    (noThree_of_valid FiniteCycleCandidates.N6.cells S PolygonGrowth.N6.ridgeList edgeCode ridge_encoding hvalid)
    (connected_of_ridgeConnected FiniteCycleCandidates.N6.cells S PolygonGrowth.N6.ridgeList edgeCode ridge_encoding hconn)
    seed (Finset.mem_toList.mpr hroot) (by rw [hseed]; exact Finset.mem_toList.mpr hneighborS)
  exact terminalCheck_sound FiniteCycleCandidates.N6.cells FiniteCycleCandidates.N6.templates (PolygonGrowth.N6.terminals j)
    (PolygonGrowth.N6.targetTemplate j) (decode (by decide : 0 < 6) (PolygonGrowth.N6.permutationCode j))
    (terminal_checked j) S (finset_eq_of_same _ S hj) hvalid

#print axioms normalized_classification
end Papers.RationalityTen.ConcretePolygonClassification.N6
