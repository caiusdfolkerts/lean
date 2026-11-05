module

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

theorem ridge_data_00000 : FiniteChecks.Interval ridgeDataTest 0 8 :=
  FiniteChecks.interval_of_check ridgeDataTest 0 8 (by decide +kernel)

theorem ridge_data_00008 : FiniteChecks.Interval ridgeDataTest 8 16 :=
  FiniteChecks.interval_of_check ridgeDataTest 8 8 (by decide +kernel)

theorem ridge_data_00016 : FiniteChecks.Interval ridgeDataTest 16 24 :=
  FiniteChecks.interval_of_check ridgeDataTest 16 8 (by decide +kernel)

theorem ridge_data_00024 : FiniteChecks.Interval ridgeDataTest 24 32 :=
  FiniteChecks.interval_of_check ridgeDataTest 24 8 (by decide +kernel)

theorem ridge_data_00032 : FiniteChecks.Interval ridgeDataTest 32 40 :=
  FiniteChecks.interval_of_check ridgeDataTest 32 8 (by decide +kernel)

theorem ridge_data_00040 : FiniteChecks.Interval ridgeDataTest 40 48 :=
  FiniteChecks.interval_of_check ridgeDataTest 40 8 (by decide +kernel)

theorem ridge_data_00048 : FiniteChecks.Interval ridgeDataTest 48 56 :=
  FiniteChecks.interval_of_check ridgeDataTest 48 8 (by decide +kernel)

theorem ridge_data_00056 : FiniteChecks.Interval ridgeDataTest 56 64 :=
  FiniteChecks.interval_of_check ridgeDataTest 56 8 (by decide +kernel)

theorem ridge_data_00064 : FiniteChecks.Interval ridgeDataTest 64 65 :=
  FiniteChecks.interval_of_check ridgeDataTest 64 1 (by decide +kernel)

theorem ridge_data_join_00000_00016 : FiniteChecks.Interval ridgeDataTest 0 16 :=
  FiniteChecks.interval_append ridgeDataTest 0 8 16 ridge_data_00000 ridge_data_00008

theorem ridge_data_join_00016_00032 : FiniteChecks.Interval ridgeDataTest 16 32 :=
  FiniteChecks.interval_append ridgeDataTest 16 24 32 ridge_data_00016 ridge_data_00024

theorem ridge_data_join_00000_00032 : FiniteChecks.Interval ridgeDataTest 0 32 :=
  FiniteChecks.interval_append ridgeDataTest 0 16 32 ridge_data_join_00000_00016 ridge_data_join_00016_00032

theorem ridge_data_join_00032_00048 : FiniteChecks.Interval ridgeDataTest 32 48 :=
  FiniteChecks.interval_append ridgeDataTest 32 40 48 ridge_data_00032 ridge_data_00040

theorem ridge_data_join_00056_00065 : FiniteChecks.Interval ridgeDataTest 56 65 :=
  FiniteChecks.interval_append ridgeDataTest 56 64 65 ridge_data_00056 ridge_data_00064

theorem ridge_data_join_00048_00065 : FiniteChecks.Interval ridgeDataTest 48 65 :=
  FiniteChecks.interval_append ridgeDataTest 48 56 65 ridge_data_00048 ridge_data_join_00056_00065

theorem ridge_data_join_00032_00065 : FiniteChecks.Interval ridgeDataTest 32 65 :=
  FiniteChecks.interval_append ridgeDataTest 32 48 65 ridge_data_join_00032_00048 ridge_data_join_00048_00065

theorem ridge_data_join_00000_00065 : FiniteChecks.Interval ridgeDataTest 0 65 :=
  FiniteChecks.interval_append ridgeDataTest 0 32 65 ridge_data_join_00000_00032 ridge_data_join_00032_00065

theorem compatibility_data_00000 : FiniteChecks.Interval compatibilityTest 0 8 :=
  FiniteChecks.interval_of_check compatibilityTest 0 8 (by decide +kernel)

theorem compatibility_data_00008 : FiniteChecks.Interval compatibilityTest 8 16 :=
  FiniteChecks.interval_of_check compatibilityTest 8 8 (by decide +kernel)

theorem compatibility_data_00016 : FiniteChecks.Interval compatibilityTest 16 24 :=
  FiniteChecks.interval_of_check compatibilityTest 16 8 (by decide +kernel)

theorem compatibility_data_00024 : FiniteChecks.Interval compatibilityTest 24 32 :=
  FiniteChecks.interval_of_check compatibilityTest 24 8 (by decide +kernel)

theorem compatibility_data_00032 : FiniteChecks.Interval compatibilityTest 32 40 :=
  FiniteChecks.interval_of_check compatibilityTest 32 8 (by decide +kernel)

theorem compatibility_data_00040 : FiniteChecks.Interval compatibilityTest 40 48 :=
  FiniteChecks.interval_of_check compatibilityTest 40 8 (by decide +kernel)

theorem compatibility_data_00048 : FiniteChecks.Interval compatibilityTest 48 56 :=
  FiniteChecks.interval_of_check compatibilityTest 48 8 (by decide +kernel)

theorem compatibility_data_00056 : FiniteChecks.Interval compatibilityTest 56 64 :=
  FiniteChecks.interval_of_check compatibilityTest 56 8 (by decide +kernel)

theorem compatibility_data_00064 : FiniteChecks.Interval compatibilityTest 64 65 :=
  FiniteChecks.interval_of_check compatibilityTest 64 1 (by decide +kernel)

theorem compatibility_data_join_00000_00016 : FiniteChecks.Interval compatibilityTest 0 16 :=
  FiniteChecks.interval_append compatibilityTest 0 8 16 compatibility_data_00000 compatibility_data_00008

theorem compatibility_data_join_00016_00032 : FiniteChecks.Interval compatibilityTest 16 32 :=
  FiniteChecks.interval_append compatibilityTest 16 24 32 compatibility_data_00016 compatibility_data_00024

theorem compatibility_data_join_00000_00032 : FiniteChecks.Interval compatibilityTest 0 32 :=
  FiniteChecks.interval_append compatibilityTest 0 16 32 compatibility_data_join_00000_00016 compatibility_data_join_00016_00032

theorem compatibility_data_join_00032_00048 : FiniteChecks.Interval compatibilityTest 32 48 :=
  FiniteChecks.interval_append compatibilityTest 32 40 48 compatibility_data_00032 compatibility_data_00040

theorem compatibility_data_join_00056_00065 : FiniteChecks.Interval compatibilityTest 56 65 :=
  FiniteChecks.interval_append compatibilityTest 56 64 65 compatibility_data_00056 compatibility_data_00064

theorem compatibility_data_join_00048_00065 : FiniteChecks.Interval compatibilityTest 48 65 :=
  FiniteChecks.interval_append compatibilityTest 48 56 65 compatibility_data_00048 compatibility_data_join_00056_00065

theorem compatibility_data_join_00032_00065 : FiniteChecks.Interval compatibilityTest 32 65 :=
  FiniteChecks.interval_append compatibilityTest 32 48 65 compatibility_data_join_00032_00048 compatibility_data_join_00048_00065

theorem compatibility_data_join_00000_00065 : FiniteChecks.Interval compatibilityTest 0 65 :=
  FiniteChecks.interval_append compatibilityTest 0 32 65 compatibility_data_join_00000_00032 compatibility_data_join_00032_00065

theorem terminal_data_00000 : FiniteChecks.Interval terminalTest 0 8 :=
  FiniteChecks.interval_of_check terminalTest 0 8 (by decide +kernel)

theorem terminal_data_00008 : FiniteChecks.Interval terminalTest 8 16 :=
  FiniteChecks.interval_of_check terminalTest 8 8 (by decide +kernel)

theorem terminal_data_00016 : FiniteChecks.Interval terminalTest 16 24 :=
  FiniteChecks.interval_of_check terminalTest 16 8 (by decide +kernel)

theorem terminal_data_00024 : FiniteChecks.Interval terminalTest 24 32 :=
  FiniteChecks.interval_of_check terminalTest 24 8 (by decide +kernel)

theorem terminal_data_00032 : FiniteChecks.Interval terminalTest 32 40 :=
  FiniteChecks.interval_of_check terminalTest 32 8 (by decide +kernel)

theorem terminal_data_00040 : FiniteChecks.Interval terminalTest 40 48 :=
  FiniteChecks.interval_of_check terminalTest 40 8 (by decide +kernel)

theorem terminal_data_00048 : FiniteChecks.Interval terminalTest 48 56 :=
  FiniteChecks.interval_of_check terminalTest 48 8 (by decide +kernel)

theorem terminal_data_00056 : FiniteChecks.Interval terminalTest 56 64 :=
  FiniteChecks.interval_of_check terminalTest 56 8 (by decide +kernel)

theorem terminal_data_00064 : FiniteChecks.Interval terminalTest 64 72 :=
  FiniteChecks.interval_of_check terminalTest 64 8 (by decide +kernel)

theorem terminal_data_00072 : FiniteChecks.Interval terminalTest 72 80 :=
  FiniteChecks.interval_of_check terminalTest 72 8 (by decide +kernel)

theorem terminal_data_00080 : FiniteChecks.Interval terminalTest 80 88 :=
  FiniteChecks.interval_of_check terminalTest 80 8 (by decide +kernel)

theorem terminal_data_00088 : FiniteChecks.Interval terminalTest 88 96 :=
  FiniteChecks.interval_of_check terminalTest 88 8 (by decide +kernel)

theorem terminal_data_00096 : FiniteChecks.Interval terminalTest 96 104 :=
  FiniteChecks.interval_of_check terminalTest 96 8 (by decide +kernel)

theorem terminal_data_00104 : FiniteChecks.Interval terminalTest 104 110 :=
  FiniteChecks.interval_of_check terminalTest 104 6 (by decide +kernel)

theorem terminal_data_join_00008_00024 : FiniteChecks.Interval terminalTest 8 24 :=
  FiniteChecks.interval_append terminalTest 8 16 24 terminal_data_00008 terminal_data_00016

theorem terminal_data_join_00000_00024 : FiniteChecks.Interval terminalTest 0 24 :=
  FiniteChecks.interval_append terminalTest 0 8 24 terminal_data_00000 terminal_data_join_00008_00024

theorem terminal_data_join_00024_00040 : FiniteChecks.Interval terminalTest 24 40 :=
  FiniteChecks.interval_append terminalTest 24 32 40 terminal_data_00024 terminal_data_00032

theorem terminal_data_join_00040_00056 : FiniteChecks.Interval terminalTest 40 56 :=
  FiniteChecks.interval_append terminalTest 40 48 56 terminal_data_00040 terminal_data_00048

theorem terminal_data_join_00024_00056 : FiniteChecks.Interval terminalTest 24 56 :=
  FiniteChecks.interval_append terminalTest 24 40 56 terminal_data_join_00024_00040 terminal_data_join_00040_00056

theorem terminal_data_join_00000_00056 : FiniteChecks.Interval terminalTest 0 56 :=
  FiniteChecks.interval_append terminalTest 0 24 56 terminal_data_join_00000_00024 terminal_data_join_00024_00056

theorem terminal_data_join_00064_00080 : FiniteChecks.Interval terminalTest 64 80 :=
  FiniteChecks.interval_append terminalTest 64 72 80 terminal_data_00064 terminal_data_00072

theorem terminal_data_join_00056_00080 : FiniteChecks.Interval terminalTest 56 80 :=
  FiniteChecks.interval_append terminalTest 56 64 80 terminal_data_00056 terminal_data_join_00064_00080

theorem terminal_data_join_00080_00096 : FiniteChecks.Interval terminalTest 80 96 :=
  FiniteChecks.interval_append terminalTest 80 88 96 terminal_data_00080 terminal_data_00088

theorem terminal_data_join_00096_00110 : FiniteChecks.Interval terminalTest 96 110 :=
  FiniteChecks.interval_append terminalTest 96 104 110 terminal_data_00096 terminal_data_00104

theorem terminal_data_join_00080_00110 : FiniteChecks.Interval terminalTest 80 110 :=
  FiniteChecks.interval_append terminalTest 80 96 110 terminal_data_join_00080_00096 terminal_data_join_00096_00110

theorem terminal_data_join_00056_00110 : FiniteChecks.Interval terminalTest 56 110 :=
  FiniteChecks.interval_append terminalTest 56 80 110 terminal_data_join_00056_00080 terminal_data_join_00080_00110

theorem terminal_data_join_00000_00110 : FiniteChecks.Interval terminalTest 0 110 :=
  FiniteChecks.interval_append terminalTest 0 56 110 terminal_data_join_00000_00056 terminal_data_join_00056_00110

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
