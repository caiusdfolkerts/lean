module
public import PackedGraphInputs
public meta import KernelDecideContext
public meta import Lean.Elab.Command

/-! Verify the given number of graph-search nodes and terminal leaves.
Each block uses the original kernel reduction and the adjacent intervals are
joined by the finite interval lemma. The final claims quantify over every
node and every leaf of the actual original RawData structure. -/

public meta section
open Lean
open Papers.RationalityTen PackedGraphCertificate FiniteChecks

private def mergeIntervals (test : Term) (bounds : Array (Nat × Term)) (total : Nat) : MacroM Term := do
  let some (_, latest) := bounds.back? | Macro.throwError "empty certificate interval"
  let mut result := latest
  for i in (Array.range (bounds.size - 1)).reverse do
    let (start, p) := bounds[i]!
    let (middle, _) := bounds[i+1]!
    result ← `(FiniteChecks.interval_append $test $(quote start) $(quote middle) $(quote total) $p $result)
  return result

syntax "certified_graph_nodes " ident num num : command
macro_rules
  | `(certified_graph_nodes $r $nodes $leaves) => do
    let localId (s : String) := mkIdentFrom r (r.getId.appendAfter s)
    let field (n : Name) := mkIdentFrom r (r.getId ++ n)
    let valid := localId "_valid"
    let nodeTest ← `($(field `nodeTestValid) $valid)
    let leafTest : Term := field `leafTest
    let mut commands : Array Syntax := #[]
    let mut nodeBlocks := #[]
    let mut leafBlocks := #[]
    for chunk in [:((nodes.getNat+31)/32)] do
      let lo := 32*chunk
      let hi := min nodes.getNat (lo+32)
      let thm := localId ("_nodes_" ++ toString lo)
      commands := commands.push (← `(command| theorem $thm ($valid : GraphGrowthInputs.Valid $(field `inputs)) :
        Interval $nodeTest $(quote lo) $(quote hi) :=
          interval_of_check _ $(quote lo) $(quote (hi-lo)) (by decide_kernel_context)))
      nodeBlocks := nodeBlocks.push (lo, ← `($thm $valid))
    let supports := localId "_supports"
    commands := commands.push (← `(command| theorem $supports : $(field `Supports) := by
      unfold RawData.Supports
      decide +kernel))
    for chunk in [:((leaves.getNat+7)/8)] do
      let lo := 8*chunk
      let hi := min leaves.getNat (lo+8)
      let thm := localId ("_leaf_" ++ toString lo)
      commands := commands.push (← `(command| theorem $thm : Interval $leafTest $(quote lo) $(quote hi) :=
        interval_of_check _ $(quote lo) $(quote (hi-lo)) (by decide +kernel)))
      leafBlocks := leafBlocks.push (lo, (thm : Term))
    let nodup := localId "_leaves_nodup"
    let joinedLeaves ← mergeIntervals leafTest leafBlocks leaves.getNat
    commands := commands.push (← `(command| theorem $nodup (j : Fin $(field `l)) : ($(field `leaf) j).Nodup :=
      $(field `leaves_nodup_of_interval) $joinedLeaves j))
    let checked := localId "_checked"
    let joinedNodes ← mergeIntervals nodeTest nodeBlocks nodes.getNat
    commands := commands.push (← `(command| theorem $checked ($valid : GraphGrowthInputs.Valid $(field `inputs)) :
      Interval $nodeTest 0 $nodes := $joinedNodes))
    let finalId := localId "_raw_node_checks"
    commands := commands.push (← `(command| theorem $finalId ($valid : GraphGrowthInputs.Valid $(field `inputs))
          (i : Fin $(field `t)) :
        RawGraphConditionedGrowth.nodeCheck ($(field `inputs.problem) $valid)
          $(field `maps) $(field `leaf) $(field `nodes) i = true :=
        $(field `node_checks_valid) $valid $supports ($checked $valid) i))
    commands := commands.push (← `(command| #print axioms $finalId))
    return mkNullNode commands
