module
prelude
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.Tactic.AuxLemma

/-!
This tactic uses the same proof construction and kernel admission as
`decide +kernel`, but closes local variables by lambda abstraction first.
It introduces no axiom and performs no native evaluation. The kernel must
reduce the proposed Boolean proof under every abstracted parameter.
-/

public meta section
open Lean Meta Elab Tactic

elab "decide_kernel_context" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let proof ← mkDecideProof target
    let locals ← getLocalHyps
    let closedTarget ← mkForallFVars locals target
    let closedProof ← mkLambdaFVars locals proof
    let levels := (collectLevelParams {} closedTarget).params.toList
    let name ← withOptions (Elab.async.set · false) do
      mkAuxLemma levels closedTarget closedProof
    goal.assign (mkAppN (mkConst name (levels.map Level.param)) locals)
  replaceMainGoal []
