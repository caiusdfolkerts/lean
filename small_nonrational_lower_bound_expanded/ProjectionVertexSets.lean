module
public meta import Lean.Elab.Command

/-! A boundary certificate names subsets of ten labelled vertices. Their
subscripts are the bit masks for those subsets. Emit the original finite
sets in increasing vertex order, retaining each original declaration name. -/
public meta section
open Lean

macro "projection_vertex_sets " "[" masks:num,* "]" : command => do
  let mut commands := #[]
  for mask in masks.getElems do
    unless mask.getNat < 1024 do Macro.throwError "expected ten-vertex mask"
    let labels : Array Term := (Array.range 10).filterMap fun j =>
      if mask.getNat.testBit j then some (quote j) else none
    let id := mkIdent ("vertices_" ++ toString mask.getNat).toName
    let fset := mkIdent `Finset
    let literal := mkIdent `literalFinset
    commands := commands.push (← `(command| noncomputable def $id : $fset (Fin 10) :=
      $literal [$labels,*] (by decide +kernel)))
  return ⟨mkNullNode commands⟩
