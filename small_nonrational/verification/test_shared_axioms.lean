module
import Lean.Elab.BuiltinEvalCommand
meta import Lean.Elab.Command
meta import all Lean.Util.CollectAxioms
public section
namespace CacheProbe
axiom badValue : Nat
axiom BadType : Type
noncomputable def leaf := badValue
noncomputable def left := leaf + leaf
noncomputable def right := leaf + left
def clean : Nat := 0
inductive Loop where
  | mk : BadType → Loop → Loop
end CacheProbe
open Lean in
run_cmd do
  let env ← getEnv
  let privateEnv := env.setExporting false
  let ext := Lean.exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let orders := #[#[`CacheProbe.right, `CacheProbe.left, `CacheProbe.clean],
    #[`CacheProbe.left, `CacheProbe.right, `CacheProbe.clean],
    #[`CacheProbe.Loop, `CacheProbe.Loop.mk, `CacheProbe.Loop.rec],
    #[`CacheProbe.Loop.rec, `CacheProbe.Loop.mk, `CacheProbe.Loop]]
  for roots in orders do
    let mut fresh : NameSet := {}
    let mut shared : NameSet := {}
    let mut state : Lean.CollectAxioms.State := {}
    for name in roots do
      unless (env.find? name).isSome do throwError "Missing fixture declaration {name}"
      let actual ← Lean.collectAxioms name
      for ax in actual do fresh := fresh.insert ax
      let (cached, next) := ((Lean.CollectAxioms.collectAndGet ext.find? name).run privateEnv).run state
      state := next
      for ax in cached do shared := shared.insert ax
    unless fresh.toArray.qsort Name.lt == shared.toArray.qsort Name.lt do
      throwError "Shared and fresh traversal disagree: {fresh.toArray} vs {shared.toArray}"
    unless shared.contains `CacheProbe.badValue || shared.contains `CacheProbe.BadType do
      throwError "Unexpected axioms were lost"
  IO.println "SHARED_AXIOM_UNION_CHECKS_OK"
