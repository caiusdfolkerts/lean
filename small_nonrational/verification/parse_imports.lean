import Lean.Elab.Import
import Lean.Data.Json.FromToJson

/-!
Use Lean's own header parser to read imports. This program neither elaborates
the inspected modules nor changes the kernel environment used for their proofs.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  let [listFile] := args | do
    IO.eprintln "Usage: ParseImports <file containing one source path per line>"
    return 2
  let paths := (← IO.FS.readFile listFile).splitOn "\n"
  let mut failed := false
  for path in paths do
    unless path.isEmpty do
      let input ← IO.FS.readFile path
      let inputCtx := Parser.mkInputContext input path
      let (header, _, messages) ← Parser.parseHeader inputCtx
      let imports := (Elab.HeaderSyntax.imports header false).map (·.module.toString)
      let errors ← messages.toList.toArray.mapM fun msg => msg.toString
      let row := Json.mkObj [
        ("path", toJson path),
        ("imports", toJson imports),
        ("errors", toJson errors)]
      IO.println row.compress
      if messages.hasErrors then failed := true
  return if failed then 1 else 0
