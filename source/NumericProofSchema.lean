module
public meta import Lean.Elab.Command

/-! A repeated proof from a finite enumeration may be shared verbatim if
every varying field is a natural numeral. Its whole declaration is visible
in the schema. Supplied data can change only those numeral positions. -/
public meta section
open Lean Elab Command

namespace NumericProofSchema

/-- Parse a single fixed proof declaration in the caller's current syntax
environment and elaborate its ordinary proof with the kernel checks of
that environment. Preserve the spelling of numerals used in indexed names. -/
def elaborate (body : String) (args : Array (TSyntax `num)) : CommandElabM Unit := do
  let mut expanded := body
  for i in [:args.size] do
    let arg := args[i]!
    let some raw := arg.raw.reprint | throwError "expected a numeral"
    let spelling := raw.trimAscii.toString
    -- A number token in this DSL can never supply a declaration or tactic.
    unless !spelling.isEmpty && spelling.toList.all (fun c =>
        c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') || c == 'x') do
      throwError "invalid numeral in a finite certificate"
    expanded := expanded.replace ("⟪" ++ toString i ++ "⟫") spelling
  let env ← getEnv
  match Parser.runParserCategory env `command expanded with
  | .error msg => throwError "invalid finite proof schema: {msg}"
  | .ok cmd => elabCommand cmd

end NumericProofSchema
