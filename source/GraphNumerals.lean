module

public meta import Lean.Elab.Term

/-! Expand a block of finite certificate data into ordinary Lean natural
number literals. The block contains only length-prefixed natural numbers.
Its decoder cannot carry a theorem, proof term or source declaration. -/

public meta section

open Lean Elab Term

namespace GraphNumerals

private def nibble (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else none

private def hexBytes (s : String) : Option ByteArray := do
  let mut high : Option Nat := none
  let mut result := ByteArray.empty
  for c in s.toList do
    let value ← nibble c
    match high with
    | none => high := some value
    | some k =>
      result := result.push (k * 16 + value).toUInt8
      high := none
  guard high.isNone
  return result

private def atByte (b : ByteArray) (i : Nat) : Option Nat := do
  return (← b[i]?).toNat

/-- LZ4's length extension consists of 255 bytes followed by a smaller byte. -/
private def blockLength (b : ByteArray) (n start : Nat) : Option (Nat × Nat) := do
  if n < 15 then return (n, start)
  let mut length := n
  let mut i := start
  for _ in [start:b.size] do
    let x ← atByte b i
    length := length + x
    i := i + 1
    if x < 255 then return (length, i)
  none

private def inflate (b : ByteArray) : Option ByteArray := do
  let mut out := ByteArray.empty
  let mut i := 0
  while i < b.size do
    let header ← atByte b i
    let (count, start) ← blockLength b (header / 16) (i+1)
    guard (start + count ≤ b.size && out.size + count ≤ 16000000)
    out := out ++ b.extract start (start + count)
    i := start + count
    if i == b.size then return out
    let lo ← atByte b i
    let hi ← atByte b (i+1)
    let offset := lo + 256 * hi
    guard (0 < offset && offset ≤ out.size)
    let (length, finish) ← blockLength b (header % 16) (i+2)
    guard (out.size + length + 4 ≤ 16000000)
    for _ in [:length+4] do
      let n ← atByte out (out.size-offset)
      out := out.push n.toUInt8
    i := finish
  return out

/-- Read a little-endian natural number using balanced joins. -/
private def littleNat (b : ByteArray) (start count : Nat) : Nat :=
  if h : count ≤ 8 then Id.run do
    let mut n := 0
    for j in [:count] do
      n := n ||| ((b[start+j]!).toNat <<< (8*j))
    return n
  else
    let low := count / 2
    littleNat b start low ||| (littleNat b (start+low) (count-low) <<< (8*low))
termination_by count
decreasing_by all_goals omega

private def number (b : ByteArray) (i : Nat) : Option (Nat × Nat) := do
  guard (i+3 ≤ b.size)
  let count := littleNat b i 3
  guard (i+3+count ≤ b.size)
  return (littleNat b (i+3) count, i+3+count)

/-- Each block contains the fields of one RawData record in constructor
order. Width/code pairs occupy two consecutive numbers. The prototype
returns a flat array for testing the transport independently of the checker. -/
def decodeNumericBlock (packed : ByteArray) : Option (Array Nat) := do
  let bytes ← inflate packed
  let mut i := 0
  let mut values := #[]
  while i < bytes.size do
    let (n, next) ← number bytes i
    values := values.push n
    i := next
  return values

def expandNumerals (s : String) : TermElabM (Array Nat) := do
  let some packed := hexBytes s | throwError "invalid certificate hex"
  let some values := decodeNumericBlock packed | throwError "invalid numerical certificate"
  return values

elab "graphNumerals% " s:str : term => do
  return ← Meta.mkListLit (mkConst ``Nat) ((← expandNumerals s.getString).map mkNatLit).toList

/-- Construct the substantive development's original RawData inductive value.
No other result type or constructor can be supplied in the input data. -/
def mkRecord (numbers : Array Nat) : TermElabM Expr := do
  let values := numbers.map mkNatLit
  let namespaceName := `Papers.RationalityTen.PackedGraphCertificate
  let fieldsName := namespaceName ++ `Fields
  let recordCtor := namespaceName ++ `RawData.mk
  let recordInfo ← getConstInfo recordCtor
  Meta.forallTelescope recordInfo.type fun args _ => do
    let mut next := 0
    let mut fields := #[]
    for arg in args do
      let ty ← Meta.inferType arg
      let some first := values[next]? | throwError "missing natural number"
      next := next + 1
      if ty.isConstOf ``Nat then
        fields := fields.push first
      else if ty.isConstOf fieldsName then
        let some second := values[next]? | throwError "incomplete packed field"
        fields := fields.push (mkApp2 (mkConst (fieldsName ++ `mk)) first second)
        next := next + 1
      else
        throwError "unsupported RawData constructor argument"
    unless next == values.size do throwError "extra certificate numbers"
    return mkAppN (mkConst recordCtor) fields

elab "graphRecord% " s:str : term => do
  mkRecord (← expandNumerals s.getString)

end GraphNumerals
