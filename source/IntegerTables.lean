module
public meta import CertificateNumbers

/-! Reconstruct a binary search table of natural numbers from its postorder
list of numeric nodes. An even node encodes a leaf value. An odd node
encodes a branch threshold and combines the preceding two subtrees. -/
public meta section
open Lean Elab Term

elab "integerTable% " start:num count:num : term => do
  let values ← CertificateNumbers.load (← CertificateNumbers.sibling "tablepack")
  let first := start.getNat
  let stop := first + count.getNat
  unless stop ≤ values.size do throwError "numeric table exceeds its certificate"
  let leaf := mkApp (mkConst `Papers.RationalityTen.ConcreteGrowth.Table.leaf) (mkConst ``Nat)
  let branch := mkApp (mkConst `Papers.RationalityTen.ConcreteGrowth.Table.branch) (mkConst ``Nat)
  let mut stack := #[]
  for j in [first:stop] do
    let code := values[j]!
    let n := mkNatLit (code / 2)
    if code % 2 == 0 then stack := stack.push (mkApp leaf n)
    else
      let some right := stack.back? | throwError "missing right subtree"
      stack := stack.pop
      let some left := stack.back? | throwError "missing left subtree"
      stack := stack.pop.push (mkApp3 branch n left right)
  unless stack.size == 1 do throwError "numeric table has extra subtrees"
  return stack[0]!
