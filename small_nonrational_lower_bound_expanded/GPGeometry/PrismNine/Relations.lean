module
public import GPGeometry.PrismNine.Permutations
public import PureGP.PrismNine.Relations
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.GPFiniteGeometry.Literal.PrismNine
open Papers.RationalityTen.PureGP
/- Actual determinant identities, not extra sign axioms. -/

def relationWitness000 : RelationTupleWitness (Papers.RationalityTen.PureGP.PrismNine.Data.relation 0) where
  «prefix» := ![0, 1, 2]
  outside := ![3, 6, 7, 8]
  permutation := ![permutation00, permutation00, permutation00, permutation00, permutation00, permutation00]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

set_option maxRecDepth 4096 in
def allRelations : (i : Fin 1) → RelationTupleWitness (Papers.RationalityTen.PureGP.PrismNine.Data.relation i.val) :=
  Fin.cases relationWitness000 (fun i => Fin.elim0 i)

end Papers.RationalityTen.GPFiniteGeometry.Literal.PrismNine
