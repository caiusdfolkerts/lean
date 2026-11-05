module
public import GPGeometry.SevenSurvivor.Permutations
public import PureGP.SevenSurvivor.Relations
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.GPFiniteGeometry.Literal.SevenSurvivor
open Papers.RationalityTen.PureGP
/- Thirteen actual determinant identities, not extra sign axioms. -/

def relationWitness000 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 0) where
  «prefix» := ![0, 1, 7]
  outside := ![2, 5, 6, 8]
  permutation := ![permutation04, permutation02, permutation04, permutation02, permutation02, permutation04]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness001 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 1) where
  «prefix» := ![0, 1, 8]
  outside := ![2, 3, 4, 9]
  permutation := ![permutation04, permutation02, permutation04, permutation02, permutation02, permutation04]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness002 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 2) where
  «prefix» := ![0, 1, 8]
  outside := ![2, 3, 5, 9]
  permutation := ![permutation04, permutation02, permutation04, permutation02, permutation02, permutation04]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness003 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 3) where
  «prefix» := ![0, 2, 5]
  outside := ![1, 7, 8, 9]
  permutation := ![permutation05, permutation00, permutation05, permutation00, permutation05, permutation00]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness004 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 4) where
  «prefix» := ![0, 2, 7]
  outside := ![1, 3, 4, 8]
  permutation := ![permutation07, permutation02, permutation07, permutation02, permutation05, permutation04]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness005 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 5) where
  «prefix» := ![0, 2, 7]
  outside := ![1, 4, 6, 8]
  permutation := ![permutation07, permutation02, permutation07, permutation02, permutation05, permutation04]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness006 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 6) where
  «prefix» := ![0, 2, 8]
  outside := ![1, 5, 6, 9]
  permutation := ![permutation07, permutation02, permutation07, permutation02, permutation05, permutation04]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness007 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 7) where
  «prefix» := ![0, 3, 5]
  outside := ![1, 7, 8, 9]
  permutation := ![permutation05, permutation00, permutation05, permutation00, permutation05, permutation00]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness008 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 8) where
  «prefix» := ![0, 3, 6]
  outside := ![1, 7, 8, 9]
  permutation := ![permutation05, permutation00, permutation05, permutation00, permutation05, permutation00]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness009 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 9) where
  «prefix» := ![0, 3, 7]
  outside := ![1, 2, 5, 8]
  permutation := ![permutation08, permutation02, permutation07, permutation05, permutation05, permutation07]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness010 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 10) where
  «prefix» := ![0, 3, 8]
  outside := ![1, 2, 5, 7]
  permutation := ![permutation08, permutation04, permutation07, permutation07, permutation07, permutation07]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness011 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 11) where
  «prefix» := ![0, 3, 9]
  outside := ![1, 2, 5, 7]
  permutation := ![permutation08, permutation04, permutation07, permutation07, permutation07, permutation07]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

def relationWitness012 : RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation 12) where
  «prefix» := ![0, 5, 7]
  outside := ![1, 2, 3, 8]
  permutation := ![permutation08, permutation05, permutation08, permutation05, permutation05, permutation08]
  rows_correct := by decide +kernel
  parity_first := by decide +kernel
  parity_second := by decide +kernel
  parity_third := by decide +kernel

set_option maxRecDepth 4096 in
def allRelations : (i : Fin 13) → RelationTupleWitness (Papers.RationalityTen.PureGP.SevenSurvivor.Data.relation i.val) :=
  Fin.cases relationWitness000 (Fin.cases relationWitness001 (Fin.cases relationWitness002 (Fin.cases relationWitness003 (Fin.cases relationWitness004 (Fin.cases relationWitness005 (Fin.cases relationWitness006 (Fin.cases relationWitness007 (Fin.cases relationWitness008 (Fin.cases relationWitness009 (Fin.cases relationWitness010 (Fin.cases relationWitness011 (Fin.cases relationWitness012 (fun i => Fin.elim0 i)))))))))))))

end Papers.RationalityTen.GPFiniteGeometry.Literal.SevenSurvivor
