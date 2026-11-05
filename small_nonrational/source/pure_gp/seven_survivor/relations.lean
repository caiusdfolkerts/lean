module
prelude
public import PureGP.SupportCore

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.SevenSurvivor.Data
def relationTable : Table Relation := (Table.node 6 (Table.node 3 (Table.node 1 (Table.leaf (Relation.mk (Six.mk 12 52 15 49 18 46) (Triple.mk Bool.true Bool.false Bool.true))) (Table.node 2 (Table.leaf (Relation.mk (Six.mk 4 45 9 35 20 24) (Triple.mk Bool.true Bool.false Bool.true))) (Table.leaf (Relation.mk (Six.mk 4 51 13 35 20 28) (Triple.mk Bool.true Bool.false Bool.true))))) (Table.node 4 (Table.leaf (Relation.mk (Six.mk 12 86 13 85 14 84) (Triple.mk Bool.false Bool.true Bool.false))) (Table.node 5 (Table.leaf (Relation.mk (Six.mk 3 78 8 68 18 58) (Triple.mk Bool.false Bool.true Bool.false))) (Table.leaf (Relation.mk (Six.mk 8 87 15 78 18 75) (Triple.mk Bool.false Bool.true Bool.false)))))) (Table.node 9 (Table.node 7 (Table.leaf (Relation.mk (Six.mk 13 89 16 86 20 82) (Triple.mk Bool.false Bool.true Bool.false))) (Table.node 8 (Table.leaf (Relation.mk (Six.mk 27 106 28 105 29 104) (Triple.mk Bool.false Bool.true Bool.false))) (Table.leaf (Relation.mk (Six.mk 30 109 31 108 32 107) (Triple.mk Bool.false Bool.true Bool.false))))) (Table.node 11 (Table.node 10 (Table.leaf (Relation.mk (Six.mk 3 104 27 68 33 62) (Triple.mk Bool.true Bool.false Bool.true))) (Table.leaf (Relation.mk (Six.mk 4 104 28 68 33 63) (Triple.mk Bool.false Bool.true Bool.false)))) (Table.node 12 (Table.leaf (Relation.mk (Six.mk 5 105 29 69 34 64) (Triple.mk Bool.false Bool.true Bool.false))) (Table.leaf (Relation.mk (Six.mk 12 104 27 84 49 62) (Triple.mk Bool.false Bool.true Bool.false)))))))
def relation (index : Nat) : Relation := relationTable.get index
def sourceIndexTable : Table Nat := (Table.node 6 (Table.node 3 (Table.node 1 (Table.leaf 191) (Table.node 2 (Table.leaf 213) (Table.leaf 216))) (Table.node 4 (Table.leaf 369) (Table.node 5 (Table.leaf 422) (Table.leaf 433)))) (Table.node 9 (Table.node 7 (Table.leaf 472) (Table.node 8 (Table.leaf 579) (Table.leaf 614))) (Table.node 11 (Table.node 10 (Table.leaf 635) (Table.leaf 670)) (Table.node 12 (Table.leaf 705) (Table.leaf 947)))))
def sourceIndex (index : Nat) : Nat := sourceIndexTable.get index
abbrev Subset := Papers.RationalityTen.PureGP.Data.Subset
def subset (index : Nat) : Subset := Papers.RationalityTen.PureGP.Data.subset index
def ValidUsedRelations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 13 → Eq ((relation index).allowed assignment) Bool.true
theorem ValidUsedRelations.with_global_negation {assignment : Nat → Sign}
    (h : ValidUsedRelations assignment) (flag : Bool) :
    ValidUsedRelations (fun index => Sign.withNegation flag (assignment index)) :=
  fun index bounded => Eq.trans
    ((relation index).allowed_global_negation assignment flag) (h index bounded)
end Papers.RationalityTen.PureGP.SevenSurvivor.Data
#print axioms Papers.RationalityTen.PureGP.SevenSurvivor.Data.ValidUsedRelations.with_global_negation
