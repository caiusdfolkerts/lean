module
prelude
public import PureGP.SupportCore

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.PrismNine.Data
def relationTable : Table Relation := (Table.leaf (Relation.mk (Six.mk 2 18 3 16 4 15) (Triple.mk Bool.false Bool.true Bool.false)))
def relation (index : Nat) : Relation := relationTable.get index
def sourceIndexTable : Table Nat := (Table.leaf 16)
def sourceIndex (index : Nat) : Nat := sourceIndexTable.get index
abbrev Subset := Papers.RationalityTen.PureGP.Data.Subset
def subset (index : Nat) : Subset := Papers.RationalityTen.PureGP.Data.subset index
def ValidUsedRelations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 1 → Eq ((relation index).allowed assignment) Bool.true
theorem ValidUsedRelations.with_global_negation {assignment : Nat → Sign}
    (h : ValidUsedRelations assignment) (flag : Bool) :
    ValidUsedRelations (fun index => Sign.withNegation flag (assignment index)) :=
  fun index bounded => Eq.trans
    ((relation index).allowed_global_negation assignment flag) (h index bounded)
end Papers.RationalityTen.PureGP.PrismNine.Data
#print axioms Papers.RationalityTen.PureGP.PrismNine.Data.ValidUsedRelations.with_global_negation
