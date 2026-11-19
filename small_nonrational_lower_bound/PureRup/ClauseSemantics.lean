module
prelude
public import Init.Data.List.Basic

@[expose] public section

/-!
# Propositional semantics for a tree of clauses

This small Init-only interface presents clauses as iterated implications and
formulas as conjunctions. The formulation allows a refutation generated from
unit propagation to be checked by Lean's ordinary kernel. It introduces no
axioms and performs no external computation.

The public interface was recovered from the earlier compiled module; the
proofs below are written afresh from the definitions.
-/

namespace Papers.RationalityTen.PureClauseSemantics

inductive Literal where
  | pos : Nat → Literal
  | neg : Nat → Literal

abbrev Clause := List Literal
abbrev Formula := List Clause
abbrev Valuation := Nat → Prop

def falsified (v : Valuation) : Literal → Prop
  | .pos i => v i → False
  | .neg i => v i

def satisfiesClause (v : Valuation) : Clause → Prop
  | [] => False
  | lit :: rest => falsified v lit → satisfiesClause v rest

def satisfiesFormula (v : Valuation) : Formula → Prop
  | [] => True
  | clause :: rest => satisfiesClause v clause ∧ satisfiesFormula v rest

def Refutation (formula : Formula) : Prop :=
  ∀ v : Valuation, satisfiesFormula v formula → False

theorem append_left (v : Valuation) (left right : Formula) :
    satisfiesFormula v (left ++ right) → satisfiesFormula v left := by
  induction left with
  | nil => exact fun _ => True.intro
  | cons clause rest ih => exact fun h => ⟨h.1, ih h.2⟩

theorem append_right (v : Valuation) (left right : Formula) :
    satisfiesFormula v (left ++ right) → satisfiesFormula v right := by
  induction left with
  | nil => exact fun h => h
  | cons clause rest ih => exact fun h => ih h.2

inductive ClauseTree where
  | empty : ClauseTree
  | leaf : Clause → ClauseTree
  | node : ClauseTree → ClauseTree → ClauseTree

def ClauseTree.formula : ClauseTree → Formula
  | .empty => []
  | .leaf clause => [clause]
  | .node left right => left.formula ++ right.formula

def ClauseTree.Holds (v : Valuation) : ClauseTree → Prop
  | .empty => True
  | .leaf clause => satisfiesClause v clause
  | .node left right => left.Holds v ∧ right.Holds v

theorem ClauseTree.holds_of_satisfies (tree : ClauseTree) (v : Valuation) :
    satisfiesFormula v tree.formula → tree.Holds v := by
  induction tree with
  | empty => exact fun _ => True.intro
  | leaf clause => exact fun h => h.1
  | node left right ihLeft ihRight =>
    exact fun h => ⟨ihLeft (append_left v _ _ h),
      ihRight (append_right v _ _ h)⟩

theorem ClauseTree.refutation (tree : ClauseTree)
    (h : ∀ v : Valuation, tree.Holds v → False) : Refutation tree.formula :=
  fun v hv => h v (tree.holds_of_satisfies v hv)

end Papers.RationalityTen.PureClauseSemantics

#print axioms Papers.RationalityTen.PureClauseSemantics.ClauseTree.refutation
