module
prelude
public import PureRup.ClauseSemantics
public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section
noncomputable section

/-!
# Exact conversion of the small clause semantics to Mathlib SAT

This adapter changes only the literal datatype and the presentation of a
formula's conjunction. Variable numbers, signs, clause order and clause
membership are preserved. The Init-only semantics can be checked without
loading Mathlib; this final adapter belongs to the Mathlib build.


-/

namespace Papers.RationalityTen.PureClauseSemantics

def Literal.toSat : Literal → Sat.Literal
  | .pos i => .pos i
  | .neg i => .neg i

def Clause.toSat (clause : Clause) : Sat.Clause := clause.map Literal.toSat

def Formula.toSat (formula : Formula) : Sat.Fmla := formula.map Clause.toSat

theorem clause_meaning_exact (v : Valuation) (clause : Clause) :
    satisfiesClause v clause = Sat.Valuation.satisfies v clause.toSat := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
    cases literal with
    | pos i =>
      simpa only [satisfiesClause,falsified,Clause.toSat,List.map,
        Literal.toSat,Sat.Valuation.satisfies,Sat.Valuation.neg] using
        congrArg (fun P : Prop => (v i → False) → P) ih
    | neg i =>
      simpa only [satisfiesClause,falsified,Clause.toSat,List.map,
        Literal.toSat,Sat.Valuation.satisfies,Sat.Valuation.neg] using
        congrArg (fun P : Prop => v i → P) ih

theorem formula_meaning_of_sat (v : Valuation) (formula : Formula)
    (h : Sat.Valuation.satisfies_fmla v formula.toSat) :
    satisfiesFormula v formula := by
  revert h
  induction formula with
  | nil => exact fun _ => True.intro
  | cons clause rest ih =>
    intro h
    constructor
    · rw [clause_meaning_exact]
      exact h.prop clause.toSat (List.Mem.head _)
    · apply ih
      refine ⟨fun C hC => ?_⟩
      exact h.prop C (List.mem_cons_of_mem _ hC)

theorem Refutation.toSat {formula : Formula} (h : Refutation formula) :
    formula.toSat.proof [] :=
  fun v hv => h v (formula_meaning_of_sat v formula hv)

end Papers.RationalityTen.PureClauseSemantics
