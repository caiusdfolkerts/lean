module
prelude
public import PureGP.Core
public import PureGP.Relations

@[expose] public section
noncomputable section

/-!
# Support-sign paths and finite initial-domain certificates

Only the equations supplied by an anchor, support comparisons, and
explicit zero witnesses are used here. Their actual determinant meaning
is a separate geometric theorem. Global sign reversal preserves every
GP constraint because each term is a product of two brackets.
-/

namespace Papers.RationalityTen.PureGP

theorem below_zero (predicate : Nat → Prop) :
    ∀ index, LT.lt index 0 → predicate index :=
  fun index impossible => False.elim (Nat.not_lt_zero index impossible)

theorem below_succ {predicate : Nat → Prop} {bound : Nat}
    (previous : ∀ index, LT.lt index bound → predicate index)
    (last : predicate bound) :
    ∀ index, LT.lt index (Nat.succ bound) → predicate index :=
  fun index h =>
    match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with
    | Or.inl equality => Eq.ndrec_symm last equality
    | Or.inr smaller => previous index smaller

theorem Sign.withNegation_twice (flag : Bool) (sign : Sign) :
    Eq (Sign.withNegation flag (Sign.withNegation flag sign)) sign :=
  match flag, sign with
  | Bool.false, _ => Eq.refl _
  | Bool.true, .negative => Eq.refl _
  | Bool.true, .zero => Eq.refl _
  | Bool.true, .positive => Eq.refl _

theorem Sign.reverse_support {left right : Sign} (flag : Bool)
    (h : Eq right (Sign.withNegation flag left)) :
    Eq left (Sign.withNegation flag right) :=
  Eq.trans (Eq.symm (Sign.withNegation_twice flag left))
    (congrArg (Sign.withNegation flag) (Eq.symm h))

theorem Sign.multiply_withNegation (flag : Bool) (left right : Sign) :
    Eq ((Sign.withNegation flag left).multiply (Sign.withNegation flag right))
      (left.multiply right) :=
  match flag, left, right with
  | Bool.false, _, _ => Eq.refl _
  | Bool.true, .negative, .negative => Eq.refl _
  | Bool.true, .negative, .zero => Eq.refl _
  | Bool.true, .negative, .positive => Eq.refl _
  | Bool.true, .zero, .negative => Eq.refl _
  | Bool.true, .zero, .zero => Eq.refl _
  | Bool.true, .zero, .positive => Eq.refl _
  | Bool.true, .positive, .negative => Eq.refl _
  | Bool.true, .positive, .zero => Eq.refl _
  | Bool.true, .positive, .positive => Eq.refl _

theorem congr_three {α β γ δ : Type} (f : α → β → γ → δ)
    {a a' : α} {b b' : β} {c c' : γ}
    (ha : Eq a a') (hb : Eq b b') (hc : Eq c c') :
    Eq (f a b c) (f a' b' c') :=
  Eq.trans (congrArg (fun x => f x b c) ha)
    (Eq.trans (congrArg (fun y => f a' y c) hb) (congrArg (f a' b') hc))

theorem Relation.allowed_global_negation (relation : Relation)
    (assignment : Nat → Sign) (flag : Bool) :
    Eq (relation.allowed (fun index => Sign.withNegation flag (assignment index)))
      (relation.allowed assignment) :=
  congr_three
    (fun a b c : Sign =>
      let x := Sign.withNegation relation.negations.a a
      let y := Sign.withNegation relation.negations.b b
      let z := Sign.withNegation relation.negations.c c
      Bool.or (Bool.and x.isZero (Bool.and y.isZero z.isZero))
        (Bool.and (Bool.or x.isNegative (Bool.or y.isNegative z.isNegative))
          (Bool.or x.isPositive (Bool.or y.isPositive z.isPositive))))
    (Sign.multiply_withNegation flag (assignment relation.indices.a) (assignment relation.indices.b))
    (Sign.multiply_withNegation flag (assignment relation.indices.c) (assignment relation.indices.d))
    (Sign.multiply_withNegation flag (assignment relation.indices.e) (assignment relation.indices.f))

theorem Data.ValidUsedRelations.with_global_negation {assignment : Nat → Sign}
    (h : Data.ValidUsedRelations assignment) (flag : Bool) :
    Data.ValidUsedRelations (fun index => Sign.withNegation flag (assignment index)) :=
  fun index bounded => Eq.trans
    ((Data.relation index).allowed_global_negation assignment flag) (h index bounded)

theorem domain_from_eq {domain : Domain} {actual known : Sign}
    (equality : Eq actual known) (checked : Eq (domain.allows known) Bool.true) :
    Eq (domain.allows actual) Bool.true :=
  Eq.trans (congrArg domain.allows equality) checked

theorem top_allows (sign : Sign) : Eq (Domain.top.allows sign) Bool.true :=
  match sign with
  | .negative => Eq.refl _
  | .zero => Eq.refl _
  | .positive => Eq.refl _

structure SupportEdge where
  source : Nat
  target : Nat
  negate : Bool

def SupportEdge.Holds (edge : SupportEdge) (assignment : Nat → Sign) : Prop :=
  Eq (assignment edge.target) (Sign.withNegation edge.negate (assignment edge.source))

end Papers.RationalityTen.PureGP

#print axioms Papers.RationalityTen.PureGP.Data.ValidUsedRelations.with_global_negation
#print axioms Papers.RationalityTen.PureGP.below_succ

end
end
