module
prelude
public import Init.Prelude

@[expose] public section
noncomputable section

/-!
# Finite sign-domain propagation

This small kernel proof uses only Init.Prelude. A local propagation step
is accepted only after all 3^6 sign choices have been checked against
the exact signed three-term relation. The soundness theorem applies it
to an arbitrary assignment; it assumes neither realizability nor a
particular propagation algorithm.
-/

namespace Papers.RationalityTen.PureGP

inductive Sign where
  | negative
  | zero
  | positive

def Sign.negate : Sign → Sign
  | .negative => .positive
  | .zero => .zero
  | .positive => .negative

def Sign.multiply : Sign → Sign → Sign
  | .zero, _ => .zero
  | _, .zero => .zero
  | .negative, .negative => .positive
  | .positive, .positive => .positive
  | .negative, .positive => .negative
  | .positive, .negative => .negative

def Sign.isNegative : Sign → Bool
  | .negative => Bool.true
  | _ => Bool.false

def Sign.isZero : Sign → Bool
  | .zero => Bool.true
  | _ => Bool.false

def Sign.isPositive : Sign → Bool
  | .positive => Bool.true
  | _ => Bool.false

def Sign.withNegation (negate : Bool) (sign : Sign) : Sign :=
  Bool.rec sign sign.negate negate

structure Domain where
  negative : Bool
  zero : Bool
  positive : Bool

def Domain.allows (domain : Domain) : Sign → Bool
  | .negative => domain.negative
  | .zero => domain.zero
  | .positive => domain.positive

def Domain.top : Domain := Domain.mk Bool.true Bool.true Bool.true

structure Triple (α : Type) where
  a : α
  b : α
  c : α

structure Six (α : Type) where
  a : α
  b : α
  c : α
  d : α
  e : α
  f : α

def gpAllowed (negations : Triple Bool) (s : Six Sign) : Bool :=
  let a := Sign.withNegation negations.a (s.a.multiply s.b)
  let b := Sign.withNegation negations.b (s.c.multiply s.d)
  let c := Sign.withNegation negations.c (s.e.multiply s.f)
  Bool.or (Bool.and a.isZero (Bool.and b.isZero c.isZero))
    (Bool.and (Bool.or a.isNegative (Bool.or b.isNegative c.isNegative))
      (Bool.or a.isPositive (Bool.or b.isPositive c.isPositive)))

structure Relation where
  indices : Six Nat
  negations : Triple Bool

def Relation.signs (relation : Relation) (assignment : Nat → Sign) : Six Sign :=
  Six.mk (assignment relation.indices.a) (assignment relation.indices.b)
    (assignment relation.indices.c) (assignment relation.indices.d)
    (assignment relation.indices.e) (assignment relation.indices.f)

def Relation.allowed (relation : Relation) (assignment : Nat → Sign) : Bool :=
  gpAllowed relation.negations (relation.signs assignment)

def fitsBool (domains : Six Domain) (signs : Six Sign) : Bool :=
  Bool.and (domains.a.allows signs.a)
    (Bool.and (domains.b.allows signs.b)
      (Bool.and (domains.c.allows signs.c)
        (Bool.and (domains.d.allows signs.d)
          (Bool.and (domains.e.allows signs.e) (domains.f.allows signs.f)))))

structure Fits (domains : Six Domain) (signs : Six Sign) : Prop where
  a : Eq (domains.a.allows signs.a) Bool.true
  b : Eq (domains.b.allows signs.b) Bool.true
  c : Eq (domains.c.allows signs.c) Bool.true
  d : Eq (domains.d.allows signs.d) Bool.true
  e : Eq (domains.e.allows signs.e) Bool.true
  f : Eq (domains.f.allows signs.f) Bool.true

theorem and_left : {a b : Bool} → Eq (Bool.and a b) Bool.true → Eq a Bool.true
  | Bool.false, _, h => False.elim (Bool.noConfusion h)
  | Bool.true, _, _ => rfl

theorem and_right : {a b : Bool} → Eq (Bool.and a b) Bool.true → Eq b Bool.true
  | Bool.false, _, h => False.elim (Bool.noConfusion h)
  | Bool.true, _, h => h

theorem and_intro {a b : Bool} (ha : Eq a Bool.true) (hb : Eq b Bool.true) :
    Eq (Bool.and a b) Bool.true :=
  Eq.trans (congrArg (fun value => Bool.and value b) ha) hb

theorem Fits.boolean {domains : Six Domain} {signs : Six Sign}
    (h : Fits domains signs) : Eq (fitsBool domains signs) Bool.true :=
  and_intro h.a (and_intro h.b (and_intro h.c (and_intro h.d (and_intro h.e h.f))))

theorem Fits.of_boolean {domains : Six Domain} {signs : Six Sign}
    (h : Eq (fitsBool domains signs) Bool.true) : Fits domains signs :=
  Fits.mk (and_left h) (and_left (and_right h))
    (and_left (and_right (and_right h)))
    (and_left (and_right (and_right (and_right h))))
    (and_left (and_right (and_right (and_right (and_right h)))))
    (and_right (and_right (and_right (and_right (and_right h)))))

def allSigns (predicate : Sign → Bool) : Bool :=
  Bool.and (predicate .negative) (Bool.and (predicate .zero) (predicate .positive))

theorem allSigns_sound (predicate : Sign → Bool)
    (h : Eq (allSigns predicate) Bool.true) (sign : Sign) :
    Eq (predicate sign) Bool.true :=
  match sign with
  | .negative => and_left h
  | .zero => and_left (and_right h)
  | .positive => and_right (and_right h)

def allSix (predicate : Six Sign → Bool) : Bool :=
  allSigns (fun a => allSigns (fun b => allSigns (fun c => allSigns (fun d =>
    allSigns (fun e => allSigns (fun f => predicate (Six.mk a b c d e f)))))))

theorem allSix_sound (predicate : Six Sign → Bool)
    (h : Eq (allSix predicate) Bool.true) (signs : Six Sign) :
    Eq (predicate signs) Bool.true :=
  match signs with
  | Six.mk a b c d e f =>
    allSigns_sound _ (allSigns_sound _ (allSigns_sound _
      (allSigns_sound _ (allSigns_sound _ (allSigns_sound _ h a) b) c) d) e) f

def implies (premise conclusion : Bool) : Bool := Bool.rec Bool.true conclusion premise

theorem implies_sound (premise conclusion : Bool)
    (h : Eq (implies premise conclusion) Bool.true) (hp : Eq premise Bool.true) :
    Eq conclusion Bool.true :=
  match premise, h, hp with
  | Bool.false, _, impossible => False.elim (Bool.noConfusion impossible)
  | Bool.true, checked, _ => checked

def stepCheck (before after : Six Domain) (negations : Triple Bool) : Bool :=
  allSix (fun signs => implies
    (Bool.and (fitsBool before signs) (gpAllowed negations signs)) (fitsBool after signs))

theorem step_sound (before after : Six Domain) (negations : Triple Bool)
    (checked : Eq (stepCheck before after negations) Bool.true)
    (signs : Six Sign) (hbefore : Fits before signs)
    (hgp : Eq (gpAllowed negations signs) Bool.true) : Fits after signs :=
  Fits.of_boolean (implies_sound _ _ (allSix_sound _ checked signs)
    (and_intro hbefore.boolean hgp))

def contradictionCheck (before : Six Domain) (negations : Triple Bool) : Bool :=
  allSix (fun signs => implies
    (Bool.and (fitsBool before signs) (gpAllowed negations signs)) Bool.false)

theorem contradiction_sound (before : Six Domain) (negations : Triple Bool)
    (checked : Eq (contradictionCheck before negations) Bool.true)
    (signs : Six Sign) (hbefore : Fits before signs)
    (hgp : Eq (gpAllowed negations signs) Bool.true) : False :=
  Bool.noConfusion (implies_sound _ _ (allSix_sound _ checked signs)
    (and_intro hbefore.boolean hgp))

/-- A balanced literal lookup is only a data presentation. Every theorem
below uses the value it actually returns; no producer invariant is assumed. -/
inductive Table (α : Type) where
  | leaf (value : α)
  | node (cut : Nat) (left right : Table α)

def Table.get {α : Type} : Table α → Nat → α
  | .leaf value, _ => value
  | .node cut left right, index =>
      Bool.rec (left.get index) (right.get index) (Nat.ble cut index)

end Papers.RationalityTen.PureGP

#print axioms Papers.RationalityTen.PureGP.step_sound
#print axioms Papers.RationalityTen.PureGP.contradiction_sound

end
end
