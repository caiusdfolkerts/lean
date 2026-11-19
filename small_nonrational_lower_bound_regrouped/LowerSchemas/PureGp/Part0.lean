module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_SupportEquations " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index ⟪0⟫ → (edge index).Holds assignment"### args

elab "cert_ZeroEquations " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index ⟪0⟫ → Eq (assignment (zero index)) Sign.zero"### args

elab "cert_after " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_14 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_15 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_after_16 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_17 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_18 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_after_19 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_after_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_after_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_after_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_after_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_after_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_after_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def after⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_anchor " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def anchor : Nat := ⟪0⟫"### args

elab "cert_before " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def before⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.true Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_before_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def before⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.true Bool.true) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_before_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def before⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.true Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_before_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def before⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.true Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_before_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def before⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.true Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_before_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def before⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.true Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true))"### args

elab "cert_before_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def before⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.true Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.true Bool.false Bool.false))"### args

elab "cert_before_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def before⟪0⟫ : Six Domain := (Six.mk (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.false Bool.false) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.false Bool.false Bool.true) (Domain.mk Bool.true Bool.true Bool.true))"### args

elab "cert_checked_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked⟪0⟫ : Eq (contradictionCheck before⟪0⟫ negations⟪0⟫) Bool.true := Eq.refl Bool.true"### args

elab "cert_checked_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked⟪0⟫ : Eq (stepCheck before⟪0⟫ after⟪0⟫ negations⟪0⟫) Bool.true := Eq.refl Bool.true"### args

elab "cert_edge " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def edge (index : Nat) : SupportEdge := edgeTable.get index"### args

elab "cert_globalNegation " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def globalNegation : Bool := Bool.false"### args

elab "cert_globalNegation_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def globalNegation : Bool := Bool.true"### args

elab "cert_initial " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def initial (index : Nat) : Domain := initialTable.get index"### args

elab "cert_negations " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def negations⟪0⟫ : Triple Bool := (Triple.mk Bool.false Bool.true Bool.false)"### args

elab "cert_negations_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def negations⟪0⟫ : Triple Bool := (Triple.mk Bool.true Bool.false Bool.true)"### args

elab "cert_support_sign_contradiction " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C⟪0⟫.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)"### args

elab "cert_zero " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def zero (index : Nat) : Nat := zeroTable.get index"### args

elab "cert_zeroTable " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def zeroTable : Table Nat := (Table.node 5 (Table.node 2 (Table.node 1 (Table.leaf ⟪0⟫) (Table.leaf ⟪1⟫)) (Table.node 3 (Table.leaf ⟪2⟫) (Table.node 4 (Table.leaf ⟪3⟫) (Table.leaf ⟪4⟫)))) (Table.node 7 (Table.node 6 (Table.leaf ⟪5⟫) (Table.leaf ⟪6⟫)) (Table.node 8 (Table.leaf ⟪7⟫) (Table.node 9 (Table.leaf ⟪8⟫) (Table.leaf ⟪9⟫)))))"### args

elab "cert_zeroTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def zeroTable : Table Nat := (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf ⟪1⟫) (Table.node 2 (Table.leaf ⟪0⟫) (Table.leaf ⟪2⟫))) (Table.node 5 (Table.node 4 (Table.leaf ⟪3⟫) (Table.leaf ⟪4⟫)) (Table.node 6 (Table.leaf ⟪5⟫) (Table.leaf ⟪6⟫)))) (Table.node 11 (Table.node 9 (Table.node 8 (Table.leaf ⟪7⟫) (Table.leaf ⟪8⟫)) (Table.node 10 (Table.leaf ⟪9⟫) (Table.leaf ⟪10⟫))) (Table.node 13 (Table.node 12 (Table.leaf ⟪11⟫) (Table.leaf ⟪12⟫)) (Table.node 14 (Table.leaf ⟪13⟫) (Table.leaf ⟪14⟫)))))"### args

