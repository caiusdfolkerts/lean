module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_Check " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem Check⟪0⟫.checked : Interval test ⟪1⟫ ⟪2⟫ :=
  (FiniteChecks.interval_append test ⟪1⟫ ⟪3⟫ ⟪2⟫
  (FiniteChecks.interval_append test ⟪1⟫ ⟪4⟫ ⟪3⟫
  (FiniteChecks.interval_append test ⟪1⟫ ⟪5⟫ ⟪4⟫
  (FiniteChecks.interval_append test ⟪1⟫ ⟪6⟫ ⟪5⟫
  Check⟪0⟫.part⟪1⟫
  Check⟪0⟫.part⟪6⟫)
  (FiniteChecks.interval_append test ⟪5⟫ ⟪7⟫ ⟪4⟫
  Check⟪0⟫.part⟪5⟫
  Check⟪0⟫.part⟪7⟫))
  (FiniteChecks.interval_append test ⟪4⟫ ⟪8⟫ ⟪3⟫
  (FiniteChecks.interval_append test ⟪4⟫ ⟪9⟫ ⟪8⟫
  Check⟪0⟫.part⟪4⟫
  Check⟪0⟫.part⟪9⟫)
  (FiniteChecks.interval_append test ⟪8⟫ ⟪10⟫ ⟪3⟫
  Check⟪0⟫.part⟪8⟫
  Check⟪0⟫.part⟪10⟫)))
  (FiniteChecks.interval_append test ⟪3⟫ ⟪11⟫ ⟪2⟫
  (FiniteChecks.interval_append test ⟪3⟫ ⟪12⟫ ⟪11⟫
  (FiniteChecks.interval_append test ⟪3⟫ ⟪13⟫ ⟪12⟫
  Check⟪0⟫.part⟪3⟫
  Check⟪0⟫.part⟪13⟫)
  (FiniteChecks.interval_append test ⟪12⟫ ⟪14⟫ ⟪11⟫
  Check⟪0⟫.part⟪12⟫
  Check⟪0⟫.part⟪14⟫))
  (FiniteChecks.interval_append test ⟪11⟫ ⟪15⟫ ⟪2⟫
  (FiniteChecks.interval_append test ⟪11⟫ ⟪16⟫ ⟪15⟫
  Check⟪0⟫.part⟪11⟫
  Check⟪0⟫.part⟪16⟫)
  (FiniteChecks.interval_append test ⟪15⟫ ⟪17⟫ ⟪2⟫
  Check⟪0⟫.part⟪15⟫
  Check⟪0⟫.part⟪17⟫))))"### args

elab "cert_Check_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem Check⟪0⟫.part⟪1⟫ : Interval test ⟪1⟫ ⟪2⟫ :=
  interval_of_check _ ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_Check_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem Check⟪0⟫.checked : Interval test ⟪1⟫ ⟪2⟫ :=
  (FiniteChecks.interval_append test ⟪1⟫ ⟪3⟫ ⟪2⟫
  (FiniteChecks.interval_append test ⟪1⟫ ⟪4⟫ ⟪3⟫
  (FiniteChecks.interval_append test ⟪1⟫ ⟪5⟫ ⟪4⟫
  Check⟪0⟫.part⟪1⟫
  Check⟪0⟫.part⟪5⟫)
  (FiniteChecks.interval_append test ⟪4⟫ ⟪6⟫ ⟪3⟫
  Check⟪0⟫.part⟪4⟫
  Check⟪0⟫.part⟪6⟫))
  (FiniteChecks.interval_append test ⟪3⟫ ⟪7⟫ ⟪2⟫
  (FiniteChecks.interval_append test ⟪3⟫ ⟪8⟫ ⟪7⟫
  Check⟪0⟫.part⟪3⟫
  Check⟪0⟫.part⟪8⟫)
  (FiniteChecks.interval_append test ⟪7⟫ ⟪9⟫ ⟪2⟫
  Check⟪0⟫.part⟪7⟫
  Check⟪0⟫.part⟪9⟫)))"### args

