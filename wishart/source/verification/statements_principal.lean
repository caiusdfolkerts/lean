module

public import wishart.verified.core05

@[expose] public section

/- Read-only exact-target and axiom display over the freshly compiled stages.
   This file does not redefine a target or supply a missing mathematical fact. -/

theorem WishartAudit.principal_exact : WishartVerification.PrincipalTheorem :=
  WishartVerification.theorem_1_1

