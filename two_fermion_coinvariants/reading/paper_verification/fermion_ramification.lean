module

public import PaperVerification.FermionLocalRoots
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic.Ring

/-!
# Exact univariate ramification and paired cofactor identities

All cancellation in this file takes place in the polynomial domain before
evaluation in a possibly nonreduced local coefficient algebra.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open Polynomial
variable {F : Type*} [Field F]

def rootCofactor (p : Polynomial F) (c : F) : Polynomial F :=
  p /ₘ (X-C c)^p.rootMultiplicity c

theorem rootCofactor_factorization (p : Polynomial F) (c : F) :
    (X-C c)^p.rootMultiplicity c*rootCofactor p c=p :=
  Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p c

theorem rootCofactor_eval_ne_zero (p : Polynomial F) (hp : p≠0) (c : F) :
    (rootCofactor p c).eval c≠0 :=
  Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hp

theorem rootCofactor_ne_zero (p : Polynomial F) (hp : p≠0) (c : F) :
    rootCofactor p c≠0 := by
  intro h
  exact rootCofactor_eval_ne_zero p hp c (by rw [h,eval_zero])

/-- The full composition identity retains its unit cofactor. -/
theorem ramification_composition_factorization (G phi : Polynomial F) (rho : F) :
    (X-C rho)^((phi-C (phi.eval rho)).rootMultiplicity rho*
      G.rootMultiplicity (phi.eval rho)) *
      (rootCofactor (phi-C (phi.eval rho)) rho^G.rootMultiplicity (phi.eval rho) *
        (rootCofactor G (phi.eval rho)).comp phi)=G.comp phi := by
  have hG := congrArg (fun p : Polynomial F ↦ p.comp phi)
    (rootCofactor_factorization G (phi.eval rho))
  have hp := rootCofactor_factorization (phi-C (phi.eval rho)) rho
  rw [mul_comp,pow_comp,sub_comp,X_comp,C_comp] at hG
  rw [←hp,mul_pow,←pow_mul] at hG
  simpa only [mul_assoc] using hG

theorem ramification_composition_multiplicity (G phi : Polynomial F) (rho : F)
    (hG : G≠0) (hphi : phi-C (phi.eval rho)≠0) :
    (G.comp phi).rootMultiplicity rho=
      (phi-C (phi.eval rho)).rootMultiplicity rho*G.rootMultiplicity (phi.eval rho) := by
  let q := rootCofactor (phi-C (phi.eval rho)) rho^G.rootMultiplicity (phi.eval rho) *
    (rootCofactor G (phi.eval rho)).comp phi
  have hqe : q.eval rho≠0 := by
    simpa only [q,eval_mul,eval_pow,eval_comp] using
      mul_ne_zero
        (pow_ne_zero _ (rootCofactor_eval_ne_zero _ hphi rho))
        (rootCofactor_eval_ne_zero G hG (phi.eval rho))
  have hq : q≠0 := by
    intro h
    exact hqe (by rw [h,eval_zero])
  rw [←ramification_composition_factorization G phi rho,mul_comm]
  change (q*(X-C rho)^_).rootMultiplicity rho=_
  rw [rootMultiplicity_mul_X_sub_C_pow hq,
    rootMultiplicity_eq_zero (show ¬q.IsRoot rho from hqe),zero_add]

theorem ramification_composition_ne_zero (G phi : Polynomial F) (rho : F)
    (hG : G≠0) (hphi : phi-C (phi.eval rho)≠0) : G.comp phi≠0 := by
  rw [←ramification_composition_factorization G phi rho]
  apply mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero rho))
  apply mul_ne_zero
    (pow_ne_zero _ (rootCofactor_ne_zero _ hphi rho))
  intro h
  have he := congrArg (Polynomial.eval rho) h
  exact rootCofactor_eval_ne_zero G hG (phi.eval rho) (by simpa only [eval_comp,eval_zero] using he)

/-- The exact exponent balance used in the homogeneous local factor. -/
theorem paired_rootMultiplicity_balance (G phi a b : Polynomial F) (rho : F)
    (hG : G≠0) (hphi : phi-C (phi.eval rho)≠0) (hab : a*b=G.comp phi) :
    a.rootMultiplicity rho+b.rootMultiplicity rho=
      (phi-C (phi.eval rho)).rootMultiplicity rho*G.rootMultiplicity (phi.eval rho) := by
  have hn : a*b≠0 := by
    rw [hab]
    exact ramification_composition_ne_zero G phi rho hG hphi
  rw [←rootMultiplicity_mul hn,hab]
  exact ramification_composition_multiplicity G phi rho hG hphi

/-- Cancel the common power in the polynomial domain, then retain this exact
identity for later evaluation. No nilpotent is cancelled in a quotient. -/
theorem paired_rootCofactor_product (G phi a b : Polynomial F) (rho : F)
    (hG : G≠0) (hphi : phi-C (phi.eval rho)≠0) (hab : a*b=G.comp phi) :
    rootCofactor a rho*rootCofactor b rho=
      rootCofactor (phi-C (phi.eval rho)) rho^G.rootMultiplicity (phi.eval rho) *
        (rootCofactor G (phi.eval rho)).comp phi := by
  have hb := paired_rootMultiplicity_balance G phi a b rho hG hphi hab
  apply mul_left_cancel₀
    (pow_ne_zero (a.rootMultiplicity rho+b.rootMultiplicity rho) (X_sub_C_ne_zero rho))
  calc
    (X-C rho)^(a.rootMultiplicity rho+b.rootMultiplicity rho) *
        (rootCofactor a rho*rootCofactor b rho) =
        ((X-C rho)^a.rootMultiplicity rho*rootCofactor a rho) *
          ((X-C rho)^b.rootMultiplicity rho*rootCofactor b rho) := by
            rw [pow_add]
            ring
    _=a*b := by rw [rootCofactor_factorization,rootCofactor_factorization]
    _=G.comp phi := hab
    _=(X-C rho)^(a.rootMultiplicity rho+b.rootMultiplicity rho) *
        (rootCofactor (phi-C (phi.eval rho)) rho^G.rootMultiplicity (phi.eval rho) *
          (rootCofactor G (phi.eval rho)).comp phi) := by
      rw [hb]
      exact (ramification_composition_factorization G phi rho).symm

end PaperVerification.Fermion

