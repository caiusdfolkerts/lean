module
public import shared_results.part017_nested

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ColoredOrderExtension -/
section

/-!
# Extending the original monomial order by color variables

The color block is compared lexicographically first, and the old block
uses the given arbitrary monomial order. Restriction therefore recovers
all original comparisons and the literal original initial ideal.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial
open scoped MonomialOrder
universe u
variable {d r : ℕ} {n : Fin d → ℕ}

/-- A block extension of any original order; no order on the old variables
is imposed beyond the supplied monomial order. -/
def coloredExtendedOrder (M : MonomialOrder (FiniteVariable.{u} n)) :
    MonomialOrder (FiniteVariable.{u} (coloredRows (r := r) n)) where
  syn := (MonomialOrder.lex (σ := ULift.{u} (Fin r))).syn ×ₗ M.syn
  toSyn :=
    { toFun := fun a => toLex
        ((MonomialOrder.lex (σ := ULift.{u} (Fin r))).toSyn (colorExponent a),
          M.toSyn (baseExponent a))
      invFun := fun a => coloredExponent
        ((MonomialOrder.lex (σ := ULift.{u} (Fin r))).toSyn.symm (ofLex a).1)
        (M.toSyn.symm (ofLex a).2)
      left_inv := by
        intro a
        simp only [ofLex_toLex, AddEquiv.symm_apply_apply]
        exact coloredExponent_reconstruct a
      right_inv := by
        intro a
        simp only [colorExponent_coloredExponent, baseExponent_coloredExponent,
          AddEquiv.apply_symm_apply, Prod.mk.eta, toLex_ofLex]
      map_add' := by
        intro a b
        simp only [map_add]
        rfl }
  toSyn_monotone := by
    intro a b hab
    apply Prod.Lex.toLex_mono
    exact ⟨(MonomialOrder.lex (σ := ULift.{u} (Fin r))).toSyn_monotone
      (fun c => hab ⟨0,c⟩), M.toSyn_monotone (fun v => hab ⟨v.1.succ,v.2⟩)⟩

@[simp] theorem coloredExtendedOrder_base_compare
    (M : MonomialOrder (FiniteVariable.{u} n)) (a b : FiniteVariable.{u} n →₀ ℕ) :
    coloredExponent (r := r) 0 a ≼[coloredExtendedOrder M]
      coloredExponent 0 b ↔ a ≼[M] b := by
  change toLex ((MonomialOrder.lex (σ := ULift.{u} (Fin r))).toSyn
      (colorExponent (coloredExponent 0 a)), M.toSyn (baseExponent (coloredExponent 0 a))) ≤
    toLex ((MonomialOrder.lex (σ := ULift.{u} (Fin r))).toSyn
      (colorExponent (coloredExponent 0 b)), M.toSyn (baseExponent (coloredExponent 0 b))) ↔ _
  simp only [colorExponent_coloredExponent, baseExponent_coloredExponent,
    Prod.Lex.toLex_le_toLex, lt_self_iff_false, true_and, false_or]

@[simp] theorem coloredRestrictedOrder_extended_compare
    (M : MonomialOrder (FiniteVariable.{u} n)) (a b : FiniteVariable.{u} n →₀ ℕ) :
    a ≼[coloredRestrictedOrder (r := r) (coloredExtendedOrder M)] b ↔ a ≼[M] b := by
  rw [coloredRestrictedOrder, monomialOrderRestriction_le, base_mapDomain, base_mapDomain]
  exact coloredExtendedOrder_base_compare M a b

variable {K : Type u} [CommRing K]

@[simp] theorem coloredRestrictedOrder_extended_degree
    (M : MonomialOrder (FiniteVariable.{u} n)) (f : MvPolynomial (FiniteVariable.{u} n) K) :
    (coloredRestrictedOrder (r := r) (coloredExtendedOrder M)).degree f = M.degree f := by
  let Q := coloredRestrictedOrder (r := r) (coloredExtendedOrder M)
  apply M.toSyn.injective
  apply le_antisymm
  · apply (coloredRestrictedOrder_extended_compare M _ _).mp
    apply Q.degree_le_iff.mpr
    intro a ha
    exact (coloredRestrictedOrder_extended_compare M _ _).mpr (M.le_degree ha)
  · apply M.degree_le_iff.mpr
    intro a ha
    exact (coloredRestrictedOrder_extended_compare M _ _).mp (Q.le_degree ha)

@[simp] theorem coloredRestrictedOrder_extended_leadingTerm
    (M : MonomialOrder (FiniteVariable.{u} n)) (f : MvPolynomial (FiniteVariable.{u} n) K) :
    (coloredRestrictedOrder (r := r) (coloredExtendedOrder M)).leadingTerm f = M.leadingTerm f := by
  change monomial ((coloredRestrictedOrder (r := r) (coloredExtendedOrder M)).degree f)
      (f.coeff ((coloredRestrictedOrder (r := r) (coloredExtendedOrder M)).degree f)) =
    monomial (M.degree f) (f.coeff (M.degree f))
  rw [coloredRestrictedOrder_extended_degree]

/-- Initial ideals after restriction are exactly those for the original
order, including arbitrary coefficient ideals. -/
@[simp] theorem coloredRestrictedOrder_extended_initialIdeal
    (M : MonomialOrder (FiniteVariable.{u} n)) (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K)) :
    FourPapers.initialIdeal (coloredRestrictedOrder (r := r) (coloredExtendedOrder M)) J =
      FourPapers.initialIdeal M J := by
  simp only [FourPapers.initialIdeal, coloredRestrictedOrder_extended_leadingTerm]

end FourPapers.Sublattice

end
end
end


end
