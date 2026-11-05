module
public import graph_foundation.part013
public import shared_results.part019_filtered_tensor_koszul

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredSymbols -/
section

/-! # Actual symbols and finite generation of the associated algebra -/

section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical
open scoped BigOperators

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A)

def symbol (n : ℤ) : F.level n →ₗ[K] F.AssociatedGraded :=
  F.leadingMap.toLinearMap.comp (F.monomial n)

theorem symbol_eq_zero (n : ℤ) (a : F.level n) :
    F.symbol n a=0 ↔ a.val ∈ F.level (n-1) := by
  change F.leadingMap (F.monomial n a)=0 ↔ _
  rw [F.leadingMap_eq_zero]
  constructor
  · intro h
    simpa only [F.monomial_coeff,ite_true] using h n
  · intro h i
    rw [F.monomial_coeff]
    split_ifs with hi
    · subst i
      exact h
    · exact Submodule.zero_mem _

theorem symbol_congr (i j : ℤ) (hij : i=j) (a : F.level i) (b : F.level j)
    (hab : a.val=b.val) : F.symbol i a=F.symbol j b := by
  subst j
  exact congrArg (F.symbol i) (Subtype.ext hab)

theorem symbol_mul (i j : ℤ) (a : F.level i) (b : F.level j) :
    F.symbol i a*F.symbol j b =
      F.symbol (i+j) ⟨a.val*b.val,F.mul_mem i j _ a.property _ b.property⟩ := by
  change F.leadingMap (F.monomial i a)*F.leadingMap (F.monomial j b)=
    F.leadingMap (F.monomial (i+j) ⟨a.val*b.val,F.mul_mem i j _ a.property _ b.property⟩)
  rw [← map_mul]
  apply congrArg F.leadingMap
  apply Subtype.ext
  exact AddMonoidAlgebra.single_mul_single _ _ _ _

theorem symbol_one : F.symbol 0 ⟨1,F.one_mem⟩=1 := by
  change F.leadingMap (F.monomial 0 ⟨1,F.one_mem⟩)=1
  have h : F.monomial 0 ⟨1,F.one_mem⟩=1 := Subtype.ext rfl
  rw [h,map_one]

theorem symbol_decomposition (p : F.rees) :
    F.leadingMap p = ∑ n ∈ p.val.coeff.support,
      F.symbol n ⟨p.val.coeff n,p.property n⟩ := by
  change F.leadingMap p = ∑ n ∈ p.val.coeff.support,
    F.leadingMap (F.monomial n ⟨p.val.coeff n,p.property n⟩)
  rw [← map_sum]
  exact congrArg F.leadingMap (coefficient_decomposition F.level F.one_mem F.mul_mem p).symm

@[elab_as_elim] theorem associated_induction
    (P : F.AssociatedGraded → Prop) (h0 : P 0)
    (hadd : ∀ a b,P a→P b→P (a+b))
    (hsymbol : ∀ n a,P (F.symbol n a)) (x : F.AssociatedGraded) : P x := by
  obtain ⟨p,rfl⟩ := F.leadingMap_surjective x
  rw [F.symbol_decomposition]
  apply Finset.sum_induction
  · exact fun a b ha hb => hadd a b ha hb
  · exact h0
  · intro n _
    exact hsymbol n _

@[simp] theorem associatedGradedEquiv_symbol (n : ℤ) (a : F.level n) :
    F.associatedGradedEquiv (F.symbol n a) =
      DirectSum.of (fun n => F.Grade n) n (Submodule.Quotient.mk a) := by
  change F.associatedGradedEquiv (F.leadingMap (F.monomial n a))=_
  rw [F.associatedGradedEquiv_leading,F.gradedCoefficients_monomial]

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
