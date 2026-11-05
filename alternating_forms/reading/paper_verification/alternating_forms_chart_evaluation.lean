module

public import PaperVerification.AlternatingFormsChartUniversal
public import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Tactic

/-!
# Split evaluation on every Grassmannian chart

The independent coefficients of every alternating form are the parameters.
On a Plücker chart the pivot columns are the identity. Restricting the ambient
coordinate two-forms supported on pairs of pivot columns therefore gives all
coordinate two-forms on the tautological plane. The matrices below record this
splitting for any finite number of alternating forms.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {t n m : ℕ}

/-- A pair of row indices determines the corresponding pair of pivot columns. -/
def chartPivotPair (p : PluckerIndex (t+2) n) (a : StrictPairs (t+2)) : StrictPairs n :=
  ⟨(p.val a.val.1,p.val a.val.2),p.property a.property⟩

/-- Restriction of a pivot-coordinate two-form to the row-reduced plane. -/
lemma chart_pivot_twoByTwo (p : PluckerIndex (t+2) n)
    (a b : StrictPairs (t+2)) :
    pluckerChartMatrix (K:=K) p a.val.1 (p.val b.val.1) *
        pluckerChartMatrix (K:=K) p a.val.2 (p.val b.val.2) -
      pluckerChartMatrix (K:=K) p a.val.1 (p.val b.val.2) *
        pluckerChartMatrix (K:=K) p a.val.2 (p.val b.val.1) =
      if a=b then 1 else 0 := by
  classical
  have he (i j : Fin (t+2)) : pluckerChartMatrix (K:=K) p i (p.val j) =
      (1 : Matrix (Fin (t+2)) (Fin (t+2))
        (MvPolynomial (PluckerChartVariable p) K)) i j :=
    congrFun (congrFun (pluckerChartMatrix_pivot (K:=K) p) i) j
  simp only [he,Matrix.one_apply]
  by_cases hab : a=b
  · subst b
    simp [a.property.ne,a.property.ne.symm]
  · have hdiag : ¬ (a.val.1=b.val.1 ∧ a.val.2=b.val.2) := by
      rintro ⟨h₁,h₂⟩
      exact hab (Subtype.ext (Prod.ext h₁ h₂))
    have hrev : ¬ (a.val.1=b.val.2 ∧ a.val.2=b.val.1) := by
      rintro ⟨h₁,h₂⟩
      have ha := a.property
      rw [h₁,h₂] at ha
      exact lt_asymm ha b.property
    simp only [if_neg hab]
    split_ifs <;> simp_all

/-- Evaluation of all ambient alternating-form coefficients on the chart. -/
def chartSectionEvaluation (p : PluckerIndex (t+2) n) :
    Matrix (Fin m × StrictPairs (t+2)) (Fin m × StrictPairs n)
      (MvPolynomial (PluckerChartVariable p) K) :=
  fun a b => if a.1=b.1 then
    pluckerChartMatrix p a.2.val.1 b.2.val.1 *
        pluckerChartMatrix p a.2.val.2 b.2.val.2 -
      pluckerChartMatrix p a.2.val.1 b.2.val.2 *
        pluckerChartMatrix p a.2.val.2 b.2.val.1
    else 0

/-- Extending a row-coordinate two-form by its pivot-coordinate two-form. -/
def chartSectionExtension (p : PluckerIndex (t+2) n) :
    Matrix (Fin m × StrictPairs n) (Fin m × StrictPairs (t+2))
      (MvPolynomial (PluckerChartVariable p) K) :=
  fun b a => if b=(a.1,chartPivotPair p a.2) then 1 else 0

lemma chartSectionEvaluation_pivot (p : PluckerIndex (t+2) n)
    (a b : Fin m × StrictPairs (t+2)) :
    chartSectionEvaluation (K:=K) p a (b.1,chartPivotPair p b.2) =
      if a=b then 1 else 0 := by
  classical
  simp only [chartSectionEvaluation,chartPivotPair,chart_pivot_twoByTwo]
  by_cases h₁ : a.1=b.1 <;> by_cases h₂ : a.2=b.2 <;>
    simp_all [Prod.ext_iff]

/-- The evaluation map is split surjective over the entire affine chart. -/
theorem chartSectionEvaluation_rightInverse (p : PluckerIndex (t+2) n) :
    chartSectionEvaluation (K:=K) (m:=m) p * chartSectionExtension (K:=K) (m:=m) p = 1 := by
  classical
  ext a b
  simp only [Matrix.mul_apply,chartSectionExtension,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,
    chartSectionEvaluation_pivot,Matrix.one_apply]

/-- The corresponding linear section is exactly the original row-isotropy
equation, with every ambient coefficient retained as a free parameter. -/
theorem chartSectionEvaluation_sum (p : PluckerIndex (t+2) n)
    (a : (Fin m × StrictPairs n) → K) (j : Fin m × StrictPairs (t+2)) :
    (∑ i, a i • chartSectionEvaluation (K:=K) p j i) =
      alternatingRowPair (fun b => a (j.1,b)) (pluckerChartMatrix p)
        j.2.val.1 j.2.val.2 := by
  classical
  simp only [Fintype.sum_prod_type,chartSectionEvaluation,smul_ite,smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true,alternatingRowPair]

end PaperVerification.AlternatingForms
