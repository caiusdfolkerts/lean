module

public import PaperVerification.AlternatingFormsBidegreeScaling
public import PaperVerification.AlternatingFormsOddExteriorBasis
public import PaperVerification.AlternatingFormsBasisDegree
public import PaperVerification.GradedComponentBasis
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The original bidegree pieces of the odd exterior quotient

A piece is defined as the image of the span of the original exterior words
having the specified numbers of `a`- and `b`-letters.  It is not defined by
counting good indices.  The diagonal action constructed from the original
vector space proves that the good basis restricts to these actual images:
scaling the `a`-variables by two separates their degrees over any
characteristic-zero field.  Thus their dimensions really are the weighted
good-word counts that enter Proposition 5.1.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.Bidegree

section EigenCoordinates

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Coordinates of an endomorphism diagonal in a genuine basis. -/
theorem repr_diagonal (B : Module.Basis I K V) (T : Module.End K V) (eigenvalue : I → K)
    (hT : ∀ i,T (B i)=eigenvalue i • B i) (x : V) (i : I) :
    B.repr (T x) i=eigenvalue i * B.repr x i := by
  have he : (B.coord i).comp T=eigenvalue i • B.coord i := by
    apply B.ext
    intro j
    by_cases hji : j=i
    · subst j
      simp only [LinearMap.comp_apply,hT,map_smul,Module.Basis.coord_apply,
        Module.Basis.repr_self,Finsupp.single_eq_same,LinearMap.smul_apply,
        smul_eq_mul,mul_one]
    · simp only [LinearMap.comp_apply,hT,map_smul,Module.Basis.coord_apply,
        Module.Basis.repr_self,Finsupp.single_eq_of_ne (Ne.symm hji),
        LinearMap.smul_apply,smul_zero]
  simpa only [LinearMap.comp_apply,LinearMap.smul_apply,
    Module.Basis.coord_apply,smul_eq_mul] using LinearMap.congr_fun he x

/-- An actual eigenvector has zero coefficients at all different eigenvalues. -/
theorem eigenvector_coordinate_zero (B : Module.Basis I K V)
    (T : Module.End K V) (eigenvalue : I → K) (hT : ∀ i,T (B i)=eigenvalue i • B i)
    (c : K) (x : V) (hx : T x=c • x) (i : I) (hi : eigenvalue i≠c) :
    B.repr x i=0 := by
  have he := congrArg (fun y : V => B.repr y i) hx
  rw [repr_diagonal B T eigenvalue hT,map_smul,Finsupp.smul_apply,smul_eq_mul] at he
  by_contra hne
  exact hi (mul_right_cancel₀ hne he)

end EigenCoordinates

section ActualPieces

variable {K : Type*} [Field K] [CharZero K]

/-- The original exterior word span with `p` odd-position letters and total
degree `s`, before taking the generated-ideal quotient. -/
def exteriorASubdegree (k s p : ℕ) :
    Submodule K (⋀[K]^s (Fin (2*k+1) → K)) :=
  Submodule.span K {x | ∃ I : PluckerIndex s (2*k+1),
    aWordDegree I.val=p ∧ x=exteriorPluckerBasis s (2*k+1) I}

/-- The image of that original span in the genuine quotient by both quadrics. -/
def quotientASubdegree (k s p : ℕ) :
    Submodule K (OddExteriorQuotientDegree (K := K) k s) :=
  (exteriorASubdegree k s p).map
    (exteriorDegreeRelations
      (oddPathFirstQuadratic (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (Pi.basisFun K (Fin (2*k+1)))) s).mkQ

/-- The paper's original `(p,q)` piece: total exterior degree `p+q`, with
exactly `p` of the `a`-variables. -/
def actualBigradedPiece (k p q : ℕ) :
    Submodule K (OddExteriorQuotientDegree (K := K) k (p+q)) :=
  quotientASubdegree k (p+q) p

def goodADegree {k s : ℕ} (I : GoodOddIndex k s) : ℕ :=
  aWordDegree I.val.val

theorem quotientScaling_goodBasis (k s : ℕ) (c : K) (I : GoodOddIndex k s) :
    quotientScaling k s c (oddExteriorBasis k s I)=
      c ^ goodADegree I • oddExteriorBasis k s I := by
  rw [oddExteriorBasis_apply,exteriorPluckerBasis_apply]
  exact quotientScaling_word k s c I.val.val

/-- The equality between a piece defined from the original quotient and
the subspace supported on good words of that degree.  The diagonal action
proves the nontrivial direction; the good-word count is not a hypothesis. -/
theorem quotientASubdegree_eq_basisPiece (k s p : ℕ) :
    quotientASubdegree (K := K) k s p=
      BasisDegree.piece (oddExteriorBasis k s) goodADegree p := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro x ⟨I,hI,rfl⟩
    change Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I)∈
      BasisDegree.piece (oddExteriorBasis k s) goodADegree p
    rw [BasisDegree.mem_piece]
    intro J hJ
    apply eigenvector_coordinate_zero (oddExteriorBasis k s)
      (quotientScaling k s (2 : K)) (fun J => (2 : K)^goodADegree J)
      (quotientScaling_goodBasis k s 2) ((2 : K)^p)
      (Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I)) ?_ J
      (fun he => hJ (two_pow_injective he))
    rw [exteriorPluckerBasis_apply,quotientScaling_word,hI]
  · rw [BasisDegree.piece_eq_span]
    apply Submodule.span_le.mpr
    rintro x ⟨I,hI,rfl⟩
    refine ⟨exteriorPluckerBasis s (2*k+1) I.val,?_,?_⟩
    · exact Submodule.subset_span ⟨I.val,hI,rfl⟩
    · exact (oddExteriorBasis_apply k s I).symm

/-- A genuine direct-sum grading of every actual total-degree quotient,
whose pieces are exactly the images of the original bidegree word spans. -/
def quotientAGrading (k s : ℕ) :
    TauCeti.InternalGrading K (OddExteriorQuotientDegree (K := K) k s) ℕ :=
  BasisDegree.grading (oddExteriorBasis k s) goodADegree

theorem quotientAGrading_piece (k s p : ℕ) :
    (quotientAGrading (K := K) k s).piece p=quotientASubdegree k s p :=
  (quotientASubdegree_eq_basisPiece k s p).symm

/-- Exact all-degree dimension formula for the genuine bidegree image. -/
theorem finrank_quotientASubdegree (k s p : ℕ) :
    Module.finrank K (quotientASubdegree (K := K) k s p)=
      Nat.card {I : GoodOddIndex k s // goodADegree I=p} := by
  rw [←quotientAGrading_piece]
  exact PaperVerification.GradedComponentBasis.finrank_piece
    (quotientAGrading k s) (oddExteriorBasis k s) goodADegree
    (BasisDegree.basis_mem_piece (oddExteriorBasis k s) goodADegree) p

/-- This is the coefficient interpretation used by Proposition5.1; the
remaining weighted path bijection and transfer recurrence are separate proofs. -/
theorem finrank_actualBigradedPiece (k p q : ℕ) :
    Module.finrank K (actualBigradedPiece (K := K) k p q)=
      Nat.card {I : GoodOddIndex k (p+q) // goodADegree I=p} :=
  finrank_quotientASubdegree k (p+q) p

end ActualPieces
end PaperVerification.AlternatingForms.Bidegree
