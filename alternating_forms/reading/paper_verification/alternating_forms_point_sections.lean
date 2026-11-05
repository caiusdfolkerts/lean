module

public import PaperVerification.AlternatingFormsProjectiveSections
public import PaperVerification.SingleGeneratorProjectiveSections

/-!
# Complete Plucker sections at the singleton interval endpoint

At s=k+1 the lower and upper good-index bounds coincide.  Every length-d
standard chain is therefore the constant chain, and the actual original
degree-d quotient has its basis vector equal to the d-th power of the
surviving coordinate.  The single standard chart covers the actual Proj.
This gives the genuine complete-section comparison in the boundary case
where a two-element regular sequence is unavailable.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms

open MvPolynomial Hibi AlgebraicGeometry

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "A" => MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q
local notation "φ" => oddGoodMap (K := K) k t hs
local notation "x" => φ (X (oddLeastGoodIndex k t hs))

/-- The constant lower-endpoint chain exists in every degree, including zero. -/
def oddLowerConstantChain (d : ℕ) : BandChain α β d :=
  ⟨fun _ ↦ α,fun _ ↦ oddIntervalLower_strictMono k (t+2) hs,
    (fun _ a ↦ ⟨le_rfl,oddIntervalLower_le_upper k (t+2) hs a⟩),monotone_const⟩

theorem odd_endpoint_bounds_eq (he : t+2=k+1) : α=β := by
  funext a
  apply Fin.ext
  dsimp only [oddIntervalLower,oddIntervalUpper]
  omega

theorem odd_endpoint_index_eq (he : t+2=k+1) (I : IntervalIndex α β) :
    I=oddLeastGoodIndex k t hs := by
  apply Subtype.ext
  apply Subtype.ext
  funext a
  apply le_antisymm
  · change I.val.val a ≤ α a
    simpa only [←odd_endpoint_bounds_eq k t hs he] using (I.property a).2
  · exact (I.property a).1

theorem odd_endpoint_chain_eq (he : t+2=k+1) (d : ℕ) (C : BandChain α β d) :
    C=oddLowerConstantChain k t hs d := by
  apply Subtype.ext
  funext j a
  apply le_antisymm
  · change C.val j a ≤ α a
    simpa only [←odd_endpoint_bounds_eq k t hs he] using (C.property.2.1 j a).2
  · exact (C.property.2.1 j a).1

theorem odd_lowerConstantChain_product (d : ℕ) :
    Ideal.Quotient.mk Q (chainPluckerProduct α β (oddLowerConstantChain k t hs d))=x^d := by
  change Ideal.Quotient.mk Q
    (∏ _ : Fin d, X (oddLeastGoodIndex k t hs).val) = x^d
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,map_pow,oddGoodMap_X]

/-- Every actual homogeneous element is a degree-zero multiple of the
power of the original surviving coordinate. -/
theorem odd_endpoint_piece (he : t+2=k+1) (d : ℕ) (r : A)
    (hr : r∈oddProjectiveGrading k t d) :
    ∃ c : A,c∈oddProjectiveGrading k t 0 ∧ r=c*x^d := by
  classical
  let B := oddPluckerDegreeBasis (K := K) k t hs d
  let C₀ := oddLowerConstantChain k t hs d
  have hr' : r∈oddPluckerDegree k t d := by
    simpa only [oddProjectiveGrading,HomogeneousQuotientProjective.grading_eq_piece,
      oddPluckerDegree] using hr
  let z : oddPluckerDegree (K := K) k t d := ⟨r,hr'⟩
  have hsum : (B.repr z C₀) • B C₀=z := by
    have h := B.sum_repr z
    rw [Finset.sum_eq_single C₀] at h
    · exact h
    · intro C hC hne
      exact (hne (odd_endpoint_chain_eq k t hs he d C)).elim
    · intro hC
      exact (hC (Finset.mem_univ C₀)).elim
  refine ⟨algebraMap K A (B.repr z C₀),?_,?_⟩
  · rw [oddProjectiveGrading,HomogeneousQuotientProjective.grading_eq_piece,
      homogeneousQuotient_degree_zero]
    exact Submodule.mem_one.mpr ⟨B.repr z C₀,rfl⟩
  · have hz := congrArg (fun v : oddPluckerDegree (K := K) k t d ↦ (v : A)) hsum
    have hz' : (B.repr z C₀) • (x ^ d : A)=r := by
      simpa only [Submodule.coe_smul,B,oddPluckerDegreeBasis_apply,C₀,
        odd_lowerConstantChain_product,z] using hz
    exact hz'.symm.trans (Algebra.smul_def (R := K) (B.repr z C₀) (x ^ d))

theorem odd_endpoint_basicOpen (he : t+2=k+1) :
    Proj.basicOpen (oddProjectiveGrading k t) x=⊤ := by
  have hcover := odd_goodCoordinate_basicOpen_cover (K := K) k t hs
  calc
    Proj.basicOpen (oddProjectiveGrading k t) x=
        ⨆ I : IntervalIndex α β,Proj.basicOpen (oddProjectiveGrading k t) (φ (X I)) := by
      apply le_antisymm
      · exact le_iSup (fun I : IntervalIndex α β ↦
          Proj.basicOpen (oddProjectiveGrading k t) (φ (X I))) _
      · apply iSup_le
        intro I
        rw [odd_endpoint_index_eq k t hs he I]
    _ = ⊤ := hcover

include hs in
/-- The singleton interval has complete original Plucker sections in every
nonnegative degree, with no missing boundary case. -/
theorem odd_endpoint_bijective_toTwistingSheaf_top (he : t+2=k+1) (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
      (rfl : (d : ℤ)=d) ⊤) :=
  SingleGeneratorProjectiveSections.bijective_toTwistingSheaf_top
    (oddProjectiveGrading k t) x (odd_goodCoordinate_degree_one k t hs _)
    (odd_goodCoordinate_isRegular k t hs _) (odd_endpoint_basicOpen k t hs he)
    (odd_endpoint_piece k t hs he) d

include hs in
/-- All sizes 2 <= s <= k+1 now have the actual complete-section comparison;
the two mutually exclusive endpoint cases are joined without weakening the range. -/
theorem odd_allSizes_bijective_toTwistingSheaf_top (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
      (rfl : (d : ℤ)=d) ⊤) := by
  rcases hs.lt_or_eq with hlt | he
  · exact odd_bijective_toTwistingSheaf_top k t hs hlt d
  · exact odd_endpoint_bijective_toTwistingSheaf_top k t hs he d

end PaperVerification.AlternatingForms
