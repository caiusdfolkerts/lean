module

public import PaperVerification.AlternatingFormsOddBarLeadingComparison
public import PaperVerification.AlternatingFormsBarFiberCoordinates

/-! # Exactness of the actual odd normalized bar complex. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open scoped Classical MonomialOrder

namespace PaperVerification.AlternatingForms

open Hibi BarCompositions BarCoefficientFormula PBWWords FilteredComparison
open PaperVerification.ReducedBarBasis PaperVerification.Fermion.BasisFiltered
open CategoryTheory CategoryTheory.Limits

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "C" => OddPositiveStandardIndex (K := K) k t hs
local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "J" => IntervalIndex α β
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs

theorem oddNormalProduct_eq_normalProduct :
    oddNormalProduct (K := K) k t hs=normalProduct e := rfl

theorem oddLeadingDegreeDifferential_tensorBasis_val (r N : ℕ)
    (L : InternalDegreeIndex e (r+1) N) :
    (leadingDegreeDifferential e r N (tensorBasis (K := K) e (r+1) N L)).val=
      -oddNormalDifferentialBasis k t hs L.val := by
  rw [leadingDegreeDifferential_tensorBasis_val,←oddNormalProduct_eq_normalProduct]
  rfl

theorem oddBigradedDifferential_tensorBasis_val (r N : ℕ)
    (L : InternalDegreeIndex e (r+1) N) :
    (oddBigradedDifferential k t hs r N (tensorBasis (K := K) e (r+1) N L)).val=
      -differentialBasis B L.val := by
  rw [oddBigradedDifferential_val,tensorBasis_val,differential_single,one_smul]

def oddBarWordWeight (m : MonomialOrder J) (r N : ℕ)
    (L : InternalDegreeIndex e r N) : ℕ :=
  weight (oddGoodOrder k t hs m) (·≤·) N (flattenBarWord e L.val)

theorem oddLeadingDegreeDifferential_homogeneous (m : MonomialOrder J)
    (r N : ℕ) (L : InternalDegreeIndex e (r+1) N) :
    Homogeneous (R := K) (M := ↥(internalDegreePiece (K := K) e r N)) (tensorBasis (K := K) e r N) (oddBarWordWeight k t hs m r N)
      (oddBarWordWeight k t hs m (r+1) N L)
      (leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) := by
  intro T hT
  rw [tensorBasis_repr_apply,oddLeadingDegreeDifferential_tensorBasis_val,
    Finsupp.neg_apply,neg_ne_zero] at hT
  have hsame := oddNormalDifferentialBasis_mem_sameWord k t hs L.val
    (Finsupp.mem_support_iff.mpr hT)
  change weight (oddGoodOrder k t hs m) (·≤·) N (flattenBarWord e T.val)=
    weight (oddGoodOrder k t hs m) (·≤·) N (flattenBarWord e L.val)
  rw [hsame]

theorem oddBigradedDifferential_hasTop_basis (m : MonomialOrder J)
    (r N : ℕ) (L : InternalDegreeIndex e (r+1) N) :
    HasTop (R := K) (M := ↥(internalDegreePiece (K := K) e r N)) (tensorBasis (K := K) e r N) (oddBarWordWeight k t hs m r N)
      (oddBarWordWeight k t hs m (r+1) N L)
      (oddBigradedDifferential k t hs r N (tensorBasis e (r+1) N L))
      (leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) := by
  apply hasTop_of_strict_difference (K := K)
    (M₀ := ↥(internalDegreePiece (K := K) e r N))
    (tensorBasis (K := K) e r N) (oddBarWordWeight k t hs m r N)
  · exact oddLeadingDegreeDifferential_homogeneous k t hs m r N L
  · intro T hT
    have he : (tensorBasis (K := K) e r N).repr
        (oddBigradedDifferential k t hs r N (tensorBasis e (r+1) N L)-
          leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) T=
        -((differentialBasis B L.val-oddNormalDifferentialBasis k t hs L.val) T.val) := by
      rw [tensorBasis_repr_sub,oddBigradedDifferential_tensorBasis_val,
        oddLeadingDegreeDifferential_tensorBasis_val]
      simp only [Finsupp.neg_apply,Finsupp.sub_apply]
      abel
    rw [he,neg_ne_zero] at hT
    have hw := oddDifferentialBasis_difference_weight_lt k t hs m L.val T.val hT
    simpa only [oddBarWordWeight,L.property.2] using hw

/-- This is exactness of the genuine internally graded tensor differential
coming from the actual free resolution of the augmentation residue. -/
theorem oddBigradedDifferential_range_eq_ker (m : MonomialOrder J)
    (r N : ℕ) (hr : r+1≠N) :
    (oddBigradedDifferential (K := K) k t hs (r+1) N).range=
      (oddBigradedDifferential k t hs r N).ker := by
  exact range_eq_ker_of_basis (K := K)
    (M₀ := ↥(internalDegreePiece (K := K) e r N))
    (M₁ := ↥(internalDegreePiece (K := K) e (r+1) N))
    (M₂ := ↥(internalDegreePiece (K := K) e (r+2) N))
    (tensorBasis (K := K) e r N) (oddBarWordWeight k t hs m r N)
    (tensorBasis (K := K) e (r+1) N) (oddBarWordWeight k t hs m (r+1) N)
    (tensorBasis (K := K) e (r+2) N) (oddBarWordWeight k t hs m (r+2) N)
    (oddBigradedDifferential k t hs r N) (oddBigradedDifferential k t hs (r+1) N)
    (leadingDegreeDifferential e r N) (leadingDegreeDifferential e (r+1) N)
    (oddBigradedDifferential_squared k t hs r N)
    (oddBigradedDifferential_hasTop_basis k t hs m r N)
    (oddBigradedDifferential_hasTop_basis k t hs m (r+1) N)
    (leadingDegree_range_eq_ker e r N hr)

/-- Every actual off-diagonal normalized bar cycle is the differential of
an actual tensor of the next length and the same internal degree. -/
theorem odd_normalized_bar_off_diagonal (m : MonomialOrder J)
    (r N : ℕ) (hr : r+1≠N) (z : List C →₀ K)
    (hz : z∈internalDegreePiece (K := K) e (r+1) N)
    (hd : differential B z=0) :
    ∃ y∈internalDegreePiece (K := K) e (r+2) N,-differential B y=z := by
  have hc : (⟨z,hz⟩ : internalDegreePiece (K := K) e (r+1) N)∈
      (oddBigradedDifferential k t hs r N).ker := by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change -differential B z=0
    rw [hd,neg_zero]
  rw [←oddBigradedDifferential_range_eq_ker k t hs m r N hr] at hc
  obtain ⟨y,hy⟩ := hc
  exact ⟨y.val,y.property,congrArg Subtype.val hy⟩

theorem oddInternalDegreeComplex_exactAt_succ (m : MonomialOrder J)
    (r N : ℕ) (hr : r+1≠N) :
    (oddInternalDegreeComplex (K := K) k t hs N).ExactAt (r+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (r+2) (r+1) r (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change (((oddInternalDegreeComplex (K := K) k t hs N).d (r+2) (r+1)).hom).range=
    (((oddInternalDegreeComplex (K := K) k t hs N).d (r+1) r).hom).ker
  rw [oddInternalDegreeComplex_d,oddInternalDegreeComplex_d]
  exact oddBigradedDifferential_range_eq_ker k t hs m r N hr

theorem oddInternalDegree_zero_eq_zero (N : ℕ) (hN : N≠0)
    (z : internalDegreePiece (K := K) e 0 N) : z=0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro L
  change z.val L=0
  apply (Finsupp.mem_supported' K z.val).mp z.property
  rintro ⟨hL,hW⟩
  have hnil : L=[] := List.length_eq_zero_iff.mp hL
  subst L
  exact hN hW.symm

/-- The homology here is Mathlib's actual homology of the actual
internal-degree subcomplex of the normalized Tor complex. -/
theorem odd_internal_bar_homology_off_diagonal (m : MonomialOrder J)
    (r N : ℕ) (hr : r≠N) :
    IsZero ((oddInternalDegreeComplex (K := K) k t hs N).homology r) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  cases r with
  | zero =>
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero (ModuleCat.of K (internalDegreePiece (K := K) e 0 N))
    letI : Subsingleton (internalDegreePiece (K := K) e 0 N) :=
      ⟨fun x y ↦ (oddInternalDegree_zero_eq_zero k t hs N (Ne.symm hr) x).trans
        (oddInternalDegree_zero_eq_zero k t hs N (Ne.symm hr) y).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  | succ r => exact oddInternalDegreeComplex_exactAt_succ k t hs m r N hr

/-- The auxiliary monomial order is constructed, not supplied as a
hypothesis in the resulting diagonal homology statement. -/
theorem odd_actual_bar_homology_diagonal (r N : ℕ) (hr : r≠N) :
    IsZero ((oddInternalDegreeComplex (K := K) k t hs N).homology r) :=
  odd_internal_bar_homology_off_diagonal k t hs
    (PaperVerification.WeightedMonomialOrder.finiteBaseOrder J) r N hr

end PaperVerification.AlternatingForms
