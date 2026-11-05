module

public import PaperVerification.AlternatingFormsOddBarDegree
public import PaperVerification.AlternatingFormsBarCoefficientFormula

/-!
# The highest terms of the actual odd bar differential

Normal adjacent products concatenate with coefficient one. Every term of
every nonnormal adjacent product strictly lowers the word order, even
inside a longer tensor. This proves the complete basis-level comparison
with the recursive normal-merge operator, including cancellation among
different adjacent multiplication positions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators MonomialOrder

namespace PaperVerification.AlternatingForms

open Hibi BarCompositions BarCoefficientFormula PBWWords
open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "C" => OddPositiveStandardIndex (K := K) k t hs
local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "J" => IntervalIndex α β
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs

def oddNormalProduct (a b : C) : C →₀ K :=
  if h : ((e a).val++(e b).val).IsChain (·≤·) then
    Finsupp.single ((e).symm (appendPositiveNormalWord k t hs (e a) (e b) h)) 1
  else 0

def oddNormalDifferentialBasis (L : List C) : List C →₀ K :=
  basisDifferential (oddNormalProduct k t hs) L

def oddStrictWordPiece (m : MonomialOrder J) (W : List J) :
    Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L |
    Before (oddGoodOrder k t hs m) (·≤·) (flattenBarWord e L) W ∧
      (flattenBarWord e L).length=W.length}

def oddSameWordPiece (W : List J) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | flattenBarWord e L=W}

theorem oddStrictWordPiece_prefix (m : MonomialOrder J) (W : List J)
    (a : C) (z : List C →₀ K) (hz : z∈oddStrictWordPiece k t hs m W) :
    prepend a z∈oddStrictWordPiece k t hs m ((e a).val++W) := by
  rw [oddStrictWordPiece,Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    constructor
    · change Before (oddGoodOrder k t hs m) (· ≤ ·)
        ((e a).val++flattenBarWord e L) ((e a).val++W)
      simpa only [List.append_nil] using
        before_context_of_before (oddGoodOrder k t hs m) (·≤·)
          (e a).val [] (flattenBarWord e L) W hL.1
    · change ((e a).val++flattenBarWord e L).length=((e a).val++W).length
      simp only [List.length_append,hL.2]
  | zero => simpa only [map_zero] using
      (oddStrictWordPiece k t hs m ((e a).val++W)).zero_mem
  | add z w hz hw ihz ihw => simpa only [map_add] using
      (oddStrictWordPiece k t hs m ((e a).val++W)).add_mem ihz ihw
  | smul c z hz ih => simpa only [map_smul] using
      (oddStrictWordPiece k t hs m ((e a).val++W)).smul_mem c ih

theorem oddSameWordPiece_prefix (W : List J) (a : C)
    (z : List C →₀ K) (hz : z∈oddSameWordPiece k t hs W) :
    prepend a z∈oddSameWordPiece k t hs ((e a).val++W) := by
  rw [oddSameWordPiece,Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    change (e a).val++flattenBarWord e L=(e a).val++W
    rw [hL]
  | zero => simpa only [map_zero] using
      (oddSameWordPiece k t hs ((e a).val++W)).zero_mem
  | add z w hz hw ihz ihw => simpa only [map_add] using
      (oddSameWordPiece k t hs ((e a).val++W)).add_mem ihz ihw
  | smul c z hz ih => simpa only [map_smul] using
      (oddSameWordPiece k t hs ((e a).val++W)).smul_mem c ih

theorem oddNormalAdjacent_mem_sameWord (a b : C) (L : List C) :
    appendTail L (oddNormalProduct k t hs a b)∈
      oddSameWordPiece k t hs (flattenBarWord e (a::b::L)) := by
  unfold oddNormalProduct
  split_ifs with h
  · rw [appendTail_single]
    apply Finsupp.single_mem_supported K 1
    change (e ((e).symm (appendPositiveNormalWord k t hs (e a) (e b) h))).val++
      flattenBarWord e L=(e a).val++((e b).val++flattenBarWord e L)
    rw [Equiv.apply_symm_apply]
    exact List.append_assoc _ _ _
  · rw [map_zero]
    exact Submodule.zero_mem _

theorem oddNormalDifferentialBasis_mem_sameWord (L : List C) :
    oddNormalDifferentialBasis k t hs L∈oddSameWordPiece k t hs (flattenBarWord e L) := by
  induction L with
  | nil => exact Submodule.zero_mem _
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [oddNormalDifferentialBasis,basisDifferential,adjacent,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons b L =>
      change appendTail L (oddNormalProduct k t hs a b)-
        prepend a (oddNormalDifferentialBasis k t hs (b::L))∈_
      exact Submodule.sub_mem _ (oddNormalAdjacent_mem_sameWord k t hs a b L)
        (oddSameWordPiece_prefix k t hs _ a _ ih)

theorem oddAdjacent_difference_mem_strict (m : MonomialOrder J)
    (a b : C) (L : List C) :
    appendTail L (productCoefficients B a b)-appendTail L (oddNormalProduct k t hs a b)∈
      oddStrictWordPiece k t hs m (flattenBarWord e (a::b::L)) := by
  by_cases h : ((e a).val++(e b).val).IsChain (·≤·)
  · rw [odd_productCoefficients_of_normal k t hs a b h,oddNormalProduct,dif_pos h,sub_self]
    exact Submodule.zero_mem _
  · rw [oddNormalProduct,dif_neg h,map_zero,sub_zero,
      appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Submodule.sum_mem
    intro c hc
    apply Submodule.smul_mem
    apply Finsupp.single_mem_supported K 1
    have hn := Finsupp.mem_support_iff.mp hc
    constructor
    · have hm := odd_productCoefficient_exponent_le k t hs m a b c hn
      have hb := before_context (oddGoodOrder k t hs m) (·≤·) []
        (flattenBarWord e L) ((e a).val++(e b).val) (e c).val
        (by simpa only [exponent_append,oddPositiveWord_exponent] using hm)
        (fun hp ↦ h (List.isChain_iff_pairwise.mpr hp))
        (List.isChain_iff_pairwise.mp (e c).property.2)
      change Before (oddGoodOrder k t hs m) (· ≤ ·)
        ((e c).val++flattenBarWord e L)
        ((e a).val++((e b).val++flattenBarWord e L))
      simpa only [List.nil_append,List.append_assoc] using hb
    · have hd := odd_productCoefficient_degree k t hs a b c hn
      change ((e c).val++flattenBarWord e L).length=
        ((e a).val++((e b).val++flattenBarWord e L)).length
      simp only [List.length_append,oddPositiveWord_degree]
      omega

/-- The full difference, including every merge position, has strictly
smaller literal word weight. The induction handles cancellations by
submodule closure, so this is stronger than a list of possible terms. -/
theorem oddDifferentialBasis_difference_mem_strict (m : MonomialOrder J) (L : List C) :
    differentialBasis B L-oddNormalDifferentialBasis k t hs L∈
      oddStrictWordPiece k t hs m (flattenBarWord e L) := by
  induction L with
  | nil => simpa only [differentialBasis,oddNormalDifferentialBasis,basisDifferential,sub_self]
      using (oddStrictWordPiece k t hs m (flattenBarWord e [])).zero_mem
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [differentialBasis,oddNormalDifferentialBasis,basisDifferential,adjacent,
        merge_single,mergeBasis,smul_zero,map_zero,sub_zero,sub_self]
      exact Submodule.zero_mem _
    | cons b L =>
      have h₁ := oddAdjacent_difference_mem_strict k t hs m a b L
      have h₂ := oddStrictWordPiece_prefix k t hs m (flattenBarWord e (b::L)) a _ ih
      have he : differentialBasis B (a::b::L)-oddNormalDifferentialBasis k t hs (a::b::L)=
          (appendTail L (productCoefficients B a b)-appendTail L (oddNormalProduct k t hs a b))-
            prepend a (differentialBasis B (b::L)-oddNormalDifferentialBasis k t hs (b::L)) := by
        simp only [differentialBasis,oddNormalDifferentialBasis,basisDifferential,adjacent,
          merge_single,mergeBasis,one_smul,map_sub]
        abel
      rw [he]
      exact Submodule.sub_mem _ h₁ h₂

theorem oddDifferentialBasis_difference_weight_lt (m : MonomialOrder J)
    (L T : List C)
    (h : (differentialBasis B L-oddNormalDifferentialBasis k t hs L) T≠0) :
    weight (oddGoodOrder k t hs m) (·≤·) (flattenBarWord e L).length (flattenBarWord e T)<
      weight (oddGoodOrder k t hs m) (·≤·) (flattenBarWord e L).length (flattenBarWord e L) := by
  have hm := oddDifferentialBasis_difference_mem_strict k t hs m L
  have hp := hm (Finsupp.mem_support_iff.mpr h)
  exact weight_lt (oddGoodOrder k t hs m) (·≤·) _ _ _ hp.2 hp.1

end PaperVerification.AlternatingForms
