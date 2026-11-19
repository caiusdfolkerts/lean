module

public import paper_verification.literal010
public import paper_verification.literal003
public import paper_verification.literal000
public import Mathlib.Data.Finset.Card
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import paper_verification.literal009
public import paper_verification.literal004
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
public import paper_verification.literal006
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import paper_verification.literal001
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Fintype.Powerset
import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option Elab.async false

section TAF_LiteralSource_0535
/- Original module: PaperVerification.AlternatingFormsOddBasisCharacteristic -/


/-!
# The full good basis below twice the characteristic

Integral standard monomials give the interval basis over every field.
Lifting through the proved exact initial ideal gives the original Plücker
basis.  Its actual degree-one component is then identified with the genuine
exterior generated-ideal quotient.  No Hilbert-function assumption is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms
namespace DegreeRestricted

open MvPolynomial
open PaperVerification.WeightedInitialFiber
open scoped BigOperators

variable {K : Type*} [Field K]

def oddInitialStandardBasis (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) :
    Module.Basis (OddStandardIndex k t hs) K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        initialIdeal (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
          (pluckerVertexWeight (oddNatVertexWeight k))) :=
  (intervalStandardBasis (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)
    (oddIntervalLower_strictMono k (t+2) hs).monotone
    (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega : 0<t+2)).map
      (Ideal.quotientEquivAlgOfEq K (odd_isotropic_initial_eq_interval_of_degree_factorials k t hs hfac).symm).toLinearEquiv

@[simp] theorem oddInitialStandardBasis_apply (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2))
    (C : OddStandardIndex k t hs) :
    oddInitialStandardBasis (K := K) k t hs hfac C=
      Ideal.Quotient.mk _ (oddStandardRepresentative k t hs C) := by
  unfold oddInitialStandardBasis
  erw [Module.Basis.map_apply]
  simp only [intervalStandardBasis]
  erw [Module.Basis.mk_apply]
  simp only [intervalAllStandardProduct,intervalStandardProduct,
    AlgEquiv.coe_toLinearEquiv,Ideal.quotientEquivAlgOfEq_mk,oddStandardRepresentative]

/-- Every actual good-coordinate standard product, in every polynomial
degree, is retained as a basis vector of the original isotropic ring. -/
def oddPluckerStandardBasis (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) :
    Module.Basis (OddStandardIndex k t hs) K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) :=
  liftedInitialBasis _ (pluckerVertexWeight (oddNatVertexWeight k))
    (oddStandardRepresentative k t hs) (oddStandardWeight k t hs)
    (oddStandardRepresentative_weighted k t hs) (oddInitialStandardBasis k t hs hfac)
    (oddInitialStandardBasis_apply k t hs hfac)

@[simp] theorem oddPluckerStandardBasis_apply (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2))
    (C : OddStandardIndex k t hs) :
    oddPluckerStandardBasis (K := K) k t hs hfac C=
      Ideal.Quotient.mk _ (oddStandardRepresentative k t hs C) :=
  liftedInitialBasis_apply _ _ _ _ _ _ _ C

theorem oddPluckerStandardBasis_mem_degree (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2))
    (C : OddStandardIndex k t hs) :
    oddPluckerStandardBasis (K := K) k t hs hfac C∈oddPluckerDegree k t C.1 := by
  rw [oddPluckerStandardBasis_apply]
  exact ⟨oddStandardRepresentative k t hs C,
    oddStandardRepresentative_homogeneous k t hs C,rfl⟩

def oddPluckerDegreeBasis (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) (r : ℕ) :
    Module.Basis
      (BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r)
      K (oddPluckerDegree (K := K) k t r) :=
  (HomogeneousIdealPieces.componentBasis _ (isotropicPluckerIdeal_isHomogeneous _)
    (oddPluckerStandardBasis k t hs hfac) (fun C => C.1)
    (oddPluckerStandardBasis_mem_degree k t hs hfac) r).reindex
      (oddStandardDegreeEquiv k t hs r)

@[simp] theorem oddPluckerDegreeBasis_apply (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) (r : ℕ)
    (C : BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r) :
    (oddPluckerDegreeBasis (K := K) k t hs hfac r C :
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))=
      Ideal.Quotient.mk _ (chainPluckerProduct _ _ C) := by
  unfold oddPluckerDegreeBasis
  erw [Module.Basis.reindex_apply,HomogeneousIdealPieces.componentBasis_coe]
  change oddPluckerStandardBasis (K := K) k t hs hfac ⟨r,C⟩ = _
  exact oddPluckerStandardBasis_apply (K := K) k t hs hfac ⟨r,C⟩

theorem oddPluckerDegree_finrank (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) (r : ℕ) :
    Module.finrank K (oddPluckerDegree (K := K) k t r)=
      Fintype.card (BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) r) :=
  Module.finrank_eq_card_basis (oddPluckerDegreeBasis k t hs hfac r)

def oddExteriorMiddleBasis (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2)) :
    Module.Basis (GoodOddIndex k (t+2)) K (OddExteriorQuotientDegree (K := K) k (t+2)) :=
  ((oddPluckerDegreeBasis k t hs hfac 1).map (oddExteriorLinearPieceEquiv k t).symm).reindex
    (goodOddBandEquiv k t hs).symm

@[simp] theorem oddExteriorMiddleBasis_apply (k t : ℕ) (hs : t+2≤k+1) (hfac : DegreeFactorials K (t+2))
    (I : GoodOddIndex k (t+2)) :
    oddExteriorMiddleBasis (K := K) k t hs hfac I=
      Submodule.Quotient.mk (exteriorPluckerBasis (t+2) (2*k+1) I.val) := by
  apply (oddExteriorLinearPieceEquiv k t).injective
  apply Subtype.ext
  simp only [oddExteriorMiddleBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    Module.Basis.map_apply,LinearEquiv.apply_symm_apply,oddPluckerDegreeBasis_apply,
    oddExteriorLinearPieceEquiv_mk,exteriorPluckerCoordinates_basis,
    goodOddBandEquiv,chainPluckerProduct,Fin.prod_univ_one]
  rfl

/-- Every degree in the permitted range, including zero and one. -/
def oddExteriorBasis (k : ℕ) : (s : ℕ) → (hs : s≤k+1) →
    DegreeFactorials K s →
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s)
  | 0, _, _ => oddExteriorLowBasis k 0 (by decide)
  | 1, _, _ => oddExteriorLowBasis k 1 (by decide)
  | t+2, hs, hfac => oddExteriorMiddleBasis k t hs hfac

@[simp] theorem oddExteriorBasis_apply (k s : ℕ) (hs : s≤k+1)
    (hfac : DegreeFactorials K s) (I : GoodOddIndex k s) :
    oddExteriorBasis (K := K) k s hs hfac I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  cases s with
  | zero => exact oddExteriorLowBasis_apply k 0 (by decide) I
  | succ s =>
      cases s with
      | zero => exact oddExteriorLowBasis_apply k 1 (by decide) I
      | succ t => exact oddExteriorMiddleBasis_apply k t hs hfac I

end DegreeRestricted

/-- The basis assertion of Theorem 7.1 with every original good monomial
identified explicitly.  This proof works over every field of the indicated
prime characteristic, so in particular over the algebraically closed fields
used in the paper. -/
theorem paper_theorem_7_1_exterior_basis
    {K : Type*} [Field K] (p k s : ℕ) [Fact p.Prime] [CharP K p]
    (hs : s≤k+1) (hp : s<2*p) :
    ∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin (2*k+1)) (I.val.val i))) := by
  refine ⟨DegreeRestricted.oddExteriorBasis k s hs
    (degreeFactorials_of_lt_twice_characteristic p s hp),?_⟩
  intro I
  rw [DegreeRestricted.oddExteriorBasis_apply,exteriorPluckerBasis_apply]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0535

section TAF_LiteralSource_0536
/- Original module: PaperVerification.AlternatingFormsHighDivision -/


/-!
# Complementary-degree division by a matching quadratic

A high-degree exterior monomial has more full matching pairs than empty
ones. Keep all empty pairs and exactly one more full pair. On this odd
subuniverse the explicit Boolean inverse applies; every omitted pair meets
the remaining word and therefore annihilates it. This proves division in
prime characteristic using only the factorial of one plus the number of
empty pairs, without imposing a condition on the ambient cardinality.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Fintype ι] [DecidableEq ι]

/-- Extract any specified subcollection of a selection as a list
permutation, retaining every multiplicity. -/
theorem selection_split_off_permutation (A C : Finset ι) (hCA : C ⊆ A) :
    A.toList.Perm ((A \ C).toList ++ C.toList) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [List.count_append, A.nodup_toList.count, (A \ C).nodup_toList.count,
    C.nodup_toList.count]
  by_cases hiC : i ∈ C
  · simp [hiC, hCA hiC]
  · by_cases hiA : i ∈ A <;> simp [hiC, hiA]

/-- Extracting the same pair labels from both halves produces actual
adjacent exterior pairs after a permutation. -/
theorem selected_pair_word_permutation (u v : ι → M) (A B C : Finset ι)
    (hCA : C ⊆ A) (hCB : C ⊆ B) :
    (A.toList.map u ++ B.toList.map v).Perm
      (((A \ C).toList.map u ++ (B \ C).toList.map v) ++
        C.toList.flatMap (fun i => [u i, v i])) := by
  have h₁ := ((selection_split_off_permutation A C hCA).map u).append
    ((selection_split_off_permutation B C hCB).map v)
  simp only [List.map_append] at h₁
  have h₂ :
      (((A \ C).toList.map u ++ C.toList.map u) ++
        ((B \ C).toList.map v ++ C.toList.map v)).Perm
      (((A \ C).toList.map u ++ (B \ C).toList.map v) ++
        (C.toList.map u ++ C.toList.map v)) := by
    simpa only [List.append_assoc] using
      (((List.perm_append_comm (l₁ := C.toList.map u)
        (l₂ := (B \ C).toList.map v)).append_left
          ((A \ C).toList.map u)).append_right (C.toList.map v))
  have h₃ : (C.toList.map u ++ C.toList.map v).Perm
      (C.toList.flatMap fun i => [u i, v i]) := by
    simpa only [← List.map_eq_flatMap, List.cons_append, List.nil_append] using
      List.flatMap_append_perm C.toList (fun i => [u i]) (fun i => [v i])
  exact h₁.trans (h₂.trans (h₃.append_left _))

/-- Division of every high-degree selection, with exactly the factorial
needed by its empty matching pairs. The vectors need not be independent. -/
theorem matching_high_selection_division_of_factorial
    (u v : ι → M) (A B : Finset ι)
    (hhigh : Fintype.card ι + 1 ≤ A.card + B.card)
    (hfac : ((((A ∪ B)ᶜ).card + 1).factorial : K) ≠ 0) :
    ∃ η : ⋀[K]^(A.card + B.card - 2) M,
      (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
          (η : ExteriorAlgebra K M) =
        ((A.toList.map u ++ B.toList.map v).map (ExteriorAlgebra.ι K)).prod := by
  classical
  let E : Finset ι := (A ∪ B)ᶜ
  let r := E.card
  have hbalance : (A ∪ B).card + E.card = Fintype.card ι := by
    simpa only [E, Finset.card_univ] using Finset.card_add_card_compl (A ∪ B)
  have hfull : r + 1 ≤ (A ∩ B).card := by
    have hc := Finset.card_union_add_card_inter A B
    dsimp [r]
    omega
  obtain ⟨C, hC, hCc⟩ := Finset.exists_subset_card_eq hfull
  have hCA : C ⊆ A := hC.trans Finset.inter_subset_left
  have hCB : C ⊆ B := hC.trans Finset.inter_subset_right
  have hEC : Disjoint E C := by
    apply Finset.disjoint_left.mpr
    intro i hiE hiC
    exact (Finset.mem_compl.mp hiE) (Finset.mem_union_left _ (hCA hiC))
  let H := E ∪ C
  let S := Hᶜ
  let L := (A \ C).toList.map u ++ (B \ C).toList.map v
  have hH : H.card = 2 * r + 1 := by
    dsimp [H]
    rw [Finset.card_union_of_disjoint hEC, hCc]
    dsimp [r]
    omega
  have hfree : Fintype.card {i : ι // i ∉ S} = 2 * r + 1 := by
    let e : {i : ι // i ∉ S} ≃ H :=
      Equiv.subtypeEquivRight (fun i => by simp only [S, Finset.mem_compl, not_not])
    rw [Fintype.card_congr e, Fintype.card_coe, hH]
  have hCP : ∀ i ∈ C, i ∉ S := by
    intro i hi
    simp only [S, Finset.mem_compl, not_not]
    exact Finset.mem_union_right E hi
  let P : FixedSubsets {i : ι // i ∉ S} (r + 1) :=
    ⟨C.subtype (fun i => i ∉ S), by
      rw [Finset.card_subtype, Finset.filter_eq_self.mpr hCP, hCc]⟩
  have hL : ∀ i ∈ S, u i ∈ L ∨ v i ∈ L := by
    intro i hi
    have hiH : i ∉ H := Finset.mem_compl.mp hi
    have hiE : i ∉ E := fun he => hiH (Finset.mem_union_left _ he)
    have hiC : i ∉ C := fun hc => hiH (Finset.mem_union_right _ hc)
    have hiAB : i ∈ A ∪ B := by
      simpa only [E, Finset.mem_compl, not_not] using hiE
    rcases Finset.mem_union.mp hiAB with hiA | hiB
    · exact Or.inl (List.mem_append_left _ (List.mem_map.mpr
        ⟨i, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hiA, hiC⟩), rfl⟩))
    · exact Or.inr (List.mem_append_right _ (List.mem_map.mpr
        ⟨i, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hiB, hiC⟩), rfl⟩))
  obtain ⟨η, hη⟩ := singleton_state_division_exists_of_factorial
    (K := K) u v S L hL r hfac hfree P
  obtain ⟨ε, hε, heq⟩ := exterior_word_permutation (K := K)
    (selected_pair_word_permutation u v A B C hCA hCB)
  have hlen : L.length + 2 * r = A.card + B.card - 2 := by
    have h₁ := Finset.card_le_card hCA
    have h₂ := Finset.card_le_card hCB
    simp only [L, List.length_append, List.length_map, Finset.length_toList,
      Finset.card_sdiff_of_subset hCA, Finset.card_sdiff_of_subset hCB]
    omega
  refine ⟨⟨ε • (η : ExteriorAlgebra K M), ?_⟩, ?_⟩
  · rw [← hlen]
    exact Submodule.smul_mem _ _ η.property
  · rw [mul_smul_comm, hη]
    have hpair := pairedMonomial_subtype (K := K) hCP u v
    change ε • ((L.map (ExteriorAlgebra.ι K)).prod *
      pairedMonomial _ _ (C.subtype fun i => i ∉ S)) = _
    rw [hpair]
    simpa only [List.map_append, List.prod_append, pair_word_product, L] using heq.symm

/-- The prime-characteristic specialization has no restriction on the
ambient number of pairs: only the number of empty pairs is bounded. -/
theorem matching_high_selection_division_charP
    (u v : ι → M) (A B : Finset ι)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hhigh : Fintype.card ι + 1 ≤ A.card + B.card)
    (hempty : ((A ∪ B)ᶜ).card + 1 < p) :
    ∃ η : ⋀[K]^(A.card + B.card - 2) M,
      (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
          (η : ExteriorAlgebra K M) =
        ((A.toList.map u ++ B.toList.map v).map (ExteriorAlgebra.ι K)).prod :=
  matching_high_selection_division_of_factorial u v A B hhigh
    (factorial_cast_ne_zero_of_lt_char p _ hempty)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0536

section TAF_LiteralSource_0537
/- Original module: PaperVerification.AlternatingFormsOddCharacteristicCutoff -/


/-!
# Full odd Hilbert series below the characteristic threshold

A word above degree `k+1` has at least `k+1` letters among the first `k`
matching pairs.  If it has `e` empty pairs, then `2*(e+1) ≤ k+1`.
The proved high-selection inverse therefore divides that word by the
first quadratic using only the factorials already required in degree
`k+1`.  This proves all higher degrees vanish, with no characteristic-zero
Lefschetz theorem and no bound on the degree being killed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {k s : ℕ}

/-- The suffix after all matching pairs contains at most the one unpaired
last vertex.  This is a fact about the literal exterior positions. -/
theorem tuplePrefixSuffix_full_card_le_one
    (I : Fin s → Fin (2*k+1)) : (tuplePrefixSuffix I k).card≤1 := by
  have hsub : tuplePrefixSuffix I k ⊆ {Fin.last (2*k)} := by
    intro j hj
    have hj' := (mem_tuplePrefixSuffix I k j).mp hj
    apply Finset.mem_singleton.mpr
    apply Fin.ext
    have hjlt := j.isLt
    change j.val=2*k
    omega
  simpa only [Finset.card_singleton] using Finset.card_le_card hsub

/-- The exact denominator bound for a high selection in `k` pairs. -/
theorem matching_high_empty_pair_bound (A B : Finset (Fin k))
    (hhigh : k+1≤A.card+B.card) : 2*(((A ∪ B)ᶜ).card+1)≤k+1 := by
  have hbalance : (A ∪ B).card+((A ∪ B)ᶜ).card=k := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_add_card_compl (A ∪ B)
  have ha := Finset.card_le_card (Finset.subset_union_left : A ⊆ A ∪ B)
  have hb := Finset.card_le_card (Finset.subset_union_right : B ⊆ A ∪ B)
  omega

/-- Every high word is an actual multiple of the first canonical form.
Only the factorials up to half the middle degree are required. -/
theorem odd_long_word_division_of_degree_factorials
    (hfac : DegreeFactorials K (k+1))
    (I : PluckerIndex s (2*k+1)) (hs : k+1<s) :
    ∃ a : ExteriorAlgebra K (Fin (2*k+1) → K),
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*a =
          indexExteriorWord (List.ofFn I.val) := by
  classical
  let A := tuplePrefixLeft I.val I.property k
  let B := tuplePrefixRight I.val I.property k
  let L := (tuplePrefixSuffix I.val k).toList
  have hlen := tuplePrefixWord_length I.val I.property (le_refl k)
  have hcount : A.card+B.card+(tuplePrefixSuffix I.val k).card=s := by
    simpa only [tuplePrefixWord, List.length_append, List.length_map,
      Finset.length_toList, A, B] using hlen
  have hhigh : k+1≤A.card+B.card := by
    have htail := tuplePrefixSuffix_full_card_le_one I.val
    omega
  have hdenom : ((((A ∪ B)ᶜ).card+1).factorial : K)≠0 :=
    hfac _ (matching_high_empty_pair_bound A B hhigh)
  let u : Fin k → (Fin (2*k+1) → K) :=
    fun i => Pi.basisFun K (Fin (2*k+1)) (oddPrefixLeft (le_refl k) i)
  let v : Fin k → (Fin (2*k+1) → K) :=
    fun i => Pi.basisFun K (Fin (2*k+1)) (oddPrefixRight (le_refl k) i)
  obtain ⟨η,hη⟩ := matching_high_selection_division_of_factorial (K := K)
    u v A B (by simpa only [Fintype.card_fin] using hhigh) hdenom
  have hform : (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) :
      ExteriorAlgebra K (Fin (2*k+1) → K)) =
      ∑ i : Fin k, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i) := by
    simp only [oddPathFirstQuadratic, matchingQuadratic_coe, u, v,
      oddPrefixLeft, oddPrefixRight, oddPathFirstLeft, oddPathMiddle,
      prefixPairEmbedding]
    rfl
  have hselected :
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*(η : ExteriorAlgebra K (Fin (2*k+1) → K)) =
      indexExteriorWord (A.toList.map (oddPrefixLeft (le_refl k)) ++
        B.toList.map (oddPrefixRight (le_refl k))) := by
    rw [hform]
    simpa only [indexExteriorWord, List.map_append, List.map_map,
      Function.comp_def, u, v] using hη
  have hword :
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) :
        ExteriorAlgebra K (Fin (2*k+1) → K)) *
          ((η : ExteriorAlgebra K (Fin (2*k+1) → K))*indexExteriorWord L) =
        indexExteriorWord (tuplePrefixWord I.val I.property (le_refl k)) := by
    rw [← mul_assoc, hselected, ← indexExteriorWord_append]
    rfl
  obtain ⟨ε,hε,he⟩ := exterior_word_permutation (K := K)
    ((tuplePrefixWord_perm I.val I.property (le_refl k)).map
      (Pi.basisFun K (Fin (2*k+1))))
  have he' : indexExteriorWord (K := K)
      (tuplePrefixWord I.val I.property (le_refl k)) =
      ε • indexExteriorWord (List.ofFn I.val) := by
    simpa only [indexExteriorWord, List.map_map, Function.comp_def] using he
  refine ⟨ε⁻¹ • ((η : ExteriorAlgebra K (Fin (2*k+1) → K))*indexExteriorWord L), ?_⟩
  rw [mul_smul_comm, hword, he', smul_smul, inv_mul_cancel₀ hε, one_smul]

/-- The actual homogeneous generated-ideal relation space is the whole
exterior power in every degree above the odd middle. -/
theorem odd_exteriorDegreeRelations_eq_top_of_degree_factorials
    (hfac : DegreeFactorials K (k+1))
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s=⊤ := by
  apply eq_top_iff.mpr
  rw [← (exteriorPluckerBasis (K := K) s (2*k+1)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨I,rfl⟩
  change ((exteriorPluckerBasis (K := K) s (2*k+1) I) :
    ExteriorAlgebra K (Fin (2*k+1) → K))∈exteriorRelationIdeal _ g
  obtain ⟨a,ha⟩ := odd_long_word_division_of_degree_factorials hfac I hs
  apply Ideal.mem_span_pair.mpr
  refine ⟨a,0,?_⟩
  rw [zero_mul,add_zero,
    ← (twoForm_commute (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) a).eq,ha]
  rw [exteriorPluckerBasis_apply]
  simp only [indexExteriorWord, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_apply, List.map_ofFn, List.map_map, Function.comp_def]

theorem odd_exteriorQuotientDegree_subsingleton_of_degree_factorials
    (hfac : DegreeFactorials K (k+1))
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    Subsingleton (ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s) := by
  change Subsingleton ((⋀[K]^s (Fin (2*k+1) → K))⧸exteriorDegreeRelations _ g s)
  rw [odd_exteriorDegreeRelations_eq_top_of_degree_factorials hfac g hs]
  infer_instance

theorem odd_exteriorQuotientDegree_finrank_eq_zero_of_degree_factorials
    (hfac : DegreeFactorials K (k+1))
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    Module.finrank K (ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s)=0 := by
  letI := odd_exteriorQuotientDegree_subsingleton_of_degree_factorials hfac g hs
  exact Module.finrank_zero_of_subsingleton

def oddExteriorBasisOfMiddleFactorials (k s : ℕ) (hfac : DegreeFactorials K (k+1)) :
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s) := by
  by_cases hs : s≤k+1
  · exact DegreeRestricted.oddExteriorBasis k s hs
      (fun r hr => hfac r (hr.trans hs))
  · letI := goodOddIndex_isEmpty k s (by omega)
    letI := odd_exteriorQuotientDegree_subsingleton_of_degree_factorials hfac
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) (by omega : k+1<s)
    exact Module.Basis.empty _

theorem oddExteriorBasisOfMiddleFactorials_apply (k s : ℕ)
    (hfac : DegreeFactorials K (k+1)) (I : GoodOddIndex k s) :
    oddExteriorBasisOfMiddleFactorials k s hfac I =
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  by_cases hs : s≤k+1
  · simp only [oddExteriorBasisOfMiddleFactorials, dif_pos hs]
    exact DegreeRestricted.oddExteriorBasis_apply k s hs _ I
  · exact (goodOddIndex_isEmpty k s (by omega)).false I |>.elim

theorem oddExterior_finrank_of_middle_factorials (k s : ℕ)
    (hfac : DegreeFactorials K (k+1)) :
    Module.finrank K (OddExteriorQuotientDegree (K := K) k s) =
      StripWalks.paperWalkCount (2*k+1) s := by
  rw [Module.finrank_eq_card_basis (oddExteriorBasisOfMiddleFactorials k s hfac),
    card_goodOddIndex_eq_paperWalkCount]

/-- The full Hilbert-series clause of Theorem 7.1, in every natural degree
and every prime characteristic, with the exact printed dimension range. -/
theorem paper_theorem_7_1_full_hilbert (p k : ℕ)
    [Fact p.Prime] [CharP K p] (hk : 2*k+1≤4*p-3) (s : ℕ) :
    Module.finrank K (OddExteriorQuotientDegree (K := K) k s) =
      StripWalks.paperWalkCount (2*k+1) s := by
  have hp := (Fact.out : p.Prime).two_le
  exact oddExterior_finrank_of_middle_factorials k s
    (degreeFactorials_of_lt_twice_characteristic p (k+1) (by omega))

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0537

section TAF_LiteralSource_0538
/- Original module: PaperVerification.FiniteFiberSpanning -/


/-!
# Spanning a finite module from all residue fibers

A proper submodule of a finite module lies in a maximal submodule.  The
quotient is simple, and its annihilator is a maximal ideal of the scalar
ring.  Therefore a family that spans modulo every maximal ideal already
spans the original module.  No flatness or absence of torsion is assumed.
-/

@[expose] public section
set_option autoImplicit false

namespace PaperVerification

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem span_restrictScalars_of_surjective
    {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    (h : Function.Surjective (algebraMap R S)) {ι : Type*} (v : ι → M) :
    Submodule.span R (Set.range v) = (Submodule.span S (Set.range v)).restrictScalars R := by
  apply le_antisymm (Submodule.span_le_restrictScalars R S _)
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
      obtain ⟨r,rfl⟩ := h c
      rw [IsScalarTower.algebraMap_smul]
      exact Submodule.smul_mem _ r ih

theorem submodule_eq_top_of_residue_sup_eq_top [Module.Finite R M]
    (N : Submodule R M)
    (h : ∀ m : Ideal R, m.IsMaximal → N ⊔ m • (⊤ : Submodule R M)=⊤) : N=⊤ := by
  rcases eq_top_or_exists_le_coatom N with hN | ⟨P,hP,hNP⟩
  · exact hN
  · letI : IsSimpleModule R (M⧸P) := isSimpleModule_iff_isCoatom.mpr hP
    let m : Ideal R := Module.annihilator R (M⧸P)
    have hm : m.IsMaximal := IsSimpleModule.annihilator_isMaximal
    have hmul : m • (⊤ : Submodule R M)≤P := by
      apply Submodule.smul_le.mpr
      intro r hr x hx
      apply (Submodule.Quotient.mk_eq_zero P).mp
      rw [Submodule.Quotient.mk_smul]
      exact Module.mem_annihilator.mp hr (Submodule.Quotient.mk x)
    have htop : (⊤ : Submodule R M)≤P := by
      rw [← h m hm]
      exact sup_le hNP hmul
    exact (hP.ne_top (top_unique htop)).elim

theorem span_eq_top_of_residue_sup_eq_top [Module.Finite R M]
    {ι : Type*} (v : ι → M)
    (h : ∀ m : Ideal R, m.IsMaximal →
      Submodule.span R (Set.range v) ⊔ m • (⊤ : Submodule R M)=⊤) :
    Submodule.span R (Set.range v)=⊤ :=
  submodule_eq_top_of_residue_sup_eq_top _ h

end PaperVerification
end
end TAF_LiteralSource_0538

section TAF_LiteralSource_0539
/- Original module: PaperVerification.AlternatingFormsOddIntegralBasis -/


/-!
# The actual odd quotient over integral coefficient rings

The good words span over every coefficient ring in which the required
factorial is a unit: this follows from the proved basis in every residue
field and the finite-module maximal-submodule argument.  Over a domain,
their independence follows by mapping to the fraction field.  Both maps
are the actual universal maps of exterior algebras, and the relation
spaces are the actual quadratic-generated ideal pieces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms.IntegralOdd

variable (R : Type*) [CommRing R]

def goodWord (k s : ℕ) (I : GoodOddIndex k s) : quotientDegree R k s :=
  Submodule.Quotient.mk (powerBasis R s (2*k+1) I.val)

theorem firstForm_eq_canonical {K : Type*} [Field K] (k : ℕ) :
    firstForm K k = oddPathFirstQuadratic (Pi.basisFun K (Fin (2*k+1))) := rfl

theorem secondForm_eq_canonical {K : Type*} [Field K] (k : ℕ) :
    secondForm K k = oddPathSecondQuadratic (Pi.basisFun K (Fin (2*k+1))) := rfl

theorem powerBasis_eq_plucker {K : Type*} [Field K] (s n : ℕ) :
    powerBasis K s n = exteriorPluckerBasis (K := K) s n := rfl

theorem goodWord_eq_canonical {K : Type*} [Field K] (k s : ℕ)
    (I : GoodOddIndex k s) :
    goodWord K k s I = Submodule.Quotient.mk
      (exteriorPluckerBasis (K := K) s (2*k+1) I.val) := rfl

variable (S : Type*) [CommRing S] [Algebra R S]

@[simp] theorem quotientMap_goodWord (k s : ℕ) (I : GoodOddIndex k s) :
    quotientMap R S k s (goodWord R k s I) = goodWord S k s I := by
  rw [goodWord, quotientMap_mk, powerMap_basis]
  rfl

variable {S}

/-- The single factorial inverted in the integral statement controls all
the middle-degree inverse coefficients in every field over the ring. -/
theorem degreeFactorials_of_middle_factorial_unit
    {K : Type*} [Field K] [Algebra R K] (k : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) : DegreeFactorials K (k+1) := by
  intro r hr
  have hr' : r≤(k+1)/2 := by omega
  have hd : (r.factorial : R) ∣ (((k+1)/2).factorial : R) := by
    obtain ⟨c,hc⟩ := Nat.factorial_dvd_factorial hr'
    refine ⟨(c : R), ?_⟩
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : R)) hc
  have hu : IsUnit (r.factorial : R) := isUnit_of_dvd_unit hd hunit
  have huK := hu.map (algebraMap R K)
  simpa only [map_natCast] using huK.ne_zero

def fieldGoodBasis {K : Type*} [Field K] (k s : ℕ)
    (hfac : DegreeFactorials K (k+1)) :
    Module.Basis (GoodOddIndex k s) K (quotientDegree K k s) :=
  oddExteriorBasisOfMiddleFactorials k s hfac

@[simp] theorem fieldGoodBasis_apply {K : Type*} [Field K] (k s : ℕ)
    (hfac : DegreeFactorials K (k+1)) (I : GoodOddIndex k s) :
    fieldGoodBasis k s hfac I = goodWord K k s I :=
  oddExteriorBasisOfMiddleFactorials_apply k s hfac I

set_option maxHeartbeats 800000 in
/-- Genuine spanning over the entire ring, including any torsion in the
quotient: all maximal residue fibers are tested. -/
theorem goodWord_span_eq_top (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) :
    Submodule.span R (Set.range (goodWord R k s)) = ⊤ := by
  classical
  apply PaperVerification.span_eq_top_of_residue_sup_eq_top
  intro m hm
  letI : m.IsMaximal := hm
  let K := R⧸m
  letI : Field K := Ideal.Quotient.field m
  let q : quotientDegree R k s →ₗ[R] quotientDegree K k s :=
    quotientMap R K k s
  have hsurj : Function.Surjective (algebraMap R K) := Ideal.Quotient.mk_surjective
  have hfac : DegreeFactorials K (k+1) :=
    degreeFactorials_of_middle_factorial_unit R k hunit
  have he : (fun I => fieldGoodBasis k s hfac I) = goodWord K k s := by
    funext I
    exact fieldGoodBasis_apply k s hfac I
  have hspanK : Submodule.span K (Set.range (goodWord K k s))=⊤ := by
    rw [← he]
    exact (fieldGoodBasis k s hfac).span_eq
  have hspanR : Submodule.span R (Set.range (goodWord K k s))=⊤ := by
    rw [PaperVerification.span_restrictScalars_of_surjective hsurj, hspanK]
    rfl
  have hmap : (Submodule.span R (Set.range (goodWord R k s))).map q=⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    have he : q ∘ goodWord R k s = goodWord K k s := by
      funext I
      exact quotientMap_goodWord R K k s I
    rw [he, hspanR]
  have hq : q.range=⊤ := LinearMap.range_eq_top.mpr
    (quotientMap_surjective R K hsurj k s)
  have hsup := (LinearMap.map_eq_top_iff hq).mp hmap
  simpa only [q, K, quotientMap_quotient_ker] using hsup

/-- Mapping to the fraction field proves independence of the same literal
good words; no assertion about saturation or torsion is used here. -/
theorem goodWord_linearIndependent [IsDomain R] (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) :
    LinearIndependent R (goodWord R k s) := by
  let K := FractionRing R
  have hfac : DegreeFactorials K (k+1) :=
    degreeFactorials_of_middle_factorial_unit R k hunit
  have he : (fun I => fieldGoodBasis k s hfac I) = goodWord K k s := by
    funext I
    exact fieldGoodBasis_apply k s hfac I
  have hK : LinearIndependent K (goodWord K k s) := by
    rw [← he]
    exact (fieldGoodBasis k s hfac).linearIndependent
  have hR : LinearIndependent R (goodWord K k s) :=
    hK.restrict_scalars' R
  have hcomp : LinearIndependent R
      ((quotientMap R K k s) ∘ goodWord R k s) := by
    simpa only [Function.comp_def, quotientMap_goodWord] using hR
  exact LinearIndependent.of_comp (quotientMap R K k s) hcomp

/-- The actual free good-word basis over a domain with the printed
factorial inverted, in every homogeneous degree. -/
def integralGoodBasis [IsDomain R] (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) :
    Module.Basis (GoodOddIndex k s) R (quotientDegree R k s) :=
  Module.Basis.mk (goodWord_linearIndependent R k s hunit)
    (by rw [goodWord_span_eq_top R k s hunit])

@[simp] theorem integralGoodBasis_apply [IsDomain R] (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) (I : GoodOddIndex k s) :
    integralGoodBasis R k s hunit I = goodWord R k s I :=
  Module.Basis.mk_apply _ _ _

end PaperVerification.AlternatingForms.IntegralOdd
end
end
end TAF_LiteralSource_0539

section TAF_LiteralSource_0540
/- Original module: PaperVerification.AlternatingFormsExteriorBaseChange -/


/-!
# Arbitrary base change of the actual odd exterior quotient

Increasing words identify the scalar extension of each exterior power
with the exterior power over the new coefficient ring.  The tensor image
of the actual relation space is exactly the target relation space because
the latter is generated by the images of multiplication by the two forms.
Right exactness of tensor products therefore gives the asserted quotient
isomorphism, without any flatness assumption on the coefficient algebra.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped TensorProduct BigOperators

namespace PaperVerification.AlternatingForms.IntegralOdd

theorem scalarExtensionQuotientEquiv_mk
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (P : Submodule R M) (Q : Submodule S N) (e : (S ⊗[R] M) ≃ₗ[S] N)
    (h : (TensorProduct.AlgebraTensorModule.lTensor S S P.subtype).range.map
      e.toLinearMap=Q) (c : S) (x : M) :
    ((TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S P).trans
      (Submodule.Quotient.equiv _ _ e h)) (c ⊗ₜ[R] Submodule.Quotient.mk x)=
        Submodule.Quotient.mk (e (c ⊗ₜ[R] x)) := by
  rfl

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

def powerBaseChangeEquiv (s n : ℕ) :
    (S ⊗[R] (⋀[R]^s (Fin n → R))) ≃ₗ[S] (⋀[S]^s (Fin n → S)) :=
  ((powerBasis R s n).baseChange S).equiv (powerBasis S s n) (Equiv.refl _)

theorem powerBaseChangeEquiv_toLinearMap (s n : ℕ) :
    (powerBaseChangeEquiv R S s n).toLinearMap =
      (powerMap R S s n).liftBaseChange S := by
  apply ((powerBasis R s n).baseChange S).ext
  intro I
  change powerBaseChangeEquiv R S s n ((powerBasis R s n).baseChange S I) =
    (powerMap R S s n).liftBaseChange S ((powerBasis R s n).baseChange S I)
  unfold powerBaseChangeEquiv
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.baseChange_apply,
    LinearMap.liftBaseChange_tmul, powerMap_basis, one_smul]

@[simp] theorem powerBaseChangeEquiv_tmul {s n : ℕ}
    (c : S) (x : ⋀[R]^s (Fin n → R)) :
    powerBaseChangeEquiv R S s n (c ⊗ₜ[R] x) = c • powerMap R S s n x := by
  change (powerBaseChangeEquiv R S s n).toLinearMap (c ⊗ₜ[R] x)=_
  rw [powerBaseChangeEquiv_toLinearMap, LinearMap.liftBaseChange_tmul]

def scalarRelationSpan (k s : ℕ) : Submodule S (⋀[S]^s (Fin (2*k+1) → S)) :=
  Submodule.span S (Set.range ((powerMap R S s (2*k+1)).comp
    (exteriorDegreeRelations (firstForm R k) (secondForm R k) s).subtype))

theorem powerMap_relation_mem_span {k s : ℕ}
    (x : ⋀[R]^s (Fin (2*k+1) → R))
    (hx : x∈exteriorDegreeRelations (firstForm R k) (secondForm R k) s) :
    powerMap R S s (2*k+1) x∈scalarRelationSpan R S k s :=
  Submodule.subset_span ⟨⟨x,hx⟩,rfl⟩

theorem scalarRelationSpan_eq (k s : ℕ) :
    scalarRelationSpan R S k s =
      exteriorDegreeRelations (firstForm S k) (secondForm S k) s := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨y,rfl⟩
    exact powerMap_relations_mem R S y.val y.property
  · by_cases hs : s<2
    · rw [exteriorDegreeRelations_eq_bot _ _ hs]
      exact bot_le
    · obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hs)
      rw [exteriorDegreeRelations_eq_images]
      apply sup_le
      · rintro _ ⟨y,rfl⟩
        rw [← (powerBasis S q (2*k+1)).sum_repr y, map_sum]
        apply Submodule.sum_mem
        intro I hI
        rw [map_smul]
        apply Submodule.smul_mem
        have hx : exteriorPower.wedge R _ 2 q (firstForm R k)
            (powerBasis R q (2*k+1) I) ∈
            exteriorDegreeRelations (firstForm R k) (secondForm R k) (2+q) := by
          rw [exteriorDegreeRelations_eq_images]
          exact Submodule.mem_sup_left (LinearMap.mem_range_self _ _)
        have hmem := powerMap_relation_mem_span R S _ hx
        simpa only [powerMap_wedge, powerMap_firstForm, powerMap_basis] using hmem
      · rintro _ ⟨y,rfl⟩
        rw [← (powerBasis S q (2*k+1)).sum_repr y, map_sum]
        apply Submodule.sum_mem
        intro I hI
        rw [map_smul]
        apply Submodule.smul_mem
        have hx : exteriorPower.wedge R _ 2 q (secondForm R k)
            (powerBasis R q (2*k+1) I) ∈
            exteriorDegreeRelations (firstForm R k) (secondForm R k) (2+q) := by
          rw [exteriorDegreeRelations_eq_images]
          exact Submodule.mem_sup_right (LinearMap.mem_range_self _ _)
        have hmem := powerMap_relation_mem_span R S _ hx
        simpa only [powerMap_wedge, powerMap_secondForm, powerMap_basis] using hmem

def tensorRelationMap (k s : ℕ) :
    (S ⊗[R] exteriorDegreeRelations (firstForm R k) (secondForm R k) s) →ₗ[S]
      (S ⊗[R] (⋀[R]^s (Fin (2*k+1) → R))) :=
  TensorProduct.AlgebraTensorModule.lTensor S S
    (exteriorDegreeRelations (firstForm R k) (secondForm R k) s).subtype

@[simp] theorem tensorRelationMap_tmul {k s : ℕ} (c : S)
    (x : exteriorDegreeRelations (firstForm R k) (secondForm R k) s) :
    tensorRelationMap R S k s (c ⊗ₜ[R] x) = c ⊗ₜ[R] x.val := rfl

theorem tensorRelationMap_comp (k s : ℕ) :
    (powerBaseChangeEquiv R S s (2*k+1)).toLinearMap.comp (tensorRelationMap R S k s) =
      ((powerMap R S s (2*k+1)).comp
        (exteriorDegreeRelations (firstForm R k) (secondForm R k) s).subtype).liftBaseChange S := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c x
  change powerBaseChangeEquiv R S s (2*k+1) (c ⊗ₜ[R] x.val) =
    c • powerMap R S s (2*k+1) x.val
  exact powerBaseChangeEquiv_tmul R S c x.val

theorem powerBaseChangeEquiv_map_relations (k s : ℕ) :
    (tensorRelationMap R S k s).range.map
        (powerBaseChangeEquiv R S s (2*k+1)).toLinearMap =
      exteriorDegreeRelations (firstForm S k) (secondForm S k) s := by
  rw [← LinearMap.range_comp, tensorRelationMap_comp,
    LinearMap.range_liftBaseChange]
  exact scalarRelationSpan_eq R S k s

/-- Scalar extension commutes with the actual quotient by the two
canonical odd quadrics for every commutative coefficient algebra. -/
def quotientBaseChangeEquiv (k s : ℕ) :
    (S ⊗[R] quotientDegree R k s) ≃ₗ[S] quotientDegree S k s :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S
    (exteriorDegreeRelations (firstForm R k) (secondForm R k) s)).trans
      (Submodule.Quotient.equiv _ _ (powerBaseChangeEquiv R S s (2*k+1))
        (powerBaseChangeEquiv_map_relations R S k s))

set_option maxHeartbeats 800000 in
@[simp] theorem quotientBaseChangeEquiv_tmul_mk {k s : ℕ}
    (c : S) (x : ⋀[R]^s (Fin (2*k+1) → R)) :
    quotientBaseChangeEquiv R S k s (c ⊗ₜ[R] Submodule.Quotient.mk x) =
      c • Submodule.Quotient.mk (powerMap R S s (2*k+1) x) := by
  calc
    quotientBaseChangeEquiv R S k s (c ⊗ₜ[R] Submodule.Quotient.mk x)=
        Submodule.Quotient.mk (powerBaseChangeEquiv R S s (2*k+1) (c ⊗ₜ[R] x)) :=
      scalarExtensionQuotientEquiv_mk
        (exteriorDegreeRelations (firstForm R k) (secondForm R k) s)
        (exteriorDegreeRelations (firstForm S k) (secondForm S k) s)
        (powerBaseChangeEquiv R S s (2*k+1))
        (powerBaseChangeEquiv_map_relations R S k s) c x
    _ = _ := by rw [powerBaseChangeEquiv_tmul,Submodule.Quotient.mk_smul]

end PaperVerification.AlternatingForms.IntegralOdd
end
end
end TAF_LiteralSource_0540

section TAF_LiteralSource_0541
/- Original module: PaperVerification.AlternatingFormsOddIntegralBaseChange -/


/-!
# Integral good bases remain bases after arbitrary base change

The source coefficient ring is a domain with the required factorial
inverted.  The target algebra is entirely arbitrary: it may have torsion,
nilpotents, or zero divisors.  The tensor-quotient equivalence identifies
the base-changed free basis with the same literal good exterior words.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped TensorProduct

namespace PaperVerification.AlternatingForms.IntegralOdd

variable (R S : Type*) [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]

def baseChangedGoodBasis (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) :
    Module.Basis (GoodOddIndex k s) S (quotientDegree S k s) :=
  ((integralGoodBasis R k s hunit).baseChange S).map (quotientBaseChangeEquiv R S k s)

@[simp] theorem baseChangedGoodBasis_apply (k s : ℕ)
    (hunit : IsUnit (((k+1)/2).factorial : R)) (I : GoodOddIndex k s) :
    baseChangedGoodBasis R S k s hunit I = goodWord S k s I := by
  simp only [baseChangedGoodBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply, integralGoodBasis_apply, goodWord,
    quotientBaseChangeEquiv_tmul_mk, powerMap_basis, one_smul]

/-- `ℤ[1/M!]`, with precisely `M=floor((k+1)/2)` as in the paper. -/
abbrev IntegralCoefficientRing (k : ℕ) :=
  Localization.Away (((k+1)/2).factorial : ℤ)

instance integralCoefficientRing_isDomain (k : ℕ) :
    IsDomain (IntegralCoefficientRing k) :=
  IsLocalization.Away.isDomain (S := IntegralCoefficientRing k)
    (x := (((k+1)/2).factorial : ℤ))
    (by exact_mod_cast Nat.factorial_ne_zero ((k+1)/2))

theorem integralCoefficientRing_factorial_unit (k : ℕ) :
    IsUnit (((k+1)/2).factorial : IntegralCoefficientRing k) := by
  simpa only [map_natCast, Int.cast_natCast] using
    (IsLocalization.Away.algebraMap_isUnit
      (S := IntegralCoefficientRing k) (((k+1)/2).factorial : ℤ))

/-- The integral good basis for the exact localization stated after
Theorem 7.1. -/
def paper_integral_good_basis (k s : ℕ) :
    Module.Basis (GoodOddIndex k s) (IntegralCoefficientRing k)
      (quotientDegree (IntegralCoefficientRing k) k s) :=
  integralGoodBasis (IntegralCoefficientRing k) k s
    (integralCoefficientRing_factorial_unit k)

/-- The same literal good-word basis for every algebra over the stated
integral coefficient ring, without any flatness or domain hypothesis. -/
def paper_integral_good_basis_after_base_change (k s : ℕ)
    (T : Type*) [CommRing T] [Algebra (IntegralCoefficientRing k) T] :
    Module.Basis (GoodOddIndex k s) T (quotientDegree T k s) :=
  baseChangedGoodBasis (IntegralCoefficientRing k) T k s
    (integralCoefficientRing_factorial_unit k)

@[simp] theorem paper_integral_good_basis_after_base_change_apply (k s : ℕ)
    (T : Type*) [CommRing T] [Algebra (IntegralCoefficientRing k) T]
    (I : GoodOddIndex k s) :
    paper_integral_good_basis_after_base_change k s T I = goodWord T k s I :=
  baseChangedGoodBasis_apply (IntegralCoefficientRing k) T k s _ I

end PaperVerification.AlternatingForms.IntegralOdd
end
end
end TAF_LiteralSource_0541

section TAF_LiteralSource_0542
/- Original module: PaperVerification.AlternatingFormsOddWeightedIntegral -/


/-!
# Independent invertible coefficients on every edge of the odd path

Successive diagonal factors solve `dᵢ*dᵢ₊₁=cᵢ` in the unit group of an
arbitrary commutative ring.  The resulting actual exterior automorphism
identifies the unweighted and weighted generated ideals.  Rescaling each
transported basis vector by its explicitly computed unit leaves the
literal good exterior words as a basis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace PaperVerification.AlternatingForms.IntegralOdd

variable (R : Type*) [CommRing R] {k s : ℕ}

def firstEdge (i : Fin k) : Fin (2*k) := ⟨2*i.val,by have := i.isLt; omega⟩
def secondEdge (i : Fin k) : Fin (2*k) := ⟨2*i.val+1,by have := i.isLt; omega⟩

def weightedFirstForm (c : Fin (2*k) → Rˣ) : ⋀[R]^2 (Fin (2*k+1) → R) :=
  ∑ i : Fin k, (c (firstEdge i) : R) • exteriorPower.ιMulti R 2
    ![Pi.basisFun R (Fin (2*k+1)) (oddPathFirstLeft i),
      Pi.basisFun R (Fin (2*k+1)) (oddPathMiddle i)]

def weightedSecondForm (c : Fin (2*k) → Rˣ) : ⋀[R]^2 (Fin (2*k+1) → R) :=
  ∑ i : Fin k, (c (secondEdge i) : R) • exteriorPower.ιMulti R 2
    ![Pi.basisFun R (Fin (2*k+1)) (oddPathMiddle i),
      Pi.basisFun R (Fin (2*k+1)) (oddPathSecondRight i)]

abbrev weightedQuotientDegree (c : Fin (2*k) → Rˣ) (s : ℕ) :=
  ExteriorQuotientDegree (weightedFirstForm R c) (weightedSecondForm R c) s

def pathEdgeExtension (c : Fin (2*k) → Rˣ) (j : ℕ) : Rˣ :=
  if h : j<2*k then c ⟨j,h⟩ else 1

def pathVertexUnitNat (c : Fin (2*k) → Rˣ) : ℕ → Rˣ
  | 0 => 1
  | j+1 => pathEdgeExtension R c j * (pathVertexUnitNat c j)⁻¹

def pathVertexUnits (c : Fin (2*k) → Rˣ) (j : Fin (2*k+1)) : Rˣ :=
  pathVertexUnitNat R c j.val

theorem pathVertexUnits_edge (c : Fin (2*k) → Rˣ) (j : Fin (2*k)) :
    pathVertexUnits R c j.castSucc * pathVertexUnits R c j.succ = c j := by
  simp only [pathVertexUnits, Fin.val_castSucc, Fin.val_succ, pathVertexUnitNat,
    pathEdgeExtension, dif_pos j.isLt]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem pathVertexUnits_first (c : Fin (2*k) → Rˣ) (i : Fin k) :
    pathVertexUnits R c (oddPathFirstLeft i) *
      pathVertexUnits R c (oddPathMiddle i) = c (firstEdge i) := by
  exact pathVertexUnits_edge R c (firstEdge i)

theorem pathVertexUnits_second (c : Fin (2*k) → Rˣ) (i : Fin k) :
    pathVertexUnits R c (oddPathMiddle i) *
      pathVertexUnits R c (oddPathSecondRight i) = c (secondEdge i) := by
  exact pathVertexUnits_edge R c (secondEdge i)

def pathDiagonalEquiv (c : Fin (2*k) → Rˣ) :
    (Fin (2*k+1) → R) ≃ₗ[R] (Fin (2*k+1) → R) :=
  (Pi.basisFun R (Fin (2*k+1))).equiv
    ((Pi.basisFun R (Fin (2*k+1))).unitsSMul (pathVertexUnits R c)) (Equiv.refl _)

@[simp] theorem pathDiagonalEquiv_basis (c : Fin (2*k) → Rˣ)
    (i : Fin (2*k+1)) :
    pathDiagonalEquiv R c (Pi.basisFun R (Fin (2*k+1)) i) =
      pathVertexUnits R c i • Pi.basisFun R (Fin (2*k+1)) i := by
  rw [pathDiagonalEquiv, Module.Basis.equiv_apply]
  exact Module.Basis.unitsSMul_apply i

def pathWordUnit (c : Fin (2*k) → Rˣ) (I : Fin s → Fin (2*k+1)) : Rˣ :=
  ∏ i, pathVertexUnits R c (I i)

theorem pathDiagonalEquiv_word (c : Fin (2*k) → Rˣ)
    (I : Fin s → Fin (2*k+1)) :
    exteriorPower.map s (pathDiagonalEquiv R c).toLinearMap
        (exteriorPower.ιMulti R s (fun i => Pi.basisFun R (Fin (2*k+1)) (I i))) =
      pathWordUnit R c I •
        exteriorPower.ιMulti R s (fun i => Pi.basisFun R (Fin (2*k+1)) (I i)) := by
  rw [exteriorPower.map_apply_ιMulti]
  simpa only [Function.comp_def, LinearEquiv.coe_coe, pathDiagonalEquiv_basis,
    Units.smul_def, pathWordUnit, Units.coe_prod] using
    (exteriorPower.ιMulti R s).map_smul_univ
      (fun i => (pathVertexUnits R c (I i) : R))
      (fun i => Pi.basisFun R (Fin (2*k+1)) (I i))

theorem pathDiagonalEquiv_pair (c : Fin (2*k) → Rˣ)
    (u v : Fin (2*k+1)) :
    exteriorPower.map 2 (pathDiagonalEquiv R c).toLinearMap
      (exteriorPower.ιMulti R 2 ![Pi.basisFun R (Fin (2*k+1)) u,
        Pi.basisFun R (Fin (2*k+1)) v]) =
      ((pathVertexUnits R c u * pathVertexUnits R c v : Rˣ) : R) •
        exteriorPower.ιMulti R 2 ![Pi.basisFun R (Fin (2*k+1)) u,
          Pi.basisFun R (Fin (2*k+1)) v] := by
  have h := pathDiagonalEquiv_word R c ![u,v]
  have he : (fun i : Fin 2 => Pi.basisFun R (Fin (2*k+1)) (![u,v] i)) =
      ![Pi.basisFun R (Fin (2*k+1)) u, Pi.basisFun R (Fin (2*k+1)) v] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    pathWordUnit, Units.smul_def, Function.comp_def] using h

theorem pathDiagonalEquiv_firstForm (c : Fin (2*k) → Rˣ) :
    exteriorPower.map 2 (pathDiagonalEquiv R c).toLinearMap (firstForm R k) =
      weightedFirstForm R c := by
  simp only [firstForm, weightedFirstForm, map_sum, pathDiagonalEquiv_pair,
    pathVertexUnits_first]

theorem pathDiagonalEquiv_secondForm (c : Fin (2*k) → Rˣ) :
    exteriorPower.map 2 (pathDiagonalEquiv R c).toLinearMap (secondForm R k) =
      weightedSecondForm R c := by
  simp only [secondForm, weightedSecondForm, map_sum, pathDiagonalEquiv_pair,
    pathVertexUnits_second]

def weightedQuotientEquiv (c : Fin (2*k) → Rˣ) (s : ℕ) :
    quotientDegree R k s ≃ₗ[R] weightedQuotientDegree R c s :=
  exteriorQuotientDegreePencilEquiv (pathDiagonalEquiv R c)
    (firstForm R k) (secondForm R k)
    (weightedFirstForm R c) (weightedSecondForm R c)
    (by rw [pathDiagonalEquiv_firstForm, pathDiagonalEquiv_secondForm]) s

def weightedGoodWord (c : Fin (2*k) → Rˣ) (s : ℕ) (I : GoodOddIndex k s) :
    weightedQuotientDegree R c s :=
  Submodule.Quotient.mk (powerBasis R s (2*k+1) I.val)

theorem weightedQuotientEquiv_goodWord (c : Fin (2*k) → Rˣ)
    (I : GoodOddIndex k s) :
    weightedQuotientEquiv R c s (goodWord R k s I) =
      pathWordUnit R c I.val.val • weightedGoodWord R c s I := by
  rw [weightedQuotientEquiv, goodWord, exteriorQuotientDegreePencilEquiv_mk,
    powerBasis_apply, pathDiagonalEquiv_word]
  simp only [weightedGoodWord, powerBasis_apply, Units.smul_def,
    Submodule.Quotient.mk_smul]

def weightedBasisOfGoodBasis (c : Fin (2*k) → Rˣ) (s : ℕ)
    (b : Module.Basis (GoodOddIndex k s) R (quotientDegree R k s)) :
    Module.Basis (GoodOddIndex k s) R (weightedQuotientDegree R c s) :=
  (b.map (weightedQuotientEquiv R c s)).unitsSMul
    (fun I => (pathWordUnit R c I.val.val)⁻¹)

theorem weightedBasisOfGoodBasis_apply (c : Fin (2*k) → Rˣ) (s : ℕ)
    (b : Module.Basis (GoodOddIndex k s) R (quotientDegree R k s))
    (hb : ∀ I, b I=goodWord R k s I) (I : GoodOddIndex k s) :
    weightedBasisOfGoodBasis R c s b I = weightedGoodWord R c s I := by
  rw [weightedBasisOfGoodBasis, Module.Basis.unitsSMul_apply, Module.Basis.map_apply,
    hb, weightedQuotientEquiv_goodWord, inv_smul_smul]

/-- The exact multivariate Laurent coefficient ring in the paper: the
group algebra of the free abelian exponent group over `ℤ[1/M!]`. -/
def IntegralLaurentRing (k : ℕ) :=
  AddMonoidAlgebra (IntegralCoefficientRing k) (Fin (2*k) →₀ ℤ)

instance integralLaurentRing_commRing (k : ℕ) : CommRing (IntegralLaurentRing k) :=
  inferInstanceAs (CommRing (AddMonoidAlgebra (IntegralCoefficientRing k) (Fin (2*k) →₀ ℤ)))

instance integralLaurentRing_algebra (k : ℕ) :
    Algebra (IntegralCoefficientRing k) (IntegralLaurentRing k) := by
  unfold IntegralLaurentRing
  infer_instance

def integralLaurentEdge (k : ℕ) (i : Fin (2*k)) : (IntegralLaurentRing k)ˣ where
  val := AddMonoidAlgebra.single (Finsupp.single i 1) 1
  inv := AddMonoidAlgebra.single (-Finsupp.single i 1) 1
  val_inv := by
    change AddMonoidAlgebra.single (Finsupp.single i 1) (1 : IntegralCoefficientRing k) *
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 =
        (1 : AddMonoidAlgebra (IntegralCoefficientRing k) (Fin (2*k) →₀ ℤ))
    simp only [AddMonoidAlgebra.single_mul_single,add_neg_cancel,
      one_mul,←AddMonoidAlgebra.one_def]
  inv_val := by
    change AddMonoidAlgebra.single (-Finsupp.single i 1) (1 : IntegralCoefficientRing k) *
      AddMonoidAlgebra.single (Finsupp.single i 1) 1 =
        (1 : AddMonoidAlgebra (IntegralCoefficientRing k) (Fin (2*k) →₀ ℤ))
    simp only [AddMonoidAlgebra.single_mul_single,neg_add_cancel,
      one_mul,←AddMonoidAlgebra.one_def]

set_option maxHeartbeats 800000 in
/-- Every degree of the literal quotient with all independent Laurent
edge coefficients has the printed good monomials as a free basis. -/
def paper_integral_laurent_basis (k s : ℕ) :
    Module.Basis (GoodOddIndex k s) (IntegralLaurentRing k)
      (weightedQuotientDegree (IntegralLaurentRing k) (integralLaurentEdge k) s) :=
  weightedBasisOfGoodBasis (IntegralLaurentRing k) (integralLaurentEdge k) s
    (paper_integral_good_basis_after_base_change k s (IntegralLaurentRing k))

@[simp] theorem paper_integral_laurent_basis_apply (k s : ℕ)
    (I : GoodOddIndex k s) :
    paper_integral_laurent_basis k s I =
      weightedGoodWord (IntegralLaurentRing k) (integralLaurentEdge k) s I :=
  weightedBasisOfGoodBasis_apply _ _ _ _
    (paper_integral_good_basis_after_base_change_apply k s _) I

/-- Actual free good-word bases after every base change from the full
Laurent coefficient ring.  The target may be nonreduced or have torsion. -/
def paper_integral_laurent_basis_after_base_change (k s : ℕ)
    (T : Type*) [CommRing T] [Algebra (IntegralCoefficientRing k) T]
    [Algebra (IntegralLaurentRing k) T]
    [IsScalarTower (IntegralCoefficientRing k) (IntegralLaurentRing k) T] :
    Module.Basis (GoodOddIndex k s) T
      (weightedQuotientDegree T
        (fun i => Units.map (algebraMap (IntegralLaurentRing k) T).toMonoidHom
          (integralLaurentEdge k i)) s) :=
  weightedBasisOfGoodBasis T _ s
    (paper_integral_good_basis_after_base_change k s T)

@[simp] theorem paper_integral_laurent_basis_after_base_change_apply (k s : ℕ)
    (T : Type*) [CommRing T] [Algebra (IntegralCoefficientRing k) T]
    [Algebra (IntegralLaurentRing k) T]
    [IsScalarTower (IntegralCoefficientRing k) (IntegralLaurentRing k) T]
    (I : GoodOddIndex k s) :
    paper_integral_laurent_basis_after_base_change k s T I =
      weightedGoodWord T
        (fun i => Units.map (algebraMap (IntegralLaurentRing k) T).toMonoidHom
          (integralLaurentEdge k i)) s I :=
  weightedBasisOfGoodBasis_apply _ _ _ _
    (paper_integral_good_basis_after_base_change_apply k s T) I

end PaperVerification.AlternatingForms.IntegralOdd
end
end
end TAF_LiteralSource_0542

section TAF_LiteralSource_0543
/- Original module: PaperVerification.AlternatingFormsOddIntegralPrincipal -/


/-!
# The integral statement following Theorem 7.1

This endpoint is a free basis of the full, literal exterior-algebra ideal
quotient over the precise Laurent coefficient ring in the paper.  It also
constructs the same literal good-word basis after every algebra base
change.  The proof includes all degrees and uses the actual homogeneous
decomposition to identify their direct sum with the full quotient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms.IntegralOdd

abbrev FullGoodOddIndex (k : ℕ) := Σ s : ℕ, GoodOddIndex k s

abbrev IntegralLaurentQuotient (k : ℕ) :=
  ExteriorAlgebra (IntegralLaurentRing k) (Fin (2*k+1) → IntegralLaurentRing k) ⧸
    exteriorRelationIdeal
      (weightedFirstForm (IntegralLaurentRing k) (integralLaurentEdge k))
      (weightedSecondForm (IntegralLaurentRing k) (integralLaurentEdge k))

/-- The full integral weighted-coefficient assertion printed immediately
after Theorem 7.1, with no omitted high-degree component. -/
def paper_theorem_7_1_integral_full_basis (k : ℕ) :
    Module.Basis (FullGoodOddIndex k) (IntegralLaurentRing k) (IntegralLaurentQuotient k) :=
  exteriorFullBasisOfDegreeBases _ _ (paper_integral_laurent_basis k)

@[simp] theorem paper_theorem_7_1_integral_full_basis_apply
    (k s : ℕ) (I : GoodOddIndex k s) :
    paper_theorem_7_1_integral_full_basis k ⟨s,I⟩ =
      Ideal.Quotient.mk (exteriorRelationIdeal
        (weightedFirstForm (IntegralLaurentRing k) (integralLaurentEdge k))
        (weightedSecondForm (IntegralLaurentRing k) (integralLaurentEdge k)))
        (exteriorPower.ιMulti (IntegralLaurentRing k) s
          (fun i => Pi.basisFun (IntegralLaurentRing k) (Fin (2*k+1)) (I.val.val i)) :
            ExteriorAlgebra (IntegralLaurentRing k) (Fin (2*k+1) → IntegralLaurentRing k)) := by
  rw [paper_theorem_7_1_integral_full_basis]
  rw [exteriorFullBasisOfDegreeBases_apply _ _ _
    (fun s I => powerBasis (IntegralLaurentRing k) s (2*k+1) I.val)]
  · rw [powerBasis_apply]
  · intro d J
    exact paper_integral_laurent_basis_apply k d J

variable (k : ℕ) (T : Type*) [CommRing T]
  [Algebra (IntegralCoefficientRing k) T] [Algebra (IntegralLaurentRing k) T]
  [IsScalarTower (IntegralCoefficientRing k) (IntegralLaurentRing k) T]

def baseChangedEdge (i : Fin (2*k)) : Tˣ :=
  Units.map (algebraMap (IntegralLaurentRing k) T).toMonoidHom (integralLaurentEdge k i)

abbrev IntegralBaseChangedQuotient :=
  ExteriorAlgebra T (Fin (2*k+1) → T) ⧸
    exteriorRelationIdeal (weightedFirstForm T (baseChangedEdge k T))
      (weightedSecondForm T (baseChangedEdge k T))

/-- The full free good-monomial basis survives arbitrary base change from
the paper's integral Laurent coefficient ring, including nonreduced rings. -/
def paper_theorem_7_1_integral_full_basis_after_base_change :
    Module.Basis (FullGoodOddIndex k) T (IntegralBaseChangedQuotient k T) :=
  exteriorFullBasisOfDegreeBases _ _
    (fun s => paper_integral_laurent_basis_after_base_change k s T)

@[simp] theorem paper_theorem_7_1_integral_full_basis_after_base_change_apply
    (s : ℕ) (I : GoodOddIndex k s) :
    paper_theorem_7_1_integral_full_basis_after_base_change k T ⟨s,I⟩ =
      Ideal.Quotient.mk (exteriorRelationIdeal
        (weightedFirstForm T (baseChangedEdge k T))
        (weightedSecondForm T (baseChangedEdge k T)))
        (exteriorPower.ιMulti T s
          (fun i => Pi.basisFun T (Fin (2*k+1)) (I.val.val i)) :
            ExteriorAlgebra T (Fin (2*k+1) → T)) := by
  rw [paper_theorem_7_1_integral_full_basis_after_base_change]
  rw [exteriorFullBasisOfDegreeBases_apply _ _ _
    (fun s I => powerBasis T s (2*k+1) I.val)]
  · rw [powerBasis_apply]
  · intro d J
    exact paper_integral_laurent_basis_after_base_change_apply k d T J

end PaperVerification.AlternatingForms.IntegralOdd
end
end
end TAF_LiteralSource_0543

section TAF_LiteralSource_0544
/- Original module: PaperVerification.AlternatingFormsOddIntegralRingHom -/


/-!
# Arbitrary ring homomorphisms in the integral base-change assertion

The endpoint is quantified over every commutative target ring and every
ring homomorphism out of the paper's Laurent coefficient ring.  All
compatible algebra structures are constructed from that homomorphism,
so no extra algebra or scalar-tower hypothesis remains in the statement.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms.IntegralOdd

def paper_theorem_7_1_integral_arbitrary_base_change
    (k : ℕ) (T : Type*) [CommRing T] (φ : IntegralLaurentRing k →+* T) :
    Module.Basis (FullGoodOddIndex k) T
      (ExteriorAlgebra T (Fin (2*k+1) → T) ⧸
        exteriorRelationIdeal
          (weightedFirstForm T (fun i => Units.map φ.toMonoidHom (integralLaurentEdge k i)))
          (weightedSecondForm T (fun i => Units.map φ.toMonoidHom (integralLaurentEdge k i)))) := by
  letI : Algebra (IntegralLaurentRing k) T := φ.toAlgebra
  letI : Algebra (IntegralCoefficientRing k) T :=
    (φ.comp (algebraMap (IntegralCoefficientRing k) (IntegralLaurentRing k))).toAlgebra
  letI : IsScalarTower (IntegralCoefficientRing k) (IntegralLaurentRing k) T :=
    IsScalarTower.of_algebraMap_eq' (R := IntegralCoefficientRing k)
      (S := IntegralLaurentRing k) (A := T) rfl
  exact paper_theorem_7_1_integral_full_basis_after_base_change k T

set_option maxRecDepth 4000 in
@[simp] theorem paper_theorem_7_1_integral_arbitrary_base_change_apply
    (k : ℕ) (T : Type*) [CommRing T] (φ : IntegralLaurentRing k →+* T)
    (s : ℕ) (I : GoodOddIndex k s) :
    paper_theorem_7_1_integral_arbitrary_base_change k T φ ⟨s,I⟩ =
      Ideal.Quotient.mk _
        (exteriorPower.ιMulti T s
          (fun i => Pi.basisFun T (Fin (2*k+1)) (I.val.val i)) :
            ExteriorAlgebra T (Fin (2*k+1) → T)) := by
  letI : Algebra (IntegralLaurentRing k) T := φ.toAlgebra
  letI : Algebra (IntegralCoefficientRing k) T :=
    (φ.comp (algebraMap (IntegralCoefficientRing k) (IntegralLaurentRing k))).toAlgebra
  letI : IsScalarTower (IntegralCoefficientRing k) (IntegralLaurentRing k) T :=
    IsScalarTower.of_algebraMap_eq' (R := IntegralCoefficientRing k)
      (S := IntegralLaurentRing k) (A := T) rfl
  change paper_theorem_7_1_integral_full_basis_after_base_change k T ⟨s,I⟩ = _
  exact paper_theorem_7_1_integral_full_basis_after_base_change_apply k T s I

end PaperVerification.AlternatingForms.IntegralOdd
end
end
end TAF_LiteralSource_0544

section TAF_LiteralSource_0545
/- Original module: PaperVerification.AlternatingFormsOddCharacteristicBoundary -/


/-!
# The one-plane boundary of Theorem 7.1

Every line is isotropic for both alternating forms.  In degree one the
printed Richardson interval contains every Plucker coordinate, so its
ideal is the actual Grassmannian ideal.  Its weight initial ideal is the
same ideal in every characteristic, completing the boundary omitted by
the convenient parameterization `s=t+2` of the nontrivial equations.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial PaperVerification.WeightedInitialFiber

variable {K : Type*} [Field K]

theorem odd_onePlane_interval_eq_matrix (k : ℕ) :
    intervalPluckerIdeal (K := K)
      (oddIntervalLower k 1 (by omega)) (oddIntervalUpper k 1 (by omega)) =
      matrixPluckerIdeal := by
  unfold intervalPluckerIdeal
  apply sup_eq_left.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨I,hbad,rfl⟩
  exfalso
  apply hbad
  intro i
  have hi := i.isLt
  have hI := (I.val i).isLt
  constructor
  · change 2*i.val≤(I.val i).val
    omega
  · change (I.val i).val≤2*(k+1-1+i.val)
    omega

/-- The exact one-plane initial-ideal clause of Theorem 7.1; no
characteristic hypothesis is needed for this boundary case. -/
theorem paper_theorem_7_1_initial_ideal_one_plane (k : ℕ) :
    initialIdeal (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
        (pluckerVertexWeight (oddNatVertexWeight k)) =
      intervalPluckerIdeal
        (oddIntervalLower k 1 (by omega)) (oddIntervalUpper k 1 (by omega)) := by
  rw [odd_onePlane_interval_eq_matrix]
  exact onePlane_initialIdeal _

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0545

section TAF_LiteralSource_0546
/- Original module: PaperVerification.AlternatingFormsTransferDefinitions -/


/-!
# The exact transfer matrix and denominator in Proposition5.1

There are `h+1` height states.  Matrix rows are source states and columns
are target states: up steps have weight one, down steps weight `u*v`,
height-zero loops weight `v`, and positive-height loops total weight `u+v`.
The denominator is an actual polynomial, defined by the printed recurrence;
its inverse is the formal power-series inverse with constant coefficient one.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BigradedTransfer

variable {R : Type*} [CommRing R]

/-- The actual finite weighted adjacency matrix, with source-to-target orientation. -/
def transferMatrix (h : ℕ) (u v : R) : Matrix (Fin (h+1)) (Fin (h+1)) R :=
  fun i j =>
    (if i=j then (if i.val=0 then v else u+v) else 0) +
    (if i.val+1=j.val then 1 else 0) +
    (if j.val+1=i.val then u*v else 0)

/-- The paper's polynomials `D_m(z;u,v)`, including `D_0=1`. -/
def denominator (u v : R) : ℕ → Polynomial R
  | 0 => 1
  | 1 => 1-Polynomial.C v*Polynomial.X
  | m+2 => (1-Polynomial.C (u+v)*Polynomial.X)*denominator u v (m+1)-
      Polynomial.C (u*v)*Polynomial.X^2*denominator u v m

@[simp] theorem denominator_zero (u v : R) : denominator u v 0=1 := rfl
@[simp] theorem denominator_one (u v : R) :
    denominator u v 1=1-Polynomial.C v*Polynomial.X := rfl

theorem denominator_recurrence (u v : R) (m : ℕ) :
    denominator u v (m+2)=
      (1-Polynomial.C (u+v)*Polynomial.X)*denominator u v (m+1)-
        Polynomial.C (u*v)*Polynomial.X^2*denominator u v m := rfl

@[simp] theorem denominator_constantCoeff (u v : R) (m : ℕ) :
    Polynomial.constantCoeff (denominator u v m)=1 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [denominator]
  | one => simp [denominator]
  | more m h0 h1 =>
      have h1' : (denominator u v (m+1)).coeff 0=1 := h1
      simp [denominator,h1']

/-- The reciprocal as a formal series; the preceding theorem proves the
unit constant term required for the inverse identities. -/
def inverseDenominator (u v : R) (m : ℕ) : PowerSeries R :=
  PowerSeries.invOfUnit (denominator u v m : PowerSeries R) 1

end PaperVerification.AlternatingForms.BigradedTransfer
end
end
end TAF_LiteralSource_0546

section TAF_LiteralSource_0547
/- Original module: PaperVerification.AlternatingFormsWeightedWalks -/


/-!
# The actual four-colored bounded walks in Proposition 5.1

A walk records every intermediate height and every selected color.  Its
weight is the product of the literal edge weights.  Thus a positive-height
loop has two distinct choices, of weights `u` and `v`, whereas a loop at zero
has only the `v` choice.  The matrix-power formula below is proved by finite
summation over these actual walks.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms.BigradedTransfer

/-- The four pairs of binary steps: `UU`, `UD`, `DU`, and `DD`. -/
inductive PairMark
  | up | bLoop | aLoop | down
  deriving DecidableEq

instance pairMark_fintype : Fintype PairMark where
  elems := {.up,.bLoop,.aLoop,.down}
  complete m := by cases m <;> simp

theorem sum_pairMark {R : Type*} [AddCommMonoid R] (f : PairMark → R) :
    (∑ m,f m)=f .up+f .bLoop+f .aLoop+f .down := by
  change (∑ m∈({.up,.bLoop,.aLoop,.down} : Finset PairMark),f m)=_
  simp [add_assoc]

/-- A legal paired step in the actual closed height strip. -/
def stepAllowed {h : ℕ} (i j : Fin (h+1)) : PairMark → Prop
  | .up => i.val+1=j.val
  | .bLoop => i=j
  | .aLoop => i=j ∧ 0 < i.val
  | .down => j.val+1=i.val

instance stepAllowed_decidable {h : ℕ} (i j : Fin (h+1)) (m : PairMark) :
    Decidable (stepAllowed i j m) := by cases m <;> unfold stepAllowed <;> infer_instance

/-- The distinct colored edges, including their literal transition proof. -/
def ColoredEdge {h : ℕ} (i j : Fin (h+1)) := {m : PairMark // stepAllowed i j m}

instance coloredEdge_fintype {h : ℕ} (i j : Fin (h+1)) : Fintype (ColoredEdge i j) :=
  inferInstanceAs (Fintype {m : PairMark // stepAllowed i j m})

def markWeight {R : Type*} [MulOneClass R] (u v : R) : PairMark → R
  | .up => 1
  | .bLoop => v
  | .aLoop => u
  | .down => u*v

/-- Summing the actual colors gives exactly the printed transfer entry. -/
theorem coloredEdge_weight_sum {R : Type*} [CommRing R] (h : ℕ) (u v : R)
    (i j : Fin (h+1)) :
    (∑ e : ColoredEdge i j,markWeight u v e.val)=transferMatrix h u v i j := by
  have hs : (∑ e : ColoredEdge i j,markWeight u v e.val)=
      ∑ m : PairMark,if stepAllowed i j m then markWeight u v m else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (stepAllowed i j))
      (by simp) (markWeight u v)).symm
  rw [hs,sum_pairMark]
  simp only [stepAllowed,markWeight,transferMatrix]
  by_cases hij : i=j
  · subst j
    by_cases hi : i.val=0
    · simp [hi]
    · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
      simp [hi,hip,add_comm,add_left_comm,add_assoc]
  · simp [hij,add_comm,add_left_comm,add_assoc]

/-- An actual colored walk with its exact initial and final vertices.
The sigma type records the first target and the remaining walk. -/
def ColoredWalk (h : ℕ) : ℕ → Fin (h+1) → Fin (h+1) → Type
  | 0,i,j => PLift (i=j)
  | n+1,i,j => (q : Fin (h+1)) × (ColoredEdge i q × ColoredWalk h n q j)

instance coloredWalk_fintype (h : ℕ) :
    (n : ℕ) → (i j : Fin (h+1)) → Fintype (ColoredWalk h n i j)
  | 0,i,j => inferInstanceAs (Fintype (PLift (i=j)))
  | n+1,i,j => by
      letI : ∀ q : Fin (h+1),Fintype (ColoredWalk h n q j) :=
        fun q => coloredWalk_fintype h n q j
      exact inferInstanceAs
        (Fintype ((q : Fin (h+1)) × (ColoredEdge i q × ColoredWalk h n q j)))

/-- The product of all literal edge weights, with the empty product one. -/
def walkWeight {R : Type*} [MulOneClass R] (h : ℕ) (u v : R) :
    {n : ℕ} → {i j : Fin (h+1)} → ColoredWalk h n i j → R
  | 0,_,_,_ => 1
  | n+1,_,_,p => markWeight u v p.2.1.val * walkWeight h u v p.2.2

/-- Weighted path enumeration is the actual matrix power, over every
commutative coefficient ring and for all heights and lengths. -/
theorem coloredWalk_weight_sum {R : Type*} [CommRing R] (h N : ℕ) (u v : R)
    (i j : Fin (h+1)) :
    (∑ p : ColoredWalk h N i j,walkWeight h u v p)=
      (transferMatrix h u v ^ N) i j := by
  induction N generalizing i j with
  | zero =>
      change (∑ _ : PLift (i=j),(1 : R))=(1 : Matrix (Fin (h+1)) (Fin (h+1)) R) i j
      by_cases hij : i=j
      · subst j
        letI : Unique (PLift (i=i)) :=
          { default := ⟨rfl⟩, uniq := fun _ => Subsingleton.elim _ _ }
        simp [Matrix.one_apply]
      · letI : IsEmpty (PLift (i=j)) := ⟨fun p => hij p.down⟩
        simp [Matrix.one_apply,hij]
  | succ N ih =>
      change (∑ p : (q : Fin (h+1)) ×
        (ColoredEdge i q × ColoredWalk h N q j),
        markWeight u v p.2.1.val * walkWeight h u v p.2.2)=_
      rw [Fintype.sum_sigma]
      simp only [Fintype.sum_prod_type,← Finset.mul_sum,← Finset.sum_mul,ih,
        coloredEdge_weight_sum]
      rw [pow_succ',Matrix.mul_apply]

/-- Numbers of selected `a` and `b` letters in one paired step. -/
def markADegree : PairMark → ℕ
  | .up => 0
  | .bLoop => 0
  | .aLoop => 1
  | .down => 1

def markBDegree : PairMark → ℕ
  | .up => 0
  | .bLoop => 1
  | .aLoop => 0
  | .down => 1

theorem markADegree_le_one (m : PairMark) : markADegree m≤1 := by
  cases m <;> decide

theorem markBDegree_le_one (m : PairMark) : markBDegree m≤1 := by
  cases m <;> decide

/-- This numerical criterion includes the missing `a` loop at zero. -/
theorem stepAllowed_iff_degree_balance {h : ℕ} (i j : Fin (h+1)) (m : PairMark) :
    stepAllowed i j m ↔
      j.val+markADegree m+markBDegree m=i.val+1 ∧ markADegree m ≤ i.val := by
  cases m <;> simp only [stepAllowed,markADegree,markBDegree,Fin.ext_iff] <;> omega

def walkADegree (h : ℕ) : {n : ℕ} → {i j : Fin (h+1)} → ColoredWalk h n i j → ℕ
  | 0,_,_,_ => 0
  | n+1,_,_,p => markADegree p.2.1.val+walkADegree h p.2.2

def walkBDegree (h : ℕ) : {n : ℕ} → {i j : Fin (h+1)} → ColoredWalk h n i j → ℕ
  | 0,_,_,_ => 0
  | n+1,_,_,p => markBDegree p.2.1.val+walkBDegree h p.2.2

/-- The endpoint determines the total number of selected original letters. -/
theorem walk_degree_balance (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) :
    walkADegree h p+walkBDegree h p+j.val=i.val+n := by
  induction n generalizing i with
  | zero =>
      change 0+0+j.val=i.val+0
      have he : i=j := p.down
      omega
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      have he := ((stepAllowed_iff_degree_balance i q e.val).mp e.property).1
      have ht := ih q p
      change (markADegree e.val+walkADegree h p)+
        (markBDegree e.val+walkBDegree h p)+j.val=i.val+(n+1)
      omega

/-- The literal product weight agrees with the two actual color counts. -/
theorem walkWeight_eq_degrees {R : Type*} [CommRing R] (h n : ℕ) (u v : R)
    (i j : Fin (h+1)) (p : ColoredWalk h n i j) :
    walkWeight h u v p=u^walkADegree h p*v^walkBDegree h p := by
  induction n generalizing i with
  | zero => simp only [walkWeight,walkADegree,walkBDegree,pow_zero,mul_one]
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      change markWeight u v e.val*walkWeight h u v p=
        u^(markADegree e.val+walkADegree h p)*v^(markBDegree e.val+walkBDegree h p)
      rw [ih q p,pow_add,pow_add]
      cases e.val <;> simp [markWeight,markADegree,markBDegree,mul_assoc,mul_left_comm,mul_comm]

end PaperVerification.AlternatingForms.BigradedTransfer
end
end
end TAF_LiteralSource_0547

section TAF_LiteralSource_0548
/- Original module: PaperVerification.AlternatingFormsWalkWords -/


/-!
# Recovering literal color words from bounded walks

A legal color and an initial height determine the next height uniquely.
Consequently the color word determines an actual bounded walk with fixed
endpoints.  The construction from a sequence of legal heights and colors is
explicit and preserves every color and both color degrees.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms.BigradedTransfer

def pairMarkOfDegrees (a b : ℕ) : PairMark :=
  if a=0 then (if b=0 then .up else .bLoop)
  else (if b=0 then .aLoop else .down)

theorem markADegree_ofDegrees (a b : ℕ) (ha : a≤1) (hb : b≤1) :
    markADegree (pairMarkOfDegrees a b)=a := by
  unfold pairMarkOfDegrees
  split_ifs <;> simp only [markADegree] <;> omega

theorem markBDegree_ofDegrees (a b : ℕ) (ha : a≤1) (hb : b≤1) :
    markBDegree (pairMarkOfDegrees a b)=b := by
  unfold pairMarkOfDegrees
  split_ifs <;> simp only [markBDegree] <;> omega

theorem pairMark_ext {a b : PairMark}
    (ha : markADegree a=markADegree b) (hb : markBDegree a=markBDegree b) : a=b := by
  cases a <;> cases b <;> simp_all [markADegree,markBDegree]

theorem step_target_unique {h : ℕ} {i j q : Fin (h+1)} {m : PairMark}
    (hj : stepAllowed i j m) (hq : stepAllowed i q m) : j=q := by
  have h1 := ((stepAllowed_iff_degree_balance i j m).mp hj).1
  have h2 := ((stepAllowed_iff_degree_balance i q m).mp hq).1
  apply Fin.ext
  omega

/-- The actual color chosen at every step of a bounded walk. -/
def walkMarks (h : ℕ) : {n : ℕ} → {i j : Fin (h+1)} →
    ColoredWalk h n i j → Fin n → PairMark
  | 0,_,_,_ => Fin.elim0
  | n+1,_,_,p => Fin.cons p.2.1.val (walkMarks h p.2.2)

/-- The initial height and the color word uniquely determine every vertex. -/
theorem walkMarks_injective (h n : ℕ) (i j : Fin (h+1)) :
    Function.Injective (walkMarks h (n := n) (i := i) (j := j)) := by
  induction n generalizing i with
  | zero =>
      intro p q hpq
      exact @Subsingleton.elim (PLift (i=j)) inferInstance p q
  | succ n ih =>
      rintro ⟨q,e,p⟩ ⟨q',e',p'⟩ he
      have hm : e.val=e'.val := by
        simpa only [walkMarks,Fin.cons_zero] using congrArg (fun f => f 0) he
      have hq : q=q' := step_target_unique e.property (hm.symm ▸ e'.property)
      subst q'
      have hee : e=e' := Subtype.ext hm
      subst e'
      have ht : walkMarks h p=walkMarks h p' := by
        funext r
        simpa only [walkMarks,Fin.cons_succ] using congrArg (fun f => f r.succ) he
      have hp : p=p' := ih q ht
      subst p'
      rfl

/-- Construct the actual walk by following a prescribed legal sequence. -/
def walkOfSteps (h : ℕ) : (n : ℕ) →
    (v : Fin (n+1) → Fin (h+1)) → (m : Fin n → PairMark) →
    (∀ r,stepAllowed (v r.castSucc) (v r.succ) (m r)) →
    ColoredWalk h n (v 0) (v (Fin.last n))
  | 0,v,m,hm => ⟨rfl⟩
  | n+1,v,m,hm =>
      ⟨v (0 : Fin (n+1)).succ,⟨m 0,hm 0⟩,
        walkOfSteps h n (fun r => v r.succ) (fun r => m r.succ)
          (fun r => by simpa only [Fin.castSucc_succ] using hm r.succ)⟩

@[simp] theorem walkOfSteps_marks (h n : ℕ)
    (v : Fin (n+1) → Fin (h+1)) (m : Fin n → PairMark)
    (hm : ∀ r,stepAllowed (v r.castSucc) (v r.succ) (m r)) :
    walkMarks h (walkOfSteps h n v m hm)=m := by
  induction n with
  | zero => funext r; exact Fin.elim0 r
  | succ n ih =>
      change Fin.cons (m 0)
        (walkMarks h (walkOfSteps h n (fun r => v r.succ) (fun r => m r.succ) _))=m
      rw [ih]
      exact Fin.cons_self_tail m

/-- Changing only proved-equal endpoint names changes no underlying colors. -/
def reindexWalk {h n : ℕ} {i j i' j' : Fin (h+1)}
    (hi : i=i') (hj : j=j') (p : ColoredWalk h n i j) : ColoredWalk h n i' j' := by
  subst i'
  subst j'
  exact p

@[simp] theorem reindexWalk_marks {h n : ℕ} {i j i' j' : Fin (h+1)}
    (hi : i=i') (hj : j=j') (p : ColoredWalk h n i j) :
    walkMarks h (reindexWalk hi hj p)=walkMarks h p := by
  subst i'
  subst j'
  rfl

theorem walkADegree_eq_sum_marks (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) :
    walkADegree h p=∑ r,markADegree (walkMarks h p r) := by
  induction n generalizing i with
  | zero => simp only [walkADegree,Fin.sum_univ_zero]
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      simp only [walkADegree,walkMarks,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,ih]

theorem walkBDegree_eq_sum_marks (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) :
    walkBDegree h p=∑ r,markBDegree (walkMarks h p r) := by
  induction n generalizing i with
  | zero => simp only [walkBDegree,Fin.sum_univ_zero]
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      simp only [walkBDegree,walkMarks,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,ih]

end PaperVerification.AlternatingForms.BigradedTransfer
end
end
end TAF_LiteralSource_0548

section TAF_LiteralSource_0549
/- Original module: PaperVerification.AlternatingFormsGoodWalkMap -/


/-!
# Pairing the literal good-monomial binary path

The first paired position is the fixed up-step followed by `b_0`.
Every subsequent pair is `(a_i,b_i)`.  Heights are computed from the actual
prefix count and divided by two.  The good inequalities prove the strip
bounds and the absence of an `a` loop at height zero.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.GoodPaths

open BigradedTransfer

/-- The same sorted selections and inequalities as the exterior good basis,
kept here independent of its algebraic proof dependencies. -/
def GoodPathIndex (k s : ℕ) :=
  {I : {I : Fin s → Fin (2*k+1) // StrictMono I} //
    ∀ i,2*i.val≤(I.val i).val ∧ (I.val i).val+2*s≤2*k+2+2*i.val}

instance goodPathIndex_fintype (k s : ℕ) : Fintype (GoodPathIndex k s) := by
  unfold GoodPathIndex
  infer_instance

theorem index_prefix_bounds {k s : ℕ} (I : GoodPathIndex k s) (q : ℕ)
    (hq : q≤2*k+3) :
    2*selectedBefore I.val.val q≤q ∧
      q+2*s≤2*k+3+2*selectedBefore I.val.val q :=
  (good_bounds_iff_prefix_strip k s I.val.val I.val.property).mp I.property q hq

/-- The even-position height, after halving the actual binary height. -/
def pairedHeight {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s)
    (r : Fin (k+2)) : Fin (k+1-s+1) :=
  ⟨r.val-selectedBefore I.val.val (2*r.val),by
    have hb := index_prefix_bounds I (2*r.val) (by have := r.isLt; omega)
    have hr := r.isLt
    omega⟩

theorem pairedHeight_zero {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    pairedHeight hs I 0=0 := by
  apply Fin.ext
  simp [pairedHeight]

theorem pairedHeight_last {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    pairedHeight hs I (Fin.last (k+1))=Fin.last (k+1-s) := by
  apply Fin.ext
  change k+1-selectedBefore I.val.val (2*(k+1))=k+1-s
  have hq : 2*(k+1)=(2*k+1)+1 := by omega
  rw [hq,selectedBefore_all]

/-- The two literal selected-position bits determine the pair's color. -/
def pairedMark {k s : ℕ} (I : GoodPathIndex k s) (r : Fin (k+1)) : PairMark :=
  pairMarkOfDegrees (selectedAt I.val.val (2*r.val))
    (selectedAt I.val.val (2*r.val+1))

theorem pairedMark_a {k s : ℕ} (I : GoodPathIndex k s) (r : Fin (k+1)) :
    markADegree (pairedMark I r)=selectedAt I.val.val (2*r.val) :=
  markADegree_ofDegrees _ _ (selectedAt_le_one _ _) (selectedAt_le_one _ _)

theorem pairedMark_b {k s : ℕ} (I : GoodPathIndex k s) (r : Fin (k+1)) :
    markBDegree (pairedMark I r)=selectedAt I.val.val (2*r.val+1) :=
  markBDegree_ofDegrees _ _ (selectedAt_le_one _ _) (selectedAt_le_one _ _)

/-- Every paired step is legal in the exact finite strip, including the
asymmetric boundary loop at zero. -/
theorem paired_step_allowed {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s)
    (r : Fin (k+1)) :
    stepAllowed (pairedHeight hs I r.castSucc) (pairedHeight hs I r.succ) (pairedMark I r) := by
  rw [stepAllowed_iff_degree_balance,pairedMark_a,pairedMark_b]
  have hr := r.isLt
  have h0 := (index_prefix_bounds I (2*r.val) (by omega)).1
  have h1 := (index_prefix_bounds I (2*r.val+1) (by omega)).1
  have h2 := (index_prefix_bounds I (2*r.val+2) (by omega)).1
  have he0 := selectedBefore_succ I.val.property (2*r.val)
  have he1 := selectedBefore_succ I.val.property (2*r.val+1)
  change selectedBefore I.val.val (2*r.val+2)=
    selectedBefore I.val.val (2*r.val+1)+selectedAt I.val.val (2*r.val+1) at he1
  have hc0 : selectedBefore I.val.val (2*r.val) ≤ r.val := by omega
  have hc1 : selectedBefore I.val.val (2*r.val+1) ≤ r.val := by omega
  have hc2 : selectedBefore I.val.val (2*r.val+2) ≤ r.val+1 := by omega
  change ((r.val+1)-selectedBefore I.val.val (2*(r.val+1)))+
      selectedAt I.val.val (2*r.val)+selectedAt I.val.val (2*r.val+1)=
        (r.val-selectedBefore I.val.val (2*r.val))+1 ∧
      selectedAt I.val.val (2*r.val)≤r.val-selectedBefore I.val.val (2*r.val)
  have hq : 2*(r.val+1)=2*r.val+2 := by omega
  rw [hq]
  omega

/-- The actual paired walk associated with a good exterior word. -/
def goodIndexToWalk {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s)) :=
  reindexWalk (pairedHeight_zero hs I) (pairedHeight_last hs I)
    (walkOfSteps (k+1-s) (k+1) (pairedHeight hs I) (pairedMark I)
      (paired_step_allowed hs I))

@[simp] theorem goodIndexToWalk_marks {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    walkMarks (k+1-s) (goodIndexToWalk hs I)=pairedMark I := by
  simp only [goodIndexToWalk,reindexWalk_marks,walkOfSteps_marks]

/-- A selected-set membership statement is the literal binary down-step. -/
theorem mem_selectedSet_iff_selectedAt {s n : ℕ} (I : Fin s → Fin n) (x : Fin n) :
    x∈selectedSet I ↔ selectedAt I (x.val+1)=1 := by
  have he : (∃ i,(I i).val+1=x.val+1) ↔ ∃ i,I i=x := by
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨i,Fin.ext (by omega)⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i,rfl⟩
  have hm : x∈selectedSet I ↔ ∃ i,I i=x := by simp [selectedSet]
  rw [hm]
  unfold selectedAt
  by_cases hsel : ∃ i,I i=x
  · have hval := he.mpr hsel
    simp only [hsel,hval,if_true]
  · have hval : ¬∃ i,(I i).val+1=x.val+1 := fun h => hsel (he.mp h)
    simp only [hsel,hval,if_false,Nat.zero_ne_one]

/-- All original selected letters are recovered from the paired colors. -/
theorem pairedMark_injective (k s : ℕ) :
    Function.Injective (pairedMark (k := k) (s := s)) := by
  intro I J he
  have hbit : ∀ q,q≤2*k+1 → selectedAt I.val.val q=selectedAt J.val.val q := by
    intro q hq
    let r : Fin (k+1) := ⟨q/2,by omega⟩
    have hm := congrFun he r
    by_cases hp : q%2=0
    · have hq' : 2*r.val=q := by dsimp [r]; omega
      have ha := congrArg markADegree hm
      simpa only [pairedMark_a,hq'] using ha
    · have hq' : 2*r.val+1=q := by dsimp [r]; omega
      have hb := congrArg markBDegree hm
      simpa only [pairedMark_b,hq'] using hb
  have hS : selectedSet I.val.val=selectedSet J.val.val := by
    ext x
    rw [mem_selectedSet_iff_selectedAt,mem_selectedSet_iff_selectedAt,
      hbit (x.val+1) (by have := x.isLt; omega)]
  apply Subtype.ext
  apply (increasingSelectionEquiv s (2*k+1)).injective
  exact Subtype.ext hS

theorem goodIndexToWalk_injective {k s : ℕ} (hs : s≤k+1) :
    Function.Injective (goodIndexToWalk (k := k) hs) := by
  intro I J he
  apply pairedMark_injective k s
  simpa only [goodIndexToWalk_marks] using congrArg (walkMarks (k+1-s)) he

end PaperVerification.AlternatingForms.GoodPaths
end
end
end TAF_LiteralSource_0549

section TAF_LiteralSource_0550
/- Original module: PaperVerification.AlternatingFormsWalkStates -/


/-!
# Literal states and binary occupations of a colored walk

The states are read from the actual recursive walk, and their transitions
are its stored edge proofs.  Splitting each color into its two occupation
bits recovers the binary path, with its first position unselected.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BigradedTransfer

/-- All actual visited vertices, including both endpoints. -/
def walkStates (h : ℕ) : {n : ℕ} → {i j : Fin (h+1)} →
    ColoredWalk h n i j → Fin (n+1) → Fin (h+1)
  | 0,i,_,_ => fun _ => i
  | n+1,i,_,p => Fin.cons i (walkStates h p.2.2)

@[simp] theorem walkStates_zero (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) : walkStates h p 0=i := by
  cases n <;> rfl

@[simp] theorem walkStates_last (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) : walkStates h p (Fin.last n)=j := by
  induction n generalizing i with
  | zero => exact p.down
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      change walkStates h p (Fin.last n)=j
      exact ih q p

theorem walkStates_step (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) (r : Fin n) :
    stepAllowed (walkStates h p r.castSucc) (walkStates h p r.succ) (walkMarks h p r) := by
  induction n generalizing i with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      refine Fin.cases ?_ (fun r => ?_) r
      · simpa only [walkStates,walkMarks,Fin.castSucc_zero,Fin.cons_zero,Fin.cons_succ,walkStates_zero]
          using e.property
      · simpa only [walkStates,walkMarks,Fin.cons_succ,Fin.castSucc_succ]
          using ih q p r

/-- Unpair a color word into its literal first/second occupation bits. -/
def binaryOccupation {n : ℕ} (m : Fin n → PairMark) (q : Fin (2*n)) : ℕ :=
  if q.val%2=0 then markADegree (m ⟨q.val/2,by have := q.isLt; omega⟩)
  else markBDegree (m ⟨q.val/2,by have := q.isLt; omega⟩)

theorem binaryOccupation_le_one {n : ℕ} (m : Fin n → PairMark) (q : Fin (2*n)) :
    binaryOccupation m q≤1 := by
  unfold binaryOccupation
  split_ifs
  · exact markADegree_le_one _
  · exact markBDegree_le_one _

theorem binaryOccupation_even {n : ℕ} (m : Fin n → PairMark) (r : Fin n) :
    binaryOccupation m ⟨2*r.val,by have := r.isLt; omega⟩=markADegree (m r) := by
  have hm : (2*r.val)%2=0 := by omega
  have hd : (⟨(2*r.val)/2,by have := r.isLt; omega⟩ : Fin n)=r := by
    apply Fin.ext
    change (2*r.val)/2=r.val
    omega
  simp only [binaryOccupation,hm,if_true,hd]

theorem binaryOccupation_odd {n : ℕ} (m : Fin n → PairMark) (r : Fin n) :
    binaryOccupation m ⟨2*r.val+1,by have := r.isLt; omega⟩=markBDegree (m r) := by
  have hm : (2*r.val+1)%2≠0 := by omega
  have hd : (⟨(2*r.val+1)/2,by have := r.isLt; omega⟩ : Fin n)=r := by
    apply Fin.ext
    change (2*r.val+1)/2=r.val
    omega
  simp only [binaryOccupation,hm,if_false,hd]

theorem walk_first_occupation_zero (h n : ℕ) (j : Fin (h+1))
    (p : ColoredWalk h (n+1) 0 j) :
    markADegree (walkMarks h p 0)=0 := by
  have he := (stepAllowed_iff_degree_balance _ _ _).mp (walkStates_step h (n+1) 0 j p 0)
  have h0 := walkStates_zero h (n+1) 0 j p
  change walkStates h p (0 : Fin (n+2))=0 at h0
  have ha : markADegree (walkMarks h p 0)≤0 := by simpa only [Fin.castSucc_zero,h0,Fin.val_zero] using he.2
  omega

/-- A selected-list prefix count with the same two literal bits satisfies
exactly the actual state conservation law at every paired position. -/
theorem prefix_count_state_balance {h n t l : ℕ}
    (p : ColoredWalk h n 0 (Fin.last h)) (I : Fin t → Fin l) (hI : StrictMono I)
    (ha : ∀ r : Fin n,GoodPaths.selectedAt I (2*r.val)=markADegree (walkMarks h p r))
    (hb : ∀ r : Fin n,GoodPaths.selectedAt I (2*r.val+1)=markBDegree (walkMarks h p r)) :
    ∀ r : Fin (n+1),GoodPaths.selectedBefore I (2*r.val)+(walkStates h p r).val=r.val := by
  intro r
  induction r using Fin.induction with
  | zero => simp only [Fin.val_zero,Nat.mul_zero,GoodPaths.selectedBefore_zero,
      walkStates_zero,Nat.add_zero]
  | succ r ih =>
      have hc0 := GoodPaths.selectedBefore_succ hI (2*r.val)
      have hc1 := GoodPaths.selectedBefore_succ hI (2*r.val+1)
      change GoodPaths.selectedBefore I (2*r.val+2)=
        GoodPaths.selectedBefore I (2*r.val+1)+GoodPaths.selectedAt I (2*r.val+1) at hc1
      have hs := ((stepAllowed_iff_degree_balance _ _ _).mp
        (walkStates_step h n 0 (Fin.last h) p r)).1
      rw [ha r] at hc0
      rw [hb r] at hc1
      change GoodPaths.selectedBefore I (2*(r.val+1))+
        (walkStates h p r.succ).val=r.val+1
      change GoodPaths.selectedBefore I (2*r.val)+
        (walkStates h p r.castSucc).val=r.val at ih
      have hq : 2*(r.val+1)=2*r.val+2 := by omega
      rw [hq]
      omega

end PaperVerification.AlternatingForms.BigradedTransfer
end
end
end TAF_LiteralSource_0550

section TAF_LiteralSource_0551
/- Original module: PaperVerification.AlternatingFormsGoodWalkEquiv -/


/-!
# The full good-selection and colored-walk bijection

The inverse selects precisely the original positions whose corresponding
binary occupation bit is one.  Its cardinality is proved from the actual
walk's endpoint conservation law.  Every prefix satisfies the two strip
bounds, so sorting this actual selected set produces a good exterior index.
Neither the desired dimension nor a path-count formula is an assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.GoodPaths

open BigradedTransfer

/-- Recover the original positions, omitting only the fixed initial up-step. -/
def walkSelection {k h : ℕ}
    (p : ColoredWalk h (k+1) 0 (Fin.last h)) : Finset (Fin (2*k+1)) :=
  Finset.univ.filter fun x => binaryOccupation (walkMarks h p)
    ⟨x.val+1,by have := x.isLt; omega⟩=1

/-- Any increasing enumeration of the recovered set has exactly the actual
binary bits, including the fixed zero at position zero. -/
theorem selectedAt_walkSelection {k h t : ℕ}
    (p : ColoredWalk h (k+1) 0 (Fin.last h)) (I : Fin t → Fin (2*k+1))
    (hS : selectedSet I=walkSelection p) (q : Fin (2*(k+1))) :
    selectedAt I q.val=binaryOccupation (walkMarks h p) q := by
  by_cases hq : q.val=0
  · have he : q=(⟨2*(0 : Fin (k+1)).val,by omega⟩ : Fin (2*(k+1))) :=
      Fin.ext hq
    rw [he,binaryOccupation_even,walk_first_occupation_zero]
    exact selectedAt_zero I
  · let x : Fin (2*k+1) := ⟨q.val-1,by have := q.isLt; omega⟩
    have hx : x.val+1=q.val := by dsimp [x]; omega
    have hq' : (⟨x.val+1,by have := x.isLt; omega⟩ : Fin (2*(k+1)))=q := Fin.ext hx
    have he : selectedAt I q.val=1 ↔ binaryOccupation (walkMarks h p) q=1 := by
      rw [←hx,←mem_selectedSet_iff_selectedAt,hS]
      simp only [walkSelection,Finset.mem_filter,Finset.mem_univ,true_and,hq']
    have h0 := selectedAt_le_one I q.val
    have h1 := binaryOccupation_le_one (walkMarks h p) q
    omega

theorem selectedAt_walkSelection_a {k h t : ℕ}
    (p : ColoredWalk h (k+1) 0 (Fin.last h)) (I : Fin t → Fin (2*k+1))
    (hS : selectedSet I=walkSelection p) (r : Fin (k+1)) :
    selectedAt I (2*r.val)=markADegree (walkMarks h p r) := by
  simpa only [binaryOccupation_even] using
    selectedAt_walkSelection p I hS ⟨2*r.val,by have := r.isLt; omega⟩

theorem selectedAt_walkSelection_b {k h t : ℕ}
    (p : ColoredWalk h (k+1) 0 (Fin.last h)) (I : Fin t → Fin (2*k+1))
    (hS : selectedSet I=walkSelection p) (r : Fin (k+1)) :
    selectedAt I (2*r.val+1)=markBDegree (walkMarks h p r) := by
  simpa only [binaryOccupation_odd] using
    selectedAt_walkSelection p I hS ⟨2*r.val+1,by have := r.isLt; omega⟩

/-- The recovered set has the exact required exterior degree. -/
theorem walkSelection_card {k s : ℕ} (hs : s≤k+1)
    (p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s))) :
    (walkSelection p).card=s := by
  let S := walkSelection p
  let I : Fin S.card → Fin (2*k+1) := S.orderEmbOfFin rfl
  have hI : StrictMono I := (S.orderEmbOfFin rfl).strictMono
  have hS : selectedSet I=walkSelection p := Finset.image_orderEmbOfFin_univ S rfl
  have he := prefix_count_state_balance p I hI
    (selectedAt_walkSelection_a p I hS) (selectedAt_walkSelection_b p I hS)
    (Fin.last (k+1))
  rw [walkStates_last] at he
  change selectedBefore I (2*(k+1))+(k+1-s)=k+1 at he
  have hq : 2*(k+1)=(2*k+1)+1 := by omega
  rw [hq,selectedBefore_all] at he
  dsimp [S] at he
  omega

/-- The recovered sorted word satisfies both walls of the original strip. -/
theorem walkSelection_good_bounds {k s : ℕ} (hs : s≤k+1)
    (p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s)))
    (I : Fin s → Fin (2*k+1)) (hI : StrictMono I)
    (hS : selectedSet I=walkSelection p) :
    ∀ i,2*i.val≤(I i).val ∧ (I i).val+2*s≤2*k+2+2*i.val := by
  apply (good_bounds_iff_prefix_strip k s I hI).mpr
  intro q hq
  have hb := prefix_count_state_balance p I hI
    (selectedAt_walkSelection_a p I hS) (selectedAt_walkSelection_b p I hS)
  by_cases hend : 2*k+2≤q
  · rw [selectedBefore_eq_card_of_ge I q (by omega)]
    constructor <;> omega
  · let r : Fin (k+1) := ⟨q/2,by omega⟩
    have hbal := hb r.castSucc
    change selectedBefore I (2*r.val)+(walkStates (k+1-s) p r.castSucc).val=r.val at hbal
    have hheight := (walkStates (k+1-s) p r.castSucc).isLt
    by_cases heven : q%2=0
    · have he : q=2*r.val := by dsimp [r]; omega
      rw [he]
      constructor <;> omega
    · have he : q=2*r.val+1 := by dsimp [r]; omega
      have hinc := selectedBefore_succ hI (2*r.val)
      rw [selectedAt_walkSelection_a p I hS r] at hinc
      have ha := ((stepAllowed_iff_degree_balance _ _ _).mp
        (walkStates_step (k+1-s) (k+1) 0 (Fin.last (k+1-s)) p r)).2
      rw [he]
      constructor <;> omega

/-- Sort the recovered original selected set, using its proved exact size. -/
def walkToGoodIndex {k s : ℕ} (hs : s≤k+1)
    (p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s))) : GoodPathIndex k s :=
  let S := walkSelection p
  let hS := walkSelection_card hs p
  let I := S.orderEmbOfFin hS
  ⟨⟨I,I.strictMono⟩,walkSelection_good_bounds hs p I I.strictMono
    (Finset.image_orderEmbOfFin_univ S hS)⟩

theorem walkToGoodIndex_selectedSet {k s : ℕ} (hs : s≤k+1)
    (p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s))) :
    selectedSet (walkToGoodIndex hs p).val.val=walkSelection p :=
  Finset.image_orderEmbOfFin_univ (walkSelection p) (walkSelection_card hs p)

/-- The inverse construction recovers every actual walk and both loop colors. -/
theorem goodIndexToWalk_walkToGoodIndex {k s : ℕ} (hs : s≤k+1)
    (p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s))) :
    goodIndexToWalk hs (walkToGoodIndex hs p)=p := by
  apply walkMarks_injective (k+1-s) (k+1) 0 (Fin.last (k+1-s))
  rw [goodIndexToWalk_marks]
  funext r
  apply pairMark_ext
  · rw [pairedMark_a]
    exact selectedAt_walkSelection_a p _ (walkToGoodIndex_selectedSet hs p) r
  · rw [pairedMark_b]
    exact selectedAt_walkSelection_b p _ (walkToGoodIndex_selectedSet hs p) r

/-- The complete, all-size good-index and actual weighted-walk equivalence. -/
def goodIndexWalkEquiv (k s : ℕ) (hs : s≤k+1) :
    GoodPathIndex k s ≃ ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s)) where
  toFun := goodIndexToWalk hs
  invFun := walkToGoodIndex hs
  left_inv I := (goodIndexToWalk_injective hs) (goodIndexToWalk_walkToGoodIndex hs _)
  right_inv := goodIndexToWalk_walkToGoodIndex hs

end PaperVerification.AlternatingForms.GoodPaths
end
end
end TAF_LiteralSource_0551

section TAF_LiteralSource_0552
/- Original module: PaperVerification.AlternatingFormsGoodWalkWeights -/


/-!
# The bijection preserves the original two exterior degrees

The odd original positions are exactly the first positions in the paired
steps; the fixed initial position contributes zero.  An explicit bijection
between selected odd letters and selected first slots proves equality of the
`a` degrees.  The endpoint conservation law then gives the `b` degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms.GoodPaths

open BigradedTransfer

def indexADegree {s n : ℕ} (I : Fin s → Fin n) : ℕ :=
  ∑ i,if (I i).val%2=1 then 1 else 0

theorem indexADegree_le {s n : ℕ} (I : Fin s → Fin n) : indexADegree I≤s := by
  calc
    indexADegree I≤∑ i : Fin s,(1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs <;> omega
    _ = s := by simp

theorem selectedAt_eq_one_iff {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) :
    selectedAt I q=1 ↔ ∃ i,(I i).val+1=q := by simp [selectedAt]

/-- Every selected original odd position is the first slot of exactly one
pair, and every selected first slot comes from one such original position. -/
def selectedOddSlotEquiv {k s : ℕ} (I : Fin s → Fin (2*k+1)) (hI : StrictMono I) :
    {i : Fin s // (I i).val%2=1} ≃
      {r : Fin (k+1) // selectedAt I (2*r.val)=1} := by
  let f : {i : Fin s // (I i).val%2=1} →
      {r : Fin (k+1) // selectedAt I (2*r.val)=1} := fun i =>
    ⟨⟨((I i.val).val+1)/2,by have := (I i.val).isLt; omega⟩,by
      change selectedAt I (2*(((I i.val).val+1)/2))=1
      rw [selectedAt_eq_one_iff]
      refine ⟨i.val,?_⟩
      change (I i.val).val+1=2*(((I i.val).val+1)/2)
      have hi := i.property
      omega⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro i j he
    apply Subtype.ext
    apply hI.injective
    apply Fin.ext
    have hv := congrArg (fun r : {r : Fin (k+1) // selectedAt I (2*r.val)=1} => r.val.val) he
    have hi := i.property
    have hj := j.property
    change ((I i.val).val+1)/2=((I j.val).val+1)/2 at hv
    omega
  · intro r
    obtain ⟨i,hi⟩ := (selectedAt_eq_one_iff I (2*r.val.val)).mp r.property
    have hip : (I i).val%2=1 := by omega
    refine ⟨⟨i,hip⟩,?_⟩
    apply Subtype.ext
    apply Fin.ext
    change ((I i).val+1)/2=r.val.val
    omega

theorem indexADegree_eq_pair_slots {k s : ℕ}
    (I : Fin s → Fin (2*k+1)) (hI : StrictMono I) :
    indexADegree I=∑ r : Fin (k+1),selectedAt I (2*r.val) := by
  have he := Fintype.card_congr (selectedOddSlotEquiv I hI)
  rw [Fintype.card_subtype,Fintype.card_subtype] at he
  rw [indexADegree,Finset.sum_boole]
  rw [he]
  symm
  calc
    (∑ r : Fin (k+1),selectedAt I (2*r.val))=
        ∑ r : Fin (k+1),if selectedAt I (2*r.val)=1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      have hle := selectedAt_le_one I (2*r.val)
      split_ifs <;> omega
    _ = _ := Finset.sum_boole _ _

theorem goodIndexToWalk_aDegree {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    walkADegree (k+1-s) (goodIndexToWalk hs I)=indexADegree I.val.val := by
  rw [walkADegree_eq_sum_marks,goodIndexToWalk_marks]
  simp only [pairedMark_a]
  exact (indexADegree_eq_pair_slots I.val.val I.val.property).symm

theorem goodIndexToWalk_bDegree {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    walkBDegree (k+1-s) (goodIndexToWalk hs I)=s-indexADegree I.val.val := by
  have he := walk_degree_balance (k+1-s) (k+1) 0 (Fin.last (k+1-s))
    (goodIndexToWalk hs I)
  rw [goodIndexToWalk_aDegree] at he
  change indexADegree I.val.val+walkBDegree (k+1-s) (goodIndexToWalk hs I)+(k+1-s)=0+(k+1) at he
  omega

/-- Exact preservation of the literal original exterior monomial weight. -/
theorem goodIndexToWalk_weight {R : Type*} [CommRing R] {k s : ℕ}
    (hs : s≤k+1) (I : GoodPathIndex k s) (u v : R) :
    walkWeight (k+1-s) u v (goodIndexToWalk hs I)=
      u^indexADegree I.val.val*v^(s-indexADegree I.val.val) := by
  rw [walkWeight_eq_degrees,goodIndexToWalk_aDegree,goodIndexToWalk_bDegree]

/-- The weighted sum over every good exterior word is the actual transfer
matrix corner, for every `k` and every printed degree `0≤s≤k+1`. -/
theorem good_index_weight_sum {R : Type*} [CommRing R] (k s : ℕ)
    (hs : s≤k+1) (u v : R) :
    (∑ I : GoodPathIndex k s,u^indexADegree I.val.val*v^(s-indexADegree I.val.val))=
      (transferMatrix (k+1-s) u v ^ (k+1)) 0 (Fin.last (k+1-s)) := by
  calc
    _ = ∑ I : GoodPathIndex k s,walkWeight (k+1-s) u v (goodIndexWalkEquiv k s hs I) := by
      apply Finset.sum_congr rfl
      intro I hI
      exact (goodIndexToWalk_weight hs I u v).symm
    _ = ∑ p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s)),
        walkWeight (k+1-s) u v p := Equiv.sum_comp (goodIndexWalkEquiv k s hs) _
    _ = _ := coloredWalk_weight_sum (k+1-s) (k+1) u v 0 (Fin.last (k+1-s))

end PaperVerification.AlternatingForms.GoodPaths
end
end
end TAF_LiteralSource_0552

section TAF_LiteralSource_0553
/- Original module: PaperVerification.AlternatingFormsTransferSeries -/


/-!
# The all-length transfer formula in Proposition 5.1

An explicit continuant row multiplies the actual resolvent to a singleton
row. The coefficient-defined matrix series then gives the reciprocal of the
paper's exact denominator. No determinant evaluation or bounded computation
is assumed. This source is pending compilation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace PaperVerification.AlternatingForms.BigradedTransfer

variable {R : Type*} [CommRing R]

/-- The ordinary continuants with the same interior recurrence. -/
def continuant (u v : R) : ℕ → Polynomial R
  | 0 => 1
  | 1 => 1-Polynomial.C (u+v)*Polynomial.X
  | m+2 => (1-Polynomial.C (u+v)*Polynomial.X)*continuant u v (m+1)-
      Polynomial.C (u*v)*Polynomial.X^2*continuant u v m

@[simp] theorem continuant_zero (u v : R) : continuant u v 0=1 := rfl
@[simp] theorem continuant_one (u v : R) :
    continuant u v 1=1-Polynomial.C (u+v)*Polynomial.X := rfl

theorem continuant_recurrence (u v : R) (m : ℕ) :
    continuant u v (m+2)=
      (1-Polynomial.C (u+v)*Polynomial.X)*continuant u v (m+1)-
        Polynomial.C (u*v)*Polynomial.X^2*continuant u v m := rfl

/-- Changing the height-zero diagonal from u+v to v gives precisely D. -/
theorem denominator_eq_continuant (u v : R) (m : ℕ) :
    denominator u v (m+1)=continuant u v (m+1)+
      Polynomial.C u*Polynomial.X*continuant u v m := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [Nat.zero_add,denominator_one,continuant_one,continuant_zero,map_add]; ring
  | one =>
      rw [denominator_recurrence,continuant_recurrence]
      simp only [Nat.zero_add,Nat.add_zero,denominator_one,denominator_zero,continuant_one,continuant_zero,map_add]
      ring
  | more m h0 h1 =>
      rw [denominator_recurrence u v (m+1),h1,h0,
        continuant_recurrence u v (m+1),continuant_recurrence u v m]
      ring

def previous {h : ℕ} (j : Fin (h+1)) : Fin (h+1) :=
  ⟨j.val-1,(Nat.sub_le j.val 1).trans_lt j.isLt⟩

def next {h : ℕ} (j : Fin (h+1)) (hj : j.val<h) : Fin (h+1) :=
  ⟨j.val+1,Nat.succ_lt_succ hj⟩

/-- Exact multiplication of a row by the tridiagonal transfer matrix,
including both boundary states. -/
theorem vecMul_transferMatrix (h : ℕ) (u v : R) (row : Fin (h+1) → R)
    (j : Fin (h+1)) :
    (row ᵥ* transferMatrix h u v) j=
      row j*(if j.val=0 then v else u+v)+
      (if hj : 0<j.val then row (previous j) else 0)+
      (if hj : j.val<h then row (next j hj)*(u*v) else 0) := by
  classical
  have hd : (∑ i,row i*(if i=j then (if i.val=0 then v else u+v) else 0))=
      row j*(if j.val=0 then v else u+v) := by
    simp [mul_ite]
  have hu : (∑ i : Fin (h+1),row i*(if i.val+1=j.val then 1 else 0))=
      (if hj : 0<j.val then row (previous j) else 0) := by
    by_cases hj : 0<j.val
    · rw [dif_pos hj,Finset.sum_eq_single (previous j)]
      · have he : (previous j).val+1=j.val := by dsimp [previous]; omega
        simp only [he,ite_true,mul_one]
      · intro i hi hne
        have he : i.val+1≠j.val := by
          intro he
          apply hne
          apply Fin.ext
          dsimp [previous]
          omega
        simp only [he,ite_false,mul_zero]
      · simp
    · rw [dif_neg hj]
      apply Finset.sum_eq_zero
      intro i hi
      have he : i.val+1≠j.val := by omega
      simp only [he,ite_false,mul_zero]
  have hl : (∑ i : Fin (h+1),row i*(if j.val+1=i.val then u*v else 0))=
      (if hj : j.val<h then row (next j hj)*(u*v) else 0) := by
    by_cases hj : j.val<h
    · rw [dif_pos hj,Finset.sum_eq_single (next j hj)]
      · simp only [next,ite_true]
      · intro i hi hne
        have he : j.val+1≠i.val := by
          intro he
          apply hne
          apply Fin.ext
          exact he.symm
        simp only [he,ite_false,mul_zero]
      · simp
    · rw [dif_neg hj]
      apply Finset.sum_eq_zero
      intro i hi
      have he : j.val+1≠i.val := by have hi' := i.isLt; omega
      simp only [he,ite_false,mul_zero]
  simp only [Matrix.vecMul,dotProduct,transferMatrix,mul_add,Finset.sum_add_distrib]
  rw [hd,hu,hl]

/-- Coefficient extension changes only u and v in the actual matrix. -/
theorem transferMatrix_map_C (h : ℕ) (u v : R) :
    (transferMatrix h u v).map PowerSeries.C=
      transferMatrix h (PowerSeries.C u) (PowerSeries.C v) := by
  classical
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply,transferMatrix,map_add,map_mul]
  split_ifs <;> simp

/-- The explicit row of continuants; all entries are genuine formal series. -/
def continuantRow (h : ℕ) (u v : R) (j : Fin (h+1)) : PowerSeries R :=
  PowerSeries.X^j.val*(continuant u v (h-j.val) : PowerSeries R)

@[simp] theorem continuantRow_last (h : ℕ) (u v : R) :
    continuantRow h u v (Fin.last h)=PowerSeries.X^h := by
  simp [continuantRow]

/-- The entry of the actual resolvent product, before inserting the row certificate. -/
theorem row_resolvent_apply (h : ℕ) (u v : R)
    (row : Fin (h+1) → PowerSeries R) (j : Fin (h+1)) :
    (row ᵥ* MatrixPowerSeries.resolventMatrix (transferMatrix h u v)) j=
      row j-PowerSeries.X*(
        row j*(if j.val=0 then PowerSeries.C v else PowerSeries.C u+PowerSeries.C v)+
        (if hj : 0<j.val then row (previous j) else 0)+
        (if hj : j.val<h then row (next j hj)*(PowerSeries.C u*PowerSeries.C v) else 0)) := by
  rw [MatrixPowerSeries.resolventMatrix,Matrix.vecMul_sub,Matrix.vecMul_one,
    Matrix.vecMul_smul,transferMatrix_map_C]
  change row j-PowerSeries.X*(row ᵥ* transferMatrix h (PowerSeries.C u) (PowerSeries.C v)) j=_
  rw [vecMul_transferMatrix]


/-- The same recurrence in the actual power-series ring. -/
theorem continuant_series_recurrence (u v : R) (m : ℕ) :
    (continuant u v (m+2) : PowerSeries R)=
      (1-(PowerSeries.C u+PowerSeries.C v)*PowerSeries.X)*
          (continuant u v (m+1) : PowerSeries R)-
        (PowerSeries.C u*PowerSeries.C v)*PowerSeries.X^2*
          (continuant u v m : PowerSeries R) := by
  simp only [continuant_recurrence,Polynomial.coe_sub,Polynomial.coe_mul,
    Polynomial.coe_one,Polynomial.coe_C,Polynomial.coe_X,Polynomial.coe_pow,
    map_add,map_mul,Polynomial.coe_add]

theorem denominator_series_eq_continuant (u v : R) (m : ℕ) :
    (denominator u v (m+1) : PowerSeries R)=
      (continuant u v (m+1) : PowerSeries R)+
        PowerSeries.C u*PowerSeries.X*(continuant u v m : PowerSeries R) := by
  rw [denominator_eq_continuant]
  simp only [Polynomial.coe_add,Polynomial.coe_mul,Polynomial.coe_C,Polynomial.coe_X]

/-- The explicit row certificate at every height, including the single-state case. -/
theorem continuantRow_resolvent (h : ℕ) (u v : R) :
    continuantRow h u v ᵥ* MatrixPowerSeries.resolventMatrix (transferMatrix h u v)=
      Pi.single 0 (denominator u v (h+1) : PowerSeries R) := by
  classical
  funext j
  rw [row_resolvent_apply]
  by_cases hj0 : j=0
  · subst j
    cases h with
    | zero =>
        simp only [continuantRow,Fin.val_zero,Nat.sub_zero,pow_zero,
          continuant_zero,Polynomial.coe_one,one_mul,Nat.lt_irrefl,
          ite_true,dite_false,add_zero,Pi.single_eq_same,Nat.zero_add,
          denominator_one,Polynomial.coe_sub,Polynomial.coe_mul,
          Polynomial.coe_C,Polynomial.coe_X]
        ring
    | succ h =>
        have H : (continuant u v (h+1) : PowerSeries R)-PowerSeries.X*(
            (continuant u v (h+1) : PowerSeries R)*PowerSeries.C v+
            PowerSeries.X*(continuant u v h : PowerSeries R)*
              (PowerSeries.C u*PowerSeries.C v))=
            (denominator u v (h+2) : PowerSeries R) := by
          rw [show h+2=(h+1)+1 by omega,denominator_series_eq_continuant]
          rw [show h+1+1=h+2 by omega,continuant_series_recurrence]
          ring
        simpa [continuantRow,next,previous] using H
  · have hjv : j.val≠0 := fun hz ↦ hj0 (Fin.ext hz)
    have hjp : 0<j.val := Nat.pos_of_ne_zero hjv
    have hrhs : (Pi.single (0 : Fin (h+1))
        (denominator u v (h+1) : PowerSeries R) : Fin (h+1) → PowerSeries R) j=0 := by
      simp [Pi.single_apply,hj0,Ne.symm hj0]
    rw [hrhs]
    by_cases hjh : j.val<h
    · have hk0 : h-j.val=(h-j.val-1)+1 := by omega
      have hkm : h-(j.val-1)=(h-j.val-1)+2 := by omega
      have hkp : h-(j.val+1)=h-j.val-1 := by omega
      have hp0 : (PowerSeries.X : PowerSeries R)^j.val=
          PowerSeries.X^(j.val-1)*PowerSeries.X := by
        conv_lhs => rw [show j.val=(j.val-1)+1 by omega,pow_succ]
      have hp1 : (PowerSeries.X : PowerSeries R)^(j.val+1)=
          PowerSeries.X^(j.val-1)*PowerSeries.X^2 := by
        rw [pow_succ,hp0]
        ring
      have H : (PowerSeries.X : PowerSeries R)^j.val*
            (continuant u v (h-j.val) : PowerSeries R)-PowerSeries.X*(
              PowerSeries.X^j.val*(continuant u v (h-j.val) : PowerSeries R)*
                (PowerSeries.C u+PowerSeries.C v)+
              PowerSeries.X^(j.val-1)*(continuant u v (h-(j.val-1)) : PowerSeries R)+
              PowerSeries.X^(j.val+1)*(continuant u v (h-(j.val+1)) : PowerSeries R)*
                (PowerSeries.C u*PowerSeries.C v))=0 := by
        rw [hk0,hkm,hkp,continuant_series_recurrence,hp0,hp1]
        ring
      simpa [continuantRow,previous,next,hjv,hjp,hjh] using H
    · have hjlast : j.val=h := by have hj' := j.isLt; omega
      have hp : (PowerSeries.X : PowerSeries R)^j.val=
          PowerSeries.X^(j.val-1)*PowerSeries.X := by
        conv_lhs => rw [show j.val=(j.val-1)+1 by omega,pow_succ]
      have hk0 : h-j.val=0 := by omega
      have hkm : h-(j.val-1)=1 := by omega
      have H : (PowerSeries.X : PowerSeries R)^j.val*
            (continuant u v (h-j.val) : PowerSeries R)-PowerSeries.X*(
              PowerSeries.X^j.val*(continuant u v (h-j.val) : PowerSeries R)*
                (PowerSeries.C u+PowerSeries.C v)+
              PowerSeries.X^(j.val-1)*(continuant u v (h-(j.val-1)) : PowerSeries R))=0 := by
        rw [hk0,hkm]
        simp only [continuant_zero,continuant_one,Polynomial.coe_one,
          Polynomial.coe_sub,Polynomial.coe_mul,Polynomial.coe_C,Polynomial.coe_X,
          map_add,Polynomial.coe_add,mul_one]
        rw [hp]
        ring
      simpa [continuantRow,previous,next,hjv,hjp,hjh] using H

/-- The row certificate proves the full generating-function identity. -/
theorem transfer_series_denominator (h : ℕ) (u v : R) :
    (denominator u v (h+1) : PowerSeries R)*
      PowerSeries.mk (fun N ↦ (transferMatrix h u v^N) 0 (Fin.last h))=
        PowerSeries.X^h := by
  have H := MatrixPowerSeries.row_certificate_entry (transferMatrix h u v)
    (continuantRow h u v) (denominator u v (h+1) : PowerSeries R) 0
    (continuantRow_resolvent h u v) (Fin.last h)
  rw [continuantRow_last] at H
  exact H

/-- The exact unrestricted coefficient formula used in Proposition5.1. -/
theorem transfer_power_entry (h s : ℕ) (u v : R) :
    (transferMatrix h u v^(s+h)) 0 (Fin.last h)=
      PowerSeries.coeff s (inverseDenominator u v (h+1)) := by
  apply MatrixPowerSeries.power_entry_of_row_certificate (transferMatrix h u v)
    (continuantRow h u v) (denominator u v (h+1) : PowerSeries R) 0 (Fin.last h) h
    (continuantRow_resolvent h u v) (continuantRow_last h u v)
  change Polynomial.constantCoeff (denominator u v (h+1))=1
  exact denominator_constantCoeff u v (h+1)

end PaperVerification.AlternatingForms.BigradedTransfer
end
end
end TAF_LiteralSource_0553

section TAF_LiteralSource_0554
/- Original module: PaperVerification.AlternatingFormsBigradedPrincipal -/


/-!
# Proposition 5.1 in its full printed parameter range

The left side uses the actual images of the original bidegree exterior-word
spans in the actual quotient by the two canonical odd quadrics.  The right
side is the coefficient of the genuine formal reciprocal of the printed
recurrence polynomial.  The proof uses the actual homogeneous good basis,
the complete weight-preserving bounded-walk equivalence, and the all-size
matrix resolvent identity.  No dimension, generic-rank, or counting premise
is introduced.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms

open Bidegree GoodPaths BigradedTransfer

/-- The pure combinatorial and algebraic good indices have identical data
and identical inequalities; this equivalence changes no selected position. -/
def goodPathExteriorIndexEquiv (k s : ℕ) : GoodOddIndex k s ≃ GoodPathIndex k s :=
  Equiv.refl _

@[simp] theorem goodPathExteriorIndexEquiv_degree {k s : ℕ} (I : GoodOddIndex k s) :
    indexADegree (goodPathExteriorIndexEquiv k s I).val.val=goodADegree I := rfl

def goodDegreeIndex {k s : ℕ} (I : GoodOddIndex k s) : Fin (s+1) :=
  ⟨goodADegree I,Nat.lt_succ_of_le (indexADegree_le I.val.val)⟩

theorem goodDegreeIndex_fiber_card (k s : ℕ) (p : Fin (s+1)) :
    Nat.card {I : GoodOddIndex k s // goodDegreeIndex I=p}=
      Nat.card {I : GoodOddIndex k s // goodADegree I=p.val} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun I => by
    change (⟨goodADegree I,_⟩ : Fin (s+1))=p ↔ goodADegree I=p.val
    exact Fin.ext_iff)

/-- Counting actual finite fibers is equivalent to summing their elements. -/
theorem sum_fiber_card_weight {I D R : Type*} [Fintype I] [Fintype D]
    [CommRing R] (δ : I → D) (f : D → R) :
    (∑ d,(Nat.card {i : I // δ i=d} : R)*f d)=∑ i,f (δ i) := by
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    using (Fintype.sum_fiberwise' δ f)

section ActualHilbertFunction

variable {K R : Type*} [Field K] [CharZero K] [CommRing R]

/-- The exact finite total-degree slice of the genuine quotient bigrading. -/
def bigradedHilbertSlice (k s : ℕ) (u v : R) : R :=
  ∑ p : Fin (s+1),(Module.finrank K (quotientASubdegree (K := K) k s p.val) : R)*
    u^p.val*v^(s-p.val)

theorem bigradedHilbertSlice_good_sum (k s : ℕ) (u v : R) :
    bigradedHilbertSlice (K := K) k s u v=
      ∑ I : GoodPathIndex k s,u^indexADegree I.val.val*v^(s-indexADegree I.val.val) := by
  calc
    _ = ∑ p : Fin (s+1),(Nat.card {I : GoodOddIndex k s // goodDegreeIndex I=p} : R)*
        (u^p.val*v^(s-p.val)) := by
      unfold bigradedHilbertSlice
      apply Finset.sum_congr rfl
      intro p hp
      rw [finrank_quotientASubdegree,←goodDegreeIndex_fiber_card]
      exact mul_assoc _ _ _
    _ = ∑ I : GoodOddIndex k s,u^(goodDegreeIndex I).val*v^(s-(goodDegreeIndex I).val) :=
      sum_fiber_card_weight goodDegreeIndex (fun p : Fin (s+1) => u^p.val*v^(s-p.val))
    _ = _ := Equiv.sum_comp (goodPathExteriorIndexEquiv k s)
      (fun I : GoodPathIndex k s => u^indexADegree I.val.val*v^(s-indexADegree I.val.val))

/-- The entire all-size coefficient identity, with the actual quotient pieces. -/
theorem bigradedHilbertSlice_coefficient (k s : ℕ) (hs : s≤k+1) (u v : R) :
    bigradedHilbertSlice (K := K) k s u v=
      PowerSeries.coeff s (inverseDenominator u v (k+2-s)) := by
  rw [bigradedHilbertSlice_good_sum,good_index_weight_sum k s hs]
  have hN : s+(k+1-s)=k+1 := by omega
  have hm : k+1-s+1=k+2-s := by omega
  simpa only [hN,hm] using transfer_power_entry (k+1-s) s u v

/-- Numbered Proposition 5.1, with the printed sum over all `p+q=s`.
`actualBigradedPiece` is defined from the original exterior words, and the
finite-antidiagonal identity proves equivalence to the finite slice above. -/
theorem paper_proposition_5_1 (k s : ℕ) (hs : s≤k+1) (u v : R) :
    (∑ pq∈Finset.antidiagonal s,
      (Module.finrank K (actualBigradedPiece (K := K) k pq.1 pq.2) : R)*
        u^pq.1*v^pq.2)=
      PowerSeries.coeff s (inverseDenominator u v (k+2-s)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ←Fin.sum_univ_eq_sum_range]
  calc
    _ = bigradedHilbertSlice (K := K) k s u v := by
      unfold bigradedHilbertSlice
      apply Finset.sum_congr rfl
      intro p hp
      have he : p.val+(s-p.val)=s := by have := p.isLt; omega
      have hdim := congrArg
        (fun d : ℕ => Module.finrank K (quotientASubdegree (K := K) k d p.val)) he
      exact congrArg (fun d : ℕ => (d : R)*u^p.val*v^(s-p.val)) hdim
    _ = _ := bigradedHilbertSlice_coefficient k s hs u v

end ActualHilbertFunction
end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0554

section TAF_LiteralSource_0555
/- Original module: TauCeti.Algebra.Module.GradedModule.Shift -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Shifting an internal grading

An internal grading may be regraded by a fixed shift `c`, so that the degree-`p` piece of the
shifted grading is the degree-`(p + c)` piece of the original one. The underlying module is
unchanged, and the shifted family is again an internal direct sum: reindexing the homogeneous
pieces along an equivalence of degrees only permutes the summands of `⨁ p, G.piece p`.
The degrees may form any additive group. Simultaneous shifts preserve the degree of a homogeneous
map when the degree group is commutative.

For integer degrees, shifting by one is the suspension `sA` in the `A∞` conventions. The
suspension leaves the underlying module unchanged and reindexes its homogeneous pieces.

## Main definitions

* `TauCeti.InternalGrading.shift`: the shift of an internal grading.

## Main results

* `TauCeti.LinearMap.isHomogeneous_shift_piece_iff`: shifting both gradings preserves degrees.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

namespace TauCeti

universe u v

namespace InternalGrading

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable {ι : Type} [DecidableEq ι] [AddGroup ι]

/-- The shift of an internal grading by `c`: its degree-`p` piece is the degree-`(p + c)` piece of
the original grading. The underlying module is unchanged. -/
def shift (G : InternalGrading R M ι) (c : ι) : InternalGrading R M ι where
  piece := fun p ↦ G.piece (Equiv.addRight c p)
  isInternal := by
    refine TauCeti.DirectSum.isInternal_of_lof
      (e := fun p ↦ LinearEquiv.refl R (G.piece (Equiv.addRight c p)))
      (E := (DirectSum.lequivCongrLeft R (Equiv.addRight c).symm).symm.trans
        (DirectSum.decomposeLinearEquiv G.piece).symm) ?_
    intro p x
    -- Express the generator family using the inverse reindexing, so the generator formula
    -- matches without unfolding the semireducible Equiv.addRight permutation.
    change (DirectSum.decomposeLinearEquiv G.piece).symm
      ((DirectSum.lequivCongrLeft R (Equiv.addRight c).symm).symm
        (DirectSum.lof R ι (fun p ↦ G.piece ((Equiv.addRight c).symm.symm p)) p x)) =
          (x : M)
    rw [DirectSum.lequivCongrLeft_symm_lof, DirectSum.decomposeLinearEquiv_symm_lof]

@[simp]
theorem shift_piece (G : InternalGrading R M ι) (c p : ι) :
    (G.shift c).piece p = G.piece (p + c) :=
  (rfl)

@[simp]
theorem shift_zero (G : InternalGrading R M ι) : G.shift 0 = G := by
  ext p
  simp

/-- Shifting twice shifts by the sum of the two amounts. -/
@[simp]
theorem shift_shift (G : InternalGrading R M ι) (c d : ι) :
    (G.shift c).shift d = G.shift (d + c) := by
  ext p
  simp [add_assoc]

/-- A Koszul twist preserves the original degree, expressed in any shifted grading. -/
theorem koszulTwist_mem_shift_piece {R : Type u} {M : Type v}
    [CommRing R] [AddCommMonoid M] [Module R M] (G : InternalGrading R M)
    {x : M} {e : ℤ} (hx : x ∈ G.piece e) (q c : ℤ) :
    G.koszulTwist q x ∈ (G.shift c).piece (e - c) := by
  rw [shift_piece, sub_add_cancel]
  exact G.koszulTwist_mem_piece hx q

/-- The Koszul twist of parameter `q` for a grading shifted by `c` differs from the unshifted
twist by the constant sign `(-1)^(q * c)`: a homogeneous element of degree `p` has degree `p - c`
after the shift. -/
theorem koszulTwist_shift {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]
    (G : InternalGrading R M) (c q : ℤ) :
    (G.shift c).koszulTwist q = (((q * c).negOnePow : ℤ) : R) • G.koszulTwist q := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  have hshift : x ∈ (G.shift c).piece (p - c) := by rwa [shift_piece, sub_add_cancel]
  rw [koszulTwist_apply_of_mem _ hshift, LinearMap.smul_apply, G.koszulTwist_apply_of_mem hx,
    smul_smul, ← Int.cast_mul, ← Units.val_mul, mul_sub, Int.negOnePow_sub]
  congr 3
  exact mul_comm _ _

/-- The degree-one Koszul twist of the suspended grading is the negative of the unsuspended one. -/
theorem koszulTwist_one_shift_one {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (G : InternalGrading R M) :
    (G.shift 1).koszulTwist 1 = -G.koszulTwist 1 := by
  rw [koszulTwist_shift]
  simp

end InternalGrading

/-- Shifting the source and the target internal grading by the same amount leaves the degree of a
homogeneous linear map unchanged. -/
theorem LinearMap.isHomogeneous_shift_piece_iff {R : Type u} {M N : Type*} [Semiring R]
    {ι : Type} [DecidableEq ι] [AddCommGroup ι]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {G : InternalGrading R M ι}
    {H : InternalGrading R N ι} {f : M →ₗ[R] N} {c q : ι} :
    LinearMap.IsHomogeneous f (G.shift c).piece (H.shift c).piece q ↔
      LinearMap.IsHomogeneous f G.piece H.piece q := by
  simp only [LinearMap.isHomogeneous_def, InternalGrading.shift_piece]
  constructor
  · intro hf p x hx
    simpa only [sub_add_cancel, sub_add_eq_add_sub] using hf (p - c) x (by rwa [sub_add_cancel])
  · intro hf p x hx
    rw [add_right_comm]
    exact hf _ x hx

end TauCeti
end
end TAF_LiteralSource_0555

section TAF_LiteralSource_0556
/- Original module: PaperVerification.AlternatingFormsIntegerGrading -/


/-!
# The actual integer grading of the exterior algebra

Natural exterior degrees are extended by zero in negative degrees.  The
internal direct-sum assertion is proved, so subsequent shifted Koszul
gradings are genuine gradings of the original modules.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms

section IntegerExtension

variable {K A : Type*} [Field K] [AddCommGroup A] [Module K A]

def nonnegativePiece (G : TauCeti.InternalGrading K A ℕ) (q : ℤ) : Submodule K A :=
  if 0 ≤ q then G.piece q.toNat else ⊥

@[simp] theorem nonnegativePiece_nat (G : TauCeti.InternalGrading K A ℕ) (q : ℕ) :
    nonnegativePiece G (q : ℤ) = G.piece q := by
  simp only [nonnegativePiece, Nat.cast_nonneg, if_pos, Int.toNat_natCast]

theorem nonnegativePiece_negative (G : TauCeti.InternalGrading K A ℕ)
    {q : ℤ} (hq : q < 0) : nonnegativePiece G q = ⊥ := by
  simp only [nonnegativePiece, if_neg (not_le_of_gt hq)]

/-- Extension by zero from natural to integer indices, with the direct-sum
property justified from the original homogeneous decomposition. -/
noncomputable def integerExtension (G : TauCeti.InternalGrading K A ℕ) :
    TauCeti.InternalGrading K A where
  piece := nonnegativePiece G
  isInternal := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · intro q
      by_cases hq : 0 ≤ q
      · rw [nonnegativePiece, if_pos hq]
        apply (G.isInternal.submodule_iSupIndep q.toNat).mono_right
        apply iSup_le
        intro r
        apply iSup_le
        intro hrq
        by_cases hr : 0 ≤ r
        · rw [nonnegativePiece, if_pos hr]
          exact le_iSup_of_le r.toNat (le_iSup_of_le (by omega : r.toNat ≠ q.toNat) le_rfl)
        · rw [nonnegativePiece, if_neg hr]
          exact bot_le
      · rw [nonnegativePiece, if_neg hq]
        exact disjoint_bot_left
    · apply top_unique
      rw [← G.isInternal.submodule_iSup_eq_top]
      exact iSup_le fun q => le_iSup_of_le (q : ℤ) (by rw [nonnegativePiece_nat])

@[simp] theorem integerExtension_piece (G : TauCeti.InternalGrading K A ℕ) (q : ℤ) :
    (integerExtension G).piece q = nonnegativePiece G q := rfl

/-- Finite-dimensional graded modules have genuine Laurent-polynomial Hilbert
series.  Finiteness of the support follows from the internal grading. -/
noncomputable def finiteHilbertLaurent (G : TauCeti.InternalGrading K A)
    [FiniteDimensional K A] : LaurentPolynomial ℤ :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.ofSupportFinite
    (fun q => (Module.finrank K (G.piece q) : ℤ))
    (G.finite_piece_ne_bot.subset (by
      intro q hq
      change (Module.finrank K (G.piece q) : ℤ) ≠ 0 at hq
      intro hbot
      rw [hbot, finrank_bot, Nat.cast_zero] at hq
      exact hq rfl))

@[simp] theorem finiteHilbertLaurent_coeff (G : TauCeti.InternalGrading K A)
    [FiniteDimensional K A] (q : ℤ) :
    (finiteHilbertLaurent G).coeff q = (Module.finrank K (G.piece q) : ℤ) := rfl

end IntegerExtension

section ExteriorIntegerGrading

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The whole exterior algebra has a finite basis, indexed by the subsets
of a finite basis of the original vector space. -/
instance exteriorAlgebra_finite [FiniteDimensional K M] :
    FiniteDimensional K (ExteriorAlgebra K M) :=
  Module.Finite.of_basis (Module.finBasis K M).ExteriorAlgebra

noncomputable def exteriorNaturalGrading :
    TauCeti.InternalGrading K (ExteriorAlgebra K M) ℕ :=
  .ofDecomposition (fun q : ℕ => ⋀[K]^q M)

noncomputable def exteriorIntegerGrading : TauCeti.InternalGrading K (ExteriorAlgebra K M) :=
  integerExtension (exteriorNaturalGrading (K := K) (M := M))

@[simp] theorem exteriorIntegerGrading_piece_nat (q : ℕ) :
    (exteriorIntegerGrading (K := K) (M := M)).piece (q : ℤ) = ⋀[K]^q M := by
  simp only [exteriorIntegerGrading, integerExtension_piece, nonnegativePiece_nat,
    exteriorNaturalGrading, TauCeti.InternalGrading.ofDecomposition_piece]

theorem exteriorIntegerGrading_piece_negative {q : ℤ} (hq : q < 0) :
    (exteriorIntegerGrading (K := K) (M := M)).piece q = ⊥ :=
  nonnegativePiece_negative _ hq

theorem exteriorIntegerGrading_piece_of_nonneg {q : ℤ} (hq : 0 ≤ q) :
    (exteriorIntegerGrading (K := K) (M := M)).piece q = ⋀[K]^q.toNat M := by
  simp only [exteriorIntegerGrading, integerExtension_piece, nonnegativePiece, if_pos hq,
    exteriorNaturalGrading, TauCeti.InternalGrading.ofDecomposition_piece]

def twoFormMultiplication (f : ⋀[K]^2 M) : Module.End K (ExteriorAlgebra K M) :=
  LinearMap.mulLeft K (f : ExteriorAlgebra K M)

theorem twoFormMultiplication_homogeneous (f : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous (twoFormMultiplication f)
      exteriorIntegerGrading.piece exteriorIntegerGrading.piece 2 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  by_cases hq : 0 ≤ q
  · rw [exteriorIntegerGrading_piece_of_nonneg hq] at ha
    rw [exteriorIntegerGrading_piece_of_nonneg (by omega : 0 ≤ q + 2)]
    have hd : (q + 2).toNat = 2 + q.toNat := by omega
    rw [hd]
    exact SetLike.mul_mem_graded f.property ha
  · rw [exteriorIntegerGrading_piece_negative (by omega : q < 0)] at ha
    have ha0 : a = 0 := ha
    rw [ha0, map_zero]
    exact Submodule.zero_mem _

theorem twoFormMultiplication_commute (f g : ⋀[K]^2 M) :
    Commute (twoFormMultiplication f) (twoFormMultiplication g) := by
  change twoFormMultiplication f * twoFormMultiplication g=
    twoFormMultiplication g * twoFormMultiplication f
  apply LinearMap.ext
  intro a
  change (f : ExteriorAlgebra K M) * (g * a) = (g : ExteriorAlgebra K M) * (f * a)
  rw [← mul_assoc, (twoForm_commute f g).eq, mul_assoc]

variable [FiniteDimensional K M]

theorem exteriorIntegerGrading_piece_above {q : ℤ}
    (hq : (Module.finrank K M : ℤ) < q) :
    (exteriorIntegerGrading (K := K) (M := M)).piece q = ⊥ := by
  rw [exteriorIntegerGrading_piece_of_nonneg (by omega : 0 ≤ q)]
  apply Submodule.finrank_eq_zero.mp
  rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt (by omega)]

theorem exteriorIntegerGrading_finrank (q : ℤ) :
    Module.finrank K ((exteriorIntegerGrading (K := K) (M := M)).piece q) =
      if 0 ≤ q then (Module.finrank K M).choose q.toNat else 0 := by
  by_cases hq : 0 ≤ q
  · rw [if_pos hq, exteriorIntegerGrading_piece_of_nonneg hq, exteriorPower.finrank_eq]
  · rw [if_neg hq, exteriorIntegerGrading_piece_negative (by omega : q < 0), finrank_bot]

end ExteriorIntegerGrading

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0556

section TAF_LiteralSource_0557
/- Original module: PaperVerification.AlternatingFormsKoszulResolution -/


/-!
# The actual two-variable Koszul resolution

The resolution in this file is over the genuine polynomial ring `K[u,v]`.
Its terms and maps are explicit.  The middle exactness proof uses primality
of the variable `u`; no homological assertion is introduced as an axiom.
The resulting `ProjectiveResolution` computes Mathlib's derived tensor
functor, and therefore supplies the comparison required to call the
homology in Proposition 5.4 graded Betti spaces.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms

open CategoryTheory CategoryTheory.Limits

section PairComplex

universe u v

variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module R A]

/-- The first differential for two commuting operators. -/
def pairFirstDifferential (F G : Module.End R A) : A × A →ₗ[R] A :=
  F.coprod G

/-- The second differential, with the usual Koszul sign. -/
def pairSecondDifferential (F G : Module.End R A) : A →ₗ[R] A × A :=
  (-G).prod F

@[simp] theorem pairFirstDifferential_apply (F G : Module.End R A) (a : A × A) :
    pairFirstDifferential F G a = F a.1 + G a.2 := rfl

@[simp] theorem pairSecondDifferential_apply (F G : Module.End R A) (a : A) :
    pairSecondDifferential F G a = (-G a, F a) := rfl

theorem pairDifferentials_comp (F G : Module.End R A) (hFG : Commute F G) :
    (pairFirstDifferential F G).comp (pairSecondDifferential F G) = 0 := by
  ext a
  have h := congrArg (fun T : Module.End R A => T a) hFG.eq
  change F (G a) = G (F a) at h
  change F (-G a) + G (F a) = 0
  rw [map_neg, h, neg_add_cancel]

/-- Terms of a length-two complex, with an actual zero module thereafter. -/
def pairTerm (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A] :
    ℕ → ModuleCat.{v} R
  | 0 => ModuleCat.of R A
  | 1 => ModuleCat.of R (A × A)
  | 2 => ModuleCat.of R A
  | _ + 3 => ModuleCat.of R (⊥ : Submodule R A)

def pairDifferential (F G : Module.End R A) :
    (n : ℕ) → pairTerm R A (n + 1) ⟶ pairTerm R A n
  | 0 => ModuleCat.ofHom (pairFirstDifferential F G)
  | 1 => ModuleCat.ofHom (pairSecondDifferential F G)
  | _ + 2 => 0

theorem pairDifferential_comp (F G : Module.End R A) (hFG : Commute F G) (n : ℕ) :
    pairDifferential F G (n + 1) ≫ pairDifferential F G n = 0 := by
  cases n with
  | zero => exact ModuleCat.hom_ext (pairDifferentials_comp F G hFG)
  | succ n =>
    change (0 : pairTerm R A (n+3) ⟶ pairTerm R A (n+2)) ≫
      pairDifferential F G (n+1)=0
    exact CategoryTheory.Limits.zero_comp

/-- The literal Koszul complex of two commuting operators. -/
def pairComplex (F G : Module.End R A) (hFG : Commute F G) :
    ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (pairTerm R A) (pairDifferential F G)
    (pairDifferential_comp F G hFG)

@[simp] theorem pairComplex_X (F G : Module.End R A) (hFG : Commute F G) (n : ℕ) :
    (pairComplex F G hFG).X n = pairTerm R A n := rfl

@[simp] theorem pairComplex_d (F G : Module.End R A) (hFG : Commute F G) (n : ℕ) :
    (pairComplex F G hFG).d (n + 1) n = pairDifferential F G n := by
  simp [pairComplex]

theorem pairComplex_isZero_X (F G : Module.End R A) (hFG : Commute F G)
    {n : ℕ} (hn : 2 < n) : IsZero ((pairComplex F G hFG).X n) := by
  have hn' : n = (n - 3) + 3 := by omega
  rw [hn']
  change IsZero (ModuleCat.of R (⊥ : Submodule R A))
  exact ModuleCat.isZero_of_subsingleton _

theorem pairComplex_isZero_homology (F G : Module.End R A) (hFG : Commute F G)
    {n : ℕ} (hn : 2 < n) : IsZero ((pairComplex F G hFG).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero (pairComplex_isZero_X F G hFG hn)).isZero_homology

end PairComplex

section PolynomialResolution

universe u

variable (K : Type u) [Field K]

abbrev PairPolynomial := MvPolynomial (Fin 2) K

def pairPolynomialFirst : Module.End (PairPolynomial K) (PairPolynomial K) :=
  LinearMap.mulLeft (PairPolynomial K) (MvPolynomial.X 0)

def pairPolynomialSecond : Module.End (PairPolynomial K) (PairPolynomial K) :=
  LinearMap.mulLeft (PairPolynomial K) (MvPolynomial.X 1)

theorem pairPolynomial_commute : Commute (pairPolynomialFirst K) (pairPolynomialSecond K) := by
  change pairPolynomialFirst K * pairPolynomialSecond K =
    pairPolynomialSecond K * pairPolynomialFirst K
  apply LinearMap.ext
  intro p
  change MvPolynomial.X 0 * (MvPolynomial.X 1 * p) =
    MvPolynomial.X 1 * (MvPolynomial.X 0 * p)
  ring

/-- The maximal ideal `(u,v)` of the polynomial ring, not an abstract residue field. -/
def pairResidueIdeal : Ideal (PairPolynomial K) :=
  Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}

abbrev PairResidue := PairPolynomial K ⧸ pairResidueIdeal K

theorem pairResidueIdeal_eq_ker_constantCoeff :
    pairResidueIdeal K = RingHom.ker (MvPolynomial.constantCoeff : PairPolynomial K →+* K) := by
  classical
  have hset : ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (PairPolynomial K)) =
      MvPolynomial.X '' (Set.univ : Set (Fin 2)) := by
    ext p
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, Set.mem_univ _, rfl⟩
      · exact ⟨1, Set.mem_univ _, rfl⟩
    · rintro ⟨i, _, rfl⟩
      fin_cases i <;> simp
  unfold pairResidueIdeal
  rw [hset, MvPolynomial.span_X_image_eq_ker_aeval_ite_mem]
  ext p
  simp only [RingHom.mem_ker, Set.compl_univ, Set.mem_empty_iff_false, if_false,
    MvPolynomial.aeval_zero', MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_zero]

/-- The residue in the displayed resolution is precisely the coefficient
field with both variables acting as zero. -/
def pairConstantCoefficient : PairPolynomial K →ₐ[K] K :=
  { MvPolynomial.constantCoeff with
    commutes' := fun c => MvPolynomial.constantCoeff_C _ c }

theorem pairConstantCoefficient_surjective :
    Function.Surjective (pairConstantCoefficient K) := by
  intro c
  exact ⟨MvPolynomial.C c, by simp [pairConstantCoefficient]⟩

theorem pairResidueIdeal_eq_ker_pairConstantCoefficient :
    pairResidueIdeal K=RingHom.ker (pairConstantCoefficient K) :=
  pairResidueIdeal_eq_ker_constantCoeff K

noncomputable def pairResidueEquivField : PairResidue K ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (pairResidueIdeal_eq_ker_pairConstantCoefficient K)).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := pairConstantCoefficient K) (pairConstantCoefficient_surjective K))

@[simp] theorem pairResidueEquivField_mk (p : PairPolynomial K) :
    pairResidueEquivField K (Ideal.Quotient.mk (pairResidueIdeal K) p) =
      MvPolynomial.constantCoeff p := by
  rfl

/-- The coefficient field equipped with the actual origin action of the
polynomial ring. The synonym records this particular polynomial-module
structure without replacing the underlying field. -/
def PairOriginModule := K

instance : AddCommGroup (PairOriginModule K) :=
  inferInstanceAs (AddCommGroup K)

instance : Module (PairPolynomial K) (PairOriginModule K) :=
  Module.compHom K (pairConstantCoefficient K).toRingHom

def pairOriginValue (a : PairOriginModule K) : K := a

@[simp] theorem pairOriginValue_smul (p : PairPolynomial K) (a : PairOriginModule K) :
    pairOriginValue K (p • a) = MvPolynomial.constantCoeff p * pairOriginValue K a := rfl

/-- The augmentation quotient and the coefficient field are isomorphic as
modules over the original polynomial ring, with its origin action. -/
def pairResidueOriginEquiv : PairResidue K ≃ₗ[PairPolynomial K] PairOriginModule K where
  toFun := pairResidueEquivField K
  invFun := (pairResidueEquivField K).symm
  left_inv := (pairResidueEquivField K).left_inv
  right_inv := (pairResidueEquivField K).right_inv
  map_add' := (pairResidueEquivField K).map_add
  map_smul' p x := by
    change pairResidueEquivField K (Ideal.Quotient.mk (pairResidueIdeal K) p * x) =
      pairConstantCoefficient K p * pairResidueEquivField K x
    rw [map_mul, pairResidueEquivField_mk]
    rfl

@[simp] theorem pairResidueOriginEquiv_mk (p : PairPolynomial K) :
    pairResidueOriginEquiv K (Ideal.Quotient.mk (pairResidueIdeal K) p) =
      ((MvPolynomial.constantCoeff : PairPolynomial K →+* K) p : PairOriginModule K) :=
  pairResidueEquivField_mk K p

def pairPolynomialComplex : ChainComplex (ModuleCat (PairPolynomial K)) ℕ :=
  pairComplex (pairPolynomialFirst K) (pairPolynomialSecond K) (pairPolynomial_commute K)

theorem pairPolynomial_range_first :
    LinearMap.range
      (pairFirstDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) =
      pairResidueIdeal K := by
  ext p
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    apply Ideal.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    change a * MvPolynomial.X 0 + b * MvPolynomial.X 1 =
      MvPolynomial.X 0 * a + MvPolynomial.X 1 * b
    ring
  · intro hp
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hp
    refine ⟨(a, b), ?_⟩
    change MvPolynomial.X 0 * a + MvPolynomial.X 1 * b = p
    rw [← hab]
    ring

/-- Exactness of `P → P² → P` for the independent variables of `P=K[u,v]`. -/
theorem pairPolynomial_exact :
    Function.Exact
      (pairSecondDifferential (pairPolynomialFirst K) (pairPolynomialSecond K))
      (pairFirstDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) := by
  intro a
  constructor
  · intro ha
    change MvPolynomial.X 0 * a.1 + MvPolynomial.X 1 * a.2 = 0 at ha
    have hu : (MvPolynomial.X (R := K) (0 : Fin 2)) ≠ 0 := MvPolynomial.X_ne_zero 0
    have hdiv : (MvPolynomial.X (R := K) (0 : Fin 2)) ∣ MvPolynomial.X 1 * a.2 := by
      refine ⟨-a.1, ?_⟩
      linear_combination ha
    have hb : (MvPolynomial.X (R := K) (0 : Fin 2)) ∣ a.2 := by
      rcases (MvPolynomial.prime_X (R := K) (i := (0 : Fin 2))).dvd_or_dvd hdiv with h | h
      · exact False.elim (by simpa using h)
      · exact h
    obtain ⟨c, hc⟩ := hb
    have hac : a.1 = -(MvPolynomial.X 1 * c) := by
      apply mul_left_cancel₀ hu
      rw [hc] at ha
      linear_combination ha
    refine ⟨c, ?_⟩
    apply Prod.ext
    · exact hac.symm
    · exact hc.symm
  · rintro ⟨c, rfl⟩
    exact congrArg (fun T : PairPolynomial K →ₗ[PairPolynomial K] PairPolynomial K => T c)
      (pairDifferentials_comp _ _ (pairPolynomial_commute K))

theorem pairPolynomial_second_injective :
    Function.Injective
      (pairSecondDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) := by
  intro a b hab
  have h := congrArg Prod.snd hab
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := K) (0 : Fin 2)) h

theorem pairPolynomial_exactAt_succ (n : ℕ) :
    (pairPolynomialComplex K).ExactAt (n + 1) := by
  cases n with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range
      (pairSecondDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) =
      LinearMap.ker (pairFirstDifferential (pairPolynomialFirst K) (pairPolynomialSecond K))
    exact (LinearMap.exact_iff.mp (pairPolynomial_exact K)).symm
  | succ n =>
    cases n with
    | zero =>
      rw [HomologicalComplex.exactAt_iff' _ 3 2 1 (by simp) (by simp),
        ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      intro a
      constructor
      · intro ha
        have ha0 : a = 0 := pairPolynomial_second_injective K
          (ha.trans (map_zero _).symm)
        exact ⟨0, ha0.symm⟩
      · rintro ⟨b, rfl⟩
        exact map_zero _
    | succ n =>
      exact HomologicalComplex.ExactAt.of_isZero
        (pairComplex_isZero_X _ _ _ (by omega))

def pairPolynomialAugmentation :
    (pairPolynomialComplex K).X 0 ⟶ ModuleCat.of (PairPolynomial K) (PairResidue K) :=
  ModuleCat.ofHom (pairResidueIdeal K).mkQ

theorem pairPolynomial_d_augmentation :
    (pairPolynomialComplex K).d 1 0 ≫ pairPolynomialAugmentation K = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.range_le_ker_iff.mp
  change LinearMap.range
    (pairFirstDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) ≤
      LinearMap.ker (pairResidueIdeal K).mkQ
  rw [Submodule.ker_mkQ]
  exact le_of_eq (pairPolynomial_range_first K)

theorem pairPolynomial_augmentation_exact :
    (ShortComplex.mk _ _ (pairPolynomial_d_augmentation K)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range
      (pairFirstDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) =
    LinearMap.ker (pairResidueIdeal K).mkQ
  rw [Submodule.ker_mkQ, pairPolynomial_range_first]

instance pairPolynomial_augmentation_epi : Epi (pairPolynomialAugmentation K) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- A genuine free resolution of `K[u,v]/(u,v)` with exactly three nonzero terms. -/
noncomputable def pairPolynomialResolution :
    ProjectiveResolution (ModuleCat.of (PairPolynomial K) (PairResidue K)) where
  complex := pairPolynomialComplex K
  projective n := by
    cases n with
    | zero =>
      change Projective (ModuleCat.of (PairPolynomial K) (PairPolynomial K))
      infer_instance
    | succ n =>
      cases n with
      | zero =>
        change Projective (ModuleCat.of (PairPolynomial K) (PairPolynomial K × PairPolynomial K))
        infer_instance
      | succ n =>
        cases n with
        | zero =>
          change Projective (ModuleCat.of (PairPolynomial K) (PairPolynomial K))
          infer_instance
        | succ n => exact (pairComplex_isZero_X _ _ _ (by omega)).projective
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨pairPolynomialAugmentation K, pairPolynomial_d_augmentation K⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk _ _ (pairPolynomial_d_augmentation K)).Exact ∧
          Epi (pairPolynomialAugmentation K)
        exact ⟨pairPolynomial_augmentation_exact K, inferInstance⟩
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact pairPolynomial_exactAt_succ K n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- Derived tensor is computed by the displayed free resolution.  The target
is the actual homology of `E ⊗_P K(u,v)`, not a stipulated Betti dimension. -/
noncomputable def pairPolynomialTorIso (E : ModuleCat (PairPolynomial K)) (i : ℕ) :
    (((Tor (ModuleCat (PairPolynomial K)) i).obj E).obj
        (ModuleCat.of (PairPolynomial K) (PairResidue K))) ≅
      ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat (PairPolynomial K))).obj E).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (pairPolynomialResolution K).complex).homology i :=
  (pairPolynomialResolution K).isoLeftDerivedObj _ i

/-- There are no later derived tensor terms for any polynomial module,
because the actual displayed free resolution stops in degree two. -/
theorem pairPolynomialTor_isZero_above (E : ModuleCat (PairPolynomial K))
    {i : ℕ} (hi : 2 < i) :
    IsZero ((((Tor (ModuleCat (PairPolynomial K)) i).obj E).obj
      (ModuleCat.of (PairPolynomial K) (PairResidue K)))) := by
  let F := (CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat (PairPolynomial K))).obj E
  have hterm : IsZero (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (pairPolynomialResolution K).complex).X i) :=
    F.map_isZero (pairComplex_isZero_X (pairPolynomialFirst K)
      (pairPolynomialSecond K) (pairPolynomial_commute K) hi)
  exact (HomologicalComplex.ExactAt.of_isZero hterm).isZero_homology.of_iso
    (pairPolynomialTorIso K E i)

end PolynomialResolution

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0557

section TAF_LiteralSource_0558
/- Original module: TauCeti.Algebra.Module.GradedModule.Prod -/
/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/


/-!
# Products of internally graded modules

The product of two internally graded modules has the componentwise grading. This supplies
the grading on finite biproducts and mapping cones of curved differential graded modules.
-/

public section

open scoped DirectSum

namespace TauCeti.InternalGrading

universe u v w

variable {R : Type u} [Semiring R] {M : Type v} {N : Type w}
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  (G : InternalGrading R M) (H : InternalGrading R N)

private def prodInl (p : ℤ) : G.piece p →ₗ[R] (G.piece p).prod (H.piece p) :=
  LinearMap.codRestrict _ ((LinearMap.inl R M N).comp (G.piece p).subtype)
    (fun x ↦ ⟨x.property, (H.piece p).zero_mem⟩)

private def prodInr (p : ℤ) : H.piece p →ₗ[R] (G.piece p).prod (H.piece p) :=
  LinearMap.codRestrict _ ((LinearMap.inr R M N).comp (H.piece p).subtype)
    (fun x ↦ ⟨(G.piece p).zero_mem, x.property⟩)

private noncomputable def prodDecompose :
    M × N →ₗ[R] ⨁ p, (G.piece p).prod (H.piece p) :=
  (DirectSum.lmap (prodInl G H)).comp
      ((DirectSum.decomposeLinearEquiv G.piece).toLinearMap.comp (LinearMap.fst R M N)) +
    (DirectSum.lmap (prodInr G H)).comp
      ((DirectSum.decomposeLinearEquiv H.piece).toLinearMap.comp (LinearMap.snd R M N))

private theorem prodDecompose_of_mem (p : ℤ) (x : M) (y : N)
    (hx : x ∈ G.piece p) (hy : y ∈ H.piece p) :
    prodDecompose G H (x, y) =
      DirectSum.lof R ℤ (fun q ↦ (G.piece q).prod (H.piece q)) p ⟨(x, y), hx, hy⟩ := by
  simp only [prodDecompose, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearEquiv.coe_toLinearMap]
  rw [DirectSum.decomposeLinearEquiv_apply_coe G.piece p ⟨x, hx⟩,
    DirectSum.decomposeLinearEquiv_apply_coe H.piece p ⟨y, hy⟩,
    DirectSum.lmap_lof, DirectSum.lmap_lof, ← map_add]
  congr 1
  apply Subtype.ext
  -- Reduce the private restricted inclusions and their subtype coercions to pair inclusions.
  change (x, 0) + (0, y) = (x, y)
  simp

private theorem coeLinearMap_comp_prodDecompose :
    (DirectSum.coeLinearMap fun p ↦ (G.piece p).prod (H.piece p)).comp
      (prodDecompose G H) = LinearMap.id := by
  apply LinearMap.prod_ext
  · apply G.linearMap_ext
    intro p x hx
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.id_apply]
    rw [prodDecompose_of_mem G H p x 0 hx (H.piece p).zero_mem,
      DirectSum.coeLinearMap_lof]
  · apply H.linearMap_ext
    intro p y hy
    simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.id_apply]
    rw [prodDecompose_of_mem G H p 0 y (G.piece p).zero_mem hy,
      DirectSum.coeLinearMap_lof]

private theorem prodDecompose_comp_coeLinearMap :
    (prodDecompose G H).comp
      (DirectSum.coeLinearMap fun p ↦ (G.piece p).prod (H.piece p)) = LinearMap.id := by
  apply DirectSum.linearMap_ext R
  intro p
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
  exact prodDecompose_of_mem G H p x.1.1 x.1.2 x.2.1 x.2.2

/-- The componentwise internal grading on a product of modules. -/
noncomputable def prod : InternalGrading R (M × N) := by
  letI := DirectSum.Decomposition.ofLinearMap (fun p ↦ (G.piece p).prod (H.piece p))
    (prodDecompose G H)
    (coeLinearMap_comp_prodDecompose G H) (prodDecompose_comp_coeLinearMap G H)
  exact InternalGrading.ofDecomposition fun p ↦ (G.piece p).prod (H.piece p)

/-- The degree-`p` piece of the product is the product of the degree-`p` pieces. -/
@[simp]
theorem prod_piece (p : ℤ) : (G.prod H).piece p = (G.piece p).prod (H.piece p) := by
  simp only [prod, ofDecomposition_piece]

end TauCeti.InternalGrading
end
end TAF_LiteralSource_0558

section TAF_LiteralSource_0559
/- Original module: PaperVerification.AlternatingFormsKoszulHomology -/


/-!
# Graded homology and the Euler identity for the two-form complex

The homology is the actual kernel modulo the actual image, equipped with
the grading inherited from the shifted exterior modules.  The dimension
identity is proved on each homogeneous component by rank-nullity.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

section GradedLinearAlgebra

variable {K A B : Type*} [Field K]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]

theorem homogeneous_image_piece
    (G : TauCeti.InternalGrading K A) (H : TauCeti.InternalGrading K B)
    (f : A →ₗ[K] B)
    (hf : TauCeti.LinearMap.IsHomogeneous f G.piece H.piece 0) (q : ℤ) :
    (G.piece q).map f = LinearMap.range f ⊓ H.piece q := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, by simpa using hf.map_mem hx⟩
  · rintro y ⟨⟨x, hxy⟩, hy⟩
    refine ⟨(DirectSum.decompose G.piece x q : A),
      (DirectSum.decompose G.piece x q).property, ?_⟩
    have h := hf.map_decompose q x
    rw [add_zero, hxy, DirectSum.decompose_of_mem_same H.piece hy] at h
    exact h

/-- Rank-nullity after restriction to a genuine homogeneous component. -/
theorem homogeneous_piece_rank_nullity
    (G : TauCeti.InternalGrading K A) (H : TauCeti.InternalGrading K B)
    (f : A →ₗ[K] B)
    (hf : TauCeti.LinearMap.IsHomogeneous f G.piece H.piece 0) (q : ℤ) :
    Module.finrank K (G.piece q) =
      Module.finrank K ((G.ker hf).piece q) +
        Module.finrank K (LinearMap.range f ⊓ H.piece q : Submodule K B) := by
  let P := G.piece q
  let fq := f.domRestrict P
  have hrange : LinearMap.range fq = LinearMap.range f ⊓ H.piece q := by
    change LinearMap.range (f.comp P.subtype) = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact homogeneous_image_piece G H f hf q
  have hker : (LinearMap.ker fq).map P.subtype = LinearMap.ker f ⊓ P := by
    change (LinearMap.ker (f.comp P.subtype)).map P.subtype = _
    rw [LinearMap.ker_comp, Submodule.map_comap_subtype, inf_comm]
  have hpiece : Module.finrank K ((G.ker hf).piece q) =
      Module.finrank K (LinearMap.ker f ⊓ P : Submodule K A) := by
    rw [← Submodule.finrank_map_subtype_eq (LinearMap.ker f) ((G.ker hf).piece q)]
    have he : (G.ker hf).piece q=P.comap (LinearMap.ker f).subtype := by
      ext z
      exact TauCeti.InternalGrading.mem_ker_piece G hf
    rw [he]
    rw [Submodule.map_comap_subtype]
  have h := fq.finrank_range_add_finrank_ker
  rw [hrange, ← Submodule.finrank_map_subtype_eq P (LinearMap.ker fq), hker,
    ← hpiece] at h
  simpa only [P,add_comm] using h.symm

/-- A homogeneous quotient has exactly the expected component kernel;
arbitrary representatives are projected to the required degree. -/
theorem homogeneous_quotient_piece_dimension
    (G : TauCeti.InternalGrading K A) (U : Submodule K A)
    (hU : DirectSum.SetLike.IsHomogeneous G.piece U) (q : ℤ) :
    Module.finrank K (G.piece q) =
      Module.finrank K ((G.quotient U hU).piece q) +
        Module.finrank K (U ⊓ G.piece q : Submodule K A) := by
  let P := G.piece q
  let π := U.mkQ.domRestrict P
  have hrange : LinearMap.range π = (G.quotient U hU).piece q := by
    change LinearMap.range (U.mkQ.comp P.subtype) = _
    rw [LinearMap.range_comp, Submodule.range_subtype]
    simpa only [TauCeti.InternalGrading.quotient_piece,LinearMap.restrictScalars_self] using
      (show P.map U.mkQ = (G.piece q).map U.mkQ from rfl)
  have hker : (LinearMap.ker π).map P.subtype = U ⊓ P := by
    change (LinearMap.ker (U.mkQ.comp P.subtype)).map P.subtype = _
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.map_comap_subtype, inf_comm]
  have h := π.finrank_range_add_finrank_ker
  rw [hrange, ← Submodule.finrank_map_subtype_eq P (LinearMap.ker π), hker] at h
  exact h.symm

end GradedLinearAlgebra

section GradedShortComplex

variable {K A₂ A₁ A₀ : Type*} [Field K]
  [AddCommGroup A₂] [Module K A₂] [FiniteDimensional K A₂]
  [AddCommGroup A₁] [Module K A₁] [FiniteDimensional K A₁]
  [AddCommGroup A₀] [Module K A₀] [FiniteDimensional K A₀]

variable (G₂ : TauCeti.InternalGrading K A₂) (G₁ : TauCeti.InternalGrading K A₁)
  (G₀ : TauCeti.InternalGrading K A₀)
  (d₂ : A₂ →ₗ[K] A₁) (d₁ : A₁ →ₗ[K] A₀) (hd : d₁.comp d₂ = 0)
  (hd₂ : TauCeti.LinearMap.IsHomogeneous d₂ G₂.piece G₁.piece 0)
  (hd₁ : TauCeti.LinearMap.IsHomogeneous d₁ G₁.piece G₀.piece 0)

def shortComplexToCycles : A₂ →ₗ[K] LinearMap.ker d₁ :=
  d₂.codRestrict _ (fun a => by
    change d₁ (d₂ a) = 0
    exact LinearMap.congr_fun hd a)

include hd₂ in
theorem shortComplexToCycles_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (shortComplexToCycles d₂ d₁ hd)
      G₂.piece (G₁.ker hd₁).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  rw [TauCeti.InternalGrading.mem_ker_piece]
  exact hd₂.map_mem ha

def shortComplexH₀Grading :
    TauCeti.InternalGrading K (A₀ ⧸ LinearMap.range d₁) :=
  G₀.quotient (LinearMap.range d₁) hd₁.isHomogeneous_range

def shortComplexH₁Grading : TauCeti.InternalGrading K
    (LinearMap.ker d₁ ⧸ LinearMap.range (shortComplexToCycles d₂ d₁ hd)) :=
  (G₁.ker hd₁).quotient (LinearMap.range (shortComplexToCycles d₂ d₁ hd))
    (shortComplexToCycles_homogeneous G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁).isHomogeneous_range

def shortComplexH₂Grading : TauCeti.InternalGrading K
    (LinearMap.ker (shortComplexToCycles d₂ d₁ hd)) :=
  G₂.ker (shortComplexToCycles_homogeneous G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁)

/-- Euler characteristic in every integer degree, with all three homology
spaces defined by the displayed maps. -/
theorem shortComplex_homogeneous_euler (q : ℤ) :
    (Module.finrank K ((shortComplexH₀Grading G₁ G₀ d₁ hd₁).piece q) : ℤ) -
      Module.finrank K ((shortComplexH₁Grading G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁).piece q) +
      Module.finrank K ((shortComplexH₂Grading G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁).piece q) =
    (Module.finrank K (G₀.piece q) : ℤ) - Module.finrank K (G₁.piece q) +
      Module.finrank K (G₂.piece q) := by
  have h₀ := homogeneous_quotient_piece_dimension G₀ (LinearMap.range d₁)
    hd₁.isHomogeneous_range q
  have h₁ := homogeneous_piece_rank_nullity G₁ G₀ d₁ hd₁ q
  have h₂ := homogeneous_quotient_piece_dimension (G₁.ker hd₁)
    (LinearMap.range (shortComplexToCycles d₂ d₁ hd))
    (shortComplexToCycles_homogeneous G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁).isHomogeneous_range q
  have h₃ := homogeneous_piece_rank_nullity G₂ (G₁.ker hd₁)
    (shortComplexToCycles d₂ d₁ hd)
    (shortComplexToCycles_homogeneous G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁) q
  change (Module.finrank K ((G₀.quotient _ _).piece q) : ℤ) -
      Module.finrank K (((G₁.ker hd₁).quotient _ _).piece q) +
      Module.finrank K ((G₂.ker _).piece q) = _
  omega

/-- The coefficientwise Euler identity is an equality of actual finite
Laurent-polynomial Hilbert series. -/
theorem shortComplex_hilbert_euler :
    finiteHilbertLaurent (shortComplexH₀Grading G₁ G₀ d₁ hd₁) -
      finiteHilbertLaurent (shortComplexH₁Grading G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁) +
      finiteHilbertLaurent (shortComplexH₂Grading G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁) =
    finiteHilbertLaurent G₀ - finiteHilbertLaurent G₁ + finiteHilbertLaurent G₂ := by
  ext q
  exact shortComplex_homogeneous_euler G₂ G₁ G₀ d₂ d₁ hd hd₂ hd₁ q

end GradedShortComplex

section ExteriorKoszul

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

def exteriorKoszulFirst (f g : ⋀[K]^2 M) :
    ExteriorAlgebra K M × ExteriorAlgebra K M →ₗ[K] ExteriorAlgebra K M :=
  pairFirstDifferential (twoFormMultiplication f) (twoFormMultiplication g)

def exteriorKoszulSecond (f g : ⋀[K]^2 M) :
    ExteriorAlgebra K M →ₗ[K] ExteriorAlgebra K M × ExteriorAlgebra K M :=
  pairSecondDifferential (twoFormMultiplication f) (twoFormMultiplication g)

theorem exteriorKoszul_comp (f g : ⋀[K]^2 M) :
    (exteriorKoszulFirst f g).comp (exteriorKoszulSecond f g) = 0 :=
  pairDifferentials_comp _ _ (twoFormMultiplication_commute f g)

def exteriorKoszulTerm₀Grading : TauCeti.InternalGrading K (ExteriorAlgebra K M) :=
  exteriorIntegerGrading

def exteriorKoszulTerm₁Grading :
    TauCeti.InternalGrading K (ExteriorAlgebra K M × ExteriorAlgebra K M) :=
  (exteriorIntegerGrading.prod exteriorIntegerGrading).shift (-2)

def exteriorKoszulTerm₂Grading : TauCeti.InternalGrading K (ExteriorAlgebra K M) :=
  exteriorIntegerGrading.shift (-4)

theorem exteriorKoszulFirst_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous (exteriorKoszulFirst f g)
      exteriorKoszulTerm₁Grading.piece exteriorKoszulTerm₀Grading.piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  rw [exteriorKoszulTerm₁Grading,TauCeti.InternalGrading.shift_piece,
    TauCeti.InternalGrading.prod_piece] at ha
  change a.1 ∈ exteriorIntegerGrading.piece (q + -2) ∧
    a.2 ∈ exteriorIntegerGrading.piece (q + -2) at ha
  have hf := (twoFormMultiplication_homogeneous f).map_mem ha.1
  have hg := (twoFormMultiplication_homogeneous g).map_mem ha.2
  have hq : q + -2 + 2 = q + 0 := by omega
  rw [hq] at hf hg
  exact Submodule.add_mem _ hf hg

theorem exteriorKoszulSecond_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous (exteriorKoszulSecond f g)
      exteriorKoszulTerm₂Grading.piece exteriorKoszulTerm₁Grading.piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  rw [exteriorKoszulTerm₂Grading,TauCeti.InternalGrading.shift_piece] at ha
  change a ∈ exteriorIntegerGrading.piece (q + -4) at ha
  have hf := (twoFormMultiplication_homogeneous f).map_mem ha
  have hg := (twoFormMultiplication_homogeneous g).map_mem ha
  rw [exteriorKoszulTerm₁Grading,TauCeti.InternalGrading.shift_piece,
    TauCeti.InternalGrading.prod_piece]
  change -((g : ExteriorAlgebra K M) * a) ∈ exteriorIntegerGrading.piece (q + 0 + -2) ∧
    (f : ExteriorAlgebra K M) * a ∈ exteriorIntegerGrading.piece (q + 0 + -2)
  have hq : q + -4 + 2 = q + 0 + -2 := by omega
  rw [hq] at hf hg
  exact ⟨Submodule.neg_mem _ hg, hf⟩

def exteriorKoszulH₀Grading (f g : ⋀[K]^2 M) :=
  shortComplexH₀Grading exteriorKoszulTerm₁Grading exteriorKoszulTerm₀Grading
    (exteriorKoszulFirst f g) (exteriorKoszulFirst_homogeneous f g)

def exteriorKoszulH₁Grading (f g : ⋀[K]^2 M) :=
  shortComplexH₁Grading exteriorKoszulTerm₂Grading exteriorKoszulTerm₁Grading
    exteriorKoszulTerm₀Grading (exteriorKoszulSecond f g) (exteriorKoszulFirst f g)
    (exteriorKoszul_comp f g) (exteriorKoszulSecond_homogeneous f g)
    (exteriorKoszulFirst_homogeneous f g)

def exteriorKoszulH₂Grading (f g : ⋀[K]^2 M) :=
  shortComplexH₂Grading exteriorKoszulTerm₂Grading exteriorKoszulTerm₁Grading
    exteriorKoszulTerm₀Grading (exteriorKoszulSecond f g) (exteriorKoszulFirst f g)
    (exteriorKoszul_comp f g) (exteriorKoszulSecond_homogeneous f g)
    (exteriorKoszulFirst_homogeneous f g)

/-- Euler characteristic for the literal two-form Koszul homology. -/
theorem exteriorKoszul_hilbert_euler (f g : ⋀[K]^2 M) :
    finiteHilbertLaurent (exteriorKoszulH₀Grading f g) -
      finiteHilbertLaurent (exteriorKoszulH₁Grading f g) +
      finiteHilbertLaurent (exteriorKoszulH₂Grading f g) =
    finiteHilbertLaurent (exteriorKoszulTerm₀Grading (K := K) (M := M)) -
      finiteHilbertLaurent (exteriorKoszulTerm₁Grading (K := K) (M := M)) +
      finiteHilbertLaurent (exteriorKoszulTerm₂Grading (K := K) (M := M)) :=
  shortComplex_hilbert_euler _ _ _ _ _ _ _ _

end ExteriorKoszul

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0559

