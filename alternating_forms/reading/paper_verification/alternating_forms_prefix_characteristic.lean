module

public import PaperVerification.AlternatingFormsPrefixSupport
public import PaperVerification.AlternatingFormsCharacteristicDivision

/-!
# Supported prefix division with the exact characteristic restriction

The inverse retains every singleton of the input word.  Its only required
denominator is the factorial of the number of doubly occupied pairs.  This
number is at most half the total exterior degree, which yields precisely
the strict inequality `s < 2*p` in Theorem 7.1.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [DecidableEq ι] [Fintype ι]

/-- The complete supported prefix inverse, with its actual factorial
condition in place of a characteristic-zero assumption. -/
theorem prefix_selection_division_with_support_of_factorial
    (u v : ι → M) (A B : Finset ι)
    (hdegree : A.card+B.card=Fintype.card ι+1)
    (hfac : ((A ∩ B).card.factorial : K) ≠ 0) :
    ∃ η : ⋀[K]^(Fintype.card ι-1) M,
      (∑ i, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i))*η =
        ((A.toList.map u++B.toList.map v).map (ExteriorAlgebra.ι K)).prod ∧
      (η : ExteriorAlgebra K M) ∈ prefixInverseSpace u v A B := by
  classical
  let S := prefixSingletons A B
  let L := prefixSingletonWord u v A B
  let n := (A ∩ B).card-1
  have hcounts := prefix_occupancy_counts A B hdegree
  have hP := doublePairs_disjoint_singletons A B
  have hPS : ∀ i ∈ A ∩ B,i ∉ S := hP
  have hn : n+1=(A ∩ B).card := by dsimp only [n]; omega
  have hfac' : ((n+1).factorial : K) ≠ 0 := by simpa only [hn] using hfac
  let P : FixedSubsets (PrefixFreePair A B) (n+1) :=
    ⟨(A ∩ B).subtype (fun i => i ∉ S),by
      rw [Finset.card_subtype,Finset.filter_eq_self.mpr hPS]
      exact hn.symm⟩
  let z : ExteriorAlgebra K M := (L.map (ExteriorAlgebra.ι K)).prod
  let η₀ : ExteriorAlgebra K M := z *
    ∑ T : FixedSubsets (PrefixFreePair A B) n,
      inverseCoefficient (K := K) n (T.val ∩ P.val).card •
        pairedMonomial (fun i : PrefixFreePair A B => u i.val)
          (fun i : PrefixFreePair A B => v i.val) T.val
  have hηmem : η₀ ∈ prefixInverseSpace (K := K) u v A B := by
    dsimp only [η₀]
    rw [Finset.mul_sum]
    apply Submodule.sum_mem
    intro T hT
    rw [mul_smul_comm]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨T,rfl⟩
  have hL : ∀ i ∈ S,u i∈L ∨ v i∈L := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Or.inl (List.mem_append_left _
        (List.mem_map.mpr ⟨i,Finset.mem_toList.mpr hi,rfl⟩))
    · exact Or.inr (List.mem_append_right _
        (List.mem_map.mpr ⟨i,Finset.mem_toList.mpr hi,rfl⟩))
  have hη := local_exterior_pair_division_with_singletons_of_factorial (K := K)
    u v S L hL n hfac' hcounts.2.1 P
  obtain ⟨ε,hε,heq⟩ := exterior_monomial_singleton_pair_factorization (K := K) u v A B
  have hηscaled : ε • η₀ ∈ prefixInverseSpace (K := K) u v A B :=
    Submodule.smul_mem _ _ hηmem
  refine ⟨⟨ε • η₀,prefixInverseSpace_le_degree u v A B hdegree hηscaled⟩,?_,hηscaled⟩
  change (∑ i, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i))*(ε • η₀)=_
  rw [mul_smul_comm]
  change ε • ((∑ i, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i))*η₀)=_
  rw [show (∑ i, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i))*η₀ =
    z * pairedMonomial (fun i : PrefixFreePair A B => u i.val)
      (fun i : PrefixFreePair A B => v i.val) P.val from hη]
  have hpair : pairedMonomial (K := K) (fun i : PrefixFreePair A B => u i.val)
      (fun i : PrefixFreePair A B => v i.val) P.val = pairedMonomial (K := K) u v (A ∩ B) := by
    exact pairedMonomial_subtype (K := K) (S := S) hPS u v
  rw [hpair]
  exact heq.symm

/-- Each double occupancy consumes two letters of the original word. -/
theorem prefix_double_pair_bound (A B : Finset ι) :
    2*(A ∩ B).card ≤ A.card+B.card := by
  have ha := Finset.card_le_card (Finset.inter_subset_left : A ∩ B ⊆ A)
  have hb := Finset.card_le_card (Finset.inter_subset_right : A ∩ B ⊆ B)
  omega

/-- The denominator condition follows from the literal exterior degree,
without an ambient-dimension or number-of-pairs restriction. -/
theorem prefix_factorial_ne_zero_below_twice_characteristic
    (p s : ℕ) [Fact p.Prime] [CharP K p]
    (A B : Finset ι) (hsize : A.card+B.card≤s) (hs : s<2*p) :
    ((A ∩ B).card.factorial : K) ≠ 0 := by
  apply factorial_cast_ne_zero_of_lt_char p
  have hpair := prefix_double_pair_bound A B
  omega

/-- Every prefix division needed in degree `s < 2*p` has the same actual
singleton-preserving support as the characteristic-zero division. -/
theorem prefix_selection_division_with_support_below_twice_characteristic
    (p s : ℕ) [Fact p.Prime] [CharP K p]
    (u v : ι → M) (A B : Finset ι)
    (hdegree : A.card+B.card=Fintype.card ι+1)
    (hsize : A.card+B.card≤s) (hs : s<2*p) :
    ∃ η : ⋀[K]^(Fintype.card ι-1) M,
      (∑ i, ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i))*η =
        ((A.toList.map u++B.toList.map v).map (ExteriorAlgebra.ι K)).prod ∧
      (η : ExteriorAlgebra K M) ∈ prefixInverseSpace u v A B :=
  prefix_selection_division_with_support_of_factorial u v A B hdegree
    (prefix_factorial_ne_zero_below_twice_characteristic p s A B hsize hs)

end PaperVerification.AlternatingForms
