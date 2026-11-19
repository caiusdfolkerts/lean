module

public import PaperVerification.AlternatingFormsSingletonStates

/-!
# The actual prefix inverse with its complete singleton-preserving support

The strict weight argument requires more than existence of an inverse in
the prefix exterior power. This file retains the actual finite Boolean
inverse formula and proves that its support changes only the unoccupied
matching pairs. The fixed singleton word is the original one throughout.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [DecidableEq ι] [Fintype ι]

def prefixSingletons (A B : Finset ι) : Finset ι := (A \ B) ∪ (B \ A)

def prefixSingletonWord (u v : ι → M) (A B : Finset ι) : List M :=
  (A \ B).toList.map u ++ (B \ A).toList.map v

abbrev PrefixFreePair (A B : Finset ι) := {i : ι // i ∉ prefixSingletons A B}

def prefixInverseState (u v : ι → M) (A B : Finset ι)
    (T : FixedSubsets (PrefixFreePair A B) ((A ∩ B).card-1)) : ExteriorAlgebra K M :=
  ((prefixSingletonWord u v A B).map (ExteriorAlgebra.ι K)).prod *
    pairedMonomial (fun i : PrefixFreePair A B => u i.val)
      (fun i : PrefixFreePair A B => v i.val) T.val

def prefixInverseSpace (u v : ι → M) (A B : Finset ι) :
    Submodule K (ExteriorAlgebra K M) :=
  Submodule.span K (Set.range (prefixInverseState (K := K) u v A B))

theorem prefixInverseState_mem_degree (u v : ι → M) (A B : Finset ι)
    (hdegree : A.card+B.card=Fintype.card ι+1)
    (T : FixedSubsets (PrefixFreePair A B) ((A ∩ B).card-1)) :
    prefixInverseState (K := K) u v A B T ∈ ⋀[K]^(Fintype.card ι-1) M := by
  have hc := (prefix_occupancy_counts A B hdegree).2.2
  have hlen : (prefixSingletonWord u v A B).length+2*T.val.card=Fintype.card ι-1 := by
    simpa only [prefixSingletonWord,List.length_append,List.length_map,
      Finset.length_toList,T.property] using hc
  rw [prefixInverseState,←hlen]
  exact SetLike.mul_mem_graded (exteriorWord_mem _)
    (pairedMonomial_mem (fun i : PrefixFreePair A B => u i.val)
      (fun i : PrefixFreePair A B => v i.val) T.val)

theorem prefixInverseSpace_le_degree (u v : ι → M) (A B : Finset ι)
    (hdegree : A.card+B.card=Fintype.card ι+1) :
    prefixInverseSpace (K := K) u v A B ≤ ⋀[K]^(Fintype.card ι-1) M := by
  apply Submodule.span_le.mpr
  rintro _ ⟨T,rfl⟩
  exact prefixInverseState_mem_degree u v A B hdegree T

/-- The prefix inverse in full generality, with its actual finite support.
The support statement is derived from the same inverse formula as the
identity; it is not an added assumption on a chosen preimage. -/
theorem prefix_selection_division_with_support [CharZero K] (u v : ι → M) (A B : Finset ι)
    (hdegree : A.card+B.card=Fintype.card ι+1) :
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
  let P : FixedSubsets (PrefixFreePair A B) (n+1) :=
    ⟨(A ∩ B).subtype (fun i => i ∉ S),by
      rw [Finset.card_subtype,Finset.filter_eq_self.mpr hPS]
      dsimp [n]
      omega⟩
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
  have hη := local_exterior_pair_division_with_singletons (K := K)
    u v S L hL n hcounts.2.1 P
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

end PaperVerification.AlternatingForms
