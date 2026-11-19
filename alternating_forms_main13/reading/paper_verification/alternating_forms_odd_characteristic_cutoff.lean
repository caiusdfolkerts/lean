module

public import PaperVerification.AlternatingFormsOddBasisCharacteristic
public import PaperVerification.AlternatingFormsHighDivision
public import PaperVerification.AlternatingFormsOddWalkCount

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
