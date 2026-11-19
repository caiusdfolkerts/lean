module

public import PaperVerification.AlternatingFormsHighDivision
public import PaperVerification.AlternatingFormsOddPencilRelations
public import Mathlib.Data.Finset.Sum
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Low-degree matching injectivity in prime characteristic

This file supplies the injectivity input of the characteristic-p dimension
argument. Every complementary exterior basis word is divided by the actual
matching form, using the factorial bound from its empty matching pairs.
The established perfect exterior pairing then gives injectivity. The proof
has no ambient-characteristic bound and no assumed rank or Hilbert series.
This source remains a candidate until its complete compilation and audit.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The two parts of a finite sum selection are an actual list permutation. -/
theorem selection_sum_list_permutation {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset (α ⊕ β)) :
    T.toList.Perm (T.toLeft.toList.map Sum.inl ++ T.toRight.toList.map Sum.inr) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [List.count_append, T.nodup_toList.count,
    (T.toLeft.nodup_toList.map Sum.inl_injective).count,
    (T.toRight.nodup_toList.map Sum.inr_injective).count]
  cases i <;> simp

/-- The paired and unpaired letters of an odd matching, with all letters retained. -/
theorem odd_selection_list_permutation {ι : Type*} [DecidableEq ι]
    (z : (ι ⊕ ι) ⊕ Fin 1 → M) (T : Finset ((ι ⊕ ι) ⊕ Fin 1)) :
    (T.toList.map z).Perm
      ((T.toLeft.toLeft.toList.map (fun i => z (.inl (.inl i))) ++
        T.toLeft.toRight.toList.map (fun i => z (.inl (.inr i)))) ++
        T.toRight.toList.map (fun i => z (.inr i))) := by
  have h₁ := (selection_sum_list_permutation T).map z
  have h₂ := (selection_sum_list_permutation T.toLeft).map (fun i => z (.inl i))
  simp only [List.map_append, List.map_map, Function.comp_def] at h₁ h₂
  exact h₁.trans (h₂.append_right _)

/-- Division of every complementary selection, for all prime characteristics
and arbitrarily many matching pairs. -/
theorem matching_complement_selection_division {k : ℕ}
    (z : (Fin k ⊕ Fin k) ⊕ Fin 1 → M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k)
    (T : Finset ((Fin k ⊕ Fin k) ⊕ Fin 1))
    (hT : T.card = 2*k+1-(2*p-4)) :
    ∃ a : ExteriorAlgebra K M,
      (matchingQuadratic (K := K) (fun i => z (.inl (.inl i)))
        (fun i => z (.inl (.inr i))) : ExteriorAlgebra K M) * a =
        ((T.toList.map z).map (ExteriorAlgebra.ι K)).prod := by
  let A := T.toLeft.toLeft
  let B := T.toLeft.toRight
  let C := T.toRight
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hc : C.card ≤ 1 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ C
  have hcard : A.card+B.card+C.card = T.card := by
    dsimp only [A, B, C]
    rw [Finset.card_toLeft_add_card_toRight, Finset.card_toLeft_add_card_toRight]
  have hhigh : Fintype.card (Fin k)+1 ≤ A.card+B.card := by
    simp only [Fintype.card_fin]
    omega
  have hU : (A ∪ B).card+((A ∪ B)ᶜ).card = k := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl (A ∪ B)
  have hA : A.card ≤ (A ∪ B).card := Finset.card_le_card Finset.subset_union_left
  have hB : B.card ≤ (A ∪ B).card := Finset.card_le_card Finset.subset_union_right
  have hempty : ((A ∪ B)ᶜ).card+1 < p := by omega
  obtain ⟨η, hη⟩ := matching_high_selection_division_charP (K := K)
    (fun i => z (.inl (.inl i))) (fun i => z (.inl (.inr i))) A B p hhigh hempty
  obtain ⟨ε, hε, heq⟩ := exterior_word_permutation (K := K)
    (odd_selection_list_permutation z T)
  let tail : ExteriorAlgebra K M :=
    ((C.toList.map (fun i => z (.inr i))).map (ExteriorAlgebra.ι K)).prod
  refine ⟨ε • ((η : ExteriorAlgebra K M)*tail), ?_⟩
  rw [mul_smul_comm, ← mul_assoc, matchingQuadratic_coe, hη]
  simpa only [A, B, C, tail, List.map_append, List.prod_append] using heq.symm

/-- The actual complementary-degree relation space is the whole exterior
power; this assertion is proved on the genuine exterior basis. -/
theorem matching_complement_relations_eq_top {k : ℕ}
    (b : Module.Basis ((Fin k ⊕ Fin k) ⊕ Fin 1) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k) :
    exteriorDegreeRelations
      (matchingQuadratic (K := K) (fun i => b (.inl (.inl i)))
        (fun i => b (.inl (.inr i)))) 0 (2*k+1-(2*p-4)) = ⊤ := by
  classical
  letI : LinearOrder ((Fin k ⊕ Fin k) ⊕ Fin 1) := linearOrderOfSTO WellOrderingRel
  let q := 2*k+1-(2*p-4)
  let F := matchingQuadratic (K := K) (fun i => b (.inl (.inl i)))
    (fun i => b (.inl (.inr i)))
  apply eq_top_iff.mpr
  rw [← (b.exteriorPower q).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨T, rfl⟩
  change ((b.exteriorPower q T) : ExteriorAlgebra K M) ∈ exteriorRelationIdeal F 0
  let e := Set.powersetCard.ofFinEmbEquiv.symm T
  have hperm : (List.ofFn (fun i => e i)).Perm T.val.toList := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr e.injective)
      T.val.nodup_toList).mpr
    intro i
    rw [List.mem_ofFn', Finset.mem_toList]
    exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T i
  obtain ⟨ε, hε, heq⟩ := exterior_word_permutation (K := K) (hperm.map b)
  obtain ⟨a, ha⟩ := matching_complement_selection_division (K := K) b p hk T.val T.property
  apply Ideal.mem_span_pair.mpr
  refine ⟨ε • a, 0, ?_⟩
  rw [zero_mul, add_zero, ← (twoForm_commute F (ε • a)).eq, mul_smul_comm, ha]
  rw [exteriorPower.basis_apply]
  simpa only [exteriorPower.ιMulti_family, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_apply, List.map_ofFn, List.map_map, Function.comp_def, e]
    using heq.symm

/-- Complementary division and perfect exterior duality imply actual
left-multiplication injectivity on degree 2p-4. -/
theorem matching_low_degree_injective {k : ℕ}
    (b : Module.Basis ((Fin k ⊕ Fin k) ⊕ Fin 1) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k) :
    ∀ h : ⋀[K]^(2*p-4) M,
      (matchingQuadratic (K := K) (fun i => b (.inl (.inl i)))
        (fun i => b (.inl (.inr i))) : ExteriorAlgebra K M)*h = 0 → h = 0 := by
  letI : FiniteDimensional K M := b.finiteDimensional_of_finite
  let F := matchingQuadratic (K := K) (fun i => b (.inl (.inl i)))
    (fun i => b (.inl (.inr i)))
  have hrank : Module.finrank K M = 2*k+1 := by
    simpa only [Fintype.card_sum, Fintype.card_fin, two_mul] using
      Module.finrank_eq_card_basis b
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hsum : (2*p-4)+(2*k+1-(2*p-4)) = Module.finrank K M := by
    rw [hrank]
    omega
  have hrel : exteriorDegreeRelations F 0 (2*k+1-(2*p-4)) = ⊤ :=
    matching_complement_relations_eq_top b p hk
  haveI : Subsingleton (ExteriorQuotientDegree F 0 (2*k+1-(2*p-4))) := by
    change Subsingleton ((⋀[K]^(2*k+1-(2*p-4)) M) ⧸
      exteriorDegreeRelations F 0 (2*k+1-(2*p-4)))
    rw [hrel]
    infer_instance
  have hdim : Module.finrank K (exteriorCommonAnnihilator F 0 (2*p-4)) = 0 := by
    rw [exterior_annihilator_quotient_duality hsum F 0]
    exact Module.finrank_zero_of_subsingleton
  have hbot : exteriorCommonAnnihilator F 0 (2*p-4) = ⊥ :=
    Submodule.finrank_eq_zero.mp hdim
  intro h hh
  have hm : h ∈ exteriorCommonAnnihilator F 0 (2*p-4) :=
    (mem_exteriorCommonAnnihilator F 0 h).mpr ⟨hh, by simp⟩
  rw [hbot, Submodule.mem_bot] at hm
  exact hm

/-- The explicit even/odd bijection, isolated from the characteristic-zero
straightening development. -/
def matchingEvenOddEquiv (k : ℕ) : Fin k ⊕ Fin k ≃ Fin (2*k) where
  toFun
    | .inl i => ⟨2*i.val, by have := i.isLt; omega⟩
    | .inr i => ⟨2*i.val+1, by have := i.isLt; omega⟩
  invFun j := if j.val%2=0 then .inl ⟨j.val/2, by have := j.isLt; omega⟩
    else .inr ⟨j.val/2, by have := j.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
        have he : (2*i.val)%2=0 := by omega
        simp only [he, if_pos, Sum.inl.injEq]
        apply Fin.ext
        dsimp only
        omega
    | inr i =>
        have he : ¬(2*i.val+1)%2=0 := by omega
        simp only [he, if_false, Sum.inr.injEq]
        apply Fin.ext
        dsimp only
        omega
  right_inv j := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> dsimp only <;> omega

def oddMatchingIndexEquiv (k : ℕ) : ((Fin k ⊕ Fin k) ⊕ Fin 1) ≃ Fin (2*k+1) :=
  (Equiv.sumCongr (matchingEvenOddEquiv k) (Equiv.refl (Fin 1))).trans finSumFinEquiv

@[simp] theorem oddMatchingIndexEquiv_first {k : ℕ} (i : Fin k) :
    oddMatchingIndexEquiv k (.inl (.inl i)) = oddPathFirstLeft i := by
  apply Fin.ext
  rfl

@[simp] theorem oddMatchingIndexEquiv_middle {k : ℕ} (i : Fin k) :
    oddMatchingIndexEquiv k (.inl (.inr i)) = oddPathMiddle i := by
  apply Fin.ext
  rfl

/-- The injectivity statement for the literal first form of the odd canonical
pencil, with every prime and every ambient dimension in the paper's range. -/
theorem oddPath_first_low_degree_injective {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k) :
    ∀ h : ⋀[K]^(2*p-4) M,
      (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M)*h = 0 → h = 0 := by
  let b' := b.reindex (oddMatchingIndexEquiv k).symm
  have hform : matchingQuadratic (K := K) (fun i => b' (.inl (.inl i)))
      (fun i => b' (.inl (.inr i))) = oddPathFirstQuadratic (K := K) b := by
    simp only [b', Module.Basis.reindex_apply, Equiv.symm_symm,
      oddMatchingIndexEquiv_first, oddMatchingIndexEquiv_middle, oddPathFirstQuadratic]
  simpa only [hform] using matching_low_degree_injective b' p hk

end PaperVerification.AlternatingForms
