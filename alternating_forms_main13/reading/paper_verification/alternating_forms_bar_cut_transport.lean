module

public import PaperVerification.AlternatingFormsBarNormalMerging
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact transport from normal bar multiplication to cut contraction

Every normal adjacent merge is precisely an optional interior cut, with
the same output word and sign. The equality below is an identity for
the full differential, not a comparison of dimensions or possible terms.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.BarCompositions

open BarCoefficientFormula

variable {K C J : Type*} [CommRing K] [Preorder J]
  (e : C ≃ PositiveNormalWord J)

theorem adjacent_normalProduct_cut (W : List J) (r : ℕ)
    (L : ActualBarIndex e W (r+1))
    (j : Fin ((factorizationComposition W (actualFactorization e W (r+1) L).val.val).length+1))
    (hj : (factorizationComposition W (actualFactorization e W (r+1) L).val.val).boundary j∉
      mandatoryCuts (·≤·) W) :
    adjacent (normalProduct (K := K) e) (j.val-1) L.val=
      barWordMap (K := K) e W r (Finsupp.single
        (mergedBarIndex (·≤·) W r (actualFactorization e W (r+1) L) j hj) 1) := by
  have hb := optional_boundary_index_bounds (·≤·) W
    (actualFactorization e W (r+1) L).val j hj
  have hi : j.val-1+1<L.val.length := by
    simpa only [actualFactorization,List.length_map] using
      (show j.val-1+1<(actualFactorization e W (r+1) L).val.val.val.length by omega)
  have hj' := hj
  have he : j.val-1+1=j.val := by omega
  have ho : ∃ M,normalMerge e (j.val-1) L.val=some M := by
    apply (normalMerge_optional e W (r+1) L (j.val-1) hi).mpr
    have hindex : (⟨j.val-1+1, by
        simpa only [factorizationComposition,Composition.length,actualFactorization,
          List.length_map] using Nat.lt_succ_of_lt hi⟩ :
        Fin ((factorizationComposition W
          (actualFactorization e W (r+1) L).val.val).length+1)) = j := by
      apply Fin.ext
      exact he
    exact hindex.symm ▸ hj'
  obtain ⟨M,hM⟩ := ho
  rw [adjacent_normalProduct,hM,optionalSingle,Option.elim_some,barWordMap_single]
  congr 1
  apply (List.map_injective_iff.mpr
    (show Function.Injective (fun a : C ↦ (e a).val) from
      fun a b hab ↦ e.injective (Subtype.ext hab)))
  rw [factorizationBarWord_map]
  exact normalMerge_map e (j.val-1) L.val M hM

theorem adjacent_normalProduct_zero_of_mandatory (W : List J) (r : ℕ)
    (L : ActualBarIndex e W r) (i : ℕ) (hi : i+1<L.val.length)
    (hj : (factorizationComposition W (actualFactorization e W r L).val.val).boundary
      ⟨i+1,by
        simpa only [factorizationComposition,Composition.length,actualFactorization,
          List.length_map] using Nat.lt_succ_of_lt hi⟩∈mandatoryCuts (·≤·) W) :
    adjacent (normalProduct (K := K) e) i L.val=0 := by
  have hnone : normalMerge e i L.val=none := by
    cases hm : normalMerge e i L.val with
    | none => rfl
    | some M =>
      have ho := (normalMerge_optional e W r L i hi).mp ⟨M,hm⟩
      exact False.elim (ho hj)
  rw [adjacent_normalProduct,hnone]
  rfl

theorem sum_interior_bar_signs {M : Type*} [AddCommGroup M] (r : ℕ) (f : ℕ → M) :
    (∑ j∈Finset.range (r+2),if 0<j ∧ j<r+1 then (-1 : ℤˣ)^j • f (j-1) else 0)=
      ∑ i∈Finset.range r,(-1 : ℤˣ)^(i+1) • f i := by
  rw [Finset.sum_range_succ]
  simp only [lt_self_iff_false,and_false,if_false,add_zero]
  rw [Finset.sum_range_succ']
  simp only [Nat.lt_irrefl,false_and,if_false,add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < r := Finset.mem_range.mp hi
  rw [if_pos (by constructor <;> omega),Nat.add_sub_cancel]

set_option maxHeartbeats 800000 in
/-- The actual tensor sign convention is the negative of the recursive
positive-first-merge convention. Endpoints contribute zero because they
are mandatory, and every interior optional cut is retained. -/
theorem cutDifferential_transport_basis (W : List J) (r : ℕ)
    (L : ActualBarIndex e W (r+1)) :
    barWordMap (K := K) e W r
      (cutModelDifferential (K := K) (·≤·) W r
        (Finsupp.single (actualFactorization e W (r+1) L) 1))=
      -basisDifferential (normalProduct (K := K) e) L.val := by
  let A := actualFactorization e W (r+1) L
  let c := factorizationComposition W A.val.val
  have hc : c.length=L.val.length := by
    simp only [c,A,factorizationComposition,Composition.length,actualFactorization,
      List.length_map]
  rw [cutModelDifferential_single_merges,map_sum,negative_basisDifferential_expansion]
  calc
    (∑ j : Fin (c.length+1),barWordMap (K := K) e W r
      (if hj : c.boundary j∉mandatoryCuts (·≤·) W
        then (-1 : ℤˣ)^j.val • Finsupp.single (mergedBarIndex (·≤·) W r A j hj) (1 : K)
        else 0)) =
      ∑ j : Fin (c.length+1),if 0<j.val ∧ j.val<L.val.length
        then (-1 : ℤˣ)^j.val • adjacent (normalProduct (K := K) e) (j.val-1) L.val else 0 := by
      apply Finset.sum_congr rfl
      intro j hjmem
      by_cases hb : 0<j.val ∧ j.val<L.val.length
      · rw [if_pos hb]
        by_cases hj : c.boundary j∉mandatoryCuts (·≤·) W
        · rw [dif_pos hj,map_zsmul_unit,←adjacent_normalProduct_cut e W r L j hj]
        · rw [dif_neg hj,map_zero]
          have hi : j.val-1+1<L.val.length := by omega
          have hm : c.boundary
              ⟨j.val-1+1,by omega⟩∈mandatoryCuts (·≤·) W := by
            convert not_not.mp hj using 1
            congr 1
            apply Fin.ext
            change j.val-1+1=j.val
            omega
          rw [adjacent_normalProduct_zero_of_mandatory e W (r+1) L
            (j.val-1) hi hm,smul_zero]
      · have hj : ¬c.boundary j∉mandatoryCuts (·≤·) W := by
          intro hj
          have hp := optional_boundary_index_bounds (·≤·) W A.val j hj
          apply hb
          exact ⟨hp.1,by simpa only [A,actualFactorization,List.length_map] using hp.2⟩
        rw [dif_neg hj,if_neg hb,map_zero]
    _ = ∑ j∈Finset.range (c.length+1),if 0<j ∧ j<L.val.length
        then (-1 : ℤˣ)^j • adjacent (normalProduct (K := K) e) (j-1) L.val else 0 :=
      Fin.sum_univ_eq_sum_range
        (fun j : ℕ => if 0<j ∧ j<L.val.length then
          (-1 : ℤˣ)^j • adjacent (normalProduct (K := K) e) (j-1) L.val else 0)
        (c.length+1)
    _ = ∑ i∈Finset.range (L.val.length-1),
        (-1 : ℤˣ)^(i+1) • adjacent (normalProduct (K := K) e) i L.val := by
      rw [hc,L.property.2,Nat.add_sub_cancel]
      simpa only [Nat.add_assoc] using sum_interior_bar_signs r
        (fun i => adjacent (normalProduct (K := K) e) i L.val)

end PaperVerification.AlternatingForms.BarCompositions
