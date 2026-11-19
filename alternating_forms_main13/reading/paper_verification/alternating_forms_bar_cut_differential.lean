module

public import PaperVerification.AlternatingFormsBarCutComplex

/-!
# The cut differential is the literal adjacent-merge differential

The coordinate operator transported from exterior contraction is expanded
on every basis tensor. Each nonzero summand joins precisely the two
adjacent normal blocks separated by the chosen optional cut, with the
sign of the actual residue-tensor bar differential. The comparison is an
identity of operators on the full coefficient modules, without a rank or
dimension argument.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

open scoped BigOperators
open PaperVerification.MonomialBarCuts

variable {K α : Type*} [CommRing K]

theorem differential_basis_composition {n : ℕ} (c : Composition n)
    (mandatory : Finset (Fin (n+1))) :
    differential (n+1) mandatory
        ((coordinateBasis (K := K) (n+1)).ExteriorAlgebra c.boundaries)=
      ∑ j : Fin (c.length+1),
        if c.boundary j∈mandatory then 0 else
          (-1 : ℤˣ)^j.val •
            (coordinateBasis (K := K) (n+1)).ExteriorAlgebra
              (c.boundaries.erase (c.boundary j)) := by
  classical
  rw [differential_basis,←Finset.sum_filter]
  have hf : (Finset.univ \ mandatory).filter (fun x ↦ x∈c.boundaries)=
      c.boundaries.filter (fun x ↦ x∉mandatory) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    exact and_comm
  rw [hf,Finset.sum_filter]
  simp only [ite_not]
  calc
    (∑ x∈c.boundaries,if x∈mandatory then 0 else
      TauCeti.ExteriorAlgebra.basisEraseSign x c.boundaries •
        (coordinateBasis (K := K) (n+1)).ExteriorAlgebra (c.boundaries.erase x)) =
      ∑ j : Fin (c.length+1),if c.boundary j∈mandatory then 0 else
        TauCeti.ExteriorAlgebra.basisEraseSign (c.boundary j) c.boundaries •
          (coordinateBasis (K := K) (n+1)).ExteriorAlgebra
            (c.boundaries.erase (c.boundary j)) := by
        change (∑ x∈Finset.univ.map c.boundary.toEmbedding,_) = _
        rw [Finset.sum_map]
        rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [boundary_erase_sign]

variable (R : α → α → Prop) (W : List α)

theorem optional_boundary_index_bounds (L : AdmissibleFactorization R W)
    (j : Fin ((factorizationComposition W L.val).length+1))
    (hj : (factorizationComposition W L.val).boundary j∉mandatoryCuts R W) :
    0<j.val ∧ j.val<L.val.val.length := by
  let c := factorizationComposition W L.val
  have h0 : j≠0 := by
    intro he
    subst j
    apply hj
    rw [Composition.boundary_zero]
    exact (mem_mandatoryCuts R W _).mpr (Or.inl rfl)
  have hlast : j≠Fin.last c.length := by
    intro he
    subst j
    apply hj
    rw [Composition.boundary_last]
    exact (mem_mandatoryCuts R W _).mpr (Or.inr (Or.inl rfl))
  have hc : c.length=L.val.val.length := by
    simp only [c,Composition.length,factorizationComposition,List.length_map]
  have hjlt : j.val<c.length+1 := j.isLt
  have hj0 : j.val≠0 := fun h ↦ h0 (Fin.ext h)
  have hjlast : j.val≠c.length := fun h ↦ hlast (Fin.ext h)
  constructor <;> omega

def mergedBarIndex (r : ℕ) (L : BarIndex R W (r+1))
    (j : Fin ((factorizationComposition W L.val.val).length+1))
    (hj : (factorizationComposition W L.val.val).boundary j∉mandatoryCuts R W) :
    BarIndex R W r := by
  have hb := optional_boundary_index_bounds R W L.val j hj
  let i := j.val-1
  have hi : i+1<L.val.val.val.length := by dsimp only [i]; omega
  have he : i+1=j.val := by dsimp only [i]; omega
  have hmerge : ∀ T∈(mergeFactorization W L.val.val i).val,T.IsChain R := by
    apply (merge_admissible_iff_optional R W L.val i hi).mpr
    let jj : Fin ((factorizationComposition W L.val.val).length+1) :=
      ⟨i+1,by
        simpa only [Composition.length,factorizationComposition,List.length_map] using
          Nat.lt_succ_of_lt hi⟩
    have hindex : jj=j := Fin.ext he
    change (factorizationComposition W L.val.val).boundary jj∉mandatoryCuts R W
    rw [hindex]
    exact hj
  refine ⟨⟨mergeFactorization W L.val.val i,hmerge⟩,?_⟩
  have hl := mergeAdjacent_length (·++·) i L.val.val.val hi
  have hr := L.property
  dsimp only [mergeFactorization]
  omega

theorem mergedBarIndex_boundaries (r : ℕ) (L : BarIndex R W (r+1))
    (j : Fin ((factorizationComposition W L.val.val).length+1))
    (hj : (factorizationComposition W L.val.val).boundary j∉mandatoryCuts R W) :
    boundaries W (mergedBarIndex R W r L j hj).val.val=
      (boundaries W L.val.val).erase
        ((factorizationComposition W L.val.val).boundary j) := by
  have hb := optional_boundary_index_bounds R W L.val j hj
  have hi : j.val-1+1<L.val.val.val.length := by omega
  change boundaries W (mergeFactorization W L.val.val (j.val-1))=_
  rw [boundaries_mergeFactorization W L.val.val (j.val-1) hi]
  apply congrArg (fun a : Fin ((factorizationComposition W L.val.val).length+1) ↦
    (boundaries W L.val.val).erase ((factorizationComposition W L.val.val).boundary a))
  apply Fin.ext
  change j.val-1+1=j.val
  omega

def barExteriorMap (r : ℕ) :
    (BarIndex R W r →₀ K) →ₗ[K] ExteriorAlgebra K (Fin (W.length+1) → K) :=
  (cutPiece (W.length+1) (mandatoryCuts R W) (r+1)).subtype.comp
    (barCutLinearEquiv R W r).toLinearMap

theorem barExteriorMap_injective (r : ℕ) :
    Function.Injective (barExteriorMap (K := K) R W r) :=
  Subtype.val_injective.comp (barCutLinearEquiv R W r).injective

@[simp] theorem barExteriorMap_single (r : ℕ) (L : BarIndex R W r) :
    barExteriorMap (K := K) R W r (Finsupp.single L 1)=
      (coordinateBasis (K := K) (W.length+1)).ExteriorAlgebra
        (boundaries W L.val.val) :=
  barCutLinearEquiv_single R W r L

theorem barExteriorMap_differential (r : ℕ) (z : BarIndex R W (r+1) →₀ K) :
    barExteriorMap R W r (cutModelDifferential (K := K) R W r z)=
      differential (W.length+1) (mandatoryCuts R W) (barExteriorMap R W (r+1) z) :=
  cutModelDifferential_comm R W r z

/-- Exact formula on every actual factorization basis vector. -/
theorem cutModelDifferential_single_merges (r : ℕ) (L : BarIndex R W (r+1)) :
    cutModelDifferential (K := K) R W r (Finsupp.single L 1)=
      ∑ j : Fin ((factorizationComposition W L.val.val).length+1),
        if hj : (factorizationComposition W L.val.val).boundary j∉mandatoryCuts R W
        then (-1 : ℤˣ)^j.val • Finsupp.single (mergedBarIndex R W r L j hj) 1
        else 0 := by
  classical
  apply barExteriorMap_injective R W r
  rw [barExteriorMap_differential,barExteriorMap_single]
  change differential (W.length+1) (mandatoryCuts R W)
      ((coordinateBasis (K := K) (W.length+1)).ExteriorAlgebra
        (factorizationComposition W L.val.val).boundaries)=_
  rw [differential_basis_composition,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : (factorizationComposition W L.val.val).boundary j∉mandatoryCuts R W
  · rw [dif_pos h,if_neg h,map_zsmul_unit,barExteriorMap_single,
      mergedBarIndex_boundaries]
    rfl
  · rw [dif_neg h,if_pos (not_not.mp h),map_zero]

end PaperVerification.AlternatingForms.BarCompositions

