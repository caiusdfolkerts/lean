/- Exact ordinary-matroid meanings of the port hypotheses in Proposition 2.2. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsFaithful
public import Recovery.Unimodular.PriorExtensions.FlowLattice
public import Mathlib.Combinatorics.Matroid.Loop
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

/- The closure and non-coloop lemmas are imported from the shared
ordinary-matroid owner through `SignedSumsFaithful`. -/

theorem flow_isColoop_iff_matroid {n : ℕ} {E : Type*} [Fintype E]
    (u : E → Lattice n) (e : E) :
    FlowOrientations.IsColoop u e ↔
      (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (u j))).IsColoop e :=
  (ofFamily_isColoop_iff (fun j => embed (u j)) e).symm

/-- For a full-rank side, deletion spans if and only if its actual selected
port is a non-coloop of the original ordinary vector matroid. -/
theorem two_sum_deleted_span_iff_noncoloop {n : ℕ} {L : Type*}
    (U : Fin 1 ⊕ L → Lattice n)
    (hfull : Submodule.span ℝ (Set.range (fun j => embed (U j))) = ⊤) :
    Submodule.span ℝ (Set.range (fun l => embed (U (.inr l)))) = ⊤ ↔
      ¬ (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j))).IsColoop (.inl 0) := by
  have himage : (fun j => embed (U j)) '' {f | f ≠ Sum.inl 0} =
      Set.range (fun l => embed (U (.inr l))) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      cases j with
      | inl t => fin_cases t; exact (hj rfl).elim
      | inr l => exact ⟨l, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨Sum.inr l, Sum.inr_ne_inl, rfl⟩
  rw [ofFamily_isColoop_iff, not_not, himage]
  constructor
  · intro h
    rw [h]
    exact Submodule.mem_top
  · intro hport
    apply top_unique
    rw [← hfull]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    cases j with
    | inl t => fin_cases t; exact hport
    | inr l => exact Submodule.subset_span ⟨l, rfl⟩

/-- Every ordinary three-element port circuit has its first two labelled
vectors independent. This directly converts the paper's triangle hypothesis. -/
theorem triangle_independent_of_circuit {n : ℕ} {L : Type*}
    (U : Fin 3 ⊕ L → Lattice n)
    (hC : (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L))) :
    LinearIndependent ℝ (fun i => embed (U (.inl (triangleBasisLabels i)))) := by
  let a : Fin 2 → Fin 3 ⊕ L := fun i => Sum.inl (triangleBasisLabels i)
  have hsub : Set.range a ⊂ Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L) := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨triangleBasisLabels i, rfl⟩
    · intro heq
      have hmem : Sum.inl (2 : Fin 3) ∈ Set.range a := by
        rw [heq]
        exact ⟨2, rfl⟩
      obtain ⟨i, hi⟩ := hmem
      fin_cases i <;> simp [a, triangleBasisLabels] at hi
  have hli := (VectorMatroid.ofFamily_indep (fun j => embed (U j)) _).mp
    (hC.ssubset_indep hsub)
  have ha : Function.Injective a := Sum.inl_injective.comp (Fin.castSucc_injective 2)
  exact (linearIndepOn_range_iff ha (fun j => embed (U j))).mp hli

/-- Literal Proposition 2.2 with its original full-rank and ordinary
non-coloop hypotheses, yielding the intrinsic ordinary-matroid sum. -/
theorem proposition_2_2_two_sum_paper {n₁ n₂ : ℕ} {L R : Type*}
    [Fintype L] [Fintype R]
    (U : Fin 1 ⊕ L → Lattice n₁) (V : Fin 1 ⊕ R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hfullU : Submodule.span ℝ (Set.range (fun j => embed (U j))) = ⊤)
    (hfullV : Submodule.span ℝ (Set.range (fun j => embed (V j))) = ⊤)
    (hpU : U (.inl 0) ≠ 0) (hpV : V (.inl 0) ≠ 0)
    (hcU : ¬ (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j))).IsColoop (.inl 0))
    (hcV : ¬ (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (V j))).IsColoop (.inl 0)) :
    SumConclusion id U V ∧ OrdinaryMatroidConclusion id U V :=
  proposition_2_2_two_sum_ordinary U V hU hV
    ((two_sum_deleted_span_iff_noncoloop U hfullU).mpr hcU)
    ((two_sum_deleted_span_iff_noncoloop V hfullV).mpr hcV) hpU hpV

/-- Literal Proposition 2.2 for aligned ordinary triangle circuits. Deleting
the ports spans each side exactly as stated in the paper. -/
theorem proposition_2_2_three_sum_paper {n₁ n₂ : ℕ} {L R : Type*}
    [Fintype L] [Fintype R]
    (U : Fin 3 ⊕ L → Lattice n₁) (V : Fin 3 ⊕ R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hspanU : Submodule.span ℝ (Set.range (fun l => embed (U (.inr l)))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun l => embed (V (.inr l)))) = ⊤)
    (hCU : (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L)))
    (hCV : (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (V j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ R)))
    (htriU : U (.inl 2) = U (.inl 0) + U (.inl 1))
    (htriV : V (.inl 2) = V (.inl 0) + V (.inl 1)) :
    SumConclusion triangleBasisLabels U V ∧ OrdinaryMatroidConclusion triangleBasisLabels U V :=
  proposition_2_2_three_sum_ordinary U V hU hV hspanU hspanV
    (triangle_independent_of_circuit U hCU) (triangle_independent_of_circuit V hCV) htriU htriV

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.ofFamily_mem_closure_iff
#print axioms Unimodular.SignedSums.flow_isColoop_iff_matroid
#print axioms Unimodular.SignedSums.two_sum_deleted_span_iff_noncoloop
#print axioms Unimodular.SignedSums.triangle_independent_of_circuit
#print axioms Unimodular.SignedSums.proposition_2_2_two_sum_paper
#print axioms Unimodular.SignedSums.proposition_2_2_three_sum_paper
