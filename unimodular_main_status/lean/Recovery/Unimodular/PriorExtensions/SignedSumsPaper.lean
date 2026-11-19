/- The signed 3-sum construction starts with arbitrary ordinary triangle
circuits; sign alignment is constructed and verified as part of the theorem. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsAlignment
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

theorem full_span_of_survivors {n : ℕ} {T L : Type*}
    (U : T ⊕ L → Lattice n)
    (hspan : Submodule.span ℝ (Set.range (fun l => embed (U (.inr l)))) = ⊤) :
    Submodule.span ℝ (Set.range (fun j => embed (U j))) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro _ ⟨l, rfl⟩
  exact ⟨Sum.inr l, rfl⟩

/-- The entire 3-sum construction on arbitrary ordinary port triangles.
The signs are constructed. Both sides keep their original ordinary matroids;
the actual signed quotient is free, integrally spanning and uniformly
unimodular, and its ordinary matroid is the corresponding binary 3-sum.
Together with `proposition_2_2_three_sum_paper`, this covers every permitted
aligned operation and proves that every input triangle admits such an operation. -/
theorem proposition_2_2_three_sum_without_prescribed_alignment
    {n₁ n₂ : ℕ} {L R : Type*} [Fintype L] [Fintype R]
    (U : Fin 3 ⊕ L → Lattice n₁) (V : Fin 3 ⊕ R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hspanU : Submodule.span ℝ (Set.range (fun l => embed (U (.inr l)))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun l => embed (V (.inr l)))) = ⊤)
    (hCU : (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L)))
    (hCV : (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (V j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ R))) :
    ∃ ε₁ δ₁ ε₂ δ₂ : ℤ,
      (ε₁ = 1 ∨ ε₁ = -1) ∧ (δ₁ = 1 ∨ δ₁ = -1) ∧
      (ε₂ = 1 ∨ ε₂ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧
      SumConclusion triangleBasisLabels (alignedTriangle U ε₁ δ₁) (alignedTriangle V ε₂ δ₂) ∧
      OrdinaryMatroidConclusion triangleBasisLabels
        (alignedTriangle U ε₁ δ₁) (alignedTriangle V ε₂ δ₂) ∧
      VectorMatroid.ofFamily (K := ℝ) (fun j => embed (alignedTriangle U ε₁ δ₁ j)) =
        VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j)) ∧
      VectorMatroid.ofFamily (K := ℝ) (fun j => embed (alignedTriangle V ε₂ δ₂ j)) =
        VectorMatroid.ofFamily (K := ℝ) (fun j => embed (V j)) := by
  obtain ⟨ε₁, δ₁, he₁, hd₁, ht₁, hU', hMU⟩ :=
    triangle_alignment_exists U hU (full_span_of_survivors U hspanU) hCU
  obtain ⟨ε₂, δ₂, he₂, hd₂, ht₂, hV', hMV⟩ :=
    triangle_alignment_exists V hV (full_span_of_survivors V hspanV) hCV
  have hsU' : Submodule.span ℝ
      (Set.range (fun l => embed (alignedTriangle U ε₁ δ₁ (.inr l)))) = ⊤ := by
    simpa only [alignedTriangle_survivor] using hspanU
  have hsV' : Submodule.span ℝ
      (Set.range (fun l => embed (alignedTriangle V ε₂ δ₂ (.inr l)))) = ⊤ := by
    simpa only [alignedTriangle_survivor] using hspanV
  have hcU' : (VectorMatroid.ofFamily (K := ℝ)
      (fun j => embed (alignedTriangle U ε₁ δ₁ j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L)) := by rw [hMU]; exact hCU
  have hcV' : (VectorMatroid.ofFamily (K := ℝ)
      (fun j => embed (alignedTriangle V ε₂ δ₂ j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ R)) := by rw [hMV]; exact hCV
  have h := proposition_2_2_three_sum_paper (alignedTriangle U ε₁ δ₁)
    (alignedTriangle V ε₂ δ₂) hU' hV' hsU' hsV' hcU' hcV' ht₁ ht₂
  exact ⟨ε₁, δ₁, ε₂, δ₂, he₁, hd₁, he₂, hd₂, h.1, h.2, hMU, hMV⟩

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.proposition_2_2_one_sum_complete
#print axioms Unimodular.SignedSums.proposition_2_2_two_sum_paper
#print axioms Unimodular.SignedSums.proposition_2_2_three_sum_paper
#print axioms Unimodular.SignedSums.triangle_alignment_exists
#print axioms Unimodular.SignedSums.proposition_2_2_three_sum_without_prescribed_alignment
#check Unimodular.SignedSums.proposition_2_2_three_sum_without_prescribed_alignment
