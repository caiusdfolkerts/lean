/- Literal signed sums with an intrinsic ordinary-matroid conclusion.
The matched side cycles are finite disjoint unions of ordinary circuits,
so the final specification refers only to the original input matroids. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsComplete
public import Recovery.Unimodular.PriorExtensions.SignedSumsCoordinates
public import Recovery.Unimodular.PriorExtensions.SignedSumsDirectMatroid
public import Recovery.Unimodular.PriorExtensions.BinaryMatroidCycles
public import Continuation.Seymour.OrdinaryPortSums
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

/- The intrinsic ordinary sum declarations are owned by
`Continuation.Seymour.OrdinaryPortSums`; reuse those exact declarations here. -/

/-- The ordinary matroid of the actual surviving quotient columns is the
binary sum of the original real input matroids. The witnesses are actual
integral coordinate isomorphisms, and the lattice is the literal quotient. -/
def OrdinaryMatroidConclusion {n₁ n₂ r : ℕ} {T L R : Type*}
    [Fintype T] [Fintype L] [Fintype R]
    (τ : Fin r → T) (U : T ⊕ L → Lattice n₁) (V : T ⊕ R → Lattice n₂) : Prop :=
  ∃ (N₁ : PortNormalization U (fun i => Sum.inl (τ i)))
    (N₂ : PortNormalization V (fun i => Sum.inl (τ i)))
    (eQ : PortQuotient τ U V ≃ₗ[ℤ]
      (Fin r → ℤ) × ((N₁.Complement → ℤ) × (N₂.Complement → ℤ))),
    (∀ j, eQ (PortOutput τ U V j) =
      joinedFamily (R := ℤ) (N₁.equiv ∘ U ∘ Sum.inr) (N₂.equiv ∘ V ∘ Sum.inr) j) ∧
    IsOrdinaryPortSum
      (VectorMatroid.ofFamily (K := ℝ)
        (fun j i => (tripleCoordinates eQ (PortOutput τ U V) i j : ℝ)))
      (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (U j)))
      (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (V j)))

theorem MatroidConclusion.to_ordinary {n₁ n₂ r : ℕ} {T L R : Type*}
    [Fintype T] [Fintype L] [Fintype R]
    {C : Matrix (Fin r) T ℤ} {τ : Fin r → T}
    {U : T ⊕ L → Lattice n₁} {V : T ⊕ R → Lattice n₂}
    (h : MatroidConclusion C τ U V)
    (hportU : ∀ t, U (.inl t) = portMap (fun i => U (.inl (τ i))) (fun i => C i t))
    (hportV : ∀ t, V (.inl t) = portMap (fun i => V (.inl (τ i))) (fun i => C i t)) :
    OrdinaryMatroidConclusion τ U V := by
  rcases h with ⟨N₁, N₂, eQ, hq, hm⟩
  exact ⟨N₁, N₂, eQ, hq, ordinaryPortSum_of_isPortSum hm
    (normalized_input_binary_matroid C τ U hportU N₁)
    (normalized_input_binary_matroid C τ V hportV N₂)⟩

/-- Full Proposition 2.2, signed 2-sum, with the intrinsic standard binary
sum rule on the original ordinary input matroids. All ranks are arbitrary. -/
theorem proposition_2_2_two_sum_ordinary {n₁ n₂ : ℕ} {L R : Type*}
    [Fintype L] [Fintype R]
    (U : Fin 1 ⊕ L → Lattice n₁) (V : Fin 1 ⊕ R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hspanU : Submodule.span ℝ (Set.range (fun l => embed (U (.inr l)))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun l => embed (V (.inr l)))) = ⊤)
    (hpU : U (.inl 0) ≠ 0) (hpV : V (.inl 0) ≠ 0) :
    SumConclusion id U V ∧ OrdinaryMatroidConclusion id U V := by
  have h := proposition_2_2_two_sum_complete U V hU hV hspanU hspanV hpU hpV
  exact ⟨h.1, h.2.to_ordinary (single_port_formula U) (single_port_formula V)⟩

/-- Full Proposition 2.2, signed 3-sum, in every ambient rank, with the exact
aligned triangle and deletion-spanning hypotheses of the paper. -/
theorem proposition_2_2_three_sum_ordinary {n₁ n₂ : ℕ} {L R : Type*}
    [Fintype L] [Fintype R]
    (U : Fin 3 ⊕ L → Lattice n₁) (V : Fin 3 ⊕ R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hspanU : Submodule.span ℝ (Set.range (fun l => embed (U (.inr l)))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun l => embed (V (.inr l)))) = ⊤)
    (haU : LinearIndependent ℝ (fun i => embed (U (.inl (triangleBasisLabels i)))))
    (haV : LinearIndependent ℝ (fun i => embed (V (.inl (triangleBasisLabels i)))))
    (htriU : U (.inl 2) = U (.inl 0) + U (.inl 1))
    (htriV : V (.inl 2) = V (.inl 0) + V (.inl 1)) :
    SumConclusion triangleBasisLabels U V ∧ OrdinaryMatroidConclusion triangleBasisLabels U V := by
  have h := proposition_2_2_three_sum_complete U V hU hV hspanU hspanV haU haV htriU htriV
  exact ⟨h.1, h.2.to_ordinary (triangle_port_formula U htriU) (triangle_port_formula V htriV)⟩

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.binary_support_indicator
#print axioms Unimodular.SignedSums.binary_support_injective
#print axioms Unimodular.SignedSums.IsOrdinaryPortSum.unique
#print axioms Unimodular.SignedSums.proposition_2_2_two_sum_ordinary
#print axioms Unimodular.SignedSums.proposition_2_2_three_sum_ordinary
