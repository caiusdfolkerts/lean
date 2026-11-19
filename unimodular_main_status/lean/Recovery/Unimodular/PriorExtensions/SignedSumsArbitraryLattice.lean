module

public import Recovery.Unimodular.PriorExtensions.SignedSumsLatticeTransport

/-!
# Signed sums on the original arbitrary integral lattices

These wrappers retain the paper's actual real embeddings, ordinary input
matroids, integral relation quotient and surviving columns. Coordinates are
chosen by an arbitrary lattice basis and eliminated from the conclusions.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open TauCeti.Toric

namespace Unimodular.SignedSums
open LatticeCoordinates

section OrdinaryMatroid
variable {r : ℕ} {N₁ N₂ V₁ V₂ T L S : Type*}
  [AddCommGroup N₁] [AddCommGroup N₂]
  [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
  [Fintype T] [Fintype L] [Fintype S]

/-- The actual original quotient has a finite integral coordinate realization
whose ordinary matroid is the intrinsic sum of the original real matroids. -/
def LatticeOrdinaryMatroidConclusion (ι₁ : N₁ →+ V₁) (ι₂ : N₂ →+ V₂)
    (τ : Fin r → T) (U : T ⊕ L → N₁) (V : T ⊕ S → N₂) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (q : LatticePortQuotient τ U V ≃ₗ[ℤ] (I → ℤ)),
    IsOrdinaryPortSum
      (VectorMatroid.ofFamily (K := ℝ) (fun j i => (q (latticePortOutput τ U V j) i : ℝ)))
      (VectorMatroid.ofFamily (K := ℝ) (fun j => ι₁ (U j)))
      (VectorMatroid.ofFamily (K := ℝ) (fun j => ι₂ (V j)))

theorem latticeOrdinaryMatroidConclusion_of_coordinates {n₁ n₂ : ℕ}
    {ι₁ : N₁ →+ V₁} {ι₂ : N₂ →+ V₂}
    (hι₁ : IsIntegralLattice ι₁) (hι₂ : IsIntegralLattice ι₂)
    (b₁ : Module.Basis (Fin n₁) ℤ N₁) (b₂ : Module.Basis (Fin n₂) ℤ N₂)
    (τ : Fin r → T) (U : T ⊕ L → N₁) (V : T ⊕ S → N₂)
    (h : OrdinaryMatroidConclusion τ (latticeEquiv b₁ ∘ U) (latticeEquiv b₂ ∘ V)) :
    LatticeOrdinaryMatroidConclusion ι₁ ι₂ τ U V := by
  classical
  obtain ⟨D₁, D₂, eQ, _hq, hm⟩ := h
  let I := Fin r ⊕ (D₁.Complement ⊕ D₂.Complement)
  let q : LatticePortQuotient τ U V ≃ₗ[ℤ] (I → ℤ) :=
    (coordinatePortQuotientEquiv (latticeEquiv b₁) (latticeEquiv b₂) τ U V).trans
      (eQ.trans (packThree (Fin r) D₁.Complement D₂.Complement ℤ).symm)
  refine ⟨I, inferInstance, q, ?_⟩
  have hout : (fun j i => (q (latticePortOutput τ U V j) i : ℝ)) =
      (fun j i => (tripleCoordinates eQ
        (PortOutput τ (latticeEquiv b₁ ∘ U) (latticeEquiv b₂ ∘ V)) i j : ℝ)) := by
    funext j i
    change ((packThree (Fin r) D₁.Complement D₂.Complement ℤ).symm
      (eQ (coordinatePortQuotientEquiv (latticeEquiv b₁) (latticeEquiv b₂) τ U V
        (latticePortOutput τ U V j))) i : ℝ) = _
    rw [coordinatePortQuotientEquiv_output]
    rfl
  rw [hout]
  simpa only [Function.comp_apply, lattice_matroid_coordinates hι₁ b₁ U,
    lattice_matroid_coordinates hι₂ b₂ V] using hm

end OrdinaryMatroid

/-- A chosen finite integral coordinate realization does not change the
ordinary real matroid of a quotient configuration. -/
theorem lattice_matroid_coordinate_independent {Q E I J : Type*}
    [AddCommGroup Q] [Fintype I] [Fintype J]
    (q : Q ≃ₗ[ℤ] (I → ℤ)) (q' : Q ≃ₗ[ℤ] (J → ℤ)) (u : E → Q) :
    VectorMatroid.ofFamily (K := ℝ) (fun j i => (q' (u j) i : ℝ)) =
      VectorMatroid.ofFamily (K := ℝ) (fun j i => (q (u j) i : ℝ)) := by
  simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, Function.comp_apply] using
    integralEquiv_matroid ℝ (q.symm.trans q') (q ∘ u)

section PaperWrappers
variable {n₁ n₂ : ℕ} {N₁ N₂ V₁ V₂ L S : Type*}
  [AddCommGroup N₁] [AddCommGroup N₂]
  [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
  {ι₁ : N₁ →+ V₁} {ι₂ : N₂ →+ V₂}
  [Fintype L] [Fintype S]

/-- Proposition2.2, signed two-sum, directly on arbitrary original lattices.
The full-rank and ordinary non-coloop hypotheses are exactly the paper's. -/
theorem proposition_2_2_two_sum_arbitrary_lattice
    (hι₁ : IsIntegralLattice ι₁) (hι₂ : IsIntegralLattice ι₂)
    (b₁ : Module.Basis (Fin n₁) ℤ N₁) (b₂ : Module.Basis (Fin n₂) ℤ N₂)
    (U : Fin 1 ⊕ L → N₁) (V : Fin 1 ⊕ S → N₂)
    (hU : IntegralRigidity.Uniform b₁ U) (hV : IntegralRigidity.Uniform b₂ V)
    (hfullU : Submodule.span ℝ (Set.range (fun j => ι₁ (U j))) = ⊤)
    (hfullV : Submodule.span ℝ (Set.range (fun j => ι₂ (V j))) = ⊤)
    (hpU : U (.inl 0) ≠ 0) (hpV : V (.inl 0) ≠ 0)
    (hcU : ¬ (VectorMatroid.ofFamily (K := ℝ) (fun j => ι₁ (U j))).IsColoop (.inl 0))
    (hcV : ¬ (VectorMatroid.ofFamily (K := ℝ) (fun j => ι₂ (V j))).IsColoop (.inl 0)) :
    LatticeSumConclusion n₁ n₂ id U V ∧ LatticeOrdinaryMatroidConclusion ι₁ ι₂ id U V := by
  have h := proposition_2_2_two_sum_paper (latticeEquiv b₁ ∘ U) (latticeEquiv b₂ ∘ V)
    ((uniform_coordinates_iff b₁ U).mpr hU) ((uniform_coordinates_iff b₂ V).mpr hV)
    ((lattice_span_coordinates_iff hι₁ b₁ U).mpr hfullU)
    ((lattice_span_coordinates_iff hι₂ b₂ V).mpr hfullV)
    (fun h => hpU ((latticeEquiv b₁).injective (by simpa only [Function.comp_apply, map_zero] using h)))
    (fun h => hpV ((latticeEquiv b₂).injective (by simpa only [Function.comp_apply, map_zero] using h)))
    (by simpa only [Function.comp_apply, lattice_matroid_coordinates hι₁ b₁ U] using hcU)
    (by simpa only [Function.comp_apply, lattice_matroid_coordinates hι₂ b₂ V] using hcV)
  exact ⟨latticeSumConclusion_of_coordinates (latticeEquiv b₁) (latticeEquiv b₂) id U V h.1,
    latticeOrdinaryMatroidConclusion_of_coordinates hι₁ hι₂ b₁ b₂ id U V h.2⟩

/-- Proposition2.2, aligned signed three-sum, on arbitrary original lattices.
No quotient saturation or additional triangle cocircuit condition is assumed. -/
theorem proposition_2_2_three_sum_arbitrary_lattice
    (hι₁ : IsIntegralLattice ι₁) (hι₂ : IsIntegralLattice ι₂)
    (b₁ : Module.Basis (Fin n₁) ℤ N₁) (b₂ : Module.Basis (Fin n₂) ℤ N₂)
    (U : Fin 3 ⊕ L → N₁) (V : Fin 3 ⊕ S → N₂)
    (hU : IntegralRigidity.Uniform b₁ U) (hV : IntegralRigidity.Uniform b₂ V)
    (hspanU : Submodule.span ℝ (Set.range (fun j => ι₁ (U (.inr j)))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun j => ι₂ (V (.inr j)))) = ⊤)
    (hCU : (VectorMatroid.ofFamily (K := ℝ) (fun j => ι₁ (U j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L)))
    (hCV : (VectorMatroid.ofFamily (K := ℝ) (fun j => ι₂ (V j))).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ S)))
    (htriU : U (.inl 2) = U (.inl 0) + U (.inl 1))
    (htriV : V (.inl 2) = V (.inl 0) + V (.inl 1)) :
    LatticeSumConclusion n₁ n₂ triangleBasisLabels U V ∧
      LatticeOrdinaryMatroidConclusion ι₁ ι₂ triangleBasisLabels U V := by
  have h := proposition_2_2_three_sum_paper (latticeEquiv b₁ ∘ U) (latticeEquiv b₂ ∘ V)
    ((uniform_coordinates_iff b₁ U).mpr hU) ((uniform_coordinates_iff b₂ V).mpr hV)
    ((lattice_span_coordinates_iff hι₁ b₁ (U ∘ Sum.inr)).mpr hspanU)
    ((lattice_span_coordinates_iff hι₂ b₂ (V ∘ Sum.inr)).mpr hspanV)
    (by simpa only [Function.comp_apply, lattice_matroid_coordinates hι₁ b₁ U] using hCU)
    (by simpa only [Function.comp_apply, lattice_matroid_coordinates hι₂ b₂ V] using hCV)
    (by simpa only [Function.comp_apply, map_add] using congrArg (latticeEquiv b₁) htriU)
    (by simpa only [Function.comp_apply, map_add] using congrArg (latticeEquiv b₂) htriV)
  exact ⟨latticeSumConclusion_of_coordinates (latticeEquiv b₁) (latticeEquiv b₂)
      triangleBasisLabels U V h.1,
    latticeOrdinaryMatroidConclusion_of_coordinates hι₁ hι₂ b₁ b₂ triangleBasisLabels U V h.2⟩

end PaperWrappers

#print axioms latticeOrdinaryMatroidConclusion_of_coordinates
#print axioms lattice_matroid_coordinate_independent
#print axioms proposition_2_2_two_sum_arbitrary_lattice
#print axioms proposition_2_2_three_sum_arbitrary_lattice

end Unimodular.SignedSums

#check Unimodular.SignedSums.proposition_2_2_three_sum_arbitrary_lattice
