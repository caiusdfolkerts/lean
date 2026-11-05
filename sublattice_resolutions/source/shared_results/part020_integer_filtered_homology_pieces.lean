module
public import graph_foundation.part014
public import shared_results.part020_multiplicative_degeneration

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredHomologyPieces -/
section

/-! # Individual homological degrees in multiplicative degeneration

The total square-zero differential is allowed to shift the grading. Projecting
an actual lifted cycle to its original homogeneous degree gives a homogeneous
cycle lift. Thus the comparison preserves each three-term homology group,
not only the sum of the homology dimensions over homological degrees.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical DirectSum
open scoped BigOperators

variable {K A Γ : Type*} [Field K] [Ring A] [Algebra K A]
  [AddCancelCommMonoid Γ] [DecidableEq Γ]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (P : Γ → Submodule K A) [DirectSum.Decomposition P]
  [∀ i, FiniteDimensional K (P i)] (δ : Γ)
  (hD : ∀ i x, x ∈ P i → D.d x ∈ P (i + δ))

include hD in
theorem shifted_differential_decompose_commutes (i : Γ) (x : A) :
    D.d (DirectSum.decompose P x i).val =
      (DirectSum.decompose P (D.d x) (i + δ)).val := by
  refine DirectSum.Decomposition.inductionOn P (by simp) ?_ ?_ x
  · intro j a
    by_cases hji : j = i
    · subst j
      rw [DirectSum.decompose_of_mem_same P a.property,
        DirectSum.decompose_of_mem_same P (hD i a.val a.property)]
    · rw [DirectSum.decompose_of_mem_ne P a.property hji,
        DirectSum.decompose_of_mem_ne P (hD j a.val a.property)
          (fun h => hji (add_right_cancel h)), map_zero]
  · intro x y hx hy
    simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply,
      Submodule.coe_add, hx, hy]

def degreeDifferential (i : Γ) : P i →ₗ[K] P (i + δ) :=
  (D.d.domRestrict (P i)).codRestrict (P (i + δ)) (fun x => hD i x.val x.property)

theorem degreeDifferential_comp (i : Γ) :
    (degreeDifferential D P δ hD (i + δ)).comp
      (degreeDifferential D P δ hD i) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact D.square_zero x.val

variable (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)

include hd in
theorem degreeDifferential_preserves (i : Γ) (L : ℤ)
    (hL : (F.level (L - 1)).comap (P i).subtype = ⊥)
    (hL' : (F.level (L - 1)).comap (P (i + δ)).subtype = ⊥) :
    FilteredHomology.Preserves (F.componentFiltration (P i) L hL)
      (F.componentFiltration (P (i + δ)) L hL') (degreeDifferential D P δ hD i) := by
  intro n x hx
  exact hd (L + (n : ℤ) - 1) x.val hx

theorem degreeDifferential_liftsCycles
    (hF : ∀ n, SetLike.IsHomogeneous P (F.level n))
    (hlift : F.LiftsCycles D) (i : Γ) (L : ℤ)
    (hL : (F.level (L - 1)).comap (P i).subtype = ⊥)
    (hL' : (F.level (L - 1)).comap (P (i + δ)).subtype = ⊥) :
    FilteredHomology.LiftsCycles (F.componentFiltration (P i) L hL)
      (F.componentFiltration (P (i + δ)) L hL') (degreeDifferential D P δ hD i) := by
  intro n x hx hdx
  have hx' : x.val ∈ F.level (L + (n : ℤ)) := by
    change x.val ∈ F.level (L + ((n + 1 : ℕ) : ℤ) - 1) at hx
    have he : L + ((n + 1 : ℕ) : ℤ) - 1 = L + (n : ℤ) := by omega
    simpa only [he] using hx
  have hdx' : D.d x.val ∈ F.level (L + (n : ℤ) - 1) := hdx
  obtain ⟨z, hzF, hzd, hxz⟩ := hlift (L + (n : ℤ)) x.val hx' hdx'
  let z' : P i := DirectSum.decompose P z i
  refine ⟨z', ?_, ?_, ?_⟩
  · change z'.val ∈ F.level (L + ((n + 1 : ℕ) : ℤ) - 1)
    have hz := hF (L + (n : ℤ)) i hzF
    have he : L + ((n + 1 : ℕ) : ℤ) - 1 = L + (n : ℤ) := by omega
    simpa only [he] using hz
  · apply Subtype.ext
    change D.d (DirectSum.decompose P z i).val = 0
    rw [shifted_differential_decompose_commutes D P δ hD, hzd]
    simp
  · have he := hF (L + (n : ℤ) - 1) i hxz
    rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      DirectSum.decompose_of_mem_same P x.property] at he
    exact he

/-- Dimension equality in one individual homogeneous homology group. -/
theorem degree_homology_dimension_eq_of_liftsCycles
    (hF : ∀ n, SetLike.IsHomogeneous P (F.level n))
    (hlift : F.LiftsCycles D) (i : Γ) (L : ℤ)
    (hL₀ : (F.level (L - 1)).comap (P i).subtype = ⊥)
    (hL₁ : (F.level (L - 1)).comap (P (i + δ)).subtype = ⊥)
    (hL₂ : (F.level (L - 1)).comap (P (i + δ + δ)).subtype = ⊥)
    (N : ℕ) (hN : (F.componentFiltration (P (i + δ)) L hL₁).level N = ⊤) :
    Module.finrank K (FilteredHomology.Homology
      (degreeDifferential D P δ hD i) (degreeDifferential D P δ hD (i + δ))
      (degreeDifferential_comp D P δ hD i)) =
      ∑ n ∈ Finset.range N,
        Module.finrank K (FilteredHomology.GradedHomology
          (F.componentFiltration (P i) L hL₀)
          (F.componentFiltration (P (i + δ)) L hL₁)
          (F.componentFiltration (P (i + δ + δ)) L hL₂)
          (degreeDifferential D P δ hD i) (degreeDifferential D P δ hD (i + δ))
          (F.degreeDifferential_preserves D P δ hD hd i L hL₀ hL₁)
          (F.degreeDifferential_preserves D P δ hD hd (i + δ) L hL₁ hL₂)
          (degreeDifferential_comp D P δ hD i) n) :=
  FilteredHomology.finrank_homology_eq_sum_graded
    (F.componentFiltration (P i) L hL₀)
    (F.componentFiltration (P (i + δ)) L hL₁)
    (F.componentFiltration (P (i + δ + δ)) L hL₂)
    (degreeDifferential D P δ hD i) (degreeDifferential D P δ hD (i + δ))
    (F.degreeDifferential_preserves D P δ hD hd i L hL₀ hL₁)
    (F.degreeDifferential_preserves D P δ hD hd (i + δ) L hL₁ hL₂)
    (degreeDifferential_comp D P δ hD i) N hN
    (F.degreeDifferential_liftsCycles D P δ hD hF hlift i L hL₀ hL₁)
    (F.degreeDifferential_liftsCycles D P δ hD hF hlift (i + δ) L hL₁ hL₂)

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
