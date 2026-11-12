module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Exactness of actual direct sums of character-weight complexes

The index set of weights is arbitrary.  Each vector still has finite
support, and the existing range formula for dependent finitely supported
functions proves exactness of the total map from exactness in every
weight.  In particular no finite bound on characters, coefficient
dimensions, or the complex is introduced.

Candidate until the pinned Lean compiler checks this source.
-/

@[expose] public noncomputable section

namespace ToricPower

open scoped Classical

variable {R : Type*} [Ring R] {I : Type*}

/-- Exactness commutes with the actual algebraic direct sum, with no
finiteness restriction on its index or summands. -/
theorem exact_dfinsupp_mapRange
    {M N P : I → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)] [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (M i)] [∀ i, Module R (N i)] [∀ i, Module R (P i)]
    (f : ∀ i, M i →ₗ[R] N i) (g : ∀ i, N i →ₗ[R] P i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DFinsupp.mapRange.linearMap f) (DFinsupp.mapRange.linearMap g) := by
  rw [LinearMap.exact_iff, DFinsupp.ker_mapRangeLinearMap,
    DFinsupp.range_mapRangeLinearMap]
  have hfg : (fun i => LinearMap.ker (g i)) = fun i => LinearMap.range (f i) :=
    funext fun i => LinearMap.exact_iff.mp (h i)
  rw [hfg]

section Sigma

variable {α β γ : I → Type*}

/-- The coordinate injection of a single weight becomes the ordinary
dependent-single injection under the actual sigma/direct-sum equivalence. -/
theorem sigmaFinsupp_split_injection (i : I) (v : α i →₀ R) :
    sigmaFinsuppLequivDFinsupp R (Finsupp.mapDomain (Sigma.mk i) v) =
      DFinsupp.single i v := by
  induction v using Finsupp.induction with
  | zero => rw [Finsupp.mapDomain_zero, map_zero, DFinsupp.single_zero]
  | single_add a r v _ _ ih =>
      rw [Finsupp.mapDomain_add, map_add, ih, DFinsupp.single_add]
      congr 1
      rw [Finsupp.mapDomain_single]
      exact sigmaFinsuppEquivDFinsupp_single (⟨i,a⟩ : Σ i, α i) r

/-- Conversely, the inverse coordinate equivalence inserts the indicated
weight by the literal `Sigma.mk` map on monomial indices. -/
theorem sigmaFinsupp_join_single (i : I) (v : α i →₀ R) :
    (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.single i v) =
      Finsupp.mapDomain (Sigma.mk i) v := by
  apply (sigmaFinsuppLequivDFinsupp R).injective
  rw [LinearEquiv.apply_symm_apply, sigmaFinsupp_split_injection]

/-- Assemble a family of actual weight-linear maps into its algebraic
direct sum, written on the combined monomial basis. -/
def sigmaWeightMap (f : ∀ i, (α i →₀ R) →ₗ[R] (β i →₀ R)) :
    ((Σ i, α i) →₀ R) →ₗ[R] ((Σ i, β i) →₀ R) :=
  (sigmaFinsuppLequivDFinsupp R).symm.toLinearMap.comp
    ((DFinsupp.mapRange.linearMap f).comp
      (sigmaFinsuppLequivDFinsupp R).toLinearMap)

/-- The assembly formula on an actual monomial basis vector. -/
theorem sigmaWeightMap_single (f : ∀ i, (α i →₀ R) →ₗ[R] (β i →₀ R))
    (i : I) (a : α i) (r : R) :
    sigmaWeightMap f (Finsupp.single ⟨i,a⟩ r) =
      Finsupp.mapDomain (Sigma.mk i) (f i (Finsupp.single a r)) := by
  change (sigmaFinsuppLequivDFinsupp R).symm
      (DFinsupp.mapRange.linearMap f
        (sigmaFinsuppLequivDFinsupp R (Finsupp.single ⟨i,a⟩ r))) = _
  have hs : sigmaFinsuppLequivDFinsupp R (Finsupp.single ⟨i,a⟩ r) =
      DFinsupp.single i (Finsupp.single a r) :=
    sigmaFinsuppEquivDFinsupp_single (⟨i,a⟩ : Σ i, α i) r
  rw [hs]
  simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single,
    sigmaFinsupp_join_single]

/-- Exactness of actual weight maps gives exactness of their combined
monomial matrix.  This is a proved assembly theorem, not an assumption
that the total complex is acyclic. -/
theorem exact_sigmaWeightMap
    (f : ∀ i, (α i →₀ R) →ₗ[R] (β i →₀ R))
    (g : ∀ i, (β i →₀ R) →ₗ[R] (γ i →₀ R))
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (sigmaWeightMap f) (sigmaWeightMap g) := by
  have hsum := exact_dfinsupp_mapRange f g h
  apply (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := sigmaFinsuppLequivDFinsupp R)
    (e₂ := sigmaFinsuppLequivDFinsupp R)
    (e₃ := sigmaFinsuppLequivDFinsupp R) ?_ ?_).mp hsum
  · ext x
    simp only [sigmaWeightMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  · ext x
    simp only [sigmaWeightMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]

end Sigma

end ToricPower
