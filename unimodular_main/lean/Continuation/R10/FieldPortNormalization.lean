module

public import Recovery.Unimodular.PriorExtensions.BinaryMatroidCycles
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Normal forms for arbitrary field representations at a port

The common port is split off from the entire representation space by an actual
linear equivalence.  No finite-dimensionality, chosen basis, or pre-existing
normal form of either factor is assumed.  For binary singletons and triangles,
the hypotheses are ordinary matroid independence and circuit predicates.
-/

noncomputable section
open Set
open scoped BigOperators

namespace Unimodular.SignedSums.FieldPorts

variable {K P V : Type*} [Field K]
  [AddCommGroup P] [Module K P] [AddCommGroup V] [Module K V]

/-- Every injectively represented port admits coordinates which fix the port
pointwise and put all remaining coordinates in a complementary vector space. -/
theorem exists_port_coordinates (a : P →ₗ[K] V) (ha : Function.Injective a) :
    ∃ N : Submodule K V, ∃ e : V ≃ₗ[K] P × N,
      ∀ p : P, e (a p) = (p, 0) := by
  obtain ⟨N, hN⟩ := (LinearMap.range a).exists_isCompl
  let b := LinearEquiv.ofInjective a ha
  let c := Submodule.prodEquivOfIsCompl (LinearMap.range a) N hN
  let e := c.symm.trans (b.symm.prodCongr (LinearEquiv.refl K N))
  refine ⟨N, e, ?_⟩
  intro p
  have hc : c.symm (a p) = (b p, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left (LinearMap.range a) N hN (b p)
  change (b.symm.prodCongr (LinearEquiv.refl K N)) (c.symm (a p)) = (p, 0)
  rw [hc]
  simp

/-- An arbitrary represented family whose ports are an injective copy of a
specified port family has the usual product normal form. -/
theorem exists_family_normal_form {T L : Type*}
    (ports : T → P) (v : T ⊕ L → V)
    (a : P →ₗ[K] V) (ha : Function.Injective a)
    (hport : ∀ t, v (Sum.inl t) = a (ports t)) :
    ∃ N : Submodule K V, ∃ e : V ≃ₗ[K] P × N, ∃ u : L → P × N,
      e ∘ v = Sum.elim (fun t ↦ (ports t, (0 : N))) u := by
  obtain ⟨N, e, he⟩ := exists_port_coordinates a ha
  refine ⟨N, e, (fun l ↦ e (v (Sum.inr l))), ?_⟩
  funext x
  cases x with
  | inl t => simpa only [Function.comp_apply, Sum.elim_inl, hport t] using he (ports t)
  | inr l => rfl

/-- The normal form preserves the actual ordinary vector matroid on every
subset of its label set, not merely the ranks of selected subsets. -/
theorem exists_matroid_normal_form {T L : Type*}
    (ports : T → P) (v : T ⊕ L → V)
    (a : P →ₗ[K] V) (ha : Function.Injective a)
    (hport : ∀ t, v (Sum.inl t) = a (ports t)) :
    ∃ N : Submodule K V, ∃ u : L → P × N,
      VectorMatroid.ofFamily (K := K) v =
        VectorMatroid.ofFamily (K := K) (Sum.elim (fun t ↦ (ports t, (0 : N))) u) := by
  obtain ⟨N, e, u, he⟩ := exists_family_normal_form ports v a ha hport
  refine ⟨N, u, ?_⟩
  rw [← he]
  apply (VectorMatroid.ofFamily_eq_iff v (e ∘ v)).2
  intro I
  exact (e.toLinearMap.linearIndepOn_iff_of_injOn e.injective.injOn).symm

end Unimodular.SignedSums.FieldPorts

namespace Unimodular.SignedSums.Binary

open Unimodular.SignedSums.FieldPorts

variable {V L : Type*} [AddCommGroup V] [Module F V]

/-- A nonloop singleton port in any binary representation has the standard
one-dimensional port coordinates. -/
theorem single_port_normal_form (v : Fin 1 ⊕ L → V)
    (hport : (VectorMatroid.ofFamily (K := F) v).Indep
      (Set.range (Sum.inl : Fin 1 → Fin 1 ⊕ L))) :
    ∃ N : Submodule F V, ∃ u : L → (Fin 1 → F) × N,
      VectorMatroid.ofFamily (K := F) v =
        VectorMatroid.ofFamily (K := F) (sideFamily singlePort u) := by
  have hli : LinearIndependent F (fun i : Fin 1 ↦ v (Sum.inl i)) :=
    (linearIndepOn_range_iff Sum.inl_injective v).mp
      ((VectorMatroid.ofFamily_indep _ _).mp hport)
  let a := Fintype.linearCombination F (fun i : Fin 1 ↦ v (Sum.inl i))
  apply exists_matroid_normal_form singlePort v a hli.fintypeLinearCombination_injective
  intro i
  fin_cases i
  simp [a, singlePort, Fintype.linearCombination_apply, Fin.sum_univ_succ]

/-- In any binary representation, a triangle circuit is represented by two
independent vectors and their sum.  This is derived from the ordinary circuit
predicate, so the normal form does not add a representation hypothesis. -/
theorem triangle_port_normal_form (v : Fin 3 ⊕ L → V)
    (hport : (VectorMatroid.ofFamily (K := F) v).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L))) :
    ∃ N : Submodule F V, ∃ u : L → (Fin 2 → F) × N,
      VectorMatroid.ofFamily (K := F) v =
        VectorMatroid.ofFamily (K := F) (sideFamily trianglePort u) := by
  classical
  let f : Fin 2 → Fin 3 ⊕ L := fun i ↦ Sum.inl i.castSucc
  have hf : Function.Injective f := fun i j h ↦ Fin.castSucc_injective 2
    (Sum.inl_injective h)
  have hsub : Set.range f ⊂ Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L) := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, rfl⟩
    · intro h
      have hlast : Sum.inl (2 : Fin 3) ∈ Set.range f := by rw [h]; exact ⟨2, rfl⟩
      obtain ⟨i, hi⟩ := hlast
      fin_cases i <;> simp [f] at hi
  have hli : LinearIndependent F (fun i : Fin 2 ↦ v (f i)) :=
    (linearIndepOn_range_iff hf v).mp
      ((VectorMatroid.ofFamily_indep _ _).mp (hport.ssubset_indep hsub))
  let C : Finset (Fin 3 ⊕ L) := Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩
  have hC : (C : Set (Fin 3 ⊕ L)) = Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L) := by
    ext x
    simp [C]
  have hsum := BinaryMatroidCycles.circuit_sum_eq_zero v (C := C) (by rw [hC]; exact hport)
  have hs : v (Sum.inl 0) + v (Sum.inl 1) + v (Sum.inl 2) = 0 := by
    simpa [C, Fin.sum_univ_succ, add_assoc] using hsum
  have hthird : v (Sum.inl 2) = v (Sum.inl 0) + v (Sum.inl 1) := by
    apply add_left_cancel (a := v (Sum.inl 0) + v (Sum.inl 1))
    exact hs.trans (ZModModule.add_self _).symm
  let a := Fintype.linearCombination F (fun i : Fin 2 ↦ v (f i))
  apply exists_matroid_normal_form trianglePort v a hli.fintypeLinearCombination_injective
  intro i
  fin_cases i <;>
    simp [a, trianglePort, Fintype.linearCombination_apply, Fin.sum_univ_succ, f, hthird]

/-- The empty common port also admits the same product presentation. -/
theorem empty_port_normal_form (v : Fin 0 ⊕ L → V) :
    ∃ N : Submodule F V, ∃ u : L → (Fin 0 → F) × N,
      VectorMatroid.ofFamily (K := F) v =
        VectorMatroid.ofFamily (K := F) (sideFamily (Fin.elim0 : Fin 0 → Fin 0 → F) u) := by
  apply exists_matroid_normal_form Fin.elim0 v (0 : (Fin 0 → F) →ₗ[F] V)
    (fun _ _ _ ↦ Subsingleton.elim _ _)
  intro i
  exact Fin.elim0 i

#print axioms triangle_port_normal_form
#print axioms single_port_normal_form
end Unimodular.SignedSums.Binary
