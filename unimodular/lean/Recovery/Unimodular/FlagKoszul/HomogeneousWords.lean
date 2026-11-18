module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Lean.Elab.Tactic.Omega

/-!
# Homogeneous word chains with genuine module coefficients

The chain module is the ordinary finitely supported module on words.
Homogeneity is measured by the exact coordinates of a specified module basis:
coefficient degree plus total word degree. No exactness property is part of
the definition. The induction and transport lemmas retain all word lengths
and internal degrees.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul.HomogeneousWords

variable {K I J J' M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

def wordDegree (δ : I → ℕ) (L : List I) : ℕ := (L.map δ).sum

@[simp] theorem wordDegree_nil (δ : I → ℕ) : wordDegree δ [] = 0 := rfl
@[simp] theorem wordDegree_cons (δ : I → ℕ) (i : I) (L : List I) :
    wordDegree δ (i :: L) = δ i + wordDegree δ L := rfl
@[simp] theorem wordDegree_append (δ : I → ℕ) (L T : List I) :
    wordDegree δ (L ++ T) = wordDegree δ L + wordDegree δ T := by
  simp [wordDegree]

def piece (D : Module.Basis J K M) (δ : I → ℕ) (d : J → ℕ) (r q : ℕ) :
    Submodule K (List I →₀ M) where
  carrier := {z | ∀ L j, D.repr (z L) j ≠ 0 → L.length = r ∧ d j + wordDegree δ L = q}
  zero_mem' := by intro L j h; exact (h (by simp)).elim
  add_mem' := by
    intro z w hz hw L j h
    by_cases hzj : D.repr (z L) j = 0
    · apply hw L j
      simpa only [Finsupp.add_apply, map_add, hzj, zero_add] using h
    · exact hz L j hzj
  smul_mem' := by
    intro c z hz L j h
    apply hz L j
    intro he
    apply h
    simp only [Finsupp.smul_apply, map_smul, smul_eq_mul, he, mul_zero]

@[simp] theorem mem_piece (D : Module.Basis J K M) (δ : I → ℕ) (d : J → ℕ)
    (r q : ℕ) (z : List I →₀ M) :
    z ∈ piece D δ d r q ↔
      ∀ L j, D.repr (z L) j ≠ 0 → L.length = r ∧ d j + wordDegree δ L = q := Iff.rfl

theorem single_basis_mem_piece (D : Module.Basis J K M) (δ : I → ℕ) (d : J → ℕ)
    {r q : ℕ} (L : List I) (j : J) (hL : L.length = r)
    (hj : d j + wordDegree δ L = q) :
    Finsupp.single L (D j) ∈ piece D δ d r q := by
  classical
  intro T a ha
  by_cases hTL : T = L
  · subst T
    by_cases haj : a = j
    · subst a
      exact ⟨hL, hj⟩
    · exact (ha (by simp [Finsupp.single_apply, haj, Ne.symm haj])).elim
  · exact (ha (by simp [Finsupp.single_apply, hTL, Ne.symm hTL])).elim

theorem single_smul_basis_mem_piece (D : Module.Basis J K M) (δ : I → ℕ) (d : J → ℕ)
    {r q : ℕ} (L : List I) (j : J) (c : K) (hL : L.length = r)
    (hj : d j + wordDegree δ L = q) :
    c • Finsupp.single L (D j) ∈ piece D δ d r q :=
  (piece D δ d r q).smul_mem c (single_basis_mem_piece D δ d L j hL hj)

private theorem property_sum {α V : Type*} [AddCommMonoid V]
    (P : V → Prop) (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (s : Finset α) (f : α → V) (h : ∀ a ∈ s, P (f a)) : P (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hzero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hadd _ _ (h a (Finset.mem_insert_self _ _))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/-- Induction over the actual homogeneous word-basis coefficients. -/
theorem piece_induction (D : Module.Basis J K M) (δ : I → ℕ) (d : J → ℕ)
    {r q : ℕ} (P : (List I →₀ M) → Prop)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hbasis : ∀ L j (c : K), L.length = r → d j + wordDegree δ L = q →
      P (c • Finsupp.single L (D j)))
    (z : List I →₀ M) (hz : z ∈ piece D δ d r q) : P z := by
  classical
  have hzsum : (∑ L ∈ z.support, Finsupp.single L (z L)) = z := by
    simpa only [Finsupp.sum] using z.sum_single
  rw [← hzsum]
  apply property_sum P hzero hadd
  intro L hL
  have hcoeff : (∑ j ∈ (D.repr (z L)).support, D.repr (z L) j • D j) = z L := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using D.linearCombination_repr (z L)
  have hexp : (∑ j ∈ (D.repr (z L)).support,
      D.repr (z L) j • Finsupp.single L (D j)) = Finsupp.single L (z L) := by
    simpa only [map_sum, map_smul, Finsupp.lsingle_apply] using
      congrArg (Finsupp.lsingle (R := K) L) hcoeff
  rw [← hexp]
  apply property_sum P hzero hadd
  intro j hj
  have hdeg := hz L j (Finsupp.mem_support_iff.mp hj)
  exact hbasis L j _ hdeg.1 hdeg.2

/-- Any word-chain linear map preserving the required basis formulas
preserves the whole actual homogeneous piece. -/
theorem linearMap_mem_piece_of_basis (D : Module.Basis J K M)
    (E : Module.Basis J' K N) (δ : I → ℕ) (d : J → ℕ) (e : J' → ℕ)
    {r q r' q' : ℕ} (f : (List I →₀ M) →ₗ[K] (List I →₀ N))
    (hbasis : ∀ L j, L.length = r → d j + wordDegree δ L = q →
      f (Finsupp.single L (D j)) ∈ piece E δ e r' q')
    {z : List I →₀ M} (hz : z ∈ piece D δ d r q) :
    f z ∈ piece E δ e r' q' := by
  apply piece_induction D δ d (fun z => f z ∈ piece E δ e r' q')
    (by simpa only [map_zero] using (piece E δ e r' q').zero_mem)
    (fun x y hx hy => by simpa only [map_add] using (piece E δ e r' q').add_mem hx hy)
    (fun L j c hL hj => by
      simpa only [map_smul] using (piece E δ e r' q').smul_mem c (hbasis L j hL hj)) z hz

/-- Exact total-degree transport by a coefficient-module map. -/
theorem coefficientMap_mem_piece (D : Module.Basis J K M)
    (E : Module.Basis J' K N) (δ : I → ℕ) (d : J → ℕ) (e : J' → ℕ)
    (f : M →ₗ[K] N) (c : ℕ)
    (hf : ∀ j a, E.repr (f (D j)) a ≠ 0 → e a = d j + c)
    {r q : ℕ} {z : List I →₀ M} (hz : z ∈ piece D δ d r q) :
    Finsupp.mapRange.linearMap f z ∈ piece E δ e r (q + c) := by
  apply linearMap_mem_piece_of_basis D E δ d e (Finsupp.mapRange.linearMap f) ?_ hz
  intro L j hL hj T a ha
  classical
  by_cases hTL : T = L
  · subst T
    have hfa : E.repr (f (D j)) a ≠ 0 := by simpa using ha
    refine ⟨hL, ?_⟩
    rw [hf j a hfa]
    omega
  · exact (ha (by simp [Finsupp.single_apply, hTL, Ne.symm hTL])).elim

#print axioms single_basis_mem_piece
#print axioms piece_induction
#print axioms linearMap_mem_piece_of_basis
#print axioms coefficientMap_mem_piece

end Unimodular.FlagKoszul.HomogeneousWords
