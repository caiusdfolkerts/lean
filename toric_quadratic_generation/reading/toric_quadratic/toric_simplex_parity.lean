module
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Lean.Elab.Tactic.Omega
@[expose] public section
/-!
# Integral simplex allocation with prescribed parity

The allocation theorem below is the homogeneous-coordinate form of Lemma 4.4
of *Quadratic generation for smooth polytopes with long edges*.
No geometric statements about arbitrary smooth polytopes are assumed here.
-/

namespace PaperVerification.Toric

open scoped BigOperators

/-- Allocate a prescribed number of tokens among finitely many integral capacities. -/
theorem allocate_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℕ) (k : ℕ) (hk : k ≤ ∑ i ∈ s, c i) :
    ∃ u : ι → ℕ, (∀ i ∈ s, u i ≤ c i) ∧ (∑ i ∈ s, u i) = k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
      have : k = 0 := by simpa using hk
      subst k
      exact ⟨fun _ => 0, by simp⟩
  | @insert a s ha ih =>
      have hk' : k ≤ c a + ∑ i ∈ s, c i := by simpa [Finset.sum_insert ha] using hk
      obtain ⟨u, hu, hsum⟩ := ih (k - min k (c a)) (by omega)
      refine ⟨Function.update u a (min k (c a)), ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp
        · simp only [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
          exact hu i hi
      · rw [Finset.sum_insert ha]
        have hupdate : ∑ i ∈ s, Function.update u a (min k (c a)) i = ∑ i ∈ s, u i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Function.update_of_ne (ne_of_mem_of_not_mem hi ha) _ _
        rw [hupdate]
        simp only [Function.update_self]
        omega

/-- A zero-one sum on `d + 1` coordinates cannot exceed `k ≥ d` if its parity is `k`'s. -/
theorem bit_sum_le {d k : ℕ} (e : Fin (d + 1) → ℕ)
    (he : ∀ i, e i ≤ 1) (hdk : d ≤ k) (hpar : (∑ i, e i) % 2 = k % 2) :
    ∑ i, e i ≤ k := by
  have hbound : (∑ i, e i) ≤ d + 1 := by
    calc
      (∑ i, e i) ≤ ∑ _ : Fin (d + 1), 1 := Finset.sum_le_sum (fun i _ => he i)
      _ = d + 1 := by simp
  omega

/-- Full homogeneous-coordinate simplex parity allocation.

`m` is an interior integral point of the sum of simplices of degrees `k` and `l`.
The requested parity `e` includes the zeroth homogeneous coordinate; its sum must
therefore have the parity of `k`. The dimension is arbitrary.
-/
theorem simplex_parity_homogeneous {d k l : ℕ}
    (hdk : d ≤ k) (hdl : d ≤ l)
    (m e : Fin (d + 1) → ℕ)
    (hm : ∀ i, 0 < m i) (he : ∀ i, e i ≤ 1)
    (hsum : ∑ i, m i = k + l)
    (hpar : (∑ i, e i) % 2 = k % 2) :
    ∃ a b : Fin (d + 1) → ℕ,
      (∀ i, a i + b i = m i) ∧
      (∑ i, a i) = k ∧ (∑ i, b i) = l ∧
      (∀ i, a i % 2 = e i) := by
  let c : Fin (d + 1) → ℕ := fun i => (m i - e i) / 2
  let f : Fin (d + 1) → ℕ := fun i => (m i - e i) % 2
  have hef : ∀ i, e i + 2 * c i + f i = m i := by
    intro i
    dsimp [c, f]
    have := Nat.mod_add_div (m i - e i) 2
    have := hm i
    have := he i
    omega
  have hf : ∀ i, f i ≤ 1 := by
    intro i
    dsimp [f]
    omega
  have htotal : (∑ i, e i) + 2 * (∑ i, c i) + (∑ i, f i) = k + l := by
    calc
      _ = ∑ i, (e i + 2 * c i + f i) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i, m i := Finset.sum_congr rfl (fun i _ => hef i)
      _ = k + l := hsum
  have hE : (∑ i, e i) ≤ k := bit_sum_le e he hdk hpar
  have hFpar : (∑ i, f i) % 2 = l % 2 := by omega
  have hF : (∑ i, f i) ≤ l := bit_sum_le f hf hdl hFpar
  have hK : k = (∑ i, e i) + 2 * ((k - ∑ i, e i) / 2) := by omega
  have hcap : (k - ∑ i, e i) / 2 ≤ ∑ i, c i := by omega
  obtain ⟨u, hu, husum⟩ := allocate_le_sum Finset.univ c ((k - ∑ i, e i) / 2) hcap
  let a : Fin (d + 1) → ℕ := fun i => e i + 2 * u i
  have ha : ∀ i, a i ≤ m i := by
    intro i
    have := hu i (Finset.mem_univ i)
    have := hef i
    dsimp [a]
    omega
  refine ⟨a, fun i => m i - a i, ?_, ?_, ?_, ?_⟩
  · intro i
    change a i + (m i - a i) = m i
    have := ha i
    omega
  · dsimp [a]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, husum]
    omega
  · have hasum : ∑ i, a i = k := by
      dsimp [a]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, husum]
      omega
    rw [Finset.sum_tsub_distrib Finset.univ (fun i _ => ha i), hsum, hasum]
    omega
  · intro i
    have := he i
    dsimp [a]
    omega

/-- Integral points of the standard affine simplex of degree `k`. -/
def NatSimplex {d : ℕ} (k : ℕ) (a : Fin d → ℕ) : Prop := ∑ i, a i ≤ k

/-- Affine-coordinate version of Lemma 4.4, including all dimensions.
The strict inequalities on `m` are exactly the interior inequalities of
`(k + l) Δ_d`. The requested residue vector is unrestricted.
-/
theorem simplex_parity_affine {d k l : ℕ}
    (hdk : d ≤ k) (hdl : d ≤ l)
    (m r : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (hmsum : (∑ i, m i) < k + l) :
    ∃ a b : Fin d → ℕ,
      NatSimplex k a ∧ NatSimplex l b ∧
      (∀ i, a i + b i = m i) ∧
      (∀ i, a i % 2 = r i % 2) := by
  let e : Fin d → ℕ := fun i => r i % 2
  have he : ∀ i, e i ≤ 1 := by
    intro i
    dsimp [e]
    omega
  have hEsum : (∑ i, e i) ≤ k := by
    calc
      (∑ i, e i) ≤ ∑ _ : Fin d, 1 := Finset.sum_le_sum (fun i _ => he i)
      _ = d := by simp
      _ ≤ k := hdk
  let m' : Fin (d + 1) → ℕ := Fin.cons (k + l - ∑ i, m i) m
  let e' : Fin (d + 1) → ℕ := Fin.cons ((k - ∑ i, e i) % 2) e
  have hm' : ∀ i, 0 < m' i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [m', Fin.cons_zero]
      omega
    · simpa [m'] using hm j
  have he' : ∀ i, e' i ≤ 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [e', Fin.cons_zero]
      omega
    · simpa [e'] using he j
  have hmsum' : ∑ i, m' i = k + l := by
    simp only [Fin.sum_univ_succ, m', Fin.cons_zero, Fin.cons_succ]
    omega
  have hepar' : (∑ i, e' i) % 2 = k % 2 := by
    simp only [Fin.sum_univ_succ, e', Fin.cons_zero, Fin.cons_succ]
    omega
  obtain ⟨a', b', hab', ha', hb', hpar'⟩ :=
    simplex_parity_homogeneous hdk hdl m' e' hm' he' hmsum' hepar'
  refine ⟨fun i => a' i.succ, fun i => b' i.succ, ?_, ?_, ?_, ?_⟩
  · change (∑ i : Fin d, a' i.succ) ≤ k
    rw [Fin.sum_univ_succ] at ha'
    omega
  · change (∑ i : Fin d, b' i.succ) ≤ l
    rw [Fin.sum_univ_succ] at hb'
    omega
  · intro i
    simpa [m'] using hab' i.succ
  · intro i
    simpa [e', e] using hpar' i.succ

/-- The actual integer-coordinate inequalities for the degree-`k` standard simplex. -/
def IntegerSimplex {d : ℕ} (k : ℕ) (a : Fin d → ℤ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∑ i, a i) ≤ k

/-- Coordinate congruence is exactly membership of the difference in the
doubled integer lattice; this identifies the residue condition with `M / 2M`. -/
theorem integer_parity_iff_double {ι : Type*} (a α : ι → ℤ) :
    (∀ i, (a i - α i) % 2 = 0) ↔ ∃ w : ι → ℤ, a - α = w + w := by
  constructor
  · intro h
    refine ⟨fun i => (a i - α i) / 2, ?_⟩
    funext i
    have hi := h i
    simp only [Pi.sub_apply, Pi.add_apply]
    omega
  · rintro ⟨w, hw⟩ i
    have hi := congrFun hw i
    simp only [Pi.sub_apply, Pi.add_apply] at hi
    omega

/-- Natural-coordinate simplex points and their integer embeddings agree exactly. -/
theorem natSimplex_iff_integerSimplex {d k : ℕ} (a : Fin d → ℕ) :
    NatSimplex k a ↔ IntegerSimplex k (fun i => (a i : ℤ)) := by
  simp [NatSimplex, IntegerSimplex, ← Nat.cast_sum]

/-- Lemma 4.4 in the ambient integer lattice, with unrestricted integer parity classes. -/
theorem simplex_parity_integer {d k l : ℕ}
    (hdk : d ≤ k) (hdl : d ≤ l)
    (m α : Fin d → ℤ)
    (hm : ∀ i, 0 < m i) (hmsum : (∑ i, m i) < (k + l : ℕ)) :
    ∃ a b : Fin d → ℤ,
      IntegerSimplex k a ∧ IntegerSimplex l b ∧
      (∀ i, a i + b i = m i) ∧
      (∀ i, (a i - α i) % 2 = 0) := by
  let mN : Fin d → ℕ := fun i => (m i).toNat
  let rN : Fin d → ℕ := fun i => (α i % 2).toNat
  have hmN : ∀ i, 0 < mN i := by
    intro i
    dsimp [mN]
    have h := hm i
    omega
  have hmcast : ∀ i, (mN i : ℤ) = m i := by
    intro i
    dsimp [mN]
    exact Int.toNat_of_nonneg (le_of_lt (hm i))
  have hmNsum : (∑ i, mN i) < k + l := by
    have hsumcast : ((∑ i, mN i : ℕ) : ℤ) = ∑ i, m i := by
      simp only [Nat.cast_sum, hmcast]
    omega
  obtain ⟨aN, bN, haN, hbN, habN, hparN⟩ :=
    simplex_parity_affine hdk hdl mN rN hmN hmNsum
  refine ⟨fun i => (aN i : ℤ), fun i => (bN i : ℤ),
    (natSimplex_iff_integerSimplex aN).mp haN,
    (natSimplex_iff_integerSimplex bN).mp hbN, ?_, ?_⟩
  · intro i
    change (aN i : ℤ) + (bN i : ℤ) = m i
    have h := habN i
    have hc := hmcast i
    omega
  · intro i
    change ((aN i : ℤ) - α i) % 2 = 0
    have h := hparN i
    have hr : (rN i : ℤ) = α i % 2 := by
      dsimp [rN]
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    omega

end PaperVerification.Toric
