module
public import PaperVerification.ToricSimplexGeometry
public import Lean.Elab.Tactic.Omega
@[expose] public section
/-!
# Adjoint simplex allocation

The second summand has every homogeneous coordinate strictly positive.
This is exactly the simplex case of the interior-summand theorem, including
the endpoint where its adjoint simplex is a point.
-/

namespace PaperVerification.Toric

open scoped BigOperators Pointwise

/-- Allocate a homogeneous simplex target so that the entire second vector
is strictly positive. Only the second degree needs the interior threshold. -/
theorem simplex_adjoint_homogeneous {d k l : ℕ}
    (hdl : d + 1 ≤ l) (m : Fin (d + 1) → ℕ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = k + l) :
    ∃ a b : Fin (d + 1) → ℕ,
      (∀ i, a i + b i = m i) ∧
      (∑ i, a i) = k ∧ (∑ i, b i) = l ∧
      (∀ i, 0 < b i) := by
  let c : Fin (d + 1) → ℕ := fun i => m i - 1
  have hc (i : Fin (d + 1)) : c i + 1 = m i := by
    dsimp [c]
    have h := hm i
    omega
  have hcSum : (∑ i, c i) + (d + 1) = k + l := by
    calc
      (∑ i, c i) + (d + 1) = ∑ i, (c i + 1) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ i, m i := Finset.sum_congr rfl (fun i _ => hc i)
      _ = k + l := hsum
  obtain ⟨a, ha, haSum⟩ := allocate_le_sum Finset.univ c k (by omega)
  let b : Fin (d + 1) → ℕ := fun i => m i - a i
  have hab (i : Fin (d + 1)) : a i + b i = m i := by
    have hai := ha i (Finset.mem_univ i)
    have hci := hc i
    dsimp [b]
    omega
  have hb (i : Fin (d + 1)) : 0 < b i := by
    have hai := ha i (Finset.mem_univ i)
    have hci := hc i
    dsimp [b]
    omega
  have habSum : (∑ i, a i) + (∑ i, b i) = k + l := by
    rw [← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl (fun i _ => hab i)).trans hsum
  exact ⟨a, b, hab, haSum, by omega, hb⟩

/-- Affine natural-coordinate form, with all coordinates of the second
summand positive and strict slack in its degree inequality. -/
theorem simplex_adjoint_affine {d k l : ℕ}
    (hdl : d + 1 ≤ l) (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (hmsum : (∑ i, m i) < k + l) :
    ∃ a b : Fin d → ℕ,
      NatSimplex k a ∧ (∀ i, 0 < b i) ∧ (∑ i, b i) < l ∧
      (∀ i, a i + b i = m i) := by
  let m' : Fin (d + 1) → ℕ := Fin.cons (k + l - ∑ i, m i) m
  have hm' : ∀ i, 0 < m' i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [m', Fin.cons_zero]
      omega
    · simpa only [m', Fin.cons_succ] using hm j
  have hsum' : ∑ i, m' i = k + l := by
    simp only [Fin.sum_univ_succ, m', Fin.cons_zero, Fin.cons_succ]
    omega
  obtain ⟨a', b', hab, ha, hb, hbpos⟩ :=
    simplex_adjoint_homogeneous hdl m' hm' hsum'
  refine ⟨fun i => a' i.succ, fun i => b' i.succ, ?_, ?_, ?_, ?_⟩
  · change (∑ i : Fin d, a' i.succ) ≤ k
    rw [Fin.sum_univ_succ] at ha
    omega
  · exact fun i => hbpos i.succ
  · change (∑ i : Fin d, b' i.succ) < l
    rw [Fin.sum_univ_succ] at hb
    have hzero := hbpos 0
    omega
  · intro i
    simpa only [m', Fin.cons_succ] using hab i.succ

/-- The full ambient integer-lattice simplex allocation. -/
theorem simplex_adjoint_integer {d k l : ℕ}
    (hdl : d + 1 ≤ l) (m : Fin d → ℤ)
    (hm : ∀ i, 0 < m i) (hmsum : (∑ i, m i) < (k + l : ℕ)) :
    ∃ a b : Fin d → ℤ,
      IntegerSimplex k a ∧ (∀ i, 0 < b i) ∧ (∑ i, b i) < (l : ℤ) ∧
      (∀ i, a i + b i = m i) := by
  let mN : Fin d → ℕ := fun i => (m i).toNat
  have hmN (i : Fin d) : 0 < mN i := by
    have h := hm i
    dsimp [mN]
    omega
  have hmcast (i : Fin d) : (mN i : ℤ) = m i :=
    Int.toNat_of_nonneg (le_of_lt (hm i))
  have hmNsum : (∑ i, mN i) < k + l := by
    have hcast : ((∑ i, mN i : ℕ) : ℤ) = ∑ i, m i := by
      simp only [Nat.cast_sum, hmcast]
    omega
  obtain ⟨aN, bN, ha, hbpos, hbSum, hab⟩ :=
    simplex_adjoint_affine hdl mN hmN hmNsum
  refine ⟨fun i => (aN i : ℤ), fun i => (bN i : ℤ),
    (natSimplex_iff_integerSimplex aN).mp ha, ?_, ?_, ?_⟩
  · intro i
    change (0 : ℤ) < (bN i : ℤ)
    exact_mod_cast hbpos i
  · change (∑ i : Fin d, (bN i : ℤ)) < (l : ℤ)
    exact_mod_cast hbSum
  · intro i
    change (aN i : ℤ) + (bN i : ℤ) = m i
    rw [← Nat.cast_add, hab, hmcast]

/-- The actual topological simplex case of the interior-summand assertion.
All dimensions, arbitrary first degree, and the second adjoint endpoint are
included. -/
theorem simplex_adjoint_topological {d k l : ℕ}
    (hdl : d + 1 ≤ l) (m : Fin d → ℤ)
    (hm : (fun i => (m i : ℝ)) ∈
      interior (RealSimplex d k + RealSimplex d l)) :
    ∃ a b : Fin d → ℤ,
      (fun i => (a i : ℝ)) ∈ RealSimplex d k ∧
      (fun i => (b i : ℝ)) ∈ interior (RealSimplex d l) ∧
      (∀ i, a i + b i = m i) := by
  cases d with
  | zero =>
      have hsimplex (r : ℕ) : RealSimplex 0 (r : ℝ) = Set.univ := by
        ext x
        simp [RealSimplex]
      refine ⟨0, m, ?_, ?_, ?_⟩
      · rw [hsimplex k]
        exact Set.mem_univ _
      · rw [hsimplex l, interior_univ]
        exact Set.mem_univ _
      · intro i
        simp
  | succ d =>
      have hm' := interior_mono (add_realSimplex_subset (d + 1) k l) hm
      rw [interior_realSimplex] at hm'
      have hmpos (i : Fin (d + 1)) : 0 < m i :=
        Int.cast_pos.mp (hm'.1 i)
      have hmsum : (∑ i, m i) < (k + l : ℕ) := by
        have h := hm'.2
        push_cast at h ⊢
        exact_mod_cast h
      obtain ⟨a, b, ha, hbpos, hbSum, hab⟩ :=
        simplex_adjoint_integer hdl m hmpos hmsum
      refine ⟨a, b, (integerSimplex_iff_realSimplex a).mp ha, ?_, hab⟩
      rw [interior_realSimplex]
      refine ⟨fun i => Int.cast_pos.mpr (hbpos i), ?_⟩
      change (∑ i : Fin (d + 1), (b i : ℝ)) < (l : ℝ)
      exact_mod_cast hbSum

end PaperVerification.Toric

