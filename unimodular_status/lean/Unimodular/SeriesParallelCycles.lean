module

public import Unimodular.SeriesParallelSlices

@[expose] public section

open scoped BigOperators Pointwise Topology
open Set TauCeti.Toric

namespace Unimodular.SeriesParallel

noncomputable section

universe u v w

/-- Column `j` of a cyclic bipartite support meets row `j` and its next row,
with the last row followed by row zero. This formula has no modular-index junk
cases and is used only for cycles with at least three row vertices. -/
def cycleSupport {k : ℕ} (i j : Fin k) : Prop :=
  i = j ∨ i.val = j.val + 1 ∨ (i.val = 0 ∧ j.val + 1 = k)

/-- Pivoting on the first cycle edge and contracting it removes one row and
one column and preserves exactly the shorter induced cycle support. All signs
are arbitrary, and the entries outside this cyclic submatrix are unrestricted. -/
theorem cycle_support_after_pivot {k : ℕ} (hk : 3 ≤ k)
    (A : Fin (k + 1) → Fin (k + 1) → ℤ)
    (hA : ∀ i j, A i j ≠ 0 ↔ cycleSupport i j) (i j : Fin k) :
    A i.succ j.succ - A i.succ 0 * A 0 0 * A 0 j.succ ≠ 0 ↔ cycleSupport i j := by
  have hbase : A i.succ j.succ ≠ 0 ↔ i.val = j.val ∨ i.val = j.val + 1 := by
    rw [hA]
    simp only [cycleSupport, Fin.ext_iff, Fin.val_succ, Fin.val_zero]
    omega
  have hleft : A i.succ 0 ≠ 0 ↔ i.val = 0 := by
    rw [hA]
    simp only [cycleSupport, Fin.ext_iff, Fin.val_succ, Fin.val_zero]
    omega
  have hright : A 0 j.succ ≠ 0 ↔ j.val + 1 = k := by
    simpa [cycleSupport, Fin.ext_iff, Fin.val_succ, Fin.val_zero] using hA 0 j.succ
  have hzero : A 0 0 ≠ 0 := (hA 0 0).mpr (Or.inl rfl)
  by_cases hcorner : i.val = 0 ∧ j.val + 1 = k
  · have hvanish : A i.succ j.succ = 0 := by
      by_contra h
      have hh := hbase.mp h
      omega
    have hprod := mul_ne_zero (mul_ne_zero (hleft.mpr hcorner.1) hzero)
      (hright.mpr hcorner.2)
    rw [hvanish, zero_sub, neg_ne_zero]
    exact iff_of_true hprod (Or.inr (Or.inr hcorner))
  · have hp : A i.succ 0 * A 0 0 * A 0 j.succ = 0 := by
      by_cases hi : i.val = 0
      · have hj : j.val + 1 ≠ k := fun h => hcorner ⟨hi, h⟩
        have hz : A 0 j.succ = 0 := by
          by_contra h
          exact hj (hright.mp h)
        simp [hz]
      · have hz : A i.succ 0 = 0 := by
          by_contra h
          exact hi (hleft.mp h)
        simp [hz]
    rw [hp, sub_zero, hbase]
    simp only [cycleSupport, Fin.ext_iff]
    tauto

/-- Every undeleted basis vector maps to exactly the standard quotient basis
vector, without a scaling factor. -/
theorem projection_basis_vector {I N : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup N] [Module ℤ N] (b : Module.Basis I ℤ N) (A : Finset I)
    (j : {i : I // i ∉ A}) :
    CoordinateQuotients.projection b A (b j.val) = Pi.basisFun ℤ _ j := by
  ext k
  simp [CoordinateQuotients.projection_apply, Module.Basis.repr_self_apply,
    Pi.basisFun_apply, Pi.single_apply, Finsupp.single_apply, Subtype.ext_iff, eq_comm]

private theorem projected_basis_rays {I N V : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (b : Module.Basis I ℤ N)
    (hb : ∀ i, ConeBases.IsRay Φ (b i)) (A : Finset I)
    (Ψ : Fan (CoordinateQuotients.quotientEmbedding A))
    (hmap : ∀ w, ConeBases.IsRay Ψ w ↔ ∃ u, ConeBases.IsRay Φ u ∧
      CoordinateQuotients.projection b A u = w ∧ w ≠ 0) :
    ∀ j, ConeBases.IsRay Ψ (Pi.basisFun ℤ _ j) := by
  intro j
  exact (hmap _).mpr ⟨b j.val, hb j.val, projection_basis_vector b A j,
    (Pi.basisFun ℤ _).ne_zero j⟩

/-- The standard coordinate lattice embedding for an arbitrary finite index type. -/
def coordinateEmbedding (I : Type*) : (I → ℤ) →+ (I → ℝ) :=
  (Int.castAddHom ℝ).compLeft I

/-- Arbitrary-length induced cycles are excluded by induction, contracting one
actual cycle ray at each step. The induction quantifies over every finite
coordinate index type, so it applies to the successive quotient lattices. -/
theorem coordinateFan_no_cycle_rows :
    ∀ k : ℕ, 3 ≤ k → ∀ (I : Type u) [Fintype I] [DecidableEq I],
      ∀ (Φ : Fan (coordinateEmbedding I)), Φ.IsComplete → Φ.IsRegular →
      ConeBases.PositiveCriterion Φ →
      ∀ (b : Module.Basis I ℤ (I → ℤ)), (∀ i, ConeBases.IsRay Φ (b i)) →
      ∀ (r : Fin k ↪ I) (v : Fin k → I → ℤ),
        (∀ j, ConeBases.IsRay Φ (v j)) →
        (∀ i j, b.repr (v j) (r i) ≠ 0 ↔ cycleSupport i j) → False := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk I _ _ Φ hc hr hp b hb r v hv hpat
    classical
    by_cases hk3 : k = 3
    · subst k
      apply fan_no_triangle_rows Φ hc hr hp b hb r (v 0) (v 2) (v 1)
        (hv 0) (hv 2) (hv 1)
      · intro i
        have h := hpat i 0
        fin_cases i <;> simpa [cycleSupport] using h
      · intro i
        have h := hpat i 2
        fin_cases i <;> simpa [cycleSupport] using h
      · intro i
        have h := hpat i 1
        fin_cases i <;> simpa [cycleSupport] using h
    cases k with
    | zero => omega
    | succ k =>
      have hk' : 3 ≤ k := by omega
      have hU := FanBridge.uniform_of_positiveCriterion Φ hc hr hp b
      have hentry := Heller.coordinate_abs_le_one b {x | ConeBases.IsRay Φ x}
        hU hb (hv 0) (r 0)
      have hn : b.repr (v 0) (r 0) ≠ 0 := (hpat 0 0).mpr (Or.inl rfl)
      have hunit : b.repr (v 0) (r 0) = 1 ∨ b.repr (v 0) (r 0) = -1 := by
        have := abs_le.mp hentry
        omega
      let b' := pivotBasis b (v 0) (r 0) hunit
      have hb' : ∀ i, ConeBases.IsRay Φ (b' i) := by
        intro i
        by_cases hi : i = r 0
        · subst i
          simpa [b'] using hv 0
        · simpa [b', pivotBasis_other b (v 0) (r 0) hunit hi] using hb i
      let A : Finset I := {r 0}
      let J := {i : I // i ∉ A}
      obtain ⟨Ψ, hΨc, hΨr, hΨp, hmap⟩ :=
        RayContractions.exists_coordinate_contraction Φ hc hr hp b' A (fun i _ => hb' i)
      let c : Module.Basis J ℤ (J → ℤ) := Pi.basisFun ℤ J
      have hcb : ∀ j, ConeBases.IsRay Ψ (c j) :=
        projected_basis_rays Φ b' hb' A Ψ hmap
      let r' : Fin k ↪ J :=
        { toFun := fun i => ⟨r i.succ, by
            change r i.succ ∉ ({r 0} : Finset I)
            simp only [Finset.mem_singleton]
            exact fun h => Fin.succ_ne_zero i (r.injective h)⟩
          inj' := by
            intro i j h
            exact Fin.succ_injective k (r.injective (congrArg Subtype.val h)) }
      let q := CoordinateQuotients.projection b' A
      let w : Fin k → J → ℤ := fun j => q (v j.succ)
      have hcoeff (i j : Fin k) : c.repr (w j) (r' i) =
          b.repr (v j.succ) (r i.succ) -
          b.repr (v 0) (r i.succ) * b.repr (v 0) (r 0) * b.repr (v j.succ) (r 0) := by
        change b'.repr (v j.succ) (r i.succ) = _
        rw [pivotBasis_repr]
        apply if_neg
        exact fun h => Fin.succ_ne_zero i (r.injective h)
      have hpat' : ∀ i j, c.repr (w j) (r' i) ≠ 0 ↔ cycleSupport i j := by
        intro i j
        rw [hcoeff]
        exact cycle_support_after_pivot hk' (fun i j => b.repr (v j) (r i)) hpat i j
      have hw : ∀ j, ConeBases.IsRay Ψ (w j) := by
        intro j
        apply (hmap _).mpr
        refine ⟨v j.succ, hv j.succ, rfl, ?_⟩
        intro hz
        have hn := (hpat' j j).mpr (Or.inl rfl)
        apply hn
        rw [hz]
        simp
      exact ih k (Nat.lt_succ_self k) hk' J Ψ hΨc hΨr hΨp c hcb r' w hw hpat'

/-- The coordinate induction transports to every actual lattice presentation.
Thus no induced cyclic support of any length occurs in a ray basis of any
complete regular positive-criterion fan. -/
theorem fan_no_cycle_rows {I : Type u} {N : Type v} {V : Type w} [Fintype I] [DecidableEq I]
    [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ)
    (b : Module.Basis I ℤ N) (hb : ∀ i, ConeBases.IsRay Φ (b i))
    (k : ℕ) (hk : 3 ≤ k) (r : Fin k ↪ I) (v : Fin k → N)
    (hv : ∀ j, ConeBases.IsRay Φ (v j))
    (hpat : ∀ i j, b.repr (v j) (r i) ≠ 0 ↔ cycleSupport i j) : False := by
  classical
  obtain ⟨Ψ, hΨc, hΨr, hΨp, hmap⟩ :=
    RayContractions.exists_coordinate_contraction Φ hc hr hp b ∅ (by simp)
  let J := {i : I // i ∉ (∅ : Finset I)}
  let c : Module.Basis J ℤ (J → ℤ) := Pi.basisFun ℤ J
  have hcb : ∀ j, ConeBases.IsRay Ψ (c j) := projected_basis_rays Φ b hb ∅ Ψ hmap
  let r' : Fin k ↪ J :=
    { toFun := fun i => ⟨r i, by simp⟩
      inj' := fun i j h => r.injective (congrArg Subtype.val h) }
  let q := CoordinateQuotients.projection b ∅
  let w : Fin k → J → ℤ := fun j => q (v j)
  have hpat' : ∀ i j, c.repr (w j) (r' i) ≠ 0 ↔ cycleSupport i j := hpat
  have hw : ∀ j, ConeBases.IsRay Ψ (w j) := by
    intro j
    apply (hmap _).mpr
    refine ⟨v j, hv j, rfl, ?_⟩
    intro hz
    have hn := (hpat' j j).mpr (Or.inl rfl)
    apply hn
    rw [hz]
    simp
  exact coordinateFan_no_cycle_rows k hk J Ψ hΨc hΨr hΨp c hcb r' w hw hpat'

#print axioms Unimodular.SeriesParallel.coordinateFan_no_cycle_rows
#print axioms Unimodular.SeriesParallel.fan_no_cycle_rows

end
end Unimodular.SeriesParallel
