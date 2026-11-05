module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.AlgebraicDependence
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Topology.Instances.Sign
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.FunProp
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# Polynomial equations on semialgebraic frontiers

This elementary boundary version of the finite-sign argument avoids a
quantifier-elimination dependency. The proof extends the argument in TauCeti's
`Semialgebraic.AlgebraicDependence`, whose Apache-2.0 source is vendored.
-/

open Filter MvPolynomial Set Topology

namespace VolumePolynomials

/-- Every frontier of a semialgebraic set is contained in a nonzero polynomial
zero set, obtained from the finite defining sign conditions. -/
theorem frontier_polynomial_relation {σ : Type*} {s : Set (σ → ℝ)}
    (hs : TauCeti.IsSemialgebraic s) :
    ∃ p : MvPolynomial σ ℝ, p ≠ 0 ∧ ∀ x ∈ frontier s, eval x p = 0 := by
  classical
  obtain ⟨m, p, Φ, hpres⟩ := hs.exists_eq_setOf_sign_eval
  let I : Finset (Fin m) := Finset.univ.filter fun i => p i ≠ 0
  refine ⟨∏ i ∈ I, p i,
    Finset.prod_ne_zero_iff.mpr (fun i hi => (Finset.mem_filter.mp hi).2), ?_⟩
  intro x hx
  have hzero : ∃ i ∈ I, eval x (p i) = 0 := by
    by_contra h
    have hne (i : Fin m) (hi : p i ≠ 0) : eval x (p i) ≠ 0 :=
      fun hxi => h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hxi⟩
    have hsign (i : Fin m) :
        ∀ᶠ y in 𝓝 x, SignType.sign (eval y (p i)) = SignType.sign (eval x (p i)) := by
      by_cases hi : p i = 0
      · simp [hi]
      · exact ((continuousAt_sign_of_ne_zero (hne i hi)).comp
          (f := fun y : σ → ℝ => eval y (p i))
          (p i).continuous_eval.continuousAt).preimage_mem_nhds
            ((isOpen_discrete _).mem_nhds (mem_singleton _))
    have hlocal : ∀ᶠ y in 𝓝 x, (y ∈ s ↔ x ∈ s) := by
      filter_upwards [eventually_all.mpr hsign] with y hy
      simp only [hpres, mem_ofPred_eq, funext hy]
    rw [frontier_eq_inter_compl_interior] at hx
    change x ∉ interior s ∧ x ∉ interior sᶜ at hx
    by_cases hxs : x ∈ s
    · apply hx.1
      apply mem_interior_iff_mem_nhds.mpr
      exact hlocal.mono fun _ hy => hy.mpr hxs
    · apply hx.2
      apply mem_interior_iff_mem_nhds.mpr
      exact hlocal.mono fun _ hy => by simpa only [mem_compl_iff, hy] using hxs
  obtain ⟨i, hi, hxi⟩ := hzero
  rw [map_prod]
  exact Finset.prod_eq_zero hi hxi

/-- An attained lower endpoint of a vertical fiber is a frontier point. -/
theorem fiber_minimum_mem_frontier {s : Set (Fin 2 → ℝ)} {x b : ℝ}
    (hmem : ![x, b] ∈ s)
    (hminimal : ∀ y : ℝ, ![x, y] ∈ s → b ≤ y) :
    ![x, b] ∈ frontier s := by
  apply (mem_frontier_iff_notMem_interior hmem).mpr
  intro hint
  have hcont : Continuous (fun y : ℝ => ![x, y]) := by
    fun_prop
  have hpre : b ∈ interior ((fun y : ℝ => ![x, y]) ⁻¹' s) :=
    preimage_interior_subset_interior_preimage hcont hint
  have hsub : (fun y : ℝ => ![x, y]) ⁻¹' s ⊆ Ici b := by
    intro y hy
    exact hminimal y hy
  have hbad := interior_mono hsub hpre
  simp only [interior_Ici, mem_Ioi, lt_self_iff_false] at hbad

end VolumePolynomials
