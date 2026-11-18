module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Shrinking bounded tests for every sufficiently large integer

The geometric step in Proposition 3.2 requires lattice approximation with a
bounded error, uniformly for every positive integer exponent.  Rounding the
coordinates of a real basis consisting of lattice vectors gives that bound.
The basis need not generate the whole lattice over the integers.

The final theorem translates and scales an arbitrary bounded set into an
arbitrarily small ball about a prescribed point of the subspace.  It also
records the affine-slice compatibility `u + m ∈ V`; no divisibility condition
is placed on the exponent.

Candidate source until ordinary compilation succeeds.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Module
open scoped BigOperators

namespace ToricPower

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- A real basis made of lattice vectors gives a uniform lattice-distance
bound by coordinate rounding. -/
theorem exists_lattice_approximation_of_basis (b : Basis ι ℝ E)
    (L : AddSubgroup E) (hb : ∀ i, b i ∈ L) (x : E) :
    ∃ v ∈ L, ‖x - v‖ ≤ ∑ i, ‖b i‖ := by
  let v : Submodule.span ℤ (Set.range b) := ZSpan.floor b x
  have hspan : Submodule.span ℤ (Set.range b) ≤ L.toIntSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i
  refine ⟨v.val, hspan v.property, ?_⟩
  exact ZSpan.norm_fract_le b x

/-- Any bounded test can be translated by actual lattice points and shrunk
into the chosen ball for every sufficiently large integer exponent. -/
theorem bounded_test_shrinks_for_every_integer
    (V : Submodule ℝ E) (b : Basis ι ℝ V) (L : AddSubgroup E)
    (hb : ∀ i, (b i : E) ∈ L) (x : V) (m : E) (hm : m ∈ L)
    (K : Set E) (hK : Bornology.IsBounded K) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ ℓ : ℕ, N ≤ ℓ →
      ∃ u ∈ L, u + m ∈ V ∧
        (fun z : E => (ℓ : ℝ)⁻¹ • (u + z)) '' K ⊆ Metric.ball (x : E) ε := by
  classical
  obtain ⟨B, hB, hKB⟩ := hK.exists_pos_norm_le
  let C : ℝ := ∑ i, ‖b i‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let D : ℝ := B + ‖m‖ + C
  have hD : 0 < D := by dsimp [D]; linarith [norm_nonneg m]
  obtain ⟨N, hN⟩ := exists_nat_gt (D / ε)
  have hNpos : 0 < N := by
    exact_mod_cast (div_pos hD hε).trans hN
  refine ⟨N, hNpos, fun ℓ hNℓ => ?_⟩
  have hℓ : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hNpos.trans_le hNℓ
  let L' : AddSubgroup V := L.comap V.subtype.toAddMonoidHom
  obtain ⟨v, hv, hdist⟩ := exists_lattice_approximation_of_basis b L'
    (fun i => hb i) ((ℓ : ℝ) • x)
  let u : E := (v : E) - m
  refine ⟨u, L.sub_mem hv hm, ?_, ?_⟩
  · simpa only [u, sub_add_cancel] using v.property
  · rintro _ ⟨z, hz, rfl⟩
    have hnorm : ‖(u + z) - (ℓ : ℝ) • (x : E)‖ ≤ D := by
      calc
        _ = ‖((v : E) - (ℓ : ℝ) • (x : E)) + (z - m)‖ := by
          congr 1
          dsimp [u]
          abel
        _ ≤ ‖(v : E) - (ℓ : ℝ) • (x : E)‖ + ‖z - m‖ := norm_add_le _ _
        _ ≤ C + (B + ‖m‖) := by
          apply add_le_add
          · change ‖(v - (ℓ : ℝ) • x : V)‖ ≤ C
            rw [norm_sub_rev]
            exact hdist
          · exact (norm_sub_le z m).trans (add_le_add (hKB z hz) le_rfl)
        _ = D := by dsimp [D]; ring
    have hratio : D / ε < (ℓ : ℝ) :=
      hN.trans_le (by exact_mod_cast hNℓ)
    have hsmall : D / (ℓ : ℝ) < ε := by
      apply (div_lt_iff₀ hℓ).mpr
      simpa only [mul_comm] using (div_lt_iff₀ hε).mp hratio
    have hidentity : (ℓ : ℝ)⁻¹ • (u + z) - (x : E) =
        (ℓ : ℝ)⁻¹ • ((u + z) - (ℓ : ℝ) • (x : E)) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hℓ.ne', one_smul]
    rw [Metric.mem_ball, dist_eq_norm, hidentity, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    calc
      _ ≤ (ℓ : ℝ)⁻¹ * D := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hℓ.le)
      _ = D / (ℓ : ℝ) := by rw [div_eq_mul_inv, mul_comm]
      _ < ε := hsmall

/-- The basis required by the shrinking construction is derived from the
full lattice span.  Thus the final geometric statement requires no chosen
lattice basis and still imposes no divisibility condition on `ℓ`. -/
theorem bounded_test_shrinks_for_every_integer_of_span
    [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (L : AddSubgroup E)
    (hspan : Submodule.span ℝ
      (L.comap V.subtype.toAddMonoidHom : Set V) = ⊤)
    (x : V) (m : E) (hm : m ∈ L) (K : Set E) (hK : Bornology.IsBounded K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ ℓ : ℕ, N ≤ ℓ →
      ∃ u ∈ L, u + m ∈ V ∧
        (fun z : E => (ℓ : ℝ)⁻¹ • (u + z)) '' K ⊆ Metric.ball (x : E) ε := by
  classical
  let S : Set V := L.comap V.subtype.toAddMonoidHom
  have hs : ⊤ ≤ Submodule.span ℝ S := by rw [show Submodule.span ℝ S = ⊤ from hspan]
  let b := Basis.ofSpan hs
  letI := b.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℝ V)
  have hb : ∀ i, (b i : E) ∈ L := fun i => Basis.ofSpan_subset hs ⟨i, rfl⟩
  exact bounded_test_shrinks_for_every_integer V b L hb x m hm K hK ε hε

end ToricPower
