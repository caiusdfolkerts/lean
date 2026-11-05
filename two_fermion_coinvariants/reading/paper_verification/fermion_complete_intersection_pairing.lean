module

public import PaperVerification.FermionKoszulSocle
public import PaperVerification.FermionSoclePairing
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Frobenius functionals for finite complete intersections at the origin

The preceding Koszul comparison theorems are connected here to the actual
quotient algebra. The hypotheses consist of a regular sequence, its radical,
and the presentation of the origin ideal by the same number of generators.
In particular the Frobenius pairing is derived, not supplied as a hypothesis.
The argument is valid in arbitrary field characteristic.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

variable {K P : Type*} [Field K] [CommRing P] [Algebra K P]

/-- A finitely generated radical becomes a nilpotent ideal in the quotient. -/
theorem quotient_radical_isNilpotent (J m : Ideal P)
    (hm : m.FG) (hrad : J.radical = m) :
    IsNilpotent (m.map (Ideal.Quotient.mk J)) := by
  obtain ⟨n, hn⟩ := J.exists_radical_pow_le_of_fg (hrad.symm ▸ hm)
  refine ⟨n, ?_⟩
  change (m.map (Ideal.Quotient.mk J)) ^ n = ⊥
  rw [← Ideal.map_pow]
  apply (Ideal.map_eq_bot_iff_le_ker _).mpr
  rw [Ideal.mk_ker, ← hrad]
  exact hn

/-- The determinant annihilator formula gives a one-dimensional socle in
the actual quotient, because the origin homomorphism removes every
nonconstant coefficient of a multiple of the determinant. -/
theorem quotient_socle_span
    (origin : P →ₐ[K] K) (J : Ideal P) (d : P)
    (hcolon : J.colon (RingHom.ker origin.toRingHom : Set P) =
      J ⊔ Ideal.span {d}) :
    ∀ x : P ⧸ J,
      (∀ r ∈ (RingHom.ker origin.toRingHom).map (Ideal.Quotient.mk J), r * x = 0) →
      ∃ c : K, x = c • Ideal.Quotient.mk J d := by
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hp : p ∈ J.colon (RingHom.ker origin.toRingHom : Set P) := by
    apply Submodule.mem_colon.mpr
    intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, smul_eq_mul, mul_comm p r] using
      hx (Ideal.Quotient.mk J r) (Ideal.mem_map_of_mem _ hr)
  rw [hcolon] at hp
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hp
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hv
  have hdcolon : d ∈ J.colon (RingHom.ker origin.toRingHom : Set P) := by
    rw [hcolon]
    exact (show Ideal.span {d} ≤ J ⊔ Ideal.span {d} from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton d))
  have hrem : c - algebraMap K P (origin c) ∈ RingHom.ker origin.toRingHom := by
    change origin (c - algebraMap K P (origin c)) = 0
    simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hremd : (c - algebraMap K P (origin c)) * d ∈ J := by
    simpa only [smul_eq_mul, mul_comm] using Submodule.mem_colon.mp hdcolon _ hrem
  have hcd : Ideal.Quotient.mk J (c * d) =
      Ideal.Quotient.mk J (algebraMap K P (origin c) * d) := by
    apply sub_eq_zero.mp
    rw [← map_sub, ← sub_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hremd
  refine ⟨origin c, ?_⟩
  rw [← huv, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hu, zero_add, ← hc, hcd]
  change (Ideal.Quotient.mkₐ K J) (algebraMap K P (origin c) * d) = _
  rw [map_mul, AlgHom.commutes, Algebra.smul_def, Ideal.Quotient.mkₐ_eq_mk]

/-- The other determinant-colon formula ensures that the socle generator
does not vanish. -/
theorem quotient_determinant_ne_zero
    (origin : P →ₐ[K] K) (J : Ideal P) (d : P)
    (hcolon : J.colon ({d} : Set P) = RingHom.ker origin.toRingHom) :
    Ideal.Quotient.mk J d ≠ 0 := by
  intro hd
  have hdJ := Ideal.Quotient.eq_zero_iff_mem.mp hd
  have hone : (1 : P) ∈ J.colon ({d} : Set P) := by
    exact Submodule.mem_colon_singleton.mpr (by simpa only [one_smul] using hdJ)
  rw [hcolon] at hone
  have : (1 : K) = 0 := by
    simpa only [RingHom.mem_ker, map_one] using hone
  exact one_ne_zero this

/-- A direct, characteristic-independent Frobenius criterion, with both
ideal comparisons explicitly checked in the original algebra. -/
theorem exists_frobenius_of_determinant_colons
    (origin : P →ₐ[K] K) (J : Ideal P) (d : P)
    [Module.Finite K (P ⧸ J)]
    (hm : (RingHom.ker origin.toRingHom).FG)
    (hrad : J.radical = RingHom.ker origin.toRingHom)
    (hprincipal : J.colon ({d} : Set P) = RingHom.ker origin.toRingHom)
    (hsocle : J.colon (RingHom.ker origin.toRingHom : Set P) =
      J ⊔ Ideal.span {d}) :
    ∃ ε : P ⧸ J →ₗ[K] K, ε (Ideal.Quotient.mk J d) = 1 ∧
      (multiplicationPairing ε).IsPerfPair := by
  obtain ⟨ε, hε⟩ := Module.Projective.exists_dual_eq_one K
    (quotient_determinant_ne_zero origin J d hprincipal)
  refine ⟨ε, hε, ?_⟩
  apply multiplicationPairing_isPerfPair_of_socle
    ((RingHom.ker origin.toRingHom).map (Ideal.Quotient.mk J))
    (quotient_radical_isNilpotent J _ hm hrad) (Ideal.Quotient.mk J d)
    (quotient_socle_span origin J d hsocle) ε
  rw [hε]
  exact one_ne_zero

/-- **Finite complete intersections supported at the origin are Frobenius.**
Both regular-sequence determinant identities are proved by Koszul comparison
in the imported files. The field may have any characteristic. -/
theorem exists_frobenius_of_regular_sequence {n : ℕ}
    (origin : P →ₐ[K] K) (a b : Fin n → P)
    (ha : Ideal.span (Set.range a) = RingHom.ker origin.toRingHom)
    (hb : RingTheory.Sequence.IsWeaklyRegular P (List.ofFn b))
    (hrad : (Ideal.span (Set.range b)).radical = RingHom.ker origin.toRingHom)
    [Module.Finite K (P ⧸ Ideal.span (Set.range b))] :
    ∃ ε : P ⧸ Ideal.span (Set.range b) →ₗ[K] K,
      (multiplicationPairing ε).IsPerfPair := by
  classical
  have hle : LinearMap.range (Fintype.linearCombination P b) ≤
      LinearMap.range (Fintype.linearCombination P a) := by
    simp only [Fintype.range_linearCombination, Ideal.submodule_span_eq]
    rw [ha, ← hrad]
    exact Ideal.le_radical
  obtain ⟨g, hg⟩ := exists_linear_lift_of_range_le
    (Fintype.linearCombination P a) (Fintype.linearCombination P b) hle
  have hm : (RingHom.ker origin.toRingHom).FG := by
    rw [← ha]
    exact Submodule.fg_span (Set.finite_range a)
  have hprincipal : (Ideal.span (Set.range b)).colon ({LinearMap.det g} : Set P) =
      RingHom.ker origin.toRingHom := by
    rw [Koszul.span_colon_det_eq_of_isWeaklyRegular a b g hg hb, ha]
  have hsocle :
      (Ideal.span (Set.range b)).colon (RingHom.ker origin.toRingHom : Set P) =
      Ideal.span (Set.range b) ⊔ Ideal.span {LinearMap.det g} := by
    rw [← ha]
    exact Koszul.span_colon_span_eq_of_isWeaklyRegular a b g hg hb
  obtain ⟨ε, _, hε⟩ := exists_frobenius_of_determinant_colons origin
    (Ideal.span (Set.range b)) (LinearMap.det g) hm hrad hprincipal hsocle
  exact ⟨ε, hε⟩

end PaperVerification.Fermion
