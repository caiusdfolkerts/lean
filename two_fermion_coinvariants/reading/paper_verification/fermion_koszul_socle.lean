module

public import PaperVerification.FermionKoszulColon
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.Ring

/-!
# Annihilators of complete-intersection quotients

The second determinant comparison identifies `(b):(a)` with `(b)+(det C)`.
Taking `a` to be the polynomial variables gives the one-dimensional socle of
a finite homogeneous complete intersection. This file proves the ideal
comparison itself, without assuming a Gorenstein or Frobenius conclusion.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Koszul

open TauCeti

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]

theorem mem_range_first_differential_iff (ψ : Module.Dual R M) (w : ⋀[R]^0 M) :
    w ∈ LinearMap.range (koszulDifferential ψ 0) ↔
      exteriorPower.zeroEquiv R M w ∈ LinearMap.range ψ := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨exteriorPower.oneEquiv R M z, (zeroEquiv_koszulDifferential_zero ψ z).symm⟩
  · rintro ⟨m, hm⟩
    refine ⟨(exteriorPower.oneEquiv R M).symm m, ?_⟩
    apply (exteriorPower.zeroEquiv R M).injective
    simpa only [zeroEquiv_koszulDifferential_zero, LinearEquiv.apply_symm_apply] using hm

/-- An endomorphism of a free rank-one module is multiplication by its value
on the element corresponding to one. -/
theorem endomorphism_eq_smul_of_equiv
    {N : Type*} [AddCommGroup N] [Module R N] (e : N ≃ₗ[R] R) (f : N →ₗ[R] N) :
    f = e (f (e.symm 1)) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hx : x = e x • e.symm 1 := by
    apply e.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  apply e.injective
  rw [hx, map_smul, map_smul]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

variable (vol : ⋀[R]^(Module.finrank R M) M ≃ₗ[R] R)

/-- A scalar annihilating the values of `φ` modulo the values of `ψ` lifts to
an actual chain comparison with that scalar in degree zero. -/
theorem exists_comparison_of_annihilation
    (φ ψ : Module.Dual R M)
    (hψ : ∀ k, Function.Exact (koszulDifferential ψ (k + 1)) (koszulDifferential ψ k))
    (z : R) (hz : ∀ m, z * φ m ∈ LinearMap.range ψ) :
    ∃ f : ∀ k, ⋀[R]^k M →ₗ[R] ⋀[R]^k M,
      f 0 = z • LinearMap.id ∧
        ∀ k, koszulDifferential ψ k ∘ₗ f (k + 1) = f k ∘ₗ koszulDifferential φ k := by
  refine exists_linear_chain_comparison
    (C := fun k => ⋀[R]^k M) (D := fun k => ⋀[R]^k M)
    (koszulDifferential φ) (koszulDifferential ψ)
    (koszulDifferential_comp_koszulDifferential φ) hψ (z • LinearMap.id) ?_
  rintro _ ⟨x, rfl⟩
  apply (mem_range_first_differential_iff ψ _).mpr
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_smul, zeroEquiv_koszulDifferential_zero, smul_eq_mul] using
    hz (exteriorPower.oneEquiv R M x)

include vol in
/-- Every annihilator class is a multiple of the comparison determinant. -/
theorem exists_sub_mul_det_mem_range
    (φ ψ : Module.Dual R M) (g : M →ₗ[R] M) (hg : φ ∘ₗ g = ψ)
    (hψ : ∀ k, Function.Exact (koszulDifferential ψ (k + 1)) (koszulDifferential ψ k))
    (z : R) (hz : ∀ m, z * φ m ∈ LinearMap.range ψ) :
    ∃ c : R, z - c * LinearMap.det g ∈ LinearMap.range ψ := by
  obtain ⟨f, hfzero, hf⟩ := exists_comparison_of_annihilation φ ψ hψ z hz
  let c := vol (f (Module.finrank R M) (vol.symm 1))
  have hftop : f (Module.finrank R M) = c • LinearMap.id :=
    endomorphism_eq_smul_of_equiv vol _
  let difference (k : ℕ) : ⋀[R]^k M →ₗ[R] ⋀[R]^k M :=
    z • LinearMap.id - f k ∘ₗ exteriorPower.map k g
  have hcomm (k : ℕ) :
      koszulDifferential ψ k ∘ₗ difference (k + 1) =
        difference k ∘ₗ koszulDifferential ψ k := by
    apply LinearMap.ext
    intro x
    have hc := LinearMap.congr_fun (hf k) (exteriorPower.map (k + 1) g x)
    simp only [LinearMap.comp_apply] at hc
    simp only [difference, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
    rw [hc, koszulDifferential_map, hg]
  have hzero : LinearMap.range (difference 0) ≤ LinearMap.range (koszulDifferential ψ 0) := by
    have heq : difference 0 = 0 := by
      apply LinearMap.ext
      intro x
      change z • x - f 0 (exteriorPower.map 0 g x) = 0
      rw [hfzero, exterior_map_zero_eq_id]
      exact sub_self (z • x)
    rw [heq, LinearMap.range_zero]
    exact bot_le
  have htop : difference (Module.finrank R M) = (z - c * LinearMap.det g) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp only [difference, hftop, LinearMap.map_exteriorPower_finrank_eq_det_smul,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_smul, mul_smul]
  exact ⟨c, top_scalar_mem_range vol ψ ψ difference hψ hcomm hzero _ htop⟩

include vol in
/-- The annihilator counterpart to the principal determinant-colon equality. -/
theorem range_colon_range_eq
    (φ ψ : Module.Dual R M) (g : M →ₗ[R] M) (hg : φ ∘ₗ g = ψ)
    (hψ : ∀ k, Function.Exact (koszulDifferential ψ (k + 1)) (koszulDifferential ψ k)) :
    (LinearMap.range ψ).colon (LinearMap.range φ : Set R) =
      LinearMap.range ψ ⊔ Ideal.span {LinearMap.det g} := by
  apply le_antisymm
  · intro z hz
    have hz' (m : M) : z * φ m ∈ LinearMap.range ψ := by
      exact Submodule.mem_colon.mp hz (φ m) (LinearMap.mem_range_self φ m)
    obtain ⟨c, hc⟩ := exists_sub_mul_det_mem_range vol φ ψ g hg hψ z hz'
    apply Submodule.mem_sup.mpr
    refine ⟨z - c * LinearMap.det g, hc, c * LinearMap.det g, ?_, by ring⟩
    exact Ideal.mul_mem_left _ c (Ideal.subset_span (Set.mem_singleton _))
  · apply sup_le
    · exact Ideal.le_colon
    · rw [Ideal.span_le]
      rintro r ⟨rfl⟩
      apply Submodule.mem_colon.mpr
      rintro s ⟨m, rfl⟩
      simpa only [smul_eq_mul, mul_comm] using
        mul_det_mem_range vol φ ψ g hg (LinearMap.mem_range_self φ m)

/-- **Determinant annihilator formula for regular sequences**, over an
arbitrary commutative coefficient ring. -/
theorem span_colon_span_eq_of_isWeaklyRegular {n : ℕ}
    (a b : Fin n → R) (g : (Fin n → R) →ₗ[R] (Fin n → R))
    (hg : Fintype.linearCombination R a ∘ₗ g = Fintype.linearCombination R b)
    (hb : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn b)) :
    (Ideal.span (Set.range b)).colon (Ideal.span (Set.range a) : Set R) =
      Ideal.span (Set.range b) ⊔ Ideal.span {LinearMap.det g} := by
  nontriviality R
  let vol := (Module.finBasis R (Fin n → R)).exteriorPowerTopEquiv
  have hψ (k : ℕ) :
      Function.Exact (koszulDifferential (Fintype.linearCombination R b) (k + 1))
        (koszulDifferential (Fintype.linearCombination R b) k) :=
    (koszulComplex.exactAt_succ_iff _ k).mp
      (koszulComplex.exactAt_of_isWeaklyRegular b hb k)
  simpa only [Fintype.range_linearCombination] using
    range_colon_range_eq vol (Fintype.linearCombination R a)
      (Fintype.linearCombination R b) g hg hψ

end PaperVerification.Fermion.Koszul
