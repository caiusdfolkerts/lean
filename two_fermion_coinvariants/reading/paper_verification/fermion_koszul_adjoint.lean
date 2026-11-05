module

public import TauCeti.RingTheory.KoszulComplex.Regular
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
public import PaperVerification.FermionKoszulHomotopy

/-!
# The complementary-degree adjoint of a Koszul comparison

For a linear map `g` with `φ ∘ g = ψ`, the usual exterior powers give a map
`K(ψ) → K(φ)`. Transposing complementary exterior powers against the perfect
wedge pairings gives a reverse map `K(φ) → K(ψ)`. Its degree-zero map is
multiplication by `det g`, and its top-degree map is the identity. These are
the two endpoint facts needed for the determinant-colon injection.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Koszul

open TauCeti

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]

variable (vol : ⋀[R]^(Module.finrank R M) M ≃ₗ[R] R)

/-- Equality of actual exterior products gives equality of their scalar-valued
complementary-degree pairings, including degree transports. -/
theorem wedgePairing_eq_of_mul_eq
    {k l p q : ℕ} (hkl : k + l = Module.finrank R M)
    (hpq : p + q = Module.finrank R M)
    (x : ⋀[R]^k M) (y : ⋀[R]^l M)
    (x' : ⋀[R]^p M) (y' : ⋀[R]^q M) (r : R)
    (h : (x : ExteriorAlgebra R M) * y = r • ((x' : ExteriorAlgebra R M) * y')) :
    exteriorPower.wedgePairing vol hkl x y =
      r * exteriorPower.wedgePairing vol hpq x' y' := by
  let z : ⋀[R]^(Module.finrank R M) M := ⟨x' * y', by
    rw [← hpq]
    exact (exteriorPower.wedge R M p q x' y').property⟩
  rw [exteriorPower.wedgePairing_apply_eq_of_coe_mul_eq vol hkl x y (r • z) h,
    exteriorPower.wedgePairing_apply_eq_of_coe_mul_eq vol hpq x' y' z rfl]
  exact vol.map_smul r z

/-- Koszul contraction is adjoint, up to the standard degree sign, in the
complementary wedge pairing. -/
theorem wedgePairing_koszulDifferential
    (φ : Module.Dual R M) (k l : ℕ) (hkl : k + (l + 1) = Module.finrank R M)
    (x : ⋀[R]^(k + 1) M) (y : ⋀[R]^(l + 1) M) :
    exteriorPower.wedgePairing vol hkl (koszulDifferential φ k x) y =
      (-1 : R) ^ k * exteriorPower.wedgePairing vol (by omega) x
        (koszulDifferential φ l y) := by
  apply wedgePairing_eq_of_mul_eq
  have hzero : (x : ExteriorAlgebra R M) * y = 0 := by
    exact congrArg Subtype.val (exteriorPower.eq_zero_of_finrank_lt
      ((k + 1) + (l + 1)) (by omega) (exteriorPower.wedge R M _ _ x y))
  have hc := congrArg (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ) hzero
  rw [CliffordAlgebra.contractLeft_mul,
    TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower x.property, map_zero,
    smul_mul_assoc, pow_succ, mul_neg_one, neg_smul] at hc
  apply sub_eq_zero.mp
  simpa only [sub_eq_add_neg, coe_koszulDifferential_apply] using hc

/-- The adjoint of the complementary exterior power. -/
def wedgeAdjoint (g : M →ₗ[R] M) {k l : ℕ} (hkl : k + l = Module.finrank R M) :
    ⋀[R]^k M →ₗ[R] ⋀[R]^k M :=
  (exteriorPower.wedgePairing vol hkl).toPerfPair.symm.toLinearMap ∘ₗ
    (exteriorPower.map l g).dualMap ∘ₗ
      (exteriorPower.wedgePairing vol hkl).toPerfPair.toLinearMap

@[simp]
theorem wedgeAdjoint_pairing (g : M →ₗ[R] M) {k l : ℕ}
    (hkl : k + l = Module.finrank R M) (x : ⋀[R]^k M) (y : ⋀[R]^l M) :
    exteriorPower.wedgePairing vol hkl (wedgeAdjoint vol g hkl x) y =
      exteriorPower.wedgePairing vol hkl x (exteriorPower.map l g y) := by
  simp [wedgeAdjoint]

theorem exterior_map_zero_eq_id (g : M →ₗ[R] M) :
    exteriorPower.map 0 g = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (exteriorPower.zeroEquiv R M).injective
  exact LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality g) x

theorem wedgeAdjoint_zero (g : M →ₗ[R] M) :
    wedgeAdjoint vol g (show 0 + Module.finrank R M = Module.finrank R M by omega) =
      LinearMap.det g • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (exteriorPower.wedgePairing (k := 0) (l := Module.finrank R M) vol
    (show 0 + Module.finrank R M = Module.finrank R M by omega)).toPerfPair.injective
  apply LinearMap.ext
  intro y
  simp only [LinearMap.toPerfPair_apply, wedgeAdjoint_pairing,
    LinearMap.map_exteriorPower_finrank_eq_det_smul, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem wedgeAdjoint_top (g : M →ₗ[R] M) :
    wedgeAdjoint vol g (show Module.finrank R M + 0 = Module.finrank R M by omega) =
      LinearMap.id := by
  letI : (exteriorPower.wedgePairing (k := Module.finrank R M) (l := 0) vol
      (show Module.finrank R M + 0 = Module.finrank R M by omega)).IsPerfPair :=
    exteriorPower.instIsPerfPairWedgePairing (k := Module.finrank R M) (l := 0) vol _
  apply LinearMap.ext
  intro x
  apply (exteriorPower.wedgePairing (k := Module.finrank R M) (l := 0) vol
    (show Module.finrank R M + 0 = Module.finrank R M by omega)).toPerfPair.injective
  apply LinearMap.ext
  intro y
  simp only [LinearMap.toPerfPair_apply, wedgeAdjoint_pairing,
    exterior_map_zero_eq_id, LinearMap.id_apply]

/-- The complementary adjoints intertwine the differentials in the reverse
direction from the ordinary exterior-power comparison. -/
theorem wedgeAdjoint_comm (φ ψ : Module.Dual R M) (g : M →ₗ[R] M)
    (hg : φ ∘ₗ g = ψ) (k l : ℕ) (hkl : k + (l + 1) = Module.finrank R M) :
    koszulDifferential ψ k ∘ₗ wedgeAdjoint vol g (show (k + 1) + l = Module.finrank R M by omega) =
      wedgeAdjoint vol g hkl ∘ₗ koszulDifferential φ k := by
  apply LinearMap.ext
  intro x
  apply (exteriorPower.wedgePairing vol hkl).toPerfPair.injective
  apply LinearMap.ext
  intro y
  change exteriorPower.wedgePairing vol hkl
      (koszulDifferential ψ k (wedgeAdjoint vol g _ x)) y =
    exteriorPower.wedgePairing vol hkl
      (wedgeAdjoint vol g hkl (koszulDifferential φ k x)) y
  rw [wedgePairing_koszulDifferential, wedgeAdjoint_pairing,
    wedgeAdjoint_pairing, wedgePairing_koszulDifferential,
    koszulDifferential_map, hg]

/-- The comparison in every natural degree; the exterior power vanishes above
the rank, so zero is the only possible map there. -/
def adjoint (g : M →ₗ[R] M) (k : ℕ) : ⋀[R]^k M →ₗ[R] ⋀[R]^k M :=
  if hk : k ≤ Module.finrank R M then wedgeAdjoint vol g (Nat.add_sub_of_le hk) else 0

@[simp]
theorem adjoint_zero (g : M →ₗ[R] M) :
    adjoint vol g 0 = LinearMap.det g • LinearMap.id := by
  simp only [adjoint, Nat.zero_le, dite_true, Nat.sub_zero]
  exact wedgeAdjoint_zero vol g

@[simp]
theorem adjoint_top (g : M →ₗ[R] M) :
    adjoint vol g (Module.finrank R M) = LinearMap.id := by
  simp only [adjoint, le_refl, dite_true, Nat.sub_self]
  exact wedgeAdjoint_top vol g

theorem adjoint_comm (φ ψ : Module.Dual R M) (g : M →ₗ[R] M)
    (hg : φ ∘ₗ g = ψ) (k : ℕ) :
    koszulDifferential ψ k ∘ₗ adjoint vol g (k + 1) =
      adjoint vol g k ∘ₗ koszulDifferential φ k := by
  by_cases hk : k + 1 ≤ Module.finrank R M
  · have hk' : k ≤ Module.finrank R M := by omega
    have hsub : Module.finrank R M - k = (Module.finrank R M - (k + 1)) + 1 := by omega
    simp only [adjoint, hk, hk', dite_true]
    simpa only [hsub] using
      wedgeAdjoint_comm vol φ ψ g hg k (Module.finrank R M - (k + 1)) (by omega)
  · apply LinearMap.ext
    intro x
    have hx : x = 0 := exteriorPower.eq_zero_of_finrank_lt _ (by omega) x
    simp only [hx, map_zero]

end PaperVerification.Fermion.Koszul
