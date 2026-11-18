module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.NormNum
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over
public import TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import TauCeti.Geometry.Toric.Algebraic.Regular
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme
public import Mathlib.Algebra.Group.UniqueProds.VectorSpace
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.CategoryTheory.Triangulated.Generators
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Regular
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Finiteness
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! Actual monomial power-module and toric scheme proofs.
Its verification status is established only by its ordinary compiler and axiom-audit records.
The source movement and exact bytes are recorded in the toric audit manifest. -/


@[expose] public noncomputable section

/-! ## MonomialBasis: reconstructed development source -/
section MonomialBasis
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from TauCeti.Algebra.MonoidAlgebra.CosetBasis at commit
6b896c7c411221eb78639e4be8ead6e479a62893: the group-coset equivalence is
replaced by a specified genuine monoid decomposition.
-/



open MonoidAlgebra

namespace ToricPower

variable {R M N ι : Type*} [Semiring R] [Monoid M] [Monoid N]

/-- Regroup the coefficients using an actual monoid-index decomposition. -/
def monoidDecompositionAddEquiv (e : (ι × M) ≃ N) :
    (ι →₀ R[M]) ≃+ R[N] :=
  (Finsupp.mapRange.addEquiv coeffAddEquiv).trans <|
    Finsupp.curryAddEquiv.symm.trans <|
      (Finsupp.domCongr e).trans coeffAddEquiv.symm

theorem monoidDecompositionAddEquiv_single_single (e : (ι × M) ≃ N)
    (i : ι) (m : M) (r : R) :
    monoidDecompositionAddEquiv e (Finsupp.single i (single m r)) =
      single (e (i, m)) r := by
  simp [monoidDecompositionAddEquiv, Finsupp.curryAddEquiv, Finsupp.curryEquiv]

theorem monoidDecompositionAddEquiv_single
    (p : M →* N) (e : (ι × M) ≃ N)
    (he : ∀ i m, e (i, m) = p m * e (i, 1)) (i : ι) (a : R[M]) :
    monoidDecompositionAddEquiv e (Finsupp.single i a) =
      mapDomain p a * single (e (i, 1)) 1 := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp [Finsupp.single_add, ha, hb, mapDomain_add, add_mul]
  | single m r =>
    rw [monoidDecompositionAddEquiv_single_single, mapDomain_single,
      single_mul_single, he i m, mul_one]

/-- The regrouping is a linear equivalence for the literal scalar action
through the monoid-algebra homomorphism. -/
def monoidDecompositionLinearEquiv
    (p : M →* N) (e : (ι × M) ≃ N)
    (he : ∀ i m, e (i, m) = p m * e (i, 1)) :
    letI := (mapDomainRingHom R p).toModule
    (ι →₀ R[M]) ≃ₗ[R[M]] R[N] := by
  letI := (mapDomainRingHom R p).toModule
  refine { monoidDecompositionAddEquiv e with map_smul' := ?_ }
  intro a x
  simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | single i b =>
    rw [Finsupp.smul_single, smul_eq_mul,
      monoidDecompositionAddEquiv_single p e he,
      monoidDecompositionAddEquiv_single p e he,
      RingHom.toModule_smul]
    simp [mapDomainRingHom_apply, mapDomain_mul, mul_assoc]

/-- The monomials at the decomposition representatives form a genuine basis
over the source monoid algebra. -/
def monoidDecompositionBasis (p : M →* N) (e : (ι × M) ≃ N)
    (he : ∀ i m, e (i, m) = p m * e (i, 1)) :
    letI := (mapDomainRingHom R p).toModule
    Module.Basis ι R[M] R[N] := by
  letI := (mapDomainRingHom R p).toModule
  exact ⟨(monoidDecompositionLinearEquiv p e he).symm⟩

@[simp] theorem monoidDecompositionBasis_apply
    (p : M →* N) (e : (ι × M) ≃ N)
    (he : ∀ i m, e (i, m) = p m * e (i, 1)) (i : ι) :
    monoidDecompositionBasis (R := R) p e he i = single (e (i, 1)) 1 := by
  simp [monoidDecompositionBasis, Module.Basis.coe_ofRepr,
    monoidDecompositionLinearEquiv, monoidDecompositionAddEquiv_single p e he]

end ToricPower
end MonomialBasis

/-! ## RegularPowerBasis: reconstructed development source -/
section RegularPowerBasis
namespace ToricPower

def natResidueEquiv (ell : ℕ) (hell : 0 < ell) : Fin ell × ℕ ≃ ℕ where
  toFun p := (p.1 : ℕ) + ell * p.2
  invFun m := (⟨m % ell, Nat.mod_lt m hell⟩, m / ell)
  left_inv p := by
    apply Prod.ext
    · apply Fin.ext
      simp [Nat.mod_eq_of_lt p.1.isLt]
    · simp [Nat.add_mul_div_left _ _ hell, Nat.div_eq_of_lt p.1.isLt]
  right_inv m := Nat.mod_add_div m ell

def intResidueEquiv (ell : ℕ) (hell : 0 < ell) : Fin ell × ℤ ≃ ℤ where
  toFun p := (p.1 : ℤ) + (ell : ℤ) * p.2
  invFun m :=
    (⟨(m % (ell : ℤ)).toNat, by
      have h0 : 0 ≤ m % (ell : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hell.ne')
      have hlt : m % (ell : ℤ) < (ell : ℤ) :=
        Int.emod_lt_of_pos _ (by exact_mod_cast hell)
      omega⟩, m / (ell : ℤ))
  left_inv p := by
    have h0 : (0 : ℤ) ≤ (p.1 : ℕ) := Int.natCast_nonneg _
    have hlt : ((p.1 : ℕ) : ℤ) < (ell : ℤ) := by exact_mod_cast p.1.isLt
    have hz : (ell : ℤ) ≠ 0 := by exact_mod_cast hell.ne'
    apply Prod.ext
    · apply Fin.ext
      simp [Int.emod_eq_of_lt h0 hlt]
    · simp [Int.add_mul_ediv_left _ _ hz, Int.ediv_eq_zero_of_lt h0 hlt]
  right_inv m := by
    have h0 : 0 ≤ m % (ell : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hell.ne')
    simp only [Int.toNat_of_nonneg h0]
    exact Int.emod_add_mul_ediv m ell

abbrev RegularExponents (α β : Type*) := (α → ℕ) × (β → ℤ)
abbrev RegularResidues (ell : ℕ) (α β : Type*) :=
  (α → Fin ell) × (β → Fin ell)

def regularResidueEquiv (ell : ℕ) (α β : Type*) (hell : 0 < ell) :
    RegularResidues ell α β × RegularExponents α β ≃ RegularExponents α β :=
  (Equiv.prodProdProdComm (α → Fin ell) (β → Fin ell)
    (α → ℕ) (β → ℤ)).trans <|
      Equiv.prodCongr
        ((Equiv.arrowProdEquivProdArrow α (fun _ => Fin ell) (fun _ => ℕ)).symm.trans
          (Equiv.piCongrRight fun _ => natResidueEquiv ell hell))
        ((Equiv.arrowProdEquivProdArrow β (fun _ => Fin ell) (fun _ => ℤ)).symm.trans
          (Equiv.piCongrRight fun _ => intResidueEquiv ell hell))

@[simp] theorem regularResidueEquiv_apply (ell : ℕ) (α β : Type*) (hell : 0 < ell)
    (u : RegularResidues ell α β) (m : RegularExponents α β) :
    regularResidueEquiv ell α β hell (u, m) =
      ((fun j => (u.1 j : ℕ) + ell * m.1 j),
       (fun j => (u.2 j : ℤ) + (ell : ℤ) * m.2 j)) := rfl

def exponentPower (ell : ℕ) (M : Type*) [AddCommMonoid M] :
    Multiplicative M →* Multiplicative M :=
  (ell • AddMonoidHom.id M).toMultiplicative

@[simp] theorem exponentPower_apply (ell : ℕ) {M : Type*} [AddCommMonoid M]
    (m : Multiplicative M) : exponentPower ell M m = m ^ ell := rfl

def regularMonoidDecomposition (ell : ℕ) (α β : Type*) (hell : 0 < ell) :
    (RegularResidues ell α β × Multiplicative (RegularExponents α β)) ≃
      Multiplicative (RegularExponents α β) :=
  (Equiv.prodCongr (Equiv.refl _) Multiplicative.toAdd).trans <|
    (regularResidueEquiv ell α β hell).trans Multiplicative.ofAdd

theorem regularMonoidDecomposition_mul (ell : ℕ) (α β : Type*) (hell : 0 < ell)
    (u : RegularResidues ell α β) (m : Multiplicative (RegularExponents α β)) :
    regularMonoidDecomposition ell α β hell (u, m) =
      exponentPower ell (RegularExponents α β) m *
        regularMonoidDecomposition ell α β hell (u, 1) := by
  apply Multiplicative.toAdd.injective
  apply Prod.ext <;> funext j
  · simp [regularMonoidDecomposition, regularResidueEquiv_apply,
      exponentPower, AddMonoidHom.toMultiplicative, add_comm]
  · simp [regularMonoidDecomposition, regularResidueEquiv_apply,
      exponentPower, AddMonoidHom.toMultiplicative, add_comm]


/-- A basis of the actual regular affine coordinate ring, viewed as a module
through the monomial power homomorphism. -/
def regularPowerBasis (R : Type*) [Semiring R] (ell : ℕ) (α β : Type*) (hell : 0 < ell) :
    let S := MonoidAlgebra R (Multiplicative (RegularExponents α β))
    letI := (MonoidAlgebra.mapDomainRingHom R
      (exponentPower ell (RegularExponents α β))).toModule
    Module.Basis (RegularResidues ell α β) S S :=
  monoidDecompositionBasis (exponentPower ell (RegularExponents α β))
    (regularMonoidDecomposition ell α β hell)
    (regularMonoidDecomposition_mul ell α β hell)

theorem regularPower_finite (R : Type*) [CommRing R] (ell : ℕ)
    (α β : Type*) [Finite α] [Finite β] (hell : 0 < ell) :
    (MonoidAlgebra.mapDomainRingHom R
      (exponentPower ell (RegularExponents α β))).Finite := by
  let S := MonoidAlgebra R (Multiplicative (RegularExponents α β))
  letI : Module S S := (MonoidAlgebra.mapDomainRingHom R
    (exponentPower ell (RegularExponents α β))).toModule
  change Module.Finite S S
  exact Module.Finite.of_basis (regularPowerBasis R ell α β hell)

theorem regularPower_flat (R : Type*) [CommRing R] (ell : ℕ)
    (α β : Type*) (hell : 0 < ell) :
    (MonoidAlgebra.mapDomainRingHom R
      (exponentPower ell (RegularExponents α β))).Flat := by
  let S := MonoidAlgebra R (Multiplicative (RegularExponents α β))
  letI : Module S S := (MonoidAlgebra.mapDomainRingHom R
    (exponentPower ell (RegularExponents α β))).toModule
  change Module.Flat S S
  letI : Module.Free S S := Module.Free.of_basis (regularPowerBasis R ell α β hell)
  exact inferInstanceAs (Module.Flat S S)

def transportedMonoidDecomposition {M : Type*} [AddCommMonoid M]
    (ell : ℕ) {α β : Type*} (hell : 0 < ell)
    (e : M ≃+ RegularExponents α β) :
    (RegularResidues ell α β × Multiplicative M) ≃ Multiplicative M :=
  (Equiv.prodCongr (Equiv.refl _) e.toMultiplicative.toEquiv).trans <|
    (regularMonoidDecomposition ell α β hell).trans e.toMultiplicative.symm.toEquiv

@[simp] theorem transportedMonoidDecomposition_apply {M : Type*} [AddCommMonoid M]
    (ell : ℕ) {α β : Type*} (hell : 0 < ell)
    (e : M ≃+ RegularExponents α β)
    (u : RegularResidues ell α β) (m : Multiplicative M) :
    transportedMonoidDecomposition ell hell e (u, m) =
      e.toMultiplicative.symm (regularMonoidDecomposition ell α β hell
        (u, e.toMultiplicative m)) := rfl

theorem transportedMonoidDecomposition_mul {M : Type*} [AddCommMonoid M]
    (ell : ℕ) {α β : Type*} (hell : 0 < ell)
    (e : M ≃+ RegularExponents α β)
    (u : RegularResidues ell α β) (m : Multiplicative M) :
    transportedMonoidDecomposition ell hell e (u, m) =
      exponentPower ell M m * transportedMonoidDecomposition ell hell e (u, 1) := by
  rw [transportedMonoidDecomposition_apply, transportedMonoidDecomposition_apply]
  apply e.toMultiplicative.injective
  simp only [map_mul, MulEquiv.apply_symm_apply, map_one]
  rw [regularMonoidDecomposition_mul]
  simp only [exponentPower_apply, map_pow]

def transportedPowerBasis (R : Type*) [Semiring R]
    {M : Type*} [AddCommMonoid M] (ell : ℕ) {α β : Type*}
    (hell : 0 < ell) (e : M ≃+ RegularExponents α β) :
    let S := MonoidAlgebra R (Multiplicative M)
    letI := (MonoidAlgebra.mapDomainRingHom R (exponentPower ell M)).toModule
    Module.Basis (RegularResidues ell α β) S S :=
  monoidDecompositionBasis (exponentPower ell M)
    (transportedMonoidDecomposition ell hell e)
    (transportedMonoidDecomposition_mul ell hell e)

theorem transportedPower_finite (R : Type*) [CommRing R]
    {M : Type*} [AddCommMonoid M] (ell : ℕ) {α β : Type*}
    [Finite α] [Finite β] (hell : 0 < ell) (e : M ≃+ RegularExponents α β) :
    (MonoidAlgebra.mapDomainRingHom R (exponentPower ell M)).Finite := by
  let S := MonoidAlgebra R (Multiplicative M)
  letI : Module S S := (MonoidAlgebra.mapDomainRingHom R (exponentPower ell M)).toModule
  change Module.Finite S S
  exact Module.Finite.of_basis (transportedPowerBasis R ell hell e)

theorem transportedPower_flat (R : Type*) [CommRing R]
    {M : Type*} [AddCommMonoid M] (ell : ℕ) {α β : Type*}
    (hell : 0 < ell) (e : M ≃+ RegularExponents α β) :
    (MonoidAlgebra.mapDomainRingHom R (exponentPower ell M)).Flat := by
  let S := MonoidAlgebra R (Multiplicative M)
  letI : Module S S := (MonoidAlgebra.mapDomainRingHom R (exponentPower ell M)).toModule
  change Module.Flat S S
  letI : Module.Free S S := Module.Free.of_basis (transportedPowerBasis R ell hell e)
  exact inferInstanceAs (Module.Flat S S)

end ToricPower
end RegularPowerBasis

/-! ## PowerScheme: reconstructed development source -/
section PowerScheme
open AlgebraicGeometry CategoryTheory
open TauCeti.Toric
open scoped NNReal

namespace ToricPower

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V}

theorem power_lattice_compatibility (i : N →+ V) (ell : ℕ) (n : N) :
    ((ell : ℝ) • (LinearMap.id : V →ₗ[ℝ] V)) (i n) =
      i ((ell • AddMonoidHom.id N) n) := by
  simp only [LinearMap.smul_apply, LinearMap.id_apply, AddMonoidHom.smul_apply,
    AddMonoidHom.id_apply, map_nsmul, Nat.cast_smul_eq_nsmul]

/-- The actual fan endomorphism induced by multiplication by a natural integer. -/
def powerFanHom (Φ : Fan i) (ell : ℕ) : FanHom Φ Φ where
  latticeMap := ell • AddMonoidHom.id N
  realMap := (ell : ℝ) • LinearMap.id
  map_lattice := power_lattice_compatibility i ell
  map_cone σ hσ := by
    refine ⟨σ, hσ, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact σ.smul_mem (Nat.cast_nonneg ell) hx

@[simp] theorem powerFanHom_latticeMap (Φ : Fan i) (ell : ℕ) :
    (powerFanHom Φ ell).latticeMap = ell • AddMonoidHom.id N := rfl

@[simp] theorem powerFanHom_realMap (Φ : Fan i) (ell : ℕ) :
    (powerFanHom Φ ell).realMap = (ell : ℝ) • LinearMap.id := rfl

theorem cone_map_power_eq (σ : PointedCone ℝ V) (ell : ℕ) (hell : 0 < ell) :
    σ.map ((ell : ℝ) • LinearMap.id) = σ := by
  have helr : (0 : ℝ) < ell := by exact_mod_cast hell
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact σ.smul_mem helr.le hx
  · intro x hx
    refine ⟨(ell : ℝ)⁻¹ • x,
      σ.smul_mem (inv_pos.mpr helr).le hx, ?_⟩
    change (ell : ℝ) • ((ell : ℝ)⁻¹ • x) = x
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
      mul_inv_cancel₀ helr.ne', one_smul]

theorem powerFanHom_leastCone (Φ : Fan i) (ell : ℕ) (hell : 0 < ell)
    {σ : PointedCone ℝ V} (hσ : σ ∈ Φ.cones) :
    (powerFanHom Φ ell).leastCone hσ = σ := by
  apply le_antisymm
  · apply (powerFanHom Φ ell).leastCone_le hσ hσ
    rw [powerFanHom_realMap, cone_map_power_eq σ ell hell]
  · have hh := (powerFanHom Φ ell).map_le_leastCone hσ
    rwa [powerFanHom_realMap, cone_map_power_eq σ ell hell] at hh

@[simp] theorem powerFanHom_one (Φ : Fan i) :
    powerFanHom Φ 1 = FanHom.id Φ := by
  apply FanHom.ext
  simp

theorem powerFanHom_comp (Φ : Fan i) (ell k : ℕ) :
    (powerFanHom Φ k).comp (powerFanHom Φ ell) = powerFanHom Φ (ell * k) := by
  apply FanHom.ext
  ext n
  simp only [FanHom.comp_latticeMap, powerFanHom_latticeMap,
    AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply,
    smul_smul, mul_comm]

/-- The actual complex scheme morphism, obtained by gluing the monomial power
maps on all affine charts of the given fan. -/
def toricPowerMap (Φ : Fan i) (ell : ℕ) :
    Φ.algebraicRealization ⟶ Φ.algebraicRealization :=
  (powerFanHom Φ ell).algebraicMap

@[simp] theorem toricPowerMap_one (Φ : Fan i) :
    toricPowerMap Φ 1 = 𝟙 Φ.algebraicRealization := by
  rw [toricPowerMap, powerFanHom_one, FanHom.algebraicMap_id]

theorem toricPowerMap_comp (Φ : Fan i) (ell k : ℕ) :
    toricPowerMap Φ ell ≫ toricPowerMap Φ k = toricPowerMap Φ (ell * k) := by
  rw [toricPowerMap, toricPowerMap, ← FanHom.algebraicMap_comp, powerFanHom_comp]
  rfl

def powerConeMapsTo (σ : PointedCone ℝ V) (ell : ℕ) :
    Set.MapsTo (((ell : ℝ) • LinearMap.id) : V →ₗ[ℝ] V) σ σ :=
  fun x hx => σ.smul_mem (Nat.cast_nonneg ell) hx

theorem toricPowerMap_affine_chart (Φ : Fan i) (ell : ℕ) (hell : 0 < ell)
    (σ : Φ.cones) :
    Φ.affineToricChartι σ ≫ toricPowerMap Φ ell =
      affineToricSchemeMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
        ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
        (powerConeMapsTo σ.val ell) ≫ Φ.affineToricChartι σ := by
  simpa only [toricPowerMap, powerFanHom_latticeMap, powerFanHom_realMap] using
    FanHom.affineToricChartι_comp_algebraicMap_of_leastCone_eq
    (powerFanHom Φ ell) σ σ (powerFanHom_leastCone Φ ell hell σ.property)
    (powerConeMapsTo σ.val ell)

theorem power_dualSemigroupMap (Φ : Fan i) (ell : ℕ)
    (σ : Φ.cones) (m : dualSemigroup Φ.lattice σ.val) :
    dualSemigroupMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
        ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
        (powerConeMapsTo σ.val ell) m = ell • m := by
  apply Subtype.ext
  ext n
  simp only [dualSemigroupMap_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply,
    map_nsmul, AddSubmonoidClass.coe_nsmul]

theorem power_affineCoordinateRingMap_single (Φ : Fan i) (ell : ℕ)
    (σ : Φ.cones) (m : dualSemigroup Φ.lattice σ.val) (z : ℂ) :
    affineCoordinateRingMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
        ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
        (powerConeMapsTo σ.val ell) (MonoidAlgebra.single (Multiplicative.ofAdd m) z) =
      MonoidAlgebra.single (Multiplicative.ofAdd (ell • m)) z := by
  rw [affineCoordinateRingMap_single, power_dualSemigroupMap]

end ToricPower
end PowerScheme

/-! ## ToricSchemeProperties: reconstructed development source -/
section ToricSchemeProperties
open AlgebraicGeometry CategoryTheory Set
open TauCeti.Toric

namespace ToricPower

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V}

/-- Embed the actual dual semigroup into a rational vector space by evaluating
each integral character and casting its values to the reals. -/
def dualSemigroupRealEmbedding (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    dualSemigroup hi σ →ₙ+ (N → ℝ) where
  toFun m n := (m.val n : ℝ)
  map_add' m k := by ext n; simp

theorem dualSemigroupRealEmbedding_injective (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) : Function.Injective (dualSemigroupRealEmbedding hi σ) := by
  intro m k h
  apply Subtype.ext
  ext n
  have hh := congrFun h n
  change ((m.val n : ℤ) : ℝ) = ((k.val n : ℤ) : ℝ) at hh
  exact_mod_cast hh

instance affineCoordinateRing_isDomain (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) : IsDomain (affineCoordinateRing hi σ) := by
  letI : UniqueSums (dualSemigroup hi σ) :=
    UniqueSums.of_injective_addHom (dualSemigroupRealEmbedding hi σ)
      (dualSemigroupRealEmbedding_injective hi σ) inferInstance
  infer_instance

instance affineToricScheme_isIntegral (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) : IsIntegral (affineToricScheme hi σ) := by
  dsimp [affineToricScheme]
  infer_instance

instance affineToricChart_isIntegral (Φ : Fan i) (σ : Φ.cones) :
    IsIntegral (Φ.affineToricChart σ) := by
  change IsIntegral (affineToricScheme Φ.lattice σ.val)
  infer_instance

theorem toricScheme_isReduced (Φ : Fan i) : IsReduced Φ.algebraicRealization := by
  letI : ∀ σ : Φ.affineToricOpenCover.I₀, IsReduced (Φ.affineToricOpenCover.X σ) :=
    fun σ => inferInstanceAs (IsReduced (Φ.affineToricChart σ))
  apply IsReduced.of_openCover _ Φ.affineToricOpenCover

theorem toricScheme_preirreducible (Φ : Fan i) :
    PreirreducibleSpace Φ.algebraicRealization := by
  let U : Φ.cones → Φ.algebraicRealization.Opens :=
    fun σ => (Φ.affineToricChartι σ).opensRange
  have hpair : Pairwise (fun σ τ => ¬Disjoint (U σ) (U τ)) := by
    intro σ τ _
    have hnonempty : ((U σ : Set Φ.algebraicRealization) ∩ U τ).Nonempty := by
      change (Set.range (Φ.affineToricChartι σ) ∩
        Set.range (Φ.affineToricChartι τ)).Nonempty
      rw [Φ.range_affineToricChartι_inter_range_affineToricChartι]
      exact Set.range_nonempty _
    intro hd
    obtain ⟨x, hx⟩ := hnonempty
    have hh : x ∈ (⊥ : Φ.algebraicRealization.Opens) :=
      (disjoint_iff_inf_le.mp hd) hx
    exact hh
  have hU (σ : Φ.cones) : IsPreirreducible (U σ : Set Φ.algebraicRealization) := by
    change IsPreirreducible (Set.range (Φ.affineToricChartι σ))
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Φ.affineToricChart σ)).2.image
        (Φ.affineToricChartι σ) (Φ.affineToricChartι σ).continuous.continuousOn
  refine ⟨IsPreirreducible.of_subset_iUnion hpair hU isOpen_univ ?_⟩
  intro x _
  obtain ⟨σ, y, rfl⟩ := Φ.exists_affineToricChartι_apply_eq x
  exact Set.mem_iUnion.mpr ⟨σ, ⟨y, rfl⟩⟩

/-- The genuine scheme glued from any nonempty toric fan is integral. -/
theorem toricScheme_isIntegral (Φ : Fan i) (hΦ : Φ.cones.Nonempty) :
    IsIntegral Φ.algebraicRealization := by
  letI := toricScheme_isReduced Φ
  letI := toricScheme_preirreducible Φ
  obtain ⟨σ, hσ⟩ := hΦ
  letI : Nonempty Φ.algebraicRealization :=
    Nonempty.map (Φ.affineToricChartι ⟨σ, hσ⟩) inferInstance
  letI : IrreducibleSpace Φ.algebraicRealization :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end ToricPower
end ToricSchemeProperties

/-! ## GeneratorTransfer: reconstructed development source -/
section GeneratorTransfer
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

namespace ToricPower

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    [IsTriangulated C] [IsTriangulated D]

/-- Exact functors send the genuine thick envelope of a family into the thick
envelope of its image. -/
theorem map_mem_triangEnvelope
    (P : ObjectProperty C) [P.Nonempty]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    {X : C} (hX : P.triangEnvelope X) :
    (P.map F).triangEnvelope (F.obj X) := by
  let Q := (P.map F).triangEnvelope
  letI : (Q.inverseImage F).IsStableUnderRetracts :=
    { of_retract := fun r h => Q.prop_of_retract (r.map F) h }
  have h : P ≤ Q.inverseImage F := by
    intro Y hY
    exact (P.map F).le_triangEnvelope _ (P.prop_map_obj F hY)
  exact (P.triangEnvelope_le_iff.mpr h) X hX

/-- If every target object is an actual retract of an object in the image,
an exact functor preserves classical generation. -/
theorem image_classicalGenerator_of_retracts
    (P : ObjectProperty C) [P.Nonempty]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hP : P.IsClassicalTriangulatedGenerator)
    (hRetract : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    (P.map F).IsClassicalTriangulatedGenerator := by
  apply le_antisymm le_top
  intro Y _
  obtain ⟨X, ⟨r⟩⟩ := hRetract Y
  apply (P.map F).triangEnvelope.prop_of_retract r
  apply map_mem_triangEnvelope P F
  rw [show P.triangEnvelope = ⊤ from hP]
  trivial

/-- The split-unit form used by power-map pushforward: the splitting is supplied
as genuine morphisms in the category, not as a generator assumption. -/
theorem image_classicalGenerator_of_split_unit
    (P : ObjectProperty C) [P.Nonempty]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (L : D ⥤ C) (η : 𝟭 D ⟶ L ⋙ F) (ρ : L ⋙ F ⟶ 𝟭 D)
    (hηρ : η ≫ ρ = 𝟙 (𝟭 D))
    (hP : P.IsClassicalTriangulatedGenerator) :
    (P.map F).IsClassicalTriangulatedGenerator := by
  apply image_classicalGenerator_of_retracts P F hP
  intro Y
  refine ⟨L.obj Y, ⟨{ i := η.app Y, r := ρ.app Y, retract := ?_ }⟩⟩
  exact congrArg (fun t => t.app Y) hηρ

end ToricPower
end GeneratorTransfer

/-! ## Finiteness of the actual coordinate rings and schemes -/
section NoetherianSchemes

open AlgebraicGeometry CategoryTheory
open TauCeti.Toric

namespace ToricPower

universe u
variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

theorem affineCoordinateRing_finiteType (hi : IsIntegralLattice i)
    {σ : PointedCone ℝ V} (hσ : IsToricCone i σ) :
    Algebra.FiniteType ℂ (affineCoordinateRing hi σ) := by
  letI := hσ.fg_dualSemigroup hi
  infer_instance

theorem affineCoordinateRing_isNoetherian (hi : IsIntegralLattice i)
    {σ : PointedCone ℝ V} (hσ : IsToricCone i σ) :
    IsNoetherianRing (affineCoordinateRing hi σ) := by
  letI := affineCoordinateRing_finiteType hi hσ
  exact Algebra.FiniteType.isNoetherianRing ℂ _

theorem affineToricScheme_isNoetherian (hi : IsIntegralLattice i)
    {σ : PointedCone ℝ V} (hσ : IsToricCone i σ) :
    IsNoetherian (affineToricScheme hi σ) := by
  letI := affineCoordinateRing_isNoetherian hi hσ
  infer_instance

instance affineToricChart_isNoetherian (Φ : Fan i) (σ : Φ.cones) :
    IsNoetherian (Φ.affineToricChart σ) :=
  affineToricScheme_isNoetherian Φ.lattice (Φ.isToricCone σ.property)

/-- Every finite toric fan in the actual integral lattice gives a Noetherian
complex scheme, including the empty fan. -/
theorem toricScheme_isNoetherian (Φ : Fan i) :
    IsNoetherian Φ.algebraicRealization := by
  letI : Finite Φ.affineToricOpenCover.I₀ := inferInstanceAs (Finite Φ.cones)
  letI : ∀ σ : Φ.affineToricOpenCover.I₀, IsAffine (Φ.affineToricOpenCover.X σ) :=
    fun σ => inferInstanceAs (IsAffine (Φ.affineToricChart σ))
  apply (isNoetherian_iff_of_finite_affine_openCover
    (𝒰 := Φ.affineToricOpenCover)).mpr
  intro σ
  change IsNoetherianRing Γ(Φ.affineToricChart σ, ⊤)
  letI := affineToricChart_isNoetherian Φ σ
  exact IsLocallyNoetherian.component_noetherian
    ⟨⊤, isAffineOpen_top (Φ.affineToricChart σ)⟩

end ToricPower
end NoetherianSchemes

/-! ## Finite flat powers on the actual regular affine charts -/
section RegularChartPowers

open AlgebraicGeometry CategoryTheory
open TauCeti.Toric

namespace ToricPower

universe u
variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

def regularDualCoordinateEquiv (hi : IsIntegralLattice i)
    {σ : PointedCone ℝ V} (hσ : IsRegularCone i σ) :
    dualSemigroup hi σ ≃+
      RegularExponents (ToricRay σ)
        (Fin (Module.finrank ℤ N - Nat.card (ToricRay σ))) := by
  letI := ToricRay.finite_of_fg hσ.fg
  exact (hσ.nonempty_dualSemigroup_addEquiv hi).some.trans
    ((Finsupp.linearEquivFunOnFinite ℕ ℕ (ToricRay σ)).toAddEquiv.prodCongr
      (Finsupp.linearEquivFunOnFinite ℕ ℤ
        (Fin (Module.finrank ℤ N - Nat.card (ToricRay σ)))).toAddEquiv)

theorem power_affineCoordinateRingMap_eq (Φ : Fan i) (ell : ℕ)
    (σ : Φ.cones) :
    (affineCoordinateRingMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
      ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
      (powerConeMapsTo σ.val ell)).toRingHom =
    MonoidAlgebra.mapDomainRingHom ℂ (exponentPower ell (dualSemigroup Φ.lattice σ.val)) := by
  apply RingHom.ext
  intro f
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single m z =>
    change affineCoordinateRingMap _ _ _ _ _ _
      (MonoidAlgebra.single (Multiplicative.ofAdd (Multiplicative.toAdd m)) z) = _
    rw [power_affineCoordinateRingMap_single, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    rfl

theorem regular_power_affineCoordinateRingMap_finite (Φ : Fan i) (ell : ℕ)
    (hell : 0 < ell) (σ : Φ.cones) (hσ : IsRegularCone i σ.val) :
    (affineCoordinateRingMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
      ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
      (powerConeMapsTo σ.val ell)).toRingHom.Finite := by
  rw [power_affineCoordinateRingMap_eq]
  letI := ToricRay.finite_of_fg hσ.fg
  exact transportedPower_finite ℂ ell hell (regularDualCoordinateEquiv Φ.lattice hσ)

theorem regular_power_affineCoordinateRingMap_flat (Φ : Fan i) (ell : ℕ)
    (hell : 0 < ell) (σ : Φ.cones) (hσ : IsRegularCone i σ.val) :
    (affineCoordinateRingMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
      ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
      (powerConeMapsTo σ.val ell)).toRingHom.Flat := by
  rw [power_affineCoordinateRingMap_eq]
  exact transportedPower_flat ℂ ell hell (regularDualCoordinateEquiv Φ.lattice hσ)

theorem regular_power_affineToricSchemeMap_finite (Φ : Fan i) (ell : ℕ)
    (hell : 0 < ell) (σ : Φ.cones) (hσ : IsRegularCone i σ.val) :
    IsFinite (affineToricSchemeMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
      ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
      (powerConeMapsTo σ.val ell)) := by
  rw [affineToricSchemeMap_def, IsFinite.SpecMap_iff]
  exact regular_power_affineCoordinateRingMap_finite Φ ell hell σ hσ

theorem regular_power_affineToricSchemeMap_flat (Φ : Fan i) (ell : ℕ)
    (hell : 0 < ell) (σ : Φ.cones) (hσ : IsRegularCone i σ.val) :
    Flat (affineToricSchemeMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
      ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
      (powerConeMapsTo σ.val ell)) := by
  rw [affineToricSchemeMap_def, Flat.SpecMap_iff]
  exact regular_power_affineCoordinateRingMap_flat Φ ell hell σ hσ

end ToricPower
end RegularChartPowers


/-! ## Global flatness for regular fans -/
section GlobalFlatness
open AlgebraicGeometry CategoryTheory
open TauCeti.Toric
namespace ToricPower
universe u
variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

set_option backward.isDefEq.respectTransparency.types false in
theorem toricPowerMap_flat (Φ : Fan i) (hΦ : Φ.IsRegular)
    (ell : ℕ) (hell : 0 < ell) : Flat (toricPowerMap Φ ell) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @Flat.{u}) Φ.affineToricOpenCover).mpr
  intro σ
  change Flat (Φ.affineToricChartι σ ≫ toricPowerMap Φ ell)
  rw [toricPowerMap_affine_chart Φ ell hell σ]
  letI := regular_power_affineToricSchemeMap_flat Φ ell hell σ ((Fan.isRegular_iff (Φ := Φ)).mp hΦ σ.val σ.property)
  infer_instance

end ToricPower
end GlobalFlatness


/-! ## Invariance of the actual affine charts under power maps -/
section ChartInvariance
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric
namespace ToricPower
universe u
variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

abbrev affinePowerMap (Φ : Fan i) (ell : ℕ) (σ : Φ.cones) :
    Φ.affineToricChart σ ⟶ Φ.affineToricChart σ :=
  affineToricSchemeMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
    ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
    (powerConeMapsTo σ.val ell)

theorem toricPowerMap_affine_chart_apply (Φ : Fan i) (ell : ℕ) (hell : 0 < ell)
    (σ : Φ.cones) (x : Φ.affineToricChart σ) :
    toricPowerMap Φ ell (Φ.affineToricChartι σ x) =
      Φ.affineToricChartι σ (affinePowerMap Φ ell σ x) :=
  congrArg (fun f => f x) (toricPowerMap_affine_chart Φ ell hell σ)

theorem affinePowerMap_mem_basicOpen (Φ : Fan i) (ell : ℕ) (hell : 0 < ell)
    (σ : Φ.cones) (m : dualSemigroup Φ.lattice σ.val)
    (x : Φ.affineToricChart σ) :
    affinePowerMap Φ ell σ x ∈
        PrimeSpectrum.basicOpen (MonoidAlgebra.single (Multiplicative.ofAdd m) (1 : ℂ)) ↔
      x ∈ PrimeSpectrum.basicOpen (MonoidAlgebra.single (Multiplicative.ofAdd m) (1 : ℂ)) := by
  rw [affinePowerMap, affineToricSchemeMap_def, Spec.map_apply]
  change ¬ (MonoidAlgebra.single (Multiplicative.ofAdd m) (1 : ℂ)) ∈
    Ideal.comap (affineCoordinateRingMap Φ.lattice Φ.lattice
      (ell • AddMonoidHom.id N) ((ell : ℝ) • LinearMap.id)
      (power_lattice_compatibility i ell) (powerConeMapsTo σ.val ell)).toRingHom
      x.asIdeal ↔ _
  rw [Ideal.mem_comap]
  change ¬ (affineCoordinateRingMap _ _ _ _ _ _
    (MonoidAlgebra.single (Multiplicative.ofAdd m) (1 : ℂ))) ∈ x.asIdeal ↔ _
  rw [power_affineCoordinateRingMap_single]
  have hs : MonoidAlgebra.single (Multiplicative.ofAdd (ell • m)) (1 : ℂ) =
      MonoidAlgebra.single (Multiplicative.ofAdd m) (1 : ℂ) ^ ell := by
    rw [MonoidAlgebra.single_pow, one_pow]
    rfl
  rw [hs]
  exact not_congr (x.isPrime.pow_mem_iff_mem ell hell)

theorem affinePowerMap_mem_face_range (Φ : Fan i) (ell : ℕ) (hell : 0 < ell)
    (σ : Φ.cones) {τ : PointedCone ℝ V} (hτ : τ.IsFaceOf σ.val)
    (x : Φ.affineToricChart σ) :
    affinePowerMap Φ ell σ x ∈ Set.range (faceAffineToricSchemeMap Φ.lattice hτ) ↔
      x ∈ Set.range (faceAffineToricSchemeMap Φ.lattice hτ) := by
  obtain ⟨m, hm, hface⟩ :=
    (Φ.isToricCone σ.property).rational.exists_mem_dualSemigroup_inf_ker_eq Φ.lattice hτ
  subst τ
  rw [range_faceAffineToricSchemeMap Φ.lattice (Φ.isToricCone σ.property).fg ⟨m, hm⟩]
  exact affinePowerMap_mem_basicOpen Φ ell hell σ ⟨m, hm⟩ x

theorem toricPowerMap_preimage_chart (Φ : Fan i) (ell : ℕ) (hell : 0 < ell)
    (σ : Φ.cones) :
    (toricPowerMap Φ ell) ⁻¹' Set.range (Φ.affineToricChartι σ) =
      Set.range (Φ.affineToricChartι σ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨τ, y, rfl⟩ := Φ.exists_affineToricChartι_apply_eq x
    obtain ⟨z, hz⟩ := hx
    have hpoints : Φ.affineToricChartι τ (affinePowerMap Φ ell τ y) =
        Φ.affineToricChartι σ z := by
      rw [← toricPowerMap_affine_chart_apply Φ ell hell τ y]
      exact hz.symm
    obtain ⟨w, hwτ, hwσ⟩ :=
      (Φ.affineToricChartι_eq_affineToricChartι_iff _ _).mp hpoints
    have hm : affinePowerMap Φ ell τ y ∈
        Set.range (faceAffineToricSchemeMap Φ.lattice (Φ.inf_isFaceOf_left τ.property σ.property)) := by
      exact ⟨w, by simpa only [Fan.affineToricOverlapLeft_def] using hwτ⟩
    obtain ⟨w₀, hw₀⟩ :=
      (affinePowerMap_mem_face_range Φ ell hell τ
        (Φ.inf_isFaceOf_left τ.property σ.property) y).mp hm
    refine ⟨Φ.affineToricOverlapRight τ σ w₀, ?_⟩
    rw [← hw₀]
    simpa only [Scheme.Hom.comp_apply, Fan.affineToricOverlapLeft_def] using
      congrArg (fun f => f w₀)
      ((Φ.affineToricOverlapRight_comp_affineToricChartι τ σ).trans
        (Φ.affineToricOverlapLeft_comp_affineToricChartι τ σ).symm)
  · rintro ⟨y, rfl⟩
    exact ⟨affinePowerMap Φ ell σ y,
      (toricPowerMap_affine_chart_apply Φ ell hell σ y).symm⟩

theorem toricPowerMap_chart_isPullback (Φ : Fan i) (ell : ℕ) (hell : 0 < ell)
    (σ : Φ.cones) :
    IsPullback (affinePowerMap Φ ell σ) (Φ.affineToricChartι σ)
      (Φ.affineToricChartι σ) (toricPowerMap Φ ell) := by
  apply IsOpenImmersion.isPullback
  · exact toricPowerMap_affine_chart Φ ell hell σ
  · apply TopologicalSpace.Opens.ext
    exact toricPowerMap_preimage_chart Φ ell hell σ

set_option backward.isDefEq.respectTransparency.types false in
theorem toricPowerMap_finite (Φ : Fan i) (hΦ : Φ.IsRegular)
    (ell : ℕ) (hell : 0 < ell) : IsFinite (toricPowerMap Φ ell) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover
    (P := @IsFinite.{u}) Φ.affineToricOpenCover).mpr
  intro σ
  change IsFinite (pullback.snd (toricPowerMap Φ ell) (Φ.affineToricChartι σ))
  have h := (toricPowerMap_chart_isPullback Φ ell hell σ).flip
  rw [← h.isoPullback_inv_snd]
  letI := regular_power_affineToricSchemeMap_finite Φ ell hell σ ((Fan.isRegular_iff (Φ := Φ)).mp hΦ σ.val σ.property)
  infer_instance

end ToricPower
end ChartInvariance

/-! ## Faithfully flat positive powers -/
section SurjectivePowers
open AlgebraicGeometry CategoryTheory
open TauCeti.Toric
namespace ToricPower

theorem transportedPower_faithfullyFlat (R : Type*) [CommRing R] [Nontrivial R]
    {M : Type*} [AddCommMonoid M] (ell : ℕ) {α β : Type*}
    (hell : 0 < ell) (e : M ≃+ RegularExponents α β) :
    (MonoidAlgebra.mapDomainRingHom R (exponentPower ell M)).FaithfullyFlat := by
  let S := MonoidAlgebra R (Multiplicative M)
  letI : Module S S := (MonoidAlgebra.mapDomainRingHom R (exponentPower ell M)).toModule
  change Module.FaithfullyFlat S S
  letI : Module.Free S S := Module.Free.of_basis (transportedPowerBasis R ell hell e)
  infer_instance

universe u
variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

theorem affinePowerMap_surjective (Φ : Fan i) (ell : ℕ) (hell : 0 < ell)
    (σ : Φ.cones) (hσ : IsRegularCone i σ.val) :
    Surjective (affinePowerMap Φ ell σ) := by
  have hf : (affineCoordinateRingMap Φ.lattice Φ.lattice (ell • AddMonoidHom.id N)
      ((ell : ℝ) • LinearMap.id) (power_lattice_compatibility i ell)
      (powerConeMapsTo σ.val ell)).toRingHom.FaithfullyFlat := by
    rw [power_affineCoordinateRingMap_eq]
    exact transportedPower_faithfullyFlat ℂ ell hell (regularDualCoordinateEquiv Φ.lattice hσ)
  rw [affinePowerMap, affineToricSchemeMap_def]
  exact ((flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (affineCoordinateRingMap Φ.lattice Φ.lattice
      (ell • AddMonoidHom.id N) ((ell : ℝ) • LinearMap.id)
      (power_lattice_compatibility i ell) (powerConeMapsTo σ.val ell)).toRingHom)).mpr hf).2

theorem toricPowerMap_surjective (Φ : Fan i) (hΦ : Φ.IsRegular)
    (ell : ℕ) (hell : 0 < ell) : Surjective (toricPowerMap Φ ell) := by
  rw [surjective_iff]
  intro x
  obtain ⟨σ, y, rfl⟩ := Φ.exists_affineToricChartι_apply_eq x
  letI := affinePowerMap_surjective Φ ell hell σ ((Fan.isRegular_iff (Φ := Φ)).mp hΦ σ.val σ.property)
  obtain ⟨z, hz⟩ := (affinePowerMap Φ ell σ).surjective y
  refine ⟨Φ.affineToricChartι σ z, ?_⟩
  rw [toricPowerMap_affine_chart_apply Φ ell hell σ z, hz]

end ToricPower
end SurjectivePowers

/-! ## Actual chart-module rank and a splitting of the structural unit -/
section ChartModuleRetraction
open MonoidAlgebra
namespace ToricPower

variable {R M N ι : Type*} [Semiring R] [Monoid M] [Monoid N]

/-- The coordinate at a representative equal to the unit is a genuine linear
retraction of the structural monoid-algebra map. -/
theorem monoidDecompositionBasis_coord_mapDomain
    (p : M →* N) (e : (ι × M) ≃ N)
    (he : ∀ i m, e (i, m) = p m * e (i, 1))
    (i₀ : ι) (h₀ : e (i₀, 1) = 1) (a : R[M]) :
    letI : Module R[M] R[N] := (mapDomainRingHom R p).toModule
    (monoidDecompositionBasis (R := R) p e he).coord i₀ (mapDomain p a) = a := by
  classical
  letI : Module R[M] R[N] := (mapDomainRingHom R p).toModule
  let b := monoidDecompositionBasis (R := R) p e he
  have hb : b i₀ = (1 : R[N]) := by
    simp only [b, monoidDecompositionBasis_apply, h₀, MonoidAlgebra.one_def]
  have hm : mapDomain p a = a • b i₀ := by
    rw [hb, RingHom.toModule_smul]
    simp only [mapDomainRingHom_apply, mul_one]
  change b.coord i₀ (mapDomain p a) = a
  rw [hm, map_smul, smul_eq_mul]
  simp [Module.Basis.coord_apply]

def regularZeroResidue (ell : ℕ) (hell : 0 < ell) (α β : Type*) :
    RegularResidues ell α β :=
  (fun _ => ⟨0, hell⟩, fun _ => ⟨0, hell⟩)

theorem regularMonoidDecomposition_zero (ell : ℕ) (hell : 0 < ell)
    (α β : Type*) :
    regularMonoidDecomposition ell α β hell (regularZeroResidue ell hell α β, 1) = 1 := by
  apply Multiplicative.toAdd.injective
  apply Prod.ext <;> funext j <;>
    simp [regularMonoidDecomposition, regularZeroResidue, regularResidueEquiv_apply]

theorem transportedMonoidDecomposition_zero {M : Type*} [AddCommMonoid M]
    (ell : ℕ) (hell : 0 < ell) {α β : Type*}
    (e : M ≃+ RegularExponents α β) :
    transportedMonoidDecomposition ell hell e (regularZeroResidue ell hell α β, 1) = 1 := by
  rw [transportedMonoidDecomposition_apply, map_one,
    regularMonoidDecomposition_zero, map_one]

/-- The residue-zero coordinate splits the actual power homomorphism on every
regular monoid coordinate ring. This is a module map, with the scalar action
through the power homomorphism; it is not asserted to be a ring homomorphism. -/
theorem transportedPowerBasis_coord_power (R : Type*) [Semiring R]
    {M : Type*} [AddCommMonoid M] (ell : ℕ) (hell : 0 < ell) {α β : Type*}
    (e : M ≃+ RegularExponents α β) (a : MonoidAlgebra R (Multiplicative M)) :
    letI : Module (MonoidAlgebra R (Multiplicative M)) (MonoidAlgebra R (Multiplicative M)) :=
      (MonoidAlgebra.mapDomainRingHom R (exponentPower ell M)).toModule
    (transportedPowerBasis R ell hell e).coord (regularZeroResidue ell hell α β)
      (MonoidAlgebra.mapDomainRingHom R (exponentPower ell M) a) = a := by
  exact monoidDecompositionBasis_coord_mapDomain (exponentPower ell M)
    (transportedMonoidDecomposition ell hell e)
    (transportedMonoidDecomposition_mul ell hell e)
    (regularZeroResidue ell hell α β) (transportedMonoidDecomposition_zero ell hell e) a

open TauCeti.Toric
universe u
variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The rank of the actual affine power-map module is exactly `ell ^ rank N`. -/
theorem regular_power_module_finrank (hi : IsIntegralLattice i)
    {σ : PointedCone ℝ V} (hσ : IsRegularCone i σ) (ell : ℕ) (hell : 0 < ell) :
    let S := affineCoordinateRing hi σ
    letI : Module S S :=
      (MonoidAlgebra.mapDomainRingHom ℂ (exponentPower ell (dualSemigroup hi σ))).toModule
    Module.finrank S S = ell ^ Module.finrank ℤ N := by
  dsimp only
  let S := affineCoordinateRing hi σ
  letI : Module S S :=
    (MonoidAlgebra.mapDomainRingHom ℂ (exponentPower ell (dualSemigroup hi σ))).toModule
  letI := ToricRay.finite_of_fg hσ.fg
  rw [Module.finrank_eq_nat_card_basis
    (transportedPowerBasis ℂ ell hell (regularDualCoordinateEquiv hi hσ))]
  simp only [RegularResidues, Nat.card_prod, Nat.card_fun, Nat.card_fin,
    ← pow_add, Nat.add_sub_of_le hσ.card_toricRay_le_finrank]

end ToricPower
end ChartModuleRetraction

end