module

public import PaperVerification.FermionHarmonicEndpoint

/-!
# Homogeneous components of actual moment harmonics

The projection is the genuine exterior grading, not a number-operator
eigenspace. Contractions commute with it with their exact degree shifts,
including the bottom degrees. Thus the endpoint conclusion applies to the
largest coefficient of an arbitrary harmonic, without homogeneity assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators
open Colex
open Endpoint

section Projection

variable {R V J : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [LinearOrder J] [Fintype J]
variable (b : Module.Basis J R V)

theorem exteriorDegreeProjection_mem (k : ℕ) (w : ExteriorAlgebra R V) :
    exteriorDegreeProjection k w ∈ ⋀[R]^k V :=
  (DirectSum.decompose (fun j : ℕ ↦ ⋀[R]^j V) w k).property

theorem exteriorDegreeProjection_coordinate (k : ℕ) (T : Finset J) (w : ExteriorAlgebra R V) :
    b.ExteriorAlgebra.repr (exteriorDegreeProjection k w) T =
      if T.card = k then b.ExteriorAlgebra.repr w T else 0 := by
  have heq : (b.ExteriorAlgebra.coord T).comp (exteriorDegreeProjection k) =
      if T.card = k then b.ExteriorAlgebra.coord T else 0 := by
    apply b.ExteriorAlgebra.ext
    intro U
    simp only [LinearMap.comp_apply]
    by_cases hU : U.card = k
    · rw [exteriorDegreeProjection_self (hU ▸ exterior_basis_mem b U)]
      by_cases hT : T.card = k
      · rw [if_pos hT]
      · have hUT : U ≠ T := fun h ↦ hT (h ▸ hU)
        simp [hT, Module.Basis.coord_apply, Finsupp.single_apply, hUT, (Ne.symm hUT)]
    · rw [exteriorDegreeProjection_zero (exterior_basis_mem b U) hU, map_zero]
      by_cases hT : T.card = k
      · have hUT : U ≠ T := fun h ↦ hU (h ▸ hT)
        simp [hT, Module.Basis.coord_apply, Finsupp.single_apply, hUT, (Ne.symm hUT)]
      · simp [hT]
  have hh := LinearMap.congr_fun heq w
  by_cases hT : T.card = k
  · simpa only [if_pos hT, LinearMap.comp_apply, Module.Basis.coord_apply] using hh
  · simpa only [if_neg hT, LinearMap.comp_apply, Module.Basis.coord_apply,
      LinearMap.zero_apply] using hh

theorem annihilation_projection_zero (l : Module.Dual R V) (w : ExteriorAlgebra R V) :
    annihilation l (exteriorDegreeProjection 0 w) = 0 :=
  TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero l
    (exteriorDegreeProjection_mem 0 w)

include b in
theorem annihilation_projection_succ (l : Module.Dual R V) (k : ℕ)
    (w : ExteriorAlgebra R V) :
    annihilation l (exteriorDegreeProjection (k + 1) w) =
      exteriorDegreeProjection k (annihilation l w) := by
  have heq : annihilation l * exteriorDegreeProjection (k + 1) =
      exteriorDegreeProjection k * annihilation l := by
    apply b.ExteriorAlgebra.ext
    intro T
    simp only [Module.End.mul_apply]
    cases hcard : T.card with
    | zero =>
      have hmem : b.ExteriorAlgebra T ∈ ⋀[R]^0 V := hcard ▸ exterior_basis_mem b T
      rw [exteriorDegreeProjection_zero hmem (by omega), map_zero,
        show annihilation l (b.ExteriorAlgebra T) = 0 from
          TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero l hmem,
        map_zero]
    | succ j =>
      have hmem : b.ExteriorAlgebra T ∈ ⋀[R]^(j + 1) V := hcard ▸ exterior_basis_mem b T
      have hann : annihilation l (b.ExteriorAlgebra T) ∈ ⋀[R]^j V :=
        TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower l hmem
      by_cases hj : j = k
      · subst j
        rw [exteriorDegreeProjection_self hmem, exteriorDegreeProjection_self hann]
      · rw [exteriorDegreeProjection_zero hmem (by omega), map_zero,
          exteriorDegreeProjection_zero hann hj]
  exact LinearMap.congr_fun heq w

end Projection

section HarmonicProjection

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    [LinearOrder (Fin n ⊕ Fin n)]
variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

/-- The literal simultaneous-kernel submodule of the odd and mixed currents. -/
def harmonicSubmodule (φ β a c : Fin n → R) : Submodule R (ExteriorAlgebra R V) where
  carrier := {w | IsHarmonic b φ β a c w}
  zero_mem' := ⟨fun _ ↦ map_zero _, fun _ ↦ map_zero _, fun _ ↦ map_zero _⟩
  add_mem' := by
    intro w z hw hz
    exact ⟨fun p ↦ by rw [map_add, hw.1 p, hz.1 p, add_zero],
      fun p ↦ by rw [map_add, hw.2.1 p, hz.2.1 p, add_zero],
      fun p ↦ by rw [map_add, hw.2.2 p, hz.2.2 p, add_zero]⟩
  smul_mem' := by
    intro d w hw
    exact ⟨fun p ↦ by rw [map_smul, hw.1 p, smul_zero],
      fun p ↦ by rw [map_smul, hw.2.1 p, smul_zero],
      fun p ↦ by rw [map_smul, hw.2.2 p, smul_zero]⟩

theorem mixedCurrent_projection_add_two (φ : Fin n → R) (p : Polynomial R)
    (k : ℕ) (w : ExteriorAlgebra R V) :
    mixedCurrent b φ p (exteriorDegreeProjection (k + 2) w) =
      exteriorDegreeProjection k (mixedCurrent b φ p w) := by
  simp only [mixedCurrent, LinearMap.sum_apply, LinearMap.smul_apply,
    pairLower, Module.End.mul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show k + 2 = (k + 1) + 1 by omega,
    annihilation_projection_succ b (b.coord (.inl i)) (k + 1),
    annihilation_projection_succ b (b.coord (.inr i)) k]

theorem mixedCurrent_projection_zero (φ : Fin n → R) (p : Polynomial R)
    (w : ExteriorAlgebra R V) : mixedCurrent b φ p (exteriorDegreeProjection 0 w) = 0 := by
  simp only [mixedCurrent, LinearMap.sum_apply, LinearMap.smul_apply,
    pairLower, Module.End.mul_apply, annihilation_projection_zero, map_zero,
    smul_zero, Finset.sum_const_zero]

theorem mixedCurrent_projection_one (φ : Fin n → R) (p : Polynomial R)
    (w : ExteriorAlgebra R V) : mixedCurrent b φ p (exteriorDegreeProjection 1 w) = 0 := by
  simp only [mixedCurrent, LinearMap.sum_apply, LinearMap.smul_apply,
    pairLower, Module.End.mul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [show 1 = 0 + 1 by rfl, annihilation_projection_succ b (b.coord (.inl i)) 0,
    annihilation_projection_zero, smul_zero]

theorem IsHarmonic.projection (φ β a c : Fin n → R) (k : ℕ)
    (w : ExteriorAlgebra R V) (hw : IsHarmonic b φ β a c w) :
    IsHarmonic b φ β a c (exteriorDegreeProjection k w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    cases k with
    | zero => exact annihilation_projection_zero _ w
    | succ k =>
      rw [thetaCurrent, annihilation_projection_succ b, show PaperVerification.Fermion.Exterior.annihilation (thetaFunctional b φ c p) w = 0 from hw.1 p,
        map_zero]
  · intro p
    cases k with
    | zero => exact annihilation_projection_zero _ w
    | succ k =>
      rw [xiCurrent, annihilation_projection_succ b, show PaperVerification.Fermion.Exterior.annihilation (xiFunctional b φ β a p) w = 0 from hw.2.1 p,
        map_zero]
  · intro p
    cases k with
    | zero => exact mixedCurrent_projection_zero b φ p w
    | succ k =>
      cases k with
      | zero => exact mixedCurrent_projection_one b φ p w
      | succ k => rw [mixedCurrent_projection_add_two b φ p k w, hw.2.2 p, map_zero]

end HarmonicProjection

section UnrestrictedHarmonic

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

local instance FermionHarmonicGrading_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionHarmonicGrading_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionHarmonicGrading_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionHarmonicGrading_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionHarmonicGrading_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionHarmonicGrading_localInst_6 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq

variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

/-- The complete endpoint annihilator applies to every harmonic, with no
extra exterior-homogeneity hypothesis. -/
theorem largest_harmonic_coefficient_endpoint_annihilates_ungraded
    (φ β a c : Fin n → R) (N : ℕ) (hφ : ∀ j, φ j ^ N = 0)
    (hfac : IsUnit (n.factorial : R)) (hβ : ∀ j, IsUnit (β j))
    (hmom : ∀ r : ℕ, moment φ (fun j ↦ β j * a j * c j) r = 0)
    (w : ExteriorAlgebra R V) (hw : IsHarmonic b φ β a c w)
    (T : Finset (Fin n ⊕ Fin n)) (hT : b.ExteriorAlgebra.repr w T ≠ 0)
    (hmax : ∀ U, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T) :
    (∀ i ≤ n, (T ∩ pairedPrefix n i).card ≤ i) ∧
      ∀ p ∈ endpointIdeal (harmonicData φ β a c T) n (wordHeight T n),
        p * b.ExteriorAlgebra.repr w T = 0 := by
  let w' := exteriorDegreeProjection T.card w
  have hw' := IsHarmonic.projection b φ β a c T.card w hw
  have hT' : b.ExteriorAlgebra.repr w' T = b.ExteriorAlgebra.repr w T := by
    simp only [w', exteriorDegreeProjection_coordinate, ite_true]
  have hmax' : ∀ U, b.ExteriorAlgebra.repr w' U ≠ 0 → toColex U ≤ toColex T := by
    intro U hU
    apply hmax U
    intro hz
    apply hU
    dsimp only [w']
    rw [exteriorDegreeProjection_coordinate, hz]
    split_ifs <;> rfl
  have hne : b.ExteriorAlgebra.repr w' T ≠ 0 := by rwa [hT']
  refine ⟨largest_harmonic_term_prefix_card_le b φ β a c hfac T.card w'
    (exteriorDegreeProjection_mem _ _) hw' T hne hmax', ?_⟩
  have hh := largest_harmonic_coefficient_endpoint_annihilates b φ β a c N hφ hfac hβ hmom
    T.card w' (exteriorDegreeProjection_mem _ _) hw' T hne hmax'
  simpa only [hT'] using hh

end UnrestrictedHarmonic

end PaperVerification.Fermion.Exterior
