module

public import PaperVerification.FermionHarmonicEndpoint
public import PaperVerification.FermionOrdinaryParameters

/-!
# Endpoint annihilation in the actual homogeneous ordinary quotient

All operator coefficients are the images of the paper's literal powers.
Ordinary moments and node nilpotence are derived from the defining ideal.
The resulting annihilator is the original endpoint ideal in the polynomial
ring, acting through its quotient map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_mem_endpointIdeal (f : R →+* S) (data : ℕ → Datum R) (n c : ℕ)
    {p : R} (hp : p ∈ endpointIdeal data n c) :
    f p ∈ endpointIdeal (fun i ↦ (data i).map f) n c := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    apply Ideal.subset_span
    rw [← generators_map]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b ha hb iha ihb => rw [map_add]; exact add_mem iha ihb
  | smul a b hb ih =>
    rw [smul_eq_mul, map_mul]
    exact (endpointIdeal _ n c).mul_mem_left _ ih

theorem pairedPowerData_map_eq_harmonicData
    {K : Type*} [CommRing K] {n : ℕ}
    (f : MvPolynomial (Fin n) K →+* R)
    (r u v : Fin n → ℕ) (β : Fin n → K) (T : Finset (Fin n ⊕ Fin n)) :
    (fun j ↦ (pairedPowerData r u v β (wordMark T) j).map f) =
      harmonicData (fun j ↦ f (MvPolynomial.X j ^ r j))
        (fun j ↦ f (MvPolynomial.C (β j)))
        (fun j ↦ f (MvPolynomial.X j ^ u j))
        (fun j ↦ f (MvPolynomial.X j ^ v j)) T := by
  funext j
  by_cases hj : j < n
  · simp only [pairedPowerData, harmonicData, dataFromFin, dif_pos hj, Datum.map, harmonicDatum]
  · simp only [pairedPowerData, harmonicData, dataFromFin, dif_neg hj, Datum.map, map_zero]

end PaperVerification.Fermion.Endpoint

namespace PaperVerification.Fermion

open scoped BigOperators
open MvPolynomial
open Exterior Endpoint Colex

variable {K : Type*} [Field K] {n : ℕ}

local notation "P" => MvPolynomial (Fin n) K

theorem powerMoment_quotient_all_moments
    (r u v : Fin n → ℕ) (β : Fin n → K) (s : ℕ)
    (huv : ∀ i, u i + v i = r i * s) :
    ∀ k : ℕ, moment
      (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ r i))
      (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (C (β i)) *
        Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ u i) *
        Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ v i)) k = 0 := by
  let q := Ideal.Quotient.mk (powerMomentIdeal r β s)
  intro k
  have hmem : powerMoment r β s k ∈ powerMomentIdeal r β s := by
    rw [powerMomentIdeal_eq_ordinary, powerMoment_eq_moment]
    exact ordinaryMoment_mem _ _ _ k
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hcoeff (i : Fin n) :
      q (C (β i) * (X i ^ r i) ^ s) = q (C (β i)) * q (X i ^ u i) * q (X i ^ v i) := by
    have hp : (C (β i) * (X i ^ r i) ^ s : P) = C (β i) * X i ^ u i * X i ^ v i := by
      rw [← pow_mul, ← huv i, pow_add]
      ring
    rw [hp, map_mul, map_mul]
  rw [powerMoment_eq_moment, scalar_moment_map] at hz
  dsimp only [q] at hcoeff
  simpa only [Polynomial.aeval_X_pow, hcoeff] using hz

section Harmonic

local instance FermionPowerHarmonicEndpoint_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionPowerHarmonicEndpoint_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionPowerHarmonicEndpoint_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionPowerHarmonicEndpoint_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionPowerHarmonicEndpoint_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT

/-- The largest coefficient in the actual ordinary quotient is annihilated
by the actual polynomial endpoint ideal. Neither nilpotence nor the ordinary
moment equations are additional assumptions of this theorem. -/
theorem pairedPower_largest_coefficient_endpoint_annihilates
    (r u v : Fin n → ℕ) (β : Fin n → K) (s : ℕ)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hfac : IsUnit (n.factorial : K))
    (k : ℕ)
    (w : ExteriorAlgebra (P ⧸ powerMomentIdeal r β s)
      (Fin n ⊕ Fin n → P ⧸ powerMomentIdeal r β s))
    (hwdegree : w ∈ ⋀[P ⧸ powerMomentIdeal r β s]^k
      (Fin n ⊕ Fin n → P ⧸ powerMomentIdeal r β s))
    (hw : IsHarmonic (Pi.basisFun (P ⧸ powerMomentIdeal r β s) (Fin n ⊕ Fin n))
      (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ r i))
      (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (C (β i)))
      (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ u i))
      (fun i ↦ Ideal.Quotient.mk (powerMomentIdeal r β s) (X i ^ v i)) w)
    (T : Finset (Fin n ⊕ Fin n))
    (hT : (Pi.basisFun (P ⧸ powerMomentIdeal r β s) (Fin n ⊕ Fin n)).ExteriorAlgebra.repr w T ≠ 0)
    (hmax : ∀ U,
      (Pi.basisFun (P ⧸ powerMomentIdeal r β s) (Fin n ⊕ Fin n)).ExteriorAlgebra.repr w U ≠ 0 →
        toColex U ≤ toColex T) :
    ∀ p ∈ endpointIdeal (pairedPowerData r u v β (wordMark T)) n (wordHeight T n),
      Ideal.Quotient.mk (powerMomentIdeal r β s) p *
        (Pi.basisFun (P ⧸ powerMomentIdeal r β s) (Fin n ⊕ Fin n)).ExteriorAlgebra.repr w T = 0 := by
  let q := Ideal.Quotient.mk (powerMomentIdeal r β s)
  let b := Pi.basisFun (P ⧸ powerMomentIdeal r β s) (Fin n ⊕ Fin n)
  obtain ⟨N, hN⟩ := powerMoment_nodes_uniformly_nilpotent r β s hr hβ
  have hβ' (i : Fin n) : IsUnit (q (C (β i))) := by
    have hi : IsUnit (β i) := by simpa only [Finset.sum_singleton] using hβ {i} (Finset.singleton_nonempty i)
    exact (hi.map MvPolynomial.C).map q
  have hfac' : IsUnit (n.factorial : P ⧸ powerMomentIdeal r β s) := by
    simpa only [map_natCast] using hfac.map (algebraMap K (P ⧸ powerMomentIdeal r β s))
  have hann := largest_harmonic_coefficient_endpoint_annihilates b
    (fun i ↦ q (X i ^ r i)) (fun i ↦ q (C (β i)))
    (fun i ↦ q (X i ^ u i)) (fun i ↦ q (X i ^ v i)) N hN hfac' hβ'
    (powerMoment_quotient_all_moments r u v β s huv) k w hwdegree hw T hT hmax
  intro p hp
  apply hann (q p)
  rw [← pairedPowerData_map_eq_harmonicData q r u v β T]
  exact map_mem_endpointIdeal q _ n (wordHeight T n) hp

end Harmonic

end PaperVerification.Fermion
