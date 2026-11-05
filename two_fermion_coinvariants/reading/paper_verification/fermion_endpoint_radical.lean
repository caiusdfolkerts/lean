module

public import PaperVerification.FermionEndpointIdeal
public import PaperVerification.FermionRadical

/-!
# Radical support and finiteness of the actual endpoint quotient

The field support argument is applied in the fraction field of every prime
quotient. This proves the radical containment over arbitrary coefficient
rings, and hence proves actual module finiteness without a Nullstellensatz.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Every endpoint node belongs to the radical of the literal endpoint
ideal, over an arbitrary commutative coefficient ring. -/
theorem node_mem_endpoint_radical
    (data : ℕ → Datum R) (height : ℕ → ℕ) (hzero : height 0 = 0) (n s : ℕ)
    (hs : 0 < s)
    (hsteps : ∀ j < n, HeightStep (data j).mark (height j) (height (j + 1)))
    (hfactor : ∀ i : Fin n, (data i).leftFactor * (data i).rightFactor = (data i).node ^ s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, (data i).beta))
    (i : Fin n) : (data i).node ∈ (endpointIdeal data n (height n)).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro J ⟨hIJ, hJ⟩
  letI : J.IsPrime := hJ
  let Q := R ⧸ J
  let F := FractionRing Q
  let f : R →+* F := (algebraMap Q F).comp (Ideal.Quotient.mk J)
  have hkill : ∀ p ∈ endpointIdeal data n (height n), f p = 0 := by
    intro p hp
    change algebraMap Q F (Ideal.Quotient.mk J p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hp), map_zero]
  obtain ⟨hrel, hterm⟩ := mapped_endpoint_equations f data n (height n) hkill
  have hn := nodes_zero_of_endpoint_equations (fun j ↦ (data j).map f)
    height hzero n s hs hsteps
    (by
      intro j
      change f (data j).leftFactor * f (data j).rightFactor = f (data j).node ^ s
      rw [← map_mul, hfactor j, map_pow])
    (by
      intro U hU
      simpa only [Datum.map, map_sum] using (hβ U hU).map f)
    hrel hterm i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsFractionRing.injective Q F
  change f (data i).node = algebraMap Q F 0
  simpa only [map_zero, Datum.map] using hn

section PolynomialRing

variable {K : Type*} [CommRing K] {n : ℕ}

local notation "P" => MvPolynomial (Fin n) K

/-- Every polynomial variable belongs to the radical of the actual covered
endpoint ideal. Zero bounds are included: they may make the ideal the unit ideal. -/
theorem variable_mem_pairedPowerEndpoint_radical
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark)
    (height : ℕ → ℕ) (hzero : height 0 = 0) (s : ℕ) (hs : 0 < s)
    (huv : ∀ i, u i + v i = r i * s)
    (hsteps : ∀ j (hj : j < n), HeightStep (marks ⟨j, hj⟩) (height j) (height (j + 1)))
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (i : Fin n) : MvPolynomial.X i ∈
      (endpointIdeal (pairedPowerData r u v β marks) n (height n)).radical := by
  have hn := node_mem_endpoint_radical (pairedPowerData r u v β marks)
    height hzero n s hs
    (by
      intro j hj
      simpa only [pairedPowerData, dif_pos hj] using hsteps j hj)
    (by
      intro j
      rw [pairedPowerData_fin]
      simp only
      rw [← pow_add, huv j, pow_mul])
    (by
      intro U hU
      simpa only [pairedPowerData_fin, map_sum] using
        (hβ U hU).map (MvPolynomial.C : K →+* P)) i
  rw [pairedPowerData_fin] at hn
  rw [← Ideal.radical_idem
    (endpointIdeal (pairedPowerData r u v β marks) n (height n))]
  exact Ideal.mem_radical_iff.mpr ⟨r i, hn⟩

/-- The full endpoint quotient is a finite module over the original
coefficient ring. No field extension or assumed length enters this result. -/
theorem pairedPowerEndpoint_quotient_finite
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark)
    (height : ℕ → ℕ) (hzero : height 0 = 0) (s : ℕ) (hs : 0 < s)
    (huv : ∀ i, u i + v i = r i * s)
    (hsteps : ∀ j (hj : j < n), HeightStep (marks ⟨j, hj⟩) (height j) (height (j + 1)))
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Module.Finite K (P ⧸ endpointIdeal (pairedPowerData r u v β marks) n (height n)) := by
  apply finite_quotient_of_univariate_radical _ (fun _ ↦ Polynomial.X)
    (fun _ ↦ Polynomial.monic_X)
  intro i
  rw [Polynomial.aeval_X]
  exact variable_mem_pairedPowerEndpoint_radical r u v β marks height hzero s hs
    huv hsteps hβ i

end PolynomialRing

end PaperVerification.Fermion.Endpoint
