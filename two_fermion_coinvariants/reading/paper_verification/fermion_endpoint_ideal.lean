module

public import PaperVerification.FermionEndpointSupport
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Evaluation of the actual endpoint ideal

All recursive divisions commute with coefficient maps because their divisor
is the monic polynomial `t-y`. Thus a common zero of the literal polynomial
generators gives exactly the endpoint equations already proved above.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

open scoped BigOperators
open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

def Datum.map (f : R →+* S) (d : Datum R) : Datum S :=
  ⟨f d.node, f d.beta, f d.leftFactor, f d.rightFactor, d.mark⟩

@[simp] theorem Datum.map_weight (f : R →+* S) (d : Datum R) :
    (d.map f).weight = f d.weight := by simp [Datum.map, Datum.weight]

def State.map (f : R →+* S) (T : State R) : State S :=
  ⟨T.A.map f, T.B.map f, T.D.map f, T.N.map f⟩

theorem quotient_map (f : R →+* S) (A : R[X]) (y : R) :
    (quotient A y).map f = quotient (A.map f) (f y) := by
  simp only [quotient, map_divByMonic f (monic_X_sub_C y),
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

theorem next_map (f : R →+* S) (T : State R) (d : Datum R) :
    (next T d).map f = next (T.map f) (d.map f) := by
  cases hm : d.mark <;>
    simp only [next, State.map, Datum.map, hm, quotient_map, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, Datum.weight,
      map_mul]

theorem relations_map (f : R →+* S) (T : State R) (d : Datum R) :
    (relations T d).map f = relations (T.map f) (d.map f) := by
  cases hm : d.mark <;>
    simp only [relations, Datum.map, State.map, hm, List.map_nil, List.map_cons,
      map_mul, ← Polynomial.eval_map_apply, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_C, quotient_map, Datum.weight]

theorem run_map (f : R →+* S) (data : ℕ → Datum R) (n : ℕ) :
    (run data n).map f = run (fun i ↦ (data i).map f) n := by
  induction n with
  | zero => simp [run, initial, State.map]
  | succ n ih => rw [run, next_map, ih, run]

theorem allRelations_map (f : R →+* S) (data : ℕ → Datum R) (n : ℕ) :
    (allRelations data n).map f = allRelations (fun i ↦ (data i).map f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allRelations, List.map_append, ih, relations_map, run_map, allRelations]

/-- The exact finite list: all step remainders followed by the terminal
coefficients of `B_n`. -/
def generators (data : ℕ → Datum R) (n c : ℕ) : List R :=
  allRelations data n ++ List.ofFn (fun j : Fin c ↦ (run data n).B.coeff j)

/-- The actual endpoint ideal in the coefficient polynomial ring. -/
def endpointIdeal (data : ℕ → Datum R) (n c : ℕ) : Ideal R :=
  Ideal.ofList (generators data n c)

theorem generators_map (f : R →+* S) (data : ℕ → Datum R) (n c : ℕ) :
    (generators data n c).map f = generators (fun i ↦ (data i).map f) n c := by
  rw [generators, List.map_append, allRelations_map, List.map_ofFn, generators]
  congr 1
  apply congrArg List.ofFn
  funext j
  have hm := congrArg State.B (run_map f data n)
  change (run data n).B.map f = (run (fun i ↦ (data i).map f) n).B at hm
  rw [← hm, coeff_map]
  rfl

theorem relation_mem_endpointIdeal (data : ℕ → Datum R) (n c : ℕ)
    {r : R} (hr : r ∈ allRelations data n) : r ∈ endpointIdeal data n c := by
  apply Ideal.subset_span
  exact List.mem_append_left _ hr

theorem allRelations_mono (data : ℕ → Datum R) {k n : ℕ} (hkn : k ≤ n)
    {a : R} (ha : a ∈ allRelations data k) : a ∈ allRelations data n := by
  induction n generalizing k with
  | zero =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero hkn
    simpa only [hk] using ha
  | succ n ih =>
    by_cases hk : k ≤ n
    · exact List.mem_append_left _ (ih hk ha)
    · have hkeq : k = n + 1 := by omega
      simpa only [hkeq] using ha

theorem step_relation_mem_endpointIdeal (data : ℕ → Datum R) (k n c : ℕ) (hk : k < n)
    {a : R} (ha : a ∈ relations (run data k) (data k)) : a ∈ endpointIdeal data n c := by
  apply relation_mem_endpointIdeal data n c
  apply allRelations_mono data (Nat.succ_le_iff.mpr hk)
  exact List.mem_append_right _ ha

theorem terminal_mem_endpointIdeal (data : ℕ → Datum R) (n c : ℕ) (j : Fin c) :
    (run data n).B.coeff j ∈ endpointIdeal data n c := by
  apply Ideal.subset_span
  apply List.mem_append_right
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- A common zero of the literal endpoint ideal satisfies all of the mapped
step equations and exactly the prescribed terminal coefficients. -/
theorem mapped_endpoint_equations (f : R →+* S) (data : ℕ → Datum R) (n c : ℕ)
    (h : ∀ p ∈ endpointIdeal data n c, f p = 0) :
    (∀ r ∈ allRelations (fun i ↦ (data i).map f) n, r = 0) ∧
      ∀ j : Fin c, (run (fun i ↦ (data i).map f) n).B.coeff j = 0 := by
  constructor
  · intro r hr
    rw [← allRelations_map] at hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact h a (relation_mem_endpointIdeal data n c ha)
  · intro j
    have hm := congrArg State.B (run_map f data n)
    change (run data n).B.map f = (run (fun i ↦ (data i).map f) n).B at hm
    rw [← hm, coeff_map]
    exact h _ (terminal_mem_endpointIdeal data n c j)

section Powers

variable {K : Type*} [CommRing K] {n : ℕ}

local notation "P" => MvPolynomial (Fin n) K

/-- The paper's homogeneous power data in the actual polynomial ring.
Values beyond the finite index set are fixed and never used by `run data n`. -/
def pairedPowerData (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark)
    (j : ℕ) : Datum P :=
  if hj : j < n then
    let i : Fin n := ⟨j, hj⟩
    ⟨MvPolynomial.X i ^ r i, MvPolynomial.C (β i),
      MvPolynomial.X i ^ u i, MvPolynomial.X i ^ v i, marks i⟩
  else ⟨0, 0, 0, 0, .unmarked⟩

@[simp] theorem pairedPowerData_fin
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark) (i : Fin n) :
    pairedPowerData r u v β marks i =
      ⟨MvPolynomial.X i ^ r i, MvPolynomial.C (β i),
        MvPolynomial.X i ^ u i, MvPolynomial.X i ^ v i, marks i⟩ := by
  simp only [pairedPowerData, dif_pos i.isLt]

variable {F : Type*} [Field F] [Algebra K F]

/-- The actual homogeneous endpoint ideal has only the origin as a common
zero, in every field extension of the coefficient field. -/
theorem pairedPowerEndpoint_zero_locus
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark)
    (height : ℕ → ℕ) (hzero : height 0 = 0) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hsteps : ∀ j (hj : j < n), HeightStep (marks ⟨j, hj⟩) (height j) (height (j + 1)))
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (z : Fin n → F)
    (hz : ∀ p ∈ endpointIdeal (pairedPowerData r u v β marks) n (height n),
      MvPolynomial.aeval z p = 0) : z = 0 := by
  let f : P →+* F := (MvPolynomial.aeval z).toRingHom
  let data : ℕ → Datum F := fun i ↦ (pairedPowerData r u v β marks i).map f
  have heq (i : Fin n) : data i =
      ⟨z i ^ r i, algebraMap K F (β i), z i ^ u i, z i ^ v i, marks i⟩ := by
    simp [data, pairedPowerData_fin, Datum.map, f, AlgHom.toRingHom_eq_coe]
  obtain ⟨hrel, hterm⟩ := mapped_endpoint_equations f
    (pairedPowerData r u v β marks) n (height n) hz
  have hnodes := nodes_zero_of_endpoint_equations data height hzero n s hs
    (by
      intro j hj
      have hm := congrArg Datum.mark (heq ⟨j, hj⟩)
      simpa only [hm] using hsteps j hj)
    (by
      intro i
      rw [heq i]
      simp only
      rw [← pow_add, huv i, pow_mul])
    (by
      intro U hU
      have hm := (hβ U hU).map (algebraMap K F)
      simpa only [map_sum, heq] using hm)
    hrel hterm
  funext i
  have hi := hnodes i
  rw [heq i] at hi
  exact (pow_eq_zero_iff (hr i).ne').mp hi

end Powers

end PaperVerification.Fermion.Endpoint
