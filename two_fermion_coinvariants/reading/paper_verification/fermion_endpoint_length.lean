module

public import PaperVerification.FermionEndpointDegrees
public import PaperVerification.FermionEndpointRadical
public import PaperVerification.FermionOrdinaryParameters
public import PaperVerification.FermionListCompleteIntersection
public import Mathlib.Tactic.Push

/-!
# The exact length of the literal paired endpoint ideal

The recursion supplies the actual generators, their actual weighted degrees,
and their count. The prime-quotient support proof supplies finiteness and the
origin radical. Positive degrees give a homogeneous parameter sequence, so
the proved complete-intersection length theorem applies to this exact ideal.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

local notation "P" => MvPolynomial (Fin n) K

def extendNat (a : Fin n → ℕ) (j : ℕ) : ℕ :=
  if hj : j < n then a ⟨j, hj⟩ else 0

@[simp] theorem extendNat_fin (a : Fin n → ℕ) (i : Fin n) : extendNat a i = a i := by
  simp only [extendNat, dif_pos i.isLt]

/-- The four polynomial side lengths, with the incoming height as argument.
These are exactly the four formulas of Theorem 1.1. -/
def pairedBoxBound (r u v s h : ℕ) : Mark → ℕ
  | .unmarked => r * (s + h)
  | .theta => r * h + v
  | .xi => r * h + u
  | .double => r * h

theorem localBoundDegree_eq_weighted_box
    (r u v : Fin n → ℕ) (s h : ℕ) (m : Mark) (i : Fin n) :
    localBoundDegree (∏ j, r j) s h (coveringWeight r i * u i) (coveringWeight r i * v i) m =
      coveringWeight r i * pairedBoxBound (r i) (u i) (v i) s h m := by
  rw [← coveringWeight_mul r i]
  cases m <;> simp only [localBoundDegree, pairedBoxBound] <;> ring

theorem pairedPowerData_node_homogeneous
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark) (i : Fin n) :
    (pairedPowerData r u v β marks i).node.IsWeightedHomogeneous (coveringWeight r) (∏ j, r j) := by
  rw [pairedPowerData_fin]
  simpa only [nsmul_eq_mul, Nat.cast_id, coveringWeight_mul] using
    (MvPolynomial.isWeightedHomogeneous_X K (coveringWeight r) i).pow (r i)

theorem pairedPowerData_left_homogeneous
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark) (i : Fin n) :
    (pairedPowerData r u v β marks i).leftFactor.IsWeightedHomogeneous (coveringWeight r)
      (coveringWeight r i * u i) := by
  rw [pairedPowerData_fin]
  simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using
    (MvPolynomial.isWeightedHomogeneous_X K (coveringWeight r) i).pow (u i)

theorem pairedPowerData_right_homogeneous
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark) (i : Fin n) :
    (pairedPowerData r u v β marks i).rightFactor.IsWeightedHomogeneous (coveringWeight r)
      (coveringWeight r i * v i) := by
  rw [pairedPowerData_fin]
  simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using
    (MvPolynomial.isWeightedHomogeneous_X K (coveringWeight r) i).pow (v i)

theorem pairedPowerData_weight_homogeneous
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark) (s : ℕ)
    (huv : ∀ i, u i + v i = r i * s) (i : Fin n) :
    (pairedPowerData r u v β marks i).weight.IsWeightedHomogeneous (coveringWeight r)
      ((∏ j, r j) * s) := by
  rw [pairedPowerData_fin]
  change MvPolynomial.IsWeightedHomogeneous (coveringWeight r)
    (MvPolynomial.C (β i) * MvPolynomial.X i ^ u i * MvPolynomial.X i ^ v i)
    ((∏ j, r j) * s)
  rw [mul_assoc, ← pow_add, huv i, pow_mul]
  have hnode := (MvPolynomial.isWeightedHomogeneous_X K (coveringWeight r) i).pow (r i)
  simpa only [nsmul_eq_mul, Nat.cast_id, coveringWeight_mul, Nat.mul_comm] using (hnode.pow s).C_mul (β i)

/-- Exact complete-intersection length for every positive paired path box.
The ideal is the literal recursion in Section 4.3; regularity, homogeneity,
finiteness, and the generator count are all derived in the proof. -/
theorem pairedPowerEndpoint_finrank_of_positive
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark)
    (height : ℕ → ℕ) (hzero : height 0 = 0) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hsteps : ∀ j (hj : j < n), HeightStep (marks ⟨j, hj⟩) (height j) (height (j + 1)))
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hbound : ∀ i : Fin n, 0 < pairedBoxBound (r i) (u i) (v i) s (height i) (marks i)) :
    Module.finrank K (P ⧸ endpointIdeal (pairedPowerData r u v β marks) n (height n)) =
      ∏ i : Fin n, pairedBoxBound (r i) (u i) (v i) s (height i) (marks i) := by
  let data := pairedPowerData r u v β marks
  let w := coveringWeight r
  let W := ∏ i, r i
  let l := extendNat (fun i ↦ w i * u i)
  let q := extendNat (fun i ↦ w i * v i)
  let ms := fun j ↦ (data j).mark
  let rs := generators data n (height n)
  let ds := generatorDegrees W s height l q ms n
  have hW : 0 < W := Finset.prod_pos (fun i hi ↦ hr i)
  have hw : ∀ i, 0 < w i := coveringWeight_positive r hr
  have hstepData : ∀ j < n, HeightStep (data j).mark (height j) (height (j + 1)) := by
    intro j hj
    simpa only [data, pairedPowerData, dif_pos hj] using hsteps j hj
  have hy : ∀ j < n, (data j).node.IsWeightedHomogeneous w W := by
    intro j hj
    exact pairedPowerData_node_homogeneous r u v β marks ⟨j, hj⟩
  have hγ : ∀ j < n, (data j).weight.IsWeightedHomogeneous w (W * s) := by
    intro j hj
    exact pairedPowerData_weight_homogeneous r u v β marks s huv ⟨j, hj⟩
  have hl : ∀ j < n, (data j).leftFactor.IsWeightedHomogeneous w (l j) := by
    intro j hj
    simpa only [l, extendNat, dif_pos hj] using
      pairedPowerData_left_homogeneous r u v β marks ⟨j, hj⟩
  have hq : ∀ j < n, (data j).rightFactor.IsWeightedHomogeneous w (q j) := by
    intro j hj
    simpa only [q, extendNat, dif_pos hj] using
      pairedPowerData_right_homogeneous r u v β marks ⟨j, hj⟩
  have hlocal (i : Fin n) :
      localBoundDegree W s (height i) (l i) (q i) (ms i) =
        w i * pairedBoxBound (r i) (u i) (v i) s (height i) (marks i) := by
    simp only [l, q, ms, data, extendNat_fin, pairedPowerData_fin]
    exact localBoundDegree_eq_weighted_box r u v s (height i) (marks i) i
  have hlocalpos : ∀ j < n, 0 < localBoundDegree W s (height j) (l j) (q j) (ms j) := by
    intro j hj
    have h := hlocal ⟨j, hj⟩
    rw [h]
    exact Nat.mul_pos (hw ⟨j, hj⟩) (hbound ⟨j, hj⟩)
  have hhom : List.Forall₂ (fun p e ↦ p.IsWeightedHomogeneous w e) rs ds :=
    generators_homogeneous w W s hs data height l q hzero n hy hγ hl hq hstepData
  have hpositive : ∀ e ∈ ds, 0 < e :=
    generator_degrees_positive W s height l q ms hW hs n hstepData hlocalpos
  have hlen : rs.length = n := generators_length data height hzero n hstepData
  have hrad : HomogeneousLocalization.originIdeal (K := K) (ι := Fin n) ≤
      (Ideal.ofList rs).radical := by
    rw [originIdeal_eq_polynomialOrigin_ker, ← span_variables_eq_origin]
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact variable_mem_pairedPowerEndpoint_radical r u v β marks height hzero s hs
      huv hsteps hβ i
  letI : Module.Finite K (P ⧸ Ideal.ofList rs) :=
    pairedPowerEndpoint_quotient_finite r u v β marks height hzero s hs huv hsteps hβ
  have hlength := GradedHilbert.weighted_list_parameters_finrank w hw rs ds hlen hhom hpositive hrad
  have hwprod : (∏ i, w i) ≠ 0 := (Finset.prod_pos (fun i hi ↦ hw i)).ne'
  apply mul_right_cancel₀ hwprod
  calc
    _ = ds.prod := hlength
    _ = ∏ i : Fin n, localBoundDegree W s (height i) (l i) (q i) (ms i) :=
      generator_degree_product W s height l q ms hzero n hstepData
    _ = ∏ i : Fin n, w i * pairedBoxBound (r i) (u i) (v i) s (height i) (marks i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hlocal i
    _ = _ := by rw [Finset.prod_mul_distrib]; ac_rfl

/-- A zero side length makes one of the literal single-mark remainders
equal to one. Thus the empty-box convention is enforced by the actual ideal. -/
theorem pairedPowerEndpoint_eq_top_of_zero_bound
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark)
    (height : ℕ → ℕ) (hzero : height 0 = 0) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i)
    (hsteps : ∀ j (hj : j < n), HeightStep (marks ⟨j, hj⟩) (height j) (height (j + 1)))
    (i : Fin n)
    (hbound : pairedBoxBound (r i) (u i) (v i) s (height i) (marks i) = 0) :
    endpointIdeal (pairedPowerData r u v β marks) n (height n) = ⊤ := by
  let data := pairedPowerData r u v β marks
  have hprefix : ∀ j < (i : ℕ), HeightStep (data j).mark (height j) (height (j + 1)) := by
    intro j hj
    have hjn : j < n := hj.trans i.isLt
    simpa only [data, pairedPowerData, dif_pos hjn] using hsteps j hjn
  obtain ⟨hA, hdegree, hB⟩ := run_shapes data height hzero i hprefix
  have hstep := hsteps i i.isLt
  apply (Ideal.eq_top_iff_one _).mpr
  apply step_relation_mem_endpointIdeal data i n (height n) i.isLt
  cases hm : marks i with
  | unmarked =>
    have hp : 0 < r i * (s + height i) := Nat.mul_pos (hr i) (by omega)
    simp only [pairedBoxBound, hm] at hbound
    omega
  | theta =>
    simp only [pairedBoxBound, hm] at hbound
    have hv : v i = 0 := by omega
    have hh : height i = 0 := by
      have hmul : r i * height i = 0 := by omega
      exact (Nat.mul_eq_zero.mp hmul).resolve_left (hr i).ne'
    have hAone : (run data i).A = 1 := hA.natDegree_eq_zero.mp (hdegree.trans hh)
    have hd : (data i).mark = .theta := by simpa only [data, pairedPowerData_fin] using hm
    have hb : (data i).rightFactor = 1 := by simp [data, pairedPowerData_fin, hv]
    simp only [relations, hd, hb, hAone, Polynomial.eval_one, mul_one,
      List.mem_cons_self]
  | xi =>
    simp only [pairedBoxBound, hm] at hbound
    have hu : u i = 0 := by omega
    have hh : height i = 0 := by
      have hmul : r i * height i = 0 := by omega
      exact (Nat.mul_eq_zero.mp hmul).resolve_left (hr i).ne'
    have hAone : (run data i).A = 1 := hA.natDegree_eq_zero.mp (hdegree.trans hh)
    have hd : (data i).mark = .xi := by simpa only [data, pairedPowerData_fin] using hm
    have ha : (data i).leftFactor = 1 := by simp [data, pairedPowerData_fin, hu]
    simp only [relations, hd, ha, hAone, Polynomial.eval_one, mul_one,
      List.mem_cons_self]
  | double =>
    have hh : height i = height ((i : ℕ) + 1) + 1 := by
      simpa only [HeightStep, hm] using hstep
    have hp : 0 < r i * height i := Nat.mul_pos (hr i) (by omega)
    simp only [pairedBoxBound, hm] at hbound
    omega

/-- The unrestricted endpoint colength formula, including all zero-bound
boxes. This concerns the actual endpoint ideal for every valid path. -/
theorem pairedPowerEndpoint_finrank
    (r u v : Fin n → ℕ) (β : Fin n → K) (marks : Fin n → Mark)
    (height : ℕ → ℕ) (hzero : height 0 = 0) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hsteps : ∀ j (hj : j < n), HeightStep (marks ⟨j, hj⟩) (height j) (height (j + 1)))
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Module.finrank K (P ⧸ endpointIdeal (pairedPowerData r u v β marks) n (height n)) =
      ∏ i : Fin n, pairedBoxBound (r i) (u i) (v i) s (height i) (marks i) := by
  by_cases hbound : ∀ i : Fin n, 0 < pairedBoxBound (r i) (u i) (v i) s (height i) (marks i)
  · exact pairedPowerEndpoint_finrank_of_positive r u v β marks height hzero s hs hr huv
      hsteps hβ hbound
  · push_neg at hbound
    obtain ⟨i, hi⟩ := hbound
    have hi0 : pairedBoxBound (r i) (u i) (v i) s (height i) (marks i) = 0 := by omega
    have hI := pairedPowerEndpoint_eq_top_of_zero_bound r u v β marks height hzero s hs hr
      hsteps i hi0
    rw [hI, Finset.prod_eq_zero (Finset.mem_univ i) hi0]
    exact Module.finrank_zero_of_subsingleton

end PaperVerification.Fermion.Endpoint
