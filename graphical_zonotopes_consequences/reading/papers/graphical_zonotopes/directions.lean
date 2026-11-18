module

public import Papers.GraphicalZonotopes.Lattice
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_orderPrefix_iff {n : ℕ} (e : Fin n ≃ V) (j : ℕ) (x : V) :
    x∈orderPrefix e j ↔ (e.symm x).val<j := by simp only [orderPrefix,mem_filter,mem_univ,true_and]

theorem card_orderPrefix {n : ℕ} (e : Fin n ≃ V) (j : ℕ) (hj : j ≤ n) :
    (orderPrefix e j).card = j := by
  have hm : orderPrefix e j = (univ.filter (fun i : Fin n => i.val < j)).map e.toEmbedding := by
    ext v
    simp [orderPrefix, Equiv.eq_symm_apply]
  rw [hm, card_map, Fin.card_filter_val_lt, Nat.min_eq_right hj]

theorem pair_enumeration_adjacent {n : ℕ} (e : Fin n ≃ V)
    (S : Finset V) {u v : V} (hu : u ∉ S)
    (h0 : orderPrefix e (e.symm u).val = S)
    (h1 : orderPrefix e (e.symm v).val = insert u S) :
    (e.symm v).val = (e.symm u).val + 1 := by
  have hc0 := congrArg Finset.card h0
  have hc1 := congrArg Finset.card h1
  rw [card_orderPrefix e _ (e.symm u).isLt.le] at hc0
  rw [card_orderPrefix e _ (e.symm v).isLt.le, card_insert_of_notMem hu] at hc1
  omega

/-- Swapping two adjacent coordinates leaves every other prefix unchanged. -/
theorem orderPrefix_swap_of_ne {n : ℕ} (e : Fin n ≃ V) {u v : V} (huv : u ≠ v)
    (hadj : (e.symm v).val = (e.symm u).val + 1) {j : ℕ}
    (hj : j ≠ (e.symm v).val) :
    orderPrefix (e.trans (Equiv.swap u v)) j = orderPrefix e j := by
  ext x
  rw [mem_orderPrefix_iff,mem_orderPrefix_iff]
  change (e.symm (Equiv.swap u v x)).val<j ↔ (e.symm x).val<j
  by_cases hxu : x = u
  · subst x
    simp only [Equiv.swap_apply_left]
    omega
  · by_cases hxv : x = v
    · subst x
      simp only [Equiv.swap_apply_right]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]

theorem orderPrefix_swap_middle {n : ℕ} (e : Fin n ≃ V) (S : Finset V)
    {u v : V} (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S)
    (h0 : orderPrefix e (e.symm u).val = S)
    (h1 : orderPrefix e (e.symm v).val = insert u S) :
    orderPrefix (e.trans (Equiv.swap u v)) (e.symm v).val = insert v S := by
  have hadj := pair_enumeration_adjacent e S hu h0 h1
  ext x
  rw [mem_orderPrefix_iff,mem_insert]
  change (e.symm (Equiv.swap u v x)).val<(e.symm v).val ↔ x=v ∨ x∈S
  by_cases hxu : x = u
  · subst x
    simp [huv, hu]
  · by_cases hxv : x = v
    · subst x
      simp [hadj]
    · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
      have hx0 : x ∈ S ↔ (e.symm x).val < (e.symm u).val := by
        rw [← h0]
        simp [orderPrefix]
      have hne : (e.symm x).val ≠ (e.symm u).val := by
        intro h
        exact hxu (e.symm.injective (Fin.ext h))
      simp only [hxv, false_or, hx0]
      omega

/-- The actual difference of the two neighboring greedy points is the elemental
slack times the corresponding standard root. -/
theorem greedyPoint_swap_difference {n : ℕ} (z : SetFunction V)
    (e : Fin n ≃ V) (S : Finset V) {u v : V} (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S)
    (h0 : orderPrefix e (e.symm u).val = S)
    (h1 : orderPrefix e (e.symm v).val = insert u S) :
    greedyPoint z (e.trans (Equiv.swap u v)) - greedyPoint z e =
      delta z u v S • (basisVector u - basisVector v) := by
  let e' := e.trans (Equiv.swap u v)
  have hadj := pair_enumeration_adjacent e S hu h0 h1
  have h2 : orderPrefix e ((e.symm v).val + 1) = insert v (insert u S) := by
    rw [orderPrefix_succ, e.apply_symm_apply, h1]
  have hu0 : orderPrefix e' (e.symm u).val = S := by
    rw [orderPrefix_swap_of_ne e huv hadj (by omega), h0]
  have hv0 : orderPrefix e' (e.symm v).val = insert v S :=
    orderPrefix_swap_middle e S huv hu hv h0 h1
  have hv1 : orderPrefix e' ((e.symm v).val + 1) = insert v (insert u S) := by
    rw [orderPrefix_swap_of_ne e huv hadj (by omega), h2]
  have hu1 : orderPrefix e ((e.symm u).val + 1) = insert u S := by rw [← hadj, h1]
  have hu' : e'.symm u = e.symm v := by simp [e']
  have hv' : e'.symm v = e.symm u := by simp [e']
  change greedyPoint z e'-greedyPoint z e=delta z u v S • (basisVector u-basisVector v)
  funext x
  by_cases hxu : x = u
  · subst x
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,greedyPoint,hu',hv1,hv0,hu1,h0]
    simp [basisVector,Pi.single_apply,huv,Ne.symm huv,delta,insert_comm u v]
    <;> ring
  · by_cases hxv : x = v
    · subst x
      simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,greedyPoint,hv',h2,h1,h0,
        ← hadj,hv0,hu0]
      simp [basisVector,Pi.single_apply,huv,Ne.symm huv,delta,insert_comm u v]
      <;> ring
    · have hx' : e'.symm x = e.symm x := by simp [e', Equiv.swap_apply_of_ne_of_ne hxu hxv]
      have hru : (e.symm x).val ≠ (e.symm u).val := by
        intro h
        exact hxu (e.symm.injective (Fin.ext h))
      have hrv : (e.symm x).val ≠ (e.symm v).val := by
        intro h
        exact hxv (e.symm.injective (Fin.ext h))
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, greedyPoint, hx']
      rw [orderPrefix_swap_of_ne e huv hadj (by omega), orderPrefix_swap_of_ne e huv hadj hrv]
      simp [basisVector, Pi.single_apply, hxu, hxv, Ne.symm hxu, Ne.symm hxv]

/-- Every nonzero elemental difference places the genuine root direction in the
affine variation space of the genuine base polytope. -/
theorem root_mem_vectorSpan_of_delta_ne_zero {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) (hδ : delta z u v S ≠ 0) :
    basisVector u - basisVector v ∈ vectorSpan ℝ (basePolytope z) := by
  obtain ⟨e, h0, h1⟩ := exists_pair_enumeration S huv hu hv
  have hmem := vsub_mem_vectorSpan ℝ
    (greedyPoint_mem_basePolytope hn hs (e.trans (Equiv.swap u v)))
    (greedyPoint_mem_basePolytope hn hs e)
  change greedyPoint z (e.trans (Equiv.swap u v)) - greedyPoint z e ∈ _ at hmem
  rw [greedyPoint_swap_difference z e S huv hu hv h0 h1] at hmem
  have h := (vectorSpan ℝ (basePolytope z)).smul_mem (delta z u v S)⁻¹ hmem
  simpa [smul_smul, inv_mul_cancel₀ hδ] using h

end GraphicalZonotopes
