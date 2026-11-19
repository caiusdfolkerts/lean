module

public import cubical.simplicial_chains

/-! # Vertex contraction and its chain homotopy over `𝔽₂` -/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
@[simp]
theorem chain_neg (c : Chain V) : -c = c := by
  exact neg_eq_iff_add_eq_zero.mpr (chain_add_self c)

/-- Keep the simplices containing a specified vertex. -/
noncomputable def star (v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  Finsupp.linearCombination (ZMod 2)
    (fun s : Finset V => if v ∈ s then Finsupp.single s 1 else 0)

/-- Erase a specified vertex, and send simplices not containing it to zero. -/
noncomputable def eraseVertex (v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  Finsupp.linearCombination (ZMod 2)
    (fun s : Finset V => if v ∈ s then Finsupp.single (s.erase v) 1 else 0)

@[simp]
theorem star_single (v : V) (s : Finset V) (a : ZMod 2) :
    star v (Finsupp.single s a) = if v ∈ s then Finsupp.single s a else 0 := by
  by_cases hv : v ∈ s <;> simp [star, hv, Finsupp.smul_single]

@[simp]
theorem eraseVertex_single (v : V) (s : Finset V) (a : ZMod 2) :
    eraseVertex v (Finsupp.single s a) =
      if v ∈ s then Finsupp.single (s.erase v) a else 0 := by
  by_cases hv : v ∈ s <;> simp [eraseVertex, hv, Finsupp.smul_single]

theorem boundary_star_add_star_boundary_single (v : V) (s : Finset V) (a : ZMod 2) :
    boundary (star v (Finsupp.single s a)) + star v (boundary (Finsupp.single s a)) =
      eraseVertex v (Finsupp.single s a) := by
  by_cases hv : v ∈ s
  · have hs : star v (boundary (Finsupp.single s a)) =
        ∑ w ∈ s.erase v, Finsupp.single (s.erase w) a := by
      rw [boundary_single, map_sum, ← Finset.add_sum_erase s _ hv]
      have hz : star v (Finsupp.single (s.erase v) a) = 0 := by simp
      rw [hz, zero_add]
      apply Finset.sum_congr rfl
      intro w hw
      have hwv := (Finset.mem_erase.mp hw).1
      simp [star_single, Finset.mem_erase, hv, hwv.symm]
    rw [star_single, ite_eq_left hv, hs, eraseVertex_single, ite_eq_left hv, boundary_single,
      ← Finset.add_sum_erase s _ hv, add_assoc, chain_add_self, add_zero]
  · simp only [star_single, hv, ↓reduceIte, map_zero, zero_add, boundary_single,
      map_sum, eraseVertex_single]
    apply Finset.sum_eq_zero
    intro w hw
    simp [Finset.mem_erase, hv]

theorem boundary_star_add_star_boundary (v : V) (c : Chain V) :
    boundary (star v c) + star v (boundary c) = eraseVertex v c := by
  have h : (boundary (V := V)).comp (star v) + (star v).comp boundary = eraseVertex v := by
    apply Finsupp.lhom_ext
    intro s a
    exact boundary_star_add_star_boundary_single v s a
  exact LinearMap.congr_fun h c

/-- The vertex contraction sending `v` to `u`, with collapsed simplices set to zero. -/
noncomputable def contract (u v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  LinearMap.id + star v + (cone u).comp (eraseVertex v)

@[simp]
theorem contract_single (u v : V) (s : Finset V) (a : ZMod 2) :
    contract u v (Finsupp.single s a) =
      if v ∈ s then cone u (Finsupp.single (s.erase v) a) else Finsupp.single s a := by
  by_cases hv : v ∈ s <;> simp [contract, hv, chain_add_self]

theorem contract_single_of_ne {u v : V} (huv : u ≠ v) (s : Finset V) (a : ZMod 2) :
    contract u v (Finsupp.single s a) =
      if u ∈ s ∧ v ∈ s then 0
      else if v ∈ s then Finsupp.single (insert u (s.erase v)) a else Finsupp.single s a := by
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;>
    simp [contract_single, cone_single, Finset.mem_erase, hu, hv, huv]

/-- A concrete chain homotopy from vertex contraction to the identity. -/
theorem contract_homotopy (u v : V) (c : Chain V) :
    contract u v c = c + boundary (cone u (star v c)) + cone u (star v (boundary c)) := by
  have hc := boundary_cone_add_cone_boundary u (star v c)
  have hc' := eq_sub_of_add_eq hc
  rw [sub_eq_add_neg, chain_neg] at hc'
  simp only [contract, LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply]
  rw [hc']
  simp only [add_assoc]
  rw [← map_add, boundary_star_add_star_boundary]

/-- Vertex contraction commutes with the augmented simplicial boundary. -/
theorem boundary_contract (u v : V) (c : Chain V) :
    boundary (contract u v c) = contract u v (boundary c) := by
  rw [contract_homotopy, map_add, map_add, boundary_boundary, add_zero,
    contract_homotopy, boundary_boundary, map_zero, map_zero, add_zero]

/-- Contraction therefore sends simplicial cycles to simplicial cycles. -/
theorem contract_cycle (u v : V) {c : Chain V} (hc : boundary c = 0) :
    boundary (contract u v c) = 0 := by
  rw [boundary_contract, hc, map_zero]

@[simp]
theorem star_apply (v : V) (c : Chain V) (s : Finset V) :
    star v c s = if v ∈ s then c s else 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      by_cases hv : v ∈ s <;> simp [hc, hd, hv]
  | single t a =>
      by_cases hts : t = s
      · subst t
        by_cases hv : v ∈ s <;> simp [hv]
      · by_cases ht : v ∈ t <;> by_cases hs : v ∈ s <;>
          simp [star_single, ht, hs, hts]

@[simp]
theorem cone_apply (v : V) (c : Chain V) (s : Finset V) :
    cone v c s = if v ∈ s then c (s.erase v) else 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      by_cases hv : v ∈ s <;> simp [hc, hd, hv]
  | single t a =>
      by_cases hs : v ∈ s
      · by_cases ht : v ∈ t
        · have hne : t ≠ s.erase v := by
            intro h; rw [h] at ht; exact Finset.notMem_erase v s ht
          simp [cone_single, hs, ht, hne]
        · have heq : insert v t = s ↔ t = s.erase v := by
            constructor
            · intro h
              rw [← h, Finset.erase_insert ht]
            · intro h
              rw [h, Finset.insert_erase hs]
          simp [cone_single, hs, ht, Finsupp.single_apply, heq]
      · have hne : insert v t ≠ s := by
          intro h; apply hs; rw [← h]; exact Finset.mem_insert_self _ _
        by_cases ht : v ∈ t <;> simp [cone_single, hs, ht, hne]

/-- The completion used in a Fogelsanger decomposition. -/
noncomputable def complete (u v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  LinearMap.id + ((cone u).comp (star v)).comp boundary

theorem complete_apply (u v : V) (c : Chain V) :
    complete u v c = c + cone u (star v (boundary c)) := rfl

theorem complete_coefficient {u v : V} (huv : u ≠ v) (c : Chain V) (s : Finset V) :
    complete u v c s = c s + if u ∈ s ∧ v ∈ s then boundary c (s.erase u) else 0 := by
  rw [complete_apply, Finsupp.add_apply, cone_apply, star_apply]
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;>
    simp [hu, hv, Finset.mem_erase, huv.symm]

theorem complete_eq_of_not_edge {u v : V} (huv : u ≠ v) (c : Chain V) (s : Finset V)
    (hs : ¬(u ∈ s ∧ v ∈ s)) : complete u v c s = c s := by
  simp [complete_coefficient huv, hs]

theorem boundary_complete (u v : V) (c : Chain V) :
    boundary (complete u v c) = boundary (contract u v c) := by
  rw [complete_apply, map_add, contract_homotopy, map_add, map_add,
    boundary_boundary, add_zero]

/-- A cycle after contraction has a canonically completed cycle before contraction. -/
theorem complete_cycle (u v : V) {c : Chain V}
    (hc : boundary (contract u v c) = 0) : boundary (complete u v c) = 0 := by
  rw [boundary_complete, hc]

theorem complete_of_cycle (u v : V) {c : Chain V} (hc : boundary c = 0) :
    complete u v c = c := by
  simp [complete_apply, hc]

theorem contract_homotopy_term {u v : V} (huv : u ≠ v) (c : Chain V) :
    contract u v (cone u (star v c)) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd]
  | single s a =>
      by_cases hv : v ∈ s <;> by_cases hu : u ∈ s <;>
        simp [star_single, cone_single, contract_single_of_ne huv, hv, hu, huv.symm]

theorem contract_complete {u v : V} (huv : u ≠ v) (c : Chain V) :
    contract u v (complete u v c) = contract u v c := by
  rw [complete_apply, map_add, contract_homotopy_term huv, add_zero]

theorem complete_single_of_edge {u v : V} (huv : u ≠ v) (s : Finset V)
    (hu : u ∈ s) (hv : v ∈ s) (a : ZMod 2) :
    complete u v (Finsupp.single s a) = 0 := by
  rw [complete_apply, boundary_single, map_sum, map_sum, Finset.sum_eq_single u]
  · simp [star_single, cone_single, Finset.mem_erase, huv.symm, hu, hv,
      Finset.insert_erase hu, chain_add_self]
  · intro w hw hwu
    by_cases hvw : v ∈ s.erase w
    · simp [star_single, cone_single, Finset.mem_erase, hu, hvw, hwu.symm]
    · simp [star_single, hvw]
  · exact fun h => (h hu).elim

end Cubical.Simplicial
