/- The actual binary-cycle rule for gluing along a spanning port.
Coefficients are elements of ZMod 2, hence exactly characteristic functions
of subsets. Both side cycles use the same port coefficients. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsQuotient
public import Mathlib.Data.ZMod.Basic
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace Unimodular.SignedSums.Binary

abbrev F := ZMod 2

def Cycle {E M : Type*} [Fintype E] [AddCommGroup M] [Module F M]
    (U : E → M) (x : E → F) : Prop := ∑ e, x e • U e = 0

variable {P A B T L R : Type*} [AddCommGroup P] [Module F P]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
  [Fintype T] [Fintype L] [Fintype R]

def sideFamily (C : T → P) (U : L → P × A) : T ⊕ L → P × A :=
  Sum.elim (fun t => (C t, 0)) U

theorem side_cycle_iff (C : T → P) (U : L → P × A) (z : T → F) (x : L → F) :
    Cycle (sideFamily C U) (Sum.elim z x) ↔
      (∑ t, z t • C t) + (∑ l, x l • (U l).1) = 0 ∧
      (∑ l, x l • (U l).2) = 0 := by
  simp [Cycle, sideFamily, Fintype.sum_sum_type, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]

theorem joined_cycle_iff (U : L → P × A) (V : R → P × B) (x : L → F) (y : R → F) :
    Cycle (joinedFamily (R := F) U V) (Sum.elim x y) ↔
      (∑ l, x l • (U l).1) + (∑ r, y r • (V r).1) = 0 ∧
      (∑ l, x l • (U l).2) = 0 ∧ (∑ r, y r • (V r).2) = 0 := by
  simp [Cycle, joinedFamily, sumLeft, sumRight, Fintype.sum_sum_type,
    Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]

/-- This is the binary 2- and 3-sum cycle condition: matched port subsets are
cancelled, leaving exactly the disjoint surviving subsets on both sides. -/
theorem joined_cycle_iff_matched (C : T → P)
    (hC : Submodule.span F (Set.range C) = ⊤)
    (U : L → P × A) (V : R → P × B) (x : L → F) (y : R → F) :
    Cycle (joinedFamily (R := F) U V) (Sum.elim x y) ↔
      ∃ z : T → F, Cycle (sideFamily C U) (Sum.elim z x) ∧
        Cycle (sideFamily C V) (Sum.elim z y) := by
  rw [joined_cycle_iff]
  simp_rw [side_cycle_iff]
  constructor
  · rintro ⟨hpq, ha, hb⟩
    have hm : (∑ l, x l • (U l).1) ∈ Submodule.span F (Set.range C) := by
      rw [hC]
      trivial
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hm
    refine ⟨z, ⟨?_, ha⟩, ?_, hb⟩
    · rw [hz]
      exact ZModModule.add_self _
    · rw [hz]
      exact hpq
  · rintro ⟨z, ⟨hp, ha⟩, hq, hb⟩
    refine ⟨?_, ha, hb⟩
    have hp' : (∑ l, x l • (U l).1) = (∑ t, z t • C t) := by
      have h := eq_neg_of_add_eq_zero_right hp
      simpa only [ZModModule.neg_eq_self] using h
    have hq' : (∑ r, y r • (V r).1) = (∑ t, z t • C t) := by
      have h := eq_neg_of_add_eq_zero_right hq
      simpa only [ZModModule.neg_eq_self] using h
    rw [hp', hq']
    exact ZModModule.add_self _

/-- Empty, single, and triangle port spans are all the actual port spaces. -/
theorem empty_ports_span :
    Submodule.span F (Set.range (fun i : Fin 0 => (Fin.elim0 i : Fin 0 → F))) = ⊤ := by
  ext p
  have hp : p = 0 := by ext i; exact Fin.elim0 i
  simp [hp]

def singlePort : Fin 1 → (Fin 1 → F) := fun _ => ![1]

theorem single_ports_span : Submodule.span F (Set.range singlePort) = ⊤ := by
  apply top_unique
  intro p _
  apply (Submodule.mem_span_range_iff_exists_fun F).mpr
  refine ⟨fun _ => p 0, ?_⟩
  ext i
  fin_cases i
  simp [singlePort]

def trianglePort : Fin 3 → (Fin 2 → F) := ![![1, 0], ![0, 1], ![1, 1]]

theorem triangle_ports_span : Submodule.span F (Set.range trianglePort) = ⊤ := by
  apply top_unique
  intro p _
  apply (Submodule.mem_span_range_iff_exists_fun F).mpr
  refine ⟨![p 0, p 1, 0], ?_⟩
  ext i
  fin_cases i <;> simp [trianglePort, Fin.sum_univ_succ]

/-- The full binary three-sum rule, with arbitrary surviving label sets. -/
theorem triangle_sum_cycles (U : L → (Fin 2 → F) × A) (V : R → (Fin 2 → F) × B)
    (x : L → F) (y : R → F) :
    Cycle (joinedFamily (R := F) U V) (Sum.elim x y) ↔
      ∃ z : Fin 3 → F, Cycle (sideFamily trianglePort U) (Sum.elim z x) ∧
        Cycle (sideFamily trianglePort V) (Sum.elim z y) :=
  joined_cycle_iff_matched trianglePort triangle_ports_span U V x y

/-- The full binary two-sum rule, with arbitrary surviving label sets. -/
theorem single_sum_cycles (U : L → (Fin 1 → F) × A) (V : R → (Fin 1 → F) × B)
    (x : L → F) (y : R → F) :
    Cycle (joinedFamily (R := F) U V) (Sum.elim x y) ↔
      ∃ z : Fin 1 → F, Cycle (sideFamily singlePort U) (Sum.elim z x) ∧
        Cycle (sideFamily singlePort V) (Sum.elim z y) :=
  joined_cycle_iff_matched singlePort single_ports_span U V x y

end Unimodular.SignedSums.Binary
#print axioms Unimodular.SignedSums.Binary.joined_cycle_iff_matched
#print axioms Unimodular.SignedSums.Binary.triangle_sum_cycles
#print axioms Unimodular.SignedSums.Binary.single_sum_cycles
