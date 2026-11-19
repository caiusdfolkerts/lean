module

public import Unimodular
public import Mathlib.Data.Fintype.Pi

@[expose] public section

set_option autoImplicit false
open scoped BigOperators

namespace Unimodular.EffectiveBinaryMoves

variable {I M : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup M] [DecidableEq M]

/-- Explicit finite cube; this is executable data, not a choice from a
nonconstructive proof of finiteness. -/
def binaryCube : Finset (I → ℤ) := Fintype.piFinset (fun _ => {0, 1})

def moveCube : Finset (I → ℤ) := Fintype.piFinset (fun _ => {-1, 0, 1})

@[simp] theorem mem_binaryCube (c : I → ℤ) :
    c ∈ binaryCube ↔ ∀ i, 0 ≤ c i ∧ c i ≤ 1 := by
  simp only [binaryCube, Fintype.mem_piFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor <;> intro h i <;> have hi := h i <;> omega

@[simp] theorem mem_moveCube (g : I → ℤ) :
    g ∈ moveCube ↔ ∀ i, -1 ≤ g i ∧ g i ≤ 1 := by
  simp only [moveCube, Fintype.mem_piFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor <;> intro h i <;> have hi := h i <;> omega

instance decidableConformalLE (g h : I → ℤ) : Decidable (Graver.ConformalLE g h) :=
  inferInstanceAs (Decidable (∀ i, (g i).toNat ≤ (h i).toNat ∧
    (-g i).toNat ≤ (-h i).toNat))

/-- Primitivehood tested over a finite, explicitly enumerated set. For a
candidate in `moveCube`, every conformal subvector belongs to this same cube. -/
def primitiveTest (A : (I → ℤ) →+ M) (g : I → ℤ) : Prop :=
  A g = 0 ∧ g ≠ 0 ∧
    ∀ h ∈ moveCube, A h = 0 → h ≠ 0 → Graver.ConformalLE h g → h = g

instance decidablePrimitiveTest (A : (I → ℤ) →+ M) (g : I → ℤ) :
    Decidable (primitiveTest A g) := by
  unfold primitiveTest
  infer_instance

/-- All and only genuine Graver-primitive vectors in the derived move cube.
The bound is uniform for arbitrary binary fibers of arbitrary integer maps. -/
def moves (A : (I → ℤ) →+ M) : Finset (I → ℤ) :=
  moveCube.filter (primitiveTest A)

/-- The complete binary fiber of the input equation system, enumerated by an
explicit finite product and a decidable exact equality test. -/
def solutions (A : (I → ℤ) →+ M) (b : M) : Finset (I → ℤ) :=
  binaryCube.filter (fun c => A c = b)

@[simp] theorem mem_solutions (A : (I → ℤ) →+ M) (b : M) (c : I → ℤ) :
    c ∈ solutions A b ↔ (∀ i, 0 ≤ c i ∧ c i ≤ 1) ∧ A c = b := by
  simp [solutions]

theorem conformal_mem_moveCube {h g : I → ℤ} (hg : g ∈ moveCube)
    (hhg : Graver.ConformalLE h g) : h ∈ moveCube := by
  rw [mem_moveCube] at hg ⊢
  intro i
  have hgi := hg i
  have hhi := (Graver.conformalLE_iff h g).1 hhg i
  omega

theorem primitiveTest_iff (A : (I → ℤ) →+ M) {g : I → ℤ}
    (hg : g ∈ moveCube) : primitiveTest A g ↔ Graver.Primitive A.ker g := by
  constructor
  · rintro ⟨hA, hn, hmin⟩
    refine ⟨hA, hn, ?_⟩
    intro h hh hn' hhg
    exact hmin h (conformal_mem_moveCube hg hhg) hh hn' hhg
  · rintro ⟨hA, hn, hmin⟩
    exact ⟨hA, hn, fun h _ hh hn' hhg => hmin h hh hn' hhg⟩

@[simp] theorem mem_moves (A : (I → ℤ) →+ M) (g : I → ℤ) :
    g ∈ moves A ↔ g ∈ moveCube ∧ Graver.Primitive A.ker g := by
  rw [moves, Finset.mem_filter]
  constructor
  · rintro ⟨hg, ht⟩
    exact ⟨hg, (primitiveTest_iff A hg).1 ht⟩
  · rintro ⟨hg, hp⟩
    exact ⟨hg, (primitiveTest_iff A hg).2 hp⟩

theorem between_mem_binaryCube {c d x : I → ℤ}
    (hc : c ∈ binaryCube) (hd : d ∈ binaryCube) (hx : Graver.Between c d x) :
    x ∈ binaryCube := by
  rw [mem_binaryCube] at hc hd ⊢
  intro i
  have hci := hc i
  have hdi := hd i
  have hxi := hx i
  constructor
  · exact (le_min hci.1 hdi.1).trans hxi.1
  · exact hxi.2.trans (max_le hci.2 hdi.2)

theorem sub_mem_moveCube {x y : I → ℤ}
    (hx : x ∈ binaryCube) (hy : y ∈ binaryCube) : y - x ∈ moveCube := by
  rw [mem_binaryCube] at hx hy
  rw [mem_moveCube]
  intro i
  have hxi := hx i
  have hyi := hy i
  simp only [Pi.sub_apply]
  omega

/-- Every pair in every binary fiber is connected by the computed genuine
primitive moves, and every intermediate coordinate stays between its endpoint
values. No dimension, matrix size, coefficient bound, or number of solutions
is fixed or restricted. -/
theorem connectivity (A : (I → ℤ) →+ M) (b : M) (c d : I → ℤ)
    (hc : c ∈ solutions A b) (hd : d ∈ solutions A b) :
    Relation.ReflTransGen
      (fun x y : I → ℤ => y - x ∈ moves A ∧
        x ∈ solutions A b ∧ y ∈ solutions A b ∧
        Graver.Between c d x ∧ Graver.Between c d y) c d := by
  have hc' := (mem_solutions A b c).1 hc
  have hd' := (mem_solutions A b d).1 hd
  have hcB : c ∈ binaryCube := (mem_binaryCube c).2 hc'.1
  have hdB : d ∈ binaryCube := (mem_binaryCube d).2 hd'.1
  obtain ⟨G, hG, hpath⟩ := Graver.finite_nonnegative_fiber_connectivity A c d
    (hc'.2.trans hd'.2.symm) (fun i => (hc'.1 i).1) (fun i => (hd'.1 i).1)
  apply Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ hpath
  obtain ⟨hm, hxA, hyA, hx, hy, _, _⟩ := hxy
  have hxB := between_mem_binaryCube hcB hdB hx
  have hyB := between_mem_binaryCube hcB hdB hy
  exact ⟨(mem_moves A _).2 ⟨sub_mem_moveCube hxB hyB, (hG _).1 hm⟩,
    (mem_solutions A b x).2 ⟨(mem_binaryCube x).1 hxB, hxA.trans hc'.2⟩,
    (mem_solutions A b y).2 ⟨(mem_binaryCube y).1 hyB, hyA.trans hc'.2⟩, hx, hy⟩

/-- An admissible primitive move between binary solutions necessarily occurs
in the computed set; no usable primitive replacement is omitted. -/
theorem usable_primitive_mem (A : (I → ℤ) →+ M) (b : M) (c g : I → ℤ)
    (hc : c ∈ solutions A b) (hcg : c + g ∈ solutions A b)
    (hg : Graver.Primitive A.ker g) : g ∈ moves A := by
  have hcB : c ∈ binaryCube := (mem_binaryCube c).2 ((mem_solutions A b c).1 hc).1
  have hcgB : c + g ∈ binaryCube :=
    (mem_binaryCube _).2 ((mem_solutions A b _).1 hcg).1
  apply (mem_moves A g).2
  refine ⟨?_, hg⟩
  have he : (c + g) - c = g := by abel
  exact he ▸ sub_mem_moveCube hcB hcgB

end Unimodular.EffectiveBinaryMoves

#print axioms Unimodular.EffectiveBinaryMoves.moves
#print axioms Unimodular.EffectiveBinaryMoves.solutions
#print axioms Unimodular.EffectiveBinaryMoves.primitiveTest_iff
#print axioms Unimodular.EffectiveBinaryMoves.connectivity
#print axioms Unimodular.EffectiveBinaryMoves.usable_primitive_mem
#check Unimodular.EffectiveBinaryMoves.connectivity
