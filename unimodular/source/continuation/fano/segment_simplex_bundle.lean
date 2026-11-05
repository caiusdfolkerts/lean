module

public import Unimodular.Extensions
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The integral segment–simplex family

The fibre has dimension `d` and the ambient lattice has dimension `d + 1`.
The last coordinate is the literal height coordinate in the displayed
inequalities.  The parameter `a` is integral throughout.  `none` indexes
the fibre corner with every x-coordinate equal to one; `some i` indexes
the other corner in direction i.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace Unimodular.SegmentSimplexBundle

open scoped BigOperators

abbrev VertexIndex (d : ℕ) := Bool × Option (Fin d)

def height (b : Bool) : ℤ := if b then 1 else -1

def width (d : ℕ) (a : ℤ) (b : Bool) : ℤ :=
  (d : ℤ) + 1 - a * height b

def simplexNormal (d : ℕ) (a : ℤ) : Option (Fin d) → Lattice (d + 1)
  | none => Fin.lastCases a (fun _ => -1)
  | some i => Fin.lastCases 0 (fun j => if j = i then 1 else 0)

def capNormal (d : ℕ) (b : Bool) : Lattice (d + 1) :=
  Fin.lastCases (height b) (fun _ => 0)

def normals (d : ℕ) (a : ℤ) : Finset (Lattice (d + 1)) :=
  (Finset.univ.image (simplexNormal d a)) ∪
    (Finset.univ.image (capNormal d))

def vertex (d : ℕ) (a : ℤ) (t : VertexIndex d) : Lattice (d + 1) :=
  Fin.lastCases (height t.1)
    (fun i => 1 - if t.2 = some i then width d a t.1 else 0)

def vertices (d : ℕ) (a : ℤ) : Finset (Lattice (d + 1)) :=
  Finset.univ.image (vertex d a)

/-- The actual real polytope in the original coordinates. -/
def Q (d : ℕ) (a : ℤ) : Set (Ambient (d + 1)) :=
  {x | -1 ≤ x (Fin.last d) ∧ x (Fin.last d) ≤ 1 ∧
    (∀ i : Fin d, x i.castSucc ≤ 1) ∧
    -(∑ i : Fin d, x i.castSucc) + (a : ℝ) * x (Fin.last d) ≤ 1}

@[simp] theorem height_false : height false = -1 := rfl
@[simp] theorem height_true : height true = 1 := rfl

theorem height_sq (b : Bool) : height b * height b = 1 := by
  cases b <;> norm_num [height]

theorem width_pos {d : ℕ} {a : ℤ} (ha : 0 ≤ a) (had : a ≤ d) (b : Bool) :
    0 < width d a b := by
  cases b <;> simp [width, height] <;> omega

theorem width_ge_two {d : ℕ} {a : ℤ} (ha : 0 ≤ a) (had : a < d) (b : Bool) :
    2 ≤ width d a b := by
  cases b <;> simp [width, height] <;> omega

@[simp] theorem simplexNormal_none_last (d : ℕ) (a : ℤ) :
    simplexNormal d a none (Fin.last d) = a := by
  simp [simplexNormal]

@[simp] theorem simplexNormal_none_castSucc (d : ℕ) (a : ℤ) (i : Fin d) :
    simplexNormal d a none i.castSucc = -1 := by
  simp [simplexNormal]

@[simp] theorem simplexNormal_some_last (d : ℕ) (a : ℤ) (i : Fin d) :
    simplexNormal d a (some i) (Fin.last d) = 0 := by
  simp [simplexNormal]

@[simp] theorem simplexNormal_some_castSucc (d : ℕ) (a : ℤ) (i j : Fin d) :
    simplexNormal d a (some i) j.castSucc = if j = i then 1 else 0 := by
  simp [simplexNormal]

@[simp] theorem capNormal_last (d : ℕ) (b : Bool) :
    capNormal d b (Fin.last d) = height b := by
  simp [capNormal]

@[simp] theorem capNormal_castSucc (d : ℕ) (b : Bool) (i : Fin d) :
    capNormal d b i.castSucc = 0 := by
  simp [capNormal]

@[simp] theorem vertex_last (d : ℕ) (a : ℤ) (t : VertexIndex d) :
    vertex d a t (Fin.last d) = height t.1 := by
  simp [vertex]

@[simp] theorem vertex_castSucc (d : ℕ) (a : ℤ) (t : VertexIndex d) (i : Fin d) :
    vertex d a t i.castSucc = 1 - if t.2 = some i then width d a t.1 else 0 := by
  simp [vertex]

theorem vertex_fibre_sum (d : ℕ) (a : ℤ) (t : VertexIndex d) :
    ∑ i : Fin d, vertex d a t i.castSucc =
      (d : ℤ) - if t.2 = none then 0 else width d a t.1 := by
  rcases t with ⟨b, k⟩
  cases k <;>
    simp [vertex, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem pairing_simplex_none (d : ℕ) (a : ℤ) (x : Ambient (d + 1)) :
    pairing x (simplexNormal d a none) =
      -(∑ i : Fin d, x i.castSucc) + (a : ℝ) * x (Fin.last d) := by
  simp [pairing, Fin.sum_univ_castSucc, mul_comm]

theorem pairing_simplex_some (d : ℕ) (a : ℤ) (x : Ambient (d + 1)) (i : Fin d) :
    pairing x (simplexNormal d a (some i)) = x i.castSucc := by
  simp [pairing, Fin.sum_univ_castSucc, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem pairing_cap (d : ℕ) (x : Ambient (d + 1)) (b : Bool) :
    pairing x (capNormal d b) = (height b : ℝ) * x (Fin.last d) := by
  simp [pairing, Fin.sum_univ_castSucc, mul_comm]

theorem simplexNormal_mem (d : ℕ) (a : ℤ) (i : Option (Fin d)) :
    simplexNormal d a i ∈ normals d a := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem capNormal_mem (d : ℕ) (a : ℤ) (b : Bool) :
    capNormal d b ∈ normals d a := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩

theorem mem_Q_iff (d : ℕ) (a : ℤ) (x : Ambient (d + 1)) :
    x ∈ Q d a ↔ ∀ u ∈ normals d a, pairing x u ≤ 1 := by
  constructor
  · rintro ⟨hl, hu, hx, hs⟩ u hmem
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
      cases i with
      | none => simpa only [pairing_simplex_none] using hs
      | some i => simpa only [pairing_simplex_some] using hx i
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hmem
      rw [pairing_cap]
      cases b <;> simp only [height_false, height_true, Int.cast_neg,
        Int.cast_one, neg_one_mul, one_mul] <;> linarith
  · intro h
    have hl := h (capNormal d false) (capNormal_mem d a false)
    have hu := h (capNormal d true) (capNormal_mem d a true)
    have hs := h (simplexNormal d a none) (simplexNormal_mem d a none)
    simp only [pairing_cap, height_false, height_true, Int.cast_neg,
      Int.cast_one, neg_one_mul, one_mul] at hl hu
    refine ⟨by linarith, hu, ?_, ?_⟩
    · intro i
      simpa only [pairing_simplex_some] using
        h (simplexNormal d a (some i)) (simplexNormal_mem d a (some i))
    · simpa only [pairing_simplex_none] using hs

theorem vertex_mem_Q {d : ℕ} {a : ℤ} (ha : 0 ≤ a) (had : a ≤ d)
    (t : VertexIndex d) : embed (vertex d a t) ∈ Q d a := by
  have hw : (0 : ℝ) < width d a t.1 := by exact_mod_cast width_pos ha had t.1
  have hs : (∑ i : Fin d, embed (vertex d a t) i.castSucc) =
      (d : ℝ) - if t.2 = none then 0 else (width d a t.1 : ℝ) := by
    simp only [embed]
    exact_mod_cast vertex_fibre_sum d a t
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases t with ⟨b, k⟩
    cases b <;> norm_num [embed, vertex, height]
  · rcases t with ⟨b, k⟩
    cases b <;> norm_num [embed, vertex, height]
  · intro i
    simp only [embed, vertex_castSucc]
    split_ifs <;> push_cast <;> linarith
  · rw [hs]
    simp only [embed, vertex_last]
    rcases t with ⟨b, k⟩
    cases k <;> simp only [Option.some_ne_none, ite_false, ite_true,
      sub_zero, width] at *
    all_goals push_cast at *
    all_goals linarith

theorem Q_convex (d : ℕ) (a : ℤ) : Convex ℝ (Q d a) := by
  intro x hx y hy s t hs ht hst
  apply (mem_Q_iff d a _).mpr
  intro u hu
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left]
  calc
    _ ≤ s * 1 + t * 1 := add_le_add
      (mul_le_mul_of_nonneg_left ((mem_Q_iff d a x).mp hx u hu) hs)
      (mul_le_mul_of_nonneg_left ((mem_Q_iff d a y).mp hy u hu) ht)
    _ = 1 := by simpa using hst

end Unimodular.SegmentSimplexBundle

#print axioms Unimodular.SegmentSimplexBundle.mem_Q_iff
#print axioms Unimodular.SegmentSimplexBundle.vertex_mem_Q
#print axioms Unimodular.SegmentSimplexBundle.Q_convex
