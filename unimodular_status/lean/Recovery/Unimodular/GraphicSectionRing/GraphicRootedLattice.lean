module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Integral coordinates on the incidence lattice of an arbitrary finite graph

Deleting one chosen vertex in each connected component gives an integral basis.
The missing coordinate is recovered from the component's zero-sum equation.
Disconnected graphs, isolated vertices and empty vertex sets are retained.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace Unimodular.GraphicRootedLattice
attribute [local instance] Classical.propDecidable Classical.decEq

section Components
variable {V C : Type*} [Fintype V] (c : V → C) (r : C → V)
    (hr : Function.RightInverse r c)

/-- Literal sum of the vertex coordinates in each component. -/
def componentSum : (V → ℤ) →ₗ[ℤ] (C → ℤ) where
  toFun x a := ∑ v ∈ Finset.univ.filter (fun v => c v = a), x v
  map_add' x y := by ext a; simp [Finset.sum_add_distrib]
  map_smul' a x := by ext b; simp [Finset.mul_sum]

/-- The actual component-balanced integral incidence lattice. -/
def balanced : Submodule ℤ (V → ℤ) := LinearMap.ker (componentSum c)

abbrev FreeVertex := {v : V // v ≠ r (c v)}

/-- An oriented edge vector in the original vertex coordinates. -/
def edge (v w : V) : V → ℤ := Pi.single v 1 - Pi.single w 1

@[simp] theorem componentSum_single (v : V) (a : C) :
    componentSum c (Pi.single v 1) a = if c v = a then 1 else 0 := by
  simp [componentSum, Pi.single_apply]

 theorem edge_mem {v w : V} (h : c v = c w) : edge v w ∈ balanced c := by
  change componentSum c (edge v w) = 0
  ext a
  simp only [edge, map_sub, Pi.sub_apply, componentSum_single, h, sub_self, Pi.zero_apply]

/-- Restrict a balanced vector to the vertices that were not chosen as roots. -/
def drop : balanced c →ₗ[ℤ] (FreeVertex c r → ℤ) where
  toFun x v := x.val v.val
  map_add' x y := rfl
  map_smul' a x := rfl

include hr in
 theorem root_ne_free (i : FreeVertex c r) (a : C) : r a ≠ i.val := by
  intro h
  have ha : a = c i.val := by simpa only [hr a] using congrArg c h
  exact i.property (by rw [← ha]; exact h.symm)

/-- Restore the omitted coordinates by summing rooted incidence vectors. -/
def lift (x : FreeVertex c r → ℤ) : balanced c :=
  ∑ i, x i • (⟨edge i.val (r (c i.val)), edge_mem c (hr (c i.val)).symm⟩ : balanced c)

 theorem drop_lift (x : FreeVertex c r → ℤ) : drop c r (lift c r hr x) = x := by
  ext i
  change (drop c r (∑ j : FreeVertex c r, x j •
    (⟨edge j.val (r (c j.val)), edge_mem c (hr (c j.val)).symm⟩ : balanced c))) i = x i
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ j : FreeVertex c r, x j * (edge j.val (r (c j.val)) i.val)) = x i
  simp only [edge, Pi.sub_apply]
  have hj : ∀ j : FreeVertex c r, (Pi.single (r (c j.val)) (1 : ℤ) : V → ℤ) i.val = 0 := by
    intro j
    simp [Pi.single_apply, root_ne_free c r hr i (c j.val)]
  simp only [hj, sub_zero]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_apply]
  · intro j _ hji
    have hne : j.val ≠ i.val := fun h => hji (Subtype.ext h)
    simp [Pi.single_apply, hne]
  · simp

 theorem drop_eq_zero {x : balanced c} (h : drop c r x = 0) : x = 0 := by
  apply Subtype.ext
  ext v
  change x.val v = 0
  have hfree (w : V) (hw : w ≠ r (c w)) : x.val w = 0 :=
    congrFun h (⟨w, hw⟩ : FreeVertex c r)
  by_cases hv : v = r (c v)
  · have hx := congrFun x.property (c v)
    change (∑ w ∈ Finset.univ.filter (fun w => c w = c v), x.val w) = 0 at hx
    have he : (∑ w ∈ Finset.univ.filter (fun w => c w = c v), x.val w) = x.val v := by
      apply Finset.sum_eq_single v
      · intro w hw hwv
        have hc : c w = c v := (Finset.mem_filter.mp hw).2
        apply hfree
        intro hwr
        exact hwv (by rw [hwr, hc, ← hv])
      · simp
    simpa only [he] using hx
  · exact hfree v hv

 theorem drop_injective : Function.Injective (drop c r) := by
  intro x y h
  apply sub_eq_zero.mp
  apply drop_eq_zero c r
  simpa only [map_sub, h, sub_self]

/-- The inverse is proved over the integers; no rational saturation is used. -/
def coordinates : balanced c ≃ₗ[ℤ] (FreeVertex c r → ℤ) :=
  LinearEquiv.ofBijective (drop c r) ⟨drop_injective c r,
    fun x => ⟨lift c r hr x, drop_lift c r hr x⟩⟩

@[simp] theorem coordinates_apply (x : balanced c) (i : FreeVertex c r) :
    coordinates c r hr x i = x.val i.val := rfl

 theorem lift_drop (x : balanced c) : lift c r hr (drop c r x) = x :=
  drop_injective c r (drop_lift c r hr (drop c r x))

/-- A chosen root is the zero coordinate; every other vertex is its own coordinate. -/
def vertexCoordinate (v : V) : Option (FreeVertex c r) :=
  if h : v = r (c v) then none else some ⟨v, h⟩

 def coordinateVertex : Option (FreeVertex c r) → FreeVertex c r → ℤ
  | none => 0
  | some j => Pi.single j 1

include hr in
 theorem single_restrict (v : V) :
    (fun i : FreeVertex c r => (Pi.single v (1 : ℤ) : V → ℤ) i.val) =
      coordinateVertex c r (vertexCoordinate c r v) := by
  ext i
  by_cases h : v = r (c v)
  · have hn : v ≠ i.val := fun he => root_ne_free c r hr i (c v) (h.symm.trans he)
    unfold vertexCoordinate
    rw [dite_eq_left h]
    change (Pi.single v (1 : ℤ) : V → ℤ) i.val = 0
    simp [Pi.single_apply, hn]
  · simp only [vertexCoordinate, dite_eq_right h, coordinateVertex]
    simp [Pi.single_apply, Subtype.ext_iff]

/-- Every original directed incidence vector becomes exactly a signed
coordinate vector or a difference of two coordinate vectors. -/
theorem coordinates_edge {v w : V} (h : c v = c w) :
    coordinates c r hr ⟨edge v w, edge_mem c h⟩ =
      coordinateVertex c r (vertexCoordinate c r v) -
      coordinateVertex c r (vertexCoordinate c r w) := by
  ext i
  change (Pi.single v (1 : ℤ) : V → ℤ) i.val -
    (Pi.single w (1 : ℤ) : V → ℤ) i.val = _
  rw [congrFun (single_restrict c r hr v) i, congrFun (single_restrict c r hr w) i]
  rfl

end Components

#print axioms coordinates
#print axioms lift_drop
#print axioms coordinates_edge

end Unimodular.GraphicRootedLattice

#check Unimodular.GraphicRootedLattice.coordinates_edge
