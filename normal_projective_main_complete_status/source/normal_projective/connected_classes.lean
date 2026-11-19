module

public import Mathlib.Topology.Connected.Clopen

/-! Generic topology used to identify locally open move classes with components.
The hypotheses are explicitly discharged by geometric constructions elsewhere. -/

@[expose] public section
open Set Filter Topology

namespace NormalProjective.ConnectedClasses

variable {X : Type*} [TopologicalSpace X] (R : X → X → Prop)

theorem isOpen_class (htrans : ∀ ⦃x y z⦄, R x y → R y z → R x z)
    (hlocal : ∀ x, {y | R x y} ∈ 𝓝 x) (a : X) : IsOpen {y | R a y} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact Filter.mem_of_superset (hlocal x) (fun y hy => htrans hx hy)

theorem isOpen_class_complement (hR : Equivalence R)
    (hlocal : ∀ x, {y | R x y} ∈ 𝓝 x) (a : X) : IsOpen ({y | R a y}ᶜ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  apply Filter.mem_of_superset (hlocal x)
  intro y hxy hay
  exact hx (hR.trans hay (hR.symm hxy))

theorem isClopen_class (hR : Equivalence R)
    (hlocal : ∀ x, {y | R x y} ∈ 𝓝 x) (a : X) : IsClopen {y | R a y} := by
  exact ⟨isOpen_compl_iff.mp (isOpen_class_complement R hR hlocal a),
    isOpen_class R (@hR.trans) hlocal a⟩

theorem connectedComponent_subset_class (hR : Equivalence R)
    (hlocal : ∀ x, {y | R x y} ∈ 𝓝 x) (a : X) :
    connectedComponent a ⊆ {y | R a y} :=
  (isClopen_class R hR hlocal a).connectedComponent_subset (hR.refl a)

theorem class_eq_connectedComponent (hR : Equivalence R)
    (hlocal : ∀ x, {y | R x y} ∈ 𝓝 x)
    (hstay : ∀ x y, R x y → y ∈ connectedComponent x) (a : X) :
    {y | R a y} = connectedComponent a := by
  exact Set.Subset.antisymm (fun y hy => hstay a y hy)
    (connectedComponent_subset_class R hR hlocal a)

theorem class_eq_connectedComponent_of_preconnected (hR : Equivalence R)
    (hlocal : ∀ x, {y | R x y} ∈ 𝓝 x)
    (hconn : ∀ x, IsPreconnected {y | R x y}) (a : X) :
    {y | R a y} = connectedComponent a :=
  Set.Subset.antisymm ((hconn a).subset_connectedComponent (hR.refl a))
    (connectedComponent_subset_class R hR hlocal a)

end NormalProjective.ConnectedClasses
