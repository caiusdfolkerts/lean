module

public import ToricPower.FiniteDimensionalCoproductCompact
public import ToricPower.CoproductProjectorMap
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Finite-dimensional diagrams have finite support in arbitrary sums

Only the set of objects is required to be finite. Naturality is retained
by using the canonical coproduct projector, rather than choosing
independent, potentially incompatible component factorizations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.CompactExtraction

universe u
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C] [Finite C]

/-- A finite common support for every component of an actual natural
transformation gives a factorization through a finite subcoproduct. -/
theorem finiteDiagram_coproductCompact (P : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (P.obj c)] : CoproductCompact P := by
  classical
  letI := Fintype.ofFinite C
  apply coproductCompact_iff_projector.mpr
  intro I family f
  let ev (c : C) := (evaluation C (ModuleCat.{u} k)).obj c
  let components (c : C) :=
    (ev c).map f ≫ (PreservesCoproduct.iso (ev c) family).hom
  have support (c : C) : ∃ s : Finset I,
      components c ≫ finiteCoproductProjector (fun i => (ev c).obj (family i)) s =
        components c :=
    (coproductCompact_iff_projector.mp
      (finiteDimensional_coproductCompact k (P.obj c))) I _ (components c)
  choose supports supported using support
  let common := Finset.univ.biUnion supports
  refine ⟨common,?_⟩
  apply NatTrans.ext
  funext c
  exact support_of_mapped_support (ev c) family f common
    (finiteSupport_mono _ (components c)
      (Finset.subset_biUnion_of_mem supports (Finset.mem_univ c)) (supported c))

end ToricPower.CompactExtraction

end
