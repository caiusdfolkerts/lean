module

public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.Data.Finset.Powerset

/-!
# The common-neighbor adjunction for finite incidence relations

The two face posets are the nonempty faces of the two Dowker complexes of
an actual finite relation.  The maps below use all common neighbors; neither
the existence of a comparison nor either composite inequality is assumed.

This file supplies the order-theoretic part of the comparison between the
negative chart nerve and the negative ray complex in Lemma 5.1.  It does not
identify simplicial cohomology with the cohomology of a face-poset nerve, and
does not assert the resulting cohomology comparison without that further step.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Classical

namespace ToricPower.Dowker

variable {Row Column : Type*}

/-- A nonempty set of columns which have a common row.  The order is literal
inclusion of finite sets, inherited from the subtype. -/
abbrev Face (relation : Row → Column → Prop) :=
  {face : Finset Column // face.Nonempty ∧
    ∃ row, ∀ column ∈ face, relation row column}

variable [Fintype Row] [Fintype Column]

/-- All common neighbors of a face form a face for the transposed relation.
Its nonemptiness comes from the witness in the original face; a vertex of
the original face witnesses that the new set is a face. -/
def commonNeighbors (relation : Row → Column → Prop) (face : Face relation) :
    Face (fun column row => relation row column) := by
  classical
  let neighbors := Finset.univ.filter (fun row =>
    ∀ column ∈ face.val, relation row column)
  refine ⟨neighbors, ?_, ?_⟩
  · obtain ⟨row, contains⟩ := face.property.2
    exact ⟨row, Finset.mem_filter.mpr ⟨Finset.mem_univ row, contains⟩⟩
  · obtain ⟨column, present⟩ := face.property.1
    exact ⟨column, fun row member =>
      (Finset.mem_filter.mp member).2 column present⟩

@[simp]
theorem mem_commonNeighbors (relation : Row → Column → Prop)
    (face : Face relation) (row : Row) :
    row ∈ (commonNeighbors relation face).val ↔
      ∀ column ∈ face.val, relation row column := by
  classical
  simp only [commonNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

theorem commonNeighbors_antitone (relation : Row → Column → Prop) :
    Antitone (commonNeighbors relation) := by
  intro first second subset row present
  rw [mem_commonNeighbors] at present ⊢
  exact fun column member => present column (subset member)

theorem le_double_commonNeighbors (relation : Row → Column → Prop)
    (face : Face relation) :
    face ≤ commonNeighbors (fun column row => relation row column)
      (commonNeighbors relation face) := by
  intro column present
  rw [mem_commonNeighbors]
  intro row neighbor
  exact (mem_commonNeighbors relation face row).mp neighbor column present

/-- Regard the common-row map as a monotone map into the opposite face order. -/
def columnsToRows (relation : Row → Column → Prop) :
    Face relation → (Face (fun column row => relation row column))ᵒᵈ :=
  fun face => OrderDual.toDual (commonNeighbors relation face)

/-- The other common-neighbor map is monotone from the opposite face order. -/
def rowsToColumns (relation : Row → Column → Prop) :
    (Face (fun column row => relation row column))ᵒᵈ → Face relation :=
  fun face => commonNeighbors (fun column row => relation row column)
    (OrderDual.ofDual face)

theorem commonNeighborGaloisConnection (relation : Row → Column → Prop) :
    GaloisConnection (columnsToRows relation) (rowsToColumns relation) := by
  intro columns rows
  change ((OrderDual.ofDual rows).val ⊆ (commonNeighbors relation columns).val) ↔
    (columns.val ⊆
      (commonNeighbors (fun column row => relation row column)
        (OrderDual.ofDual rows)).val)
  constructor
  · intro allRows column columnPresent
    rw [mem_commonNeighbors]
    intro row rowPresent
    exact (mem_commonNeighbors relation columns row).mp (allRows rowPresent)
      column columnPresent
  · intro allColumns row rowPresent
    rw [mem_commonNeighbors]
    intro column columnPresent
    exact (mem_commonNeighbors (fun column row => relation row column)
      (OrderDual.ofDual rows) column).mp (allColumns columnPresent) row rowPresent

/-- The resulting actual adjunction of the two face-poset categories. -/
def commonNeighborAdjunction (relation : Row → Column → Prop) :
    (commonNeighborGaloisConnection relation).monotone_l.functor ⊣
      (commonNeighborGaloisConnection relation).monotone_u.functor :=
  (commonNeighborGaloisConnection relation).adjunction

/-- The unit is the inclusion into the double common-neighbor face. -/
theorem unit_inclusion (relation : Row → Column → Prop) (face : Face relation) :
    face ≤ rowsToColumns relation (columnsToRows relation face) :=
  (commonNeighborGaloisConnection relation).le_u_l face

/-- The counit is the corresponding inclusion on rows, expressed in the
opposite order.  No component is asserted to be an isomorphism. -/
theorem counit_inclusion (relation : Row → Column → Prop)
    (face : (Face (fun column row => relation row column))ᵒᵈ) :
    columnsToRows relation (rowsToColumns relation face) ≤ face :=
  (commonNeighborGaloisConnection relation).l_u_le face

end ToricPower.Dowker
