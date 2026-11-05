module

public import Continuation.CycleBounds.CycleWords

@[expose] public section

/-! # A connected component crossing two cycle arcs supplies a chord -/

noncomputable section
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E α : Type*}

/-- A walk in one component, joining the two arcs cut out by vertices of a
 different component, has a segment which joins the arcs and otherwise avoids
 the entire cycle. Its endpoints and interior remain in the original component. -/
theorem bridge_across_arcs {G : IncidenceGraph V E} (c : V → α)
    (A B : α) (hAB : A ≠ B) (b d a : V) (I O l : List V)
    (hcycle : CycleWord G (b :: (I ++ d :: O)))
    (hb : c b = B) (hd : c d = B) (ha : a ∈ O)
    (hwalk : (a :: l).IsChain (Adj G))
    (hmono : ∀ x ∈ a :: l, c x = A)
    (hfuture : ∃ a' ∈ l, a' ∈ I) :
    ∃ x ∈ O, ∃ y ∈ I, ∃ inside : List V,
      (x :: (inside ++ [y])).IsChain (Adj G) ∧
      (∀ z ∈ inside, z ∉ b :: (I ++ d :: O)) ∧
      (∀ z ∈ x :: (inside ++ [y]), c z = A) := by
  let S : Set V := {x | x ∈ b :: (I ++ d :: O)}
  let color : V → Bool := fun x ↦ decide (x ∈ I)
  have hIO : List.Disjoint I (d :: O) := by
    apply List.disjoint_left.mpr
    intro x hxI hxO
    exact (List.nodup_append.mp (List.nodup_cons.mp hcycle.nodup).2).2.2 x hxI x hxO rfl
  have haI : a ∉ I := fun hai ↦ List.disjoint_left.mp hIO hai (List.mem_cons_of_mem _ ha)
  have haS : a ∈ S := by simp [S, ha]
  have hfuture' : ∃ a' ∈ l, a' ∈ S ∧ color a ≠ color a' := by
    obtain ⟨a', ha'l, ha'I⟩ := hfuture
    exact ⟨a', ha'l, by simp [S, ha'I], by simp [color, haI, ha'I]⟩
  obtain ⟨pre, x, inside, y, post, heq, hxS, hyS, hxy, hins⟩ :=
    exists_bridge_segment S color l a [] haS (by simp) hfuture'
  simp only [List.nil_append] at heq
  have hxmem : x ∈ a :: l := by rw [heq]; simp
  have hymem : y ∈ a :: l := by rw [heq]; simp
  have hcx : c x = A := hmono x hxmem
  have hcy : c y = A := hmono y hymem
  have hxne (z : V) (hz : c z = B) : x ≠ z :=
    fun hxz ↦ hAB (hcx.symm.trans ((congrArg c hxz).trans hz))
  have hyne (z : V) (hz : c z = B) : y ≠ z :=
    fun hyz ↦ hAB (hcy.symm.trans ((congrArg c hyz).trans hz))
  have hxIO : x ∈ I ∨ x ∈ O := by
    have hh := hxS
    change x ∈ b :: (I ++ d :: O) at hh
    simpa only [List.mem_cons, List.mem_append, hxne b hb, hxne d hd,
      false_or] using hh
  have hyIO : y ∈ I ∨ y ∈ O := by
    have hh := hyS
    change y ∈ b :: (I ++ d :: O) at hh
    simpa only [List.mem_cons, List.mem_append, hyne b hb, hyne d hd,
      false_or] using hh
  have hchain := bridge_isChain hwalk heq
  have hinside : ∀ z ∈ inside, z ∉ b :: (I ++ d :: O) := hins
  have hsegment : ∀ z ∈ x :: (inside ++ [y]), c z = A := by
    intro z hz
    apply hmono z
    rw [heq]
    simp only [List.mem_append, List.mem_cons, List.mem_singleton] at hz ⊢
    tauto
  by_cases hxI : x ∈ I
  · have hyI : y ∉ I := by
      intro hyI
      exact hxy (by simp [color, hxI, hyI])
    have hyO := hyIO.resolve_left hyI
    refine ⟨y, hyO, x, hxI, inside.reverse, ?_, ?_, ?_⟩
    · have hh := List.isChain_reverse.mpr (hchain.imp (fun _ _ h ↦ h.symm))
      simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
        List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append,
        List.append_assoc] using hh
    · intro z hz
      exact hinside z (List.mem_reverse.mp hz)
    · intro z hz
      apply hsegment z
      simpa only [List.mem_cons, List.mem_append, List.mem_singleton,
        List.mem_reverse, or_assoc, or_comm, or_left_comm] using hz
  · have hyI : y ∈ I := by
      by_contra hyI
      exact hxy (by simp [color, hxI, hyI])
    exact ⟨x, hxIO.resolve_left hxI, y, hyI, inside, hchain, hinside, hsegment⟩

end Unimodular.CycleBounds
