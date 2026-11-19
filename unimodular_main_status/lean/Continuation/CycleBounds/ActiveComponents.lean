module

public import Continuation.CycleBounds.NoncrossingGraph

@[expose] public section

/-! # Actual active components of a graph potential -/

noncomputable section
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E : Type*}

/-- Active adjacency is ordinary adjacency with equal endpoint potentials. -/
def ActiveAdj (G : IncidenceGraph V E) (h : V → ℝ) (a b : V) : Prop :=
  Adj G a b ∧ h a = h b

theorem ActiveAdj.symm {G : IncidenceGraph V E} {h : V → ℝ} {a b : V}
    (hab : ActiveAdj G h a b) : ActiveAdj G h b a := ⟨hab.1.symm, hab.2.symm⟩

def activeSetoid (G : IncidenceGraph V E) (h : V → ℝ) : Setoid V where
  r := Relation.ReflTransGen (ActiveAdj G h)
  iseqv := ⟨fun _ ↦ .refl, by
    intro a b hab
    induction hab with
    | refl => exact .refl
    | tail _ hxy ih => exact (Relation.ReflTransGen.single hxy.symm).trans ih,
    fun hab hbc ↦ hab.trans hbc⟩

def ActiveComponent (G : IncidenceGraph V E) (h : V → ℝ) := Quotient (activeSetoid G h)

def activeComponent (G : IncidenceGraph V E) (h : V → ℝ) (a : V) : ActiveComponent G h :=
  Quotient.mk _ a

theorem potential_eq_of_active {G : IncidenceGraph V E} {h : V → ℝ} {a b : V}
    (hab : Relation.ReflTransGen (ActiveAdj G h) a b) : h a = h b := by
  induction hab with
  | refl => rfl
  | tail _ hxy ih => exact ih.trans hxy.2

def componentPotential (G : IncidenceGraph V E) (h : V → ℝ) : ActiveComponent G h → ℝ :=
  Quotient.lift h (fun _ _ hab ↦ potential_eq_of_active hab)

@[simp] theorem componentPotential_apply (G : IncidenceGraph V E) (h : V → ℝ) (a : V) :
    componentPotential G h (activeComponent G h a) = h a := rfl

theorem activeComponent_edge (G : IncidenceGraph V E) (h : V → ℝ) (e : E)
    (he : e ∈ G.edges) (hactive : h (G.source e) = h (G.target e)) :
    activeComponent G h (G.source e) = activeComponent G h (G.target e) := by
  by_cases hst : G.source e = G.target e
  · exact congrArg (activeComponent G h) hst
  · apply Quotient.sound
    exact Relation.ReflTransGen.single ⟨⟨hst, e, he, Or.inl ⟨rfl, rfl⟩⟩, hactive⟩

/-- Distinct vertices in the same actual active component have an ordinary
monochromatic walk between them. -/
theorem activeComponent_connected (G : IncidenceGraph V E) (h : V → ℝ)
    (x y : V) (hne : x ≠ y)
    (hxy : activeComponent G h x = activeComponent G h y) :
    ∃ l : List V, (x :: (l ++ [y])).IsChain (Adj G) ∧
      ∀ z ∈ x :: (l ++ [y]), activeComponent G h z = activeComponent G h x := by
  have hr : Relation.ReflTransGen (ActiveAdj G h) x y := Quotient.exact hxy
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hr
  have hlne : l ≠ [] := by
    intro he
    subst l
    exact hne (by simpa using hlast)
  have hlast' : l.getLast hlne = y := by simpa only [List.getLast_cons hlne] using hlast
  have hsplit : l.dropLast ++ [y] = l := by
    simpa only [hlast'] using List.dropLast_append_getLast hlne
  refine ⟨l.dropLast, ?_, ?_⟩
  · rw [hsplit]
    exact hl.imp (fun _ _ hab ↦ hab.1)
  · rw [hsplit]
    apply hl.induction (fun z ↦ activeComponent G h z = activeComponent G h x) (x :: l)
    · intro a b hab ha
      have hh : activeComponent G h a = activeComponent G h b :=
        Quotient.sound (Relation.ReflTransGen.single hab)
      exact hh.symm.trans ha
    · intro _
      rfl

/-- The actual active-component partition is noncrossing on every cycle of a
literal K4-minor-free graph. -/
theorem active_components_noncrossing (G : IncidenceGraph V E) (h : V → ℝ)
    (hK : ¬G.HasK4Minor) (w : List V) (hw : CycleWord G w) :
    Noncrossing (w.map (activeComponent G h)) :=
  noncrossing_of_no_K4 hK (activeComponent G h) (activeComponent_connected G h) w hw

#print axioms active_components_noncrossing
end Unimodular.CycleBounds
