module
prelude
public import GraphCatalogueCore

@[expose] public section

/-!
# Kernel checker for the finite graph catalogue

Each row accounts for every possible edge.  It either records that the edge is
already present, identifies a vertex whose degree bound would be exceeded, or
supplies a checked renamed extension in the next catalogue.  Stored masks are
checked against explicit duplicate-free edge lists before they are used.
-/

namespace Papers.RationalityTen.GraphCatalogueCheck

open GrowthDAG SparseGrowthDAG GrowthRenaming GrowthBitsets GraphCatalogueCore ConcreteGrowth

variable {n v g before after : Nat}

structure State (n : Nat) where
  edges : List (Fin n)
  mask : Nat

def stateCheck (state : State n) : Bool :=
  decide state.edges.Nodup && decide (state.mask = ofList state.edges)

inductive Choice (v after g : Nat) where
  | selected
  | saturated (vertex : Fin v)
  | extension (model : Fin after) (frame : Fin g)

def extensionCheck (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (renamings : Fin g → IncidenceRenaming incidence)
    (source : State n) (next : Fin after → State n) (edge : Fin n) :
    Choice v after g → Bool
  | .selected => bitAt source.mask edge.val
  | .saturated vertex =>
      incidence edge vertex && decide (bound ≤ degree incidence source.edges vertex)
  | .extension model frame =>
      decide ((next model).mask =
        ofList ((edge :: source.edges).map (renamings frame).cells.forward))

theorem perm_of_masks (S T : List (Fin n)) (hS : S.Nodup) (hT : T.Nodup)
    (hmask : ofList S = ofList T) : S.Perm T := by
  have hsame := sameCheck_sound S T (FastBatchedGrowth.sameCheck_of_masks S T hmask)
  apply (List.perm_ext_iff_of_nodup hS hT).mpr
  intro edge
  change edge ∈ S ↔ edge ∈ T
  rw [← has_true S edge, ← has_true T edge]
  exact Iff.of_eq (congrArg (fun value => value = true) (hsame edge))

theorem extensionCheck_sound (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (renamings : Fin g → IncidenceRenaming incidence)
    (source : State n) (next : Fin after → State n)
    (hsource : stateCheck source = true)
    (hnext : ∀ i, stateCheck (next i) = true)
    (edge : Fin n) (choice : Choice v after g)
    (hcheck : extensionCheck incidence bound renamings source next edge choice = true)
    (habsent : edge ∉ source.edges)
    (hvalid : Valid incidence bound (edge :: source.edges)) :
    ∃ model frame, (next model).edges.Perm
      ((edge :: source.edges).map (renamings frame).cells.forward) := by
  have hmask : source.mask = ofList source.edges :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hsource).2
  cases choice with
  | selected =>
      have hmem : edge ∈ source.edges := by
        change bitAt source.mask edge.val = true at hcheck
        rw [hmask, bitAt_ofList] at hcheck
        exact hcheck
      exact False.elim (habsent hmem)
  | saturated vertex =>
      obtain ⟨hinc, hfull⟩ := Bool.and_eq_true_iff.mp hcheck
      have hfull' : bound ≤ degree incidence source.edges vertex := of_decide_eq_true hfull
      have hbound := hvalid.degree_le vertex
      simp only [degree, List.filter_cons, hinc, ↓reduceIte,
        List.length_cons] at hbound
      change (source.edges.filter fun e => incidence e vertex).length + 1 ≤ bound at hbound
      change bound ≤ (source.edges.filter fun e => incidence e vertex).length at hfull'
      omega
  | extension model frame =>
      refine ⟨model, frame, ?_⟩
      obtain ⟨hnd, hnextmask⟩ := Bool.and_eq_true_iff.mp (hnext model)
      apply perm_of_masks _ _ (of_decide_eq_true hnd)
        (hvalid.rename (renamings frame)).nodup
      exact (of_decide_eq_true hnextmask).symm.trans (of_decide_eq_true hcheck)

/-- A complete finite row check discharges precisely the extension obligation
of the general catalogue induction. -/
theorem covers_step_of_checks (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (renamings : Fin g → IncidenceRenaming incidence)
    (models : Fin before → State n) (next : Fin after → State n)
    (choices : Fin before → Fin n → Choice v after g)
    (hmodels : ∀ i, stateCheck (models i) = true)
    (hnext : ∀ i, stateCheck (next i) = true)
    (hchoices : ∀ i edge,
      extensionCheck incidence bound renamings (models i) next edge (choices i edge) = true)
    {size : Nat}
    (hprevious : Covers incidence bound renamings (fun i => (models i).edges) size) :
    Covers incidence bound renamings (fun i => (next i).edges) (size + 1) := by
  apply GraphCatalogueCore.covers_step renamings (fun i => (models i).edges)
    (fun i => (next i).edges) hprevious
  intro i edge habsent hvalid
  exact extensionCheck_sound incidence bound renamings (models i) next
    (hmodels i) hnext edge (choices i edge) (hchoices i edge) habsent hvalid

#print axioms covers_step_of_checks

end Papers.RationalityTen.GraphCatalogueCheck
