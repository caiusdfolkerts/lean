module

public import Continuation.CycleBounds.AcrossArcs
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Pairwise

@[expose] public section

/-! # An alternating pair of disjoint chords gives a K4 minor -/

noncomputable section
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E : Type*}

 theorem reverse_arc {G : IncidenceGraph V E} {a b : V} {inside : List V}
    (h : (a :: (inside ++ [b])).IsChain (Adj G)) :
    (b :: (inside.reverse ++ [a])).IsChain (Adj G) := by
  have hh := List.isChain_reverse.mpr (h.imp (fun _ _ hxy ↦ hxy.symm))
  simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
    List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append,
        List.append_assoc] using hh

private def endpointIndex : Option (Fin 3) → Fin 10
  | none => 0
  | some i => ![2, 4, 6] i

private def pathIndex : Fin 6 → Fin 10 := ![1, 8, 7, 3, 9, 5]

private theorem endpointIndex_injective : Function.Injective endpointIndex := by
  unfold Function.Injective
  decide

private theorem pathIndex_injective : Function.Injective pathIndex := by
  unfold Function.Injective
  decide

private theorem pathIndex_ne_endpointIndex :
    ∀ e i, pathIndex e ≠ endpointIndex i := by decide

/-- Four arcs of a simple cycle, together with two internally disjoint chords
joining opposite vertices, contain an actual K4 graph minor. -/
theorem cycle_two_chords_hasK4Minor {G : IncidenceGraph V E}
    (a b c d : V) (p q r s pa pb : List V)
    (hcycle : CycleWord G (a :: (p ++ b :: (q ++ c :: (r ++ d :: s)))))
    (hpa : (a :: (pa ++ [c])).IsChain (Adj G))
    (hpb : (b :: (pb ++ [d])).IsChain (Adj G))
    (hpaAvoid : ∀ x ∈ pa, x ∉ a :: (p ++ b :: (q ++ c :: (r ++ d :: s))))
    (hpbAvoid : ∀ x ∈ pb, x ∉ a :: (p ++ b :: (q ++ c :: (r ++ d :: s))))
    (hchords : List.Disjoint pa pb) : G.HasK4Minor := by
  let blocks : List (List V) := [[a], p, [b], q, [c], r, [d], s]
  let parts : List (List V) := blocks ++ [pa, pb]
  have hblocks : blocks.Pairwise List.Disjoint := by
    have hflat : blocks.flatten.Nodup := by simpa [blocks] using hcycle.nodup
    exact (List.nodup_flatten.mp hflat).2
  have hparts : parts.Pairwise List.Disjoint := by
    apply List.pairwise_append.mpr
    refine ⟨hblocks, ?_, ?_⟩
    · simpa using hchords
    · intro u hu v hv
      have hsub : ∀ x ∈ u, x ∈ a :: (p ++ b :: (q ++ c :: (r ++ d :: s))) := by
        intro x hx
        have hh : x ∈ blocks.flatten := List.mem_flatten.mpr ⟨u, hu, hx⟩
        simpa [blocks] using hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact List.disjoint_left.mpr (fun x hx hxp ↦ hpaAvoid x hxp (hsub x hx))
      · exact List.disjoint_left.mpr (fun x hx hxp ↦ hpbAvoid x hxp (hsub x hx))
  have hdis (i j : Fin 10) (hij : i ≠ j) : List.Disjoint (parts.get i) (parts.get j) := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hparts.rel_get_of_lt hlt
    · exact (hparts.rel_get_of_lt hgt).symm
  let v : Option (Fin 3) → V := fun i ↦ i.elim a (fun j ↦ ![b, c, d] j)
  have hv (i : Option (Fin 3)) : parts.get (endpointIndex i) = [v i] := by
    cases i with
    | none => rfl
    | some i => fin_cases i <;> rfl
  have hvi : Function.Injective v := by
    intro i j hij
    by_contra hne
    have hd := hdis (endpointIndex i) (endpointIndex j)
      (fun hh ↦ hne (endpointIndex_injective hh))
    rw [hv, hv] at hd
    exact List.disjoint_left.mp hd (List.mem_singleton_self _) (by simpa only [hij] using List.mem_singleton_self (v j))
  let inside : Fin 6 → List V := ![p.reverse, pa.reverse, s, q, pb, r]
  have hmem (e : Fin 6) (x : V) : x ∈ inside e ↔ x ∈ parts.get (pathIndex e) := by
    fin_cases e <;> simp [inside, pathIndex, parts, blocks]
  have hab : (a :: (p ++ [b])).IsChain (Adj G) :=
    hcycle.arc (pre := []) (post := q ++ c :: (r ++ d :: s)) rfl
  have hbc : (b :: (q ++ [c])).IsChain (Adj G) :=
    hcycle.arc (pre := a :: p) (post := r ++ d :: s) (by simp only [List.cons_append, List.append_assoc])
  have hcd : (c :: (r ++ [d])).IsChain (Adj G) :=
    hcycle.arc (pre := (a :: p) ++ (b :: q)) (post := s) (by simp only [List.cons_append, List.append_assoc])
  have hda : (d :: (s ++ [a])).IsChain (Adj G) := by
    apply bridge_isChain hcycle.chain (pre := ((a :: p) ++ (b :: q)) ++ (c :: r))
      (post := p ++ b :: (q ++ c :: (r ++ d :: s)))
    simp only [List.cons_append, List.append_assoc]
  let D : K4Subdivision G :=
    { vertex := ⟨v, hvi⟩
      inside := inside
      chain := by
        intro e
        fin_cases e
        · change (b :: (p.reverse ++ [a])).IsChain (Adj G)
          exact reverse_arc hab
        · change (c :: (pa.reverse ++ [a])).IsChain (Adj G)
          exact reverse_arc hpa
        · change (d :: (s ++ [a])).IsChain (Adj G)
          exact hda
        · change (b :: (q ++ [c])).IsChain (Adj G)
          exact hbc
        · change (b :: (pb ++ [d])).IsChain (Adj G)
          exact hpb
        · change (c :: (r ++ [d])).IsChain (Adj G)
          exact hcd
      avoids := by
        intro e i hi
        have hh := (hmem e (v i)).mp hi
        have hd := hdis (pathIndex e) (endpointIndex i) (pathIndex_ne_endpointIndex e i)
        exact List.disjoint_left.mp hd hh (by rw [hv]; simp)
      disjoint := by
        intro e f hef x hx hf
        exact List.disjoint_left.mp
          (hdis (pathIndex e) (pathIndex f) (fun hh ↦ hef (pathIndex_injective hh)))
          ((hmem e x).mp hx) ((hmem f x).mp hf) }
  exact D.hasK4Minor

end Unimodular.CycleBounds
