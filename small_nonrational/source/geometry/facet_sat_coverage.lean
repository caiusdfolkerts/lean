module
prelude
public import FacetSat

@[expose] public section

/-!
# SAT certificates for coverage by classified terminal families

A graph need not be impossible: some of its boundaries may be the already
classified catalogue leaves.  To prove coverage, a SAT refutation can add one
blocking clause for each such leaf.  Exact kind quotas make a short clause
sufficient: if every facet of a complete leaf is selected, the whole boundary
is that leaf.  No literals for the other candidate facets are needed.
-/

namespace Papers.RationalityTen.FacetSat

open GrowthDAG SparseGrowthDAG GrowthPruning

variable {n r l : Nat}

namespace Boundary

variable {kind : Fin n → Nat} {relation : Fin n → Fin n → Bool}
  {ridges : Fin n → Fin r → Bool} {quota : Nat → Nat} {S : List (Fin n)}

/-- Count equality is needed only for kinds actually occurring in the local
candidate universe.  This form admits a finite executable certificate. -/
theorem same_of_subset_at_kinds (H : Boundary kind relation ridges quota S)
    (leaf : List (Fin n)) (hnodup : leaf.Nodup)
    (hcounts : ∀ c, kindCount kind leaf (kind c) = quota (kind c))
    (hsub : leaf ⊆ S) : Same (family leaf) (family S) := by
  have hreverse : S ⊆ leaf := by
    intro c hc
    by_cases hmem : c ∈ leaf
    · exact hmem
    · have hstrict := kindCount_lt kind leaf S c hnodup hsub hc hmem
      rw [hcounts c, H.exactQuota] at hstrict
      exact False.elim (Nat.lt_irrefl _ hstrict)
  apply sameCheck_sound leaf S
  apply Bool.and_eq_true_iff.mpr
  exact ⟨List.all_eq_true.mpr (fun c hc => (has_true S c).mpr (hsub hc)),
    List.all_eq_true.mpr (fun c hc => (has_true leaf c).mpr (hreverse hc))⟩

theorem same_of_subset (H : Boundary kind relation ridges quota S)
    (leaf : List (Fin n)) (hnodup : leaf.Nodup)
    (hcounts : ∀ key, kindCount kind leaf key = quota key)
    (hsub : leaf ⊆ S) : Same (family leaf) (family S) :=
  H.same_of_subset_at_kinds leaf hnodup (fun c => hcounts (kind c)) hsub

/-- A complete leaf has the prescribed counts at every possible selected
kind.  The check does not quantify over unbounded natural numbers. -/
def leafCheck (kind : Fin n → Nat) (quota : Nat → Nat) (leaf : List (Fin n)) : Bool :=
  decide leaf.Nodup && (List.finRange n).all fun c =>
    decide (kindCount kind leaf (kind c) = quota (kind c))

theorem same_of_subset_checked (H : Boundary kind relation ridges quota S)
    (leaf : List (Fin n)) (hcheck : leafCheck kind quota leaf = true)
    (hsub : leaf ⊆ S) : Same (family leaf) (family S) := by
  obtain ⟨hnodup, hcounts⟩ := Bool.and_eq_true_iff.mp hcheck
  exact H.same_of_subset_at_kinds leaf (of_decide_eq_true hnodup)
    (fun c => of_decide_eq_true (List.all_eq_true.mp hcounts c (List.mem_finRange c))) hsub

/-- The blocking clause for a classified leaf contains only its negative
selection literals.  Its falsities assert that every leaf facet is selected. -/
theorem block_leaf (H : Boundary kind relation ridges quota S)
    (leaf : List (Fin n)) (hnodup : leaf.Nodup)
    (hcounts : ∀ key, kindCount kind leaf key = quota key)
    (hnot : ¬Same (family leaf) (family S)) :
    (∀ c ∈ leaf, c ∈ S) → False :=
  fun hsub => hnot (H.same_of_subset leaf hnodup hcounts hsub)

theorem block_leaf_checked (H : Boundary kind relation ridges quota S)
    (leaf : List (Fin n)) (hcheck : leafCheck kind quota leaf = true)
    (hnot : ¬Same (family leaf) (family S)) :
    (∀ c ∈ leaf, c ∈ S) → False :=
  fun hsub => hnot (H.same_of_subset_checked leaf hcheck hsub)

end Boundary

theorem all_mem_nil (P : Fin n → Prop) : ∀ c ∈ ([] : List (Fin n)), P c := by
  intro c hc
  exact False.elim (List.not_mem_nil hc)

theorem all_mem_cons (P : Fin n → Prop) (a : Fin n) (tail : List (Fin n))
    (ha : P a) (ht : ∀ c ∈ tail, P c) : ∀ c ∈ a :: tail, P c := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ha
  · exact ht c hc

/-- Refuting boundaries which escape every classified leaf proves catalogue
coverage.  The refutation may use all the geometric and counter clauses plus
the short blocking clauses justified above. -/
theorem coverage_of_unsat
    (kind : Fin n → Nat) (relation : Fin n → Fin n → Bool)
    (ridges : Fin n → Fin r → Bool) (quota : Nat → Nat)
    (leaves : Fin l → List (Fin n))
    (hunsat : ∀ S, Boundary kind relation ridges quota S →
      (∀ j, ¬Same (family (leaves j)) (family S)) → False)
    (S : List (Fin n)) (H : Boundary kind relation ridges quota S) :
    ∃ j, Same (family (leaves j)) (family S) := by
  apply Classical.byContradiction
  intro hmissing
  exact hunsat S H (fun j hsame => hmissing ⟨j, hsame⟩)

#print axioms Boundary.same_of_subset
#print axioms Boundary.block_leaf_checked
#print axioms coverage_of_unsat

end Papers.RationalityTen.FacetSat
