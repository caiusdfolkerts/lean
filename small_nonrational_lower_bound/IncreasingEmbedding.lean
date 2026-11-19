module
prelude
public import GraphCoverageDescriptions

@[expose] public section
namespace Papers.RationalityTen.GraphCoverageDescriptions

/-- Linear adjacent comparisons certify the strict order of an embedding.
The implication to full pairwise distinctness is proved below; no ordering
property of the untrusted producer is assumed. -/
def increasing {N : Nat} : List (Fin N) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.val < b.val) && increasing (b :: rest)

theorem pairwise_of_increasing {N : Nat} (xs : List (Fin N))
    (h : increasing xs = true) : xs.Pairwise (fun a b => a.val < b.val) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons a tail ih =>
    cases tail with
    | nil => exact List.pairwise_singleton _ _
    | cons b rest =>
      have hparts : a.val < b.val ∧ increasing (b :: rest) = true := by
        simpa only [increasing, Bool.and_eq_true_iff, decide_eq_true_eq] using h
      have ht := ih hparts.2
      apply List.pairwise_cons.mpr
      refine ⟨?_, ht⟩
      intro c hc
      rcases List.mem_cons.mp hc with heq | hc
      · subst c; exact hparts.1
      · exact Nat.lt_trans hparts.1 ((List.pairwise_cons.mp ht).1 c hc)

theorem nodup_of_increasing {N : Nat} (xs : List (Fin N))
    (h : increasing xs = true) : xs.Nodup := by
  apply List.Pairwise.imp _ (pairwise_of_increasing xs h)
  intro a b hab heq
  cases heq
  exact Nat.lt_irrefl _ hab

#print axioms nodup_of_increasing
end Papers.RationalityTen.GraphCoverageDescriptions
