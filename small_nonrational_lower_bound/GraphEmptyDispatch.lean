module
prelude
public import GraphCaseCertificate
public import SharedEmptyKeysChecked

@[expose] public section
namespace Papers.RationalityTen.GraphFiniteDispatch
open GraphCaseCertificate GraphRowSpecifications

theorem empty16 (i : Fin SharedSmallRootCertificates.Row16.rootCount) :
    Result (16, SharedSmallRootReplay.complement (SharedEmptyKeys.Row16.rootCode i)) := by
  apply of_empty 16 _ (by decide)
  refine ⟨SharedEmptyKeys.Row16.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row16.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty19 (i : Fin SharedSmallRootCertificates.Row19.rootCount) :
    Result (19, SharedSmallRootReplay.complement (SharedEmptyKeys.Row19.rootCode i)) := by
  apply of_empty 19 _ (by decide)
  refine ⟨SharedEmptyKeys.Row19.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row19.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty23 (i : Fin SharedSmallRootCertificates.Row23.rootCount) :
    Result (23, SharedSmallRootReplay.complement (SharedEmptyKeys.Row23.rootCode i)) := by
  apply of_empty 23 _ (by decide)
  refine ⟨SharedEmptyKeys.Row23.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row23.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty24 (i : Fin SharedSmallRootCertificates.Row24.rootCount) :
    Result (24, SharedSmallRootReplay.complement (SharedEmptyKeys.Row24.rootCode i)) := by
  apply of_empty 24 _ (by decide)
  refine ⟨SharedEmptyKeys.Row24.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row24.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty25 (i : Fin SharedSmallRootCertificates.Row25.rootCount) :
    Result (25, SharedSmallRootReplay.complement (SharedEmptyKeys.Row25.rootCode i)) := by
  apply of_empty 25 _ (by decide)
  refine ⟨SharedEmptyKeys.Row25.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row25.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty26 (i : Fin SharedSmallRootCertificates.Row26.rootCount) :
    Result (26, SharedSmallRootReplay.complement (SharedEmptyKeys.Row26.rootCode i)) := by
  apply of_empty 26 _ (by decide)
  refine ⟨SharedEmptyKeys.Row26.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row26.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty27 (i : Fin SharedSmallRootCertificates.Row27.rootCount) :
    Result (27, SharedSmallRootReplay.complement (SharedEmptyKeys.Row27.rootCode i)) := by
  apply of_empty 27 _ (by decide)
  refine ⟨SharedEmptyKeys.Row27.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row27.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty28 (i : Fin SharedSmallRootCertificates.Row28.rootCount) :
    Result (28, SharedSmallRootReplay.complement (SharedEmptyKeys.Row28.rootCode i)) := by
  apply of_empty 28 _ (by decide)
  refine ⟨SharedEmptyKeys.Row28.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row28.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty29 (i : Fin SharedSmallRootCertificates.Row29.rootCount) :
    Result (29, SharedSmallRootReplay.complement (SharedEmptyKeys.Row29.rootCode i)) := by
  apply of_empty 29 _ (by decide)
  refine ⟨SharedEmptyKeys.Row29.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row29.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty30 (i : Fin SharedSmallRootCertificates.Row30.rootCount) :
    Result (30, SharedSmallRootReplay.complement (SharedEmptyKeys.Row30.rootCode i)) := by
  apply of_empty 30 _ (by decide)
  refine ⟨SharedEmptyKeys.Row30.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row30.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty31 (i : Fin SharedSmallRootCertificates.Row31.rootCount) :
    Result (31, SharedSmallRootReplay.complement (SharedEmptyKeys.Row31.rootCode i)) := by
  apply of_empty 31 _ (by decide)
  refine ⟨SharedEmptyKeys.Row31.rootCode i, rfl, ?_⟩
  have h := SharedSmallRootCertificates.Row31.entry_checked i
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem empty_resolved (i : Nat) (hi : i < GraphRoutes.emptyRootKeys.count) :
    Result (GraphRoutes.emptyRootKeys.entry i) :=
  SharedEmptyKeys.resolved Result empty16 empty19 empty23 empty24 empty25 empty26 empty27 empty28 empty29 empty30 empty31 i hi

#print axioms empty_resolved
end Papers.RationalityTen.GraphFiniteDispatch
