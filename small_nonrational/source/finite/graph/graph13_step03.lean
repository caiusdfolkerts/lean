module
prelude
public import Graph13Step03Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step03
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 5
noncomputable def dispatch : Table (Nat → Nat) :=
(.leaf Part000.lookup)
noncomputable def lookup (i : Nat) : Nat := (dispatch.get i) i
noncomputable def test (i : Nat) : Bool := (List.finRange 45).all fun edge =>
  FastGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level03.entry (Fin.ofNat 5 i)) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level04.entry edge
    (choiceAt (lookup i) edge)
theorem checked : Interval test 0 5 := by
  intro i hlo hhi
  have hlocal := Part000.checked i (by omega) (by omega)
  simpa only [test, lookup, dispatch, Table.get, Part000.test] using hlocal
noncomputable def entry (i : Fin count) : Nat := lookup i.val

noncomputable def choices (i : Fin 5) (edge : Fin 45) :
    Choice 10 11 24505 := choiceAt (lookup i.val) edge
theorem choices_checked (i : Fin 5) (edge : Fin 45) :
    extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level03.entry i) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level04.entry edge (choices i edge) = true := by
  have hi := checked i.val (Nat.zero_le _) i.isLt
  have he := List.all_eq_true.mp hi edge (List.mem_finRange edge)
  simpa only [choices, Fin.ofNat_val_eq_self, FastGraphCatalogueCheck.extensionCheck_eq] using he
theorem covers_step (hprevious : Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level03.entry i).edges) 3) :
    Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level04.entry i).edges) 4 :=
  covers_step_of_checks TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level03.entry Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level04.entry choices
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level03.entry_checked Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level04.entry_checked choices_checked hprevious

end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step03
