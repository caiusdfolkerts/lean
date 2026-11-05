module
prelude
public import Graph13Step09Part000
public import Graph13Step09Part001
public import Graph13Step09Part002
public import Graph13Step09Part003
public import Graph13Step09Part004
public import Graph13Step09Part005
public import Graph13Step09Part006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step09
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 883
noncomputable def dispatch : Table (Nat → Nat) :=
(.branch 384
 (.branch 128
 (.leaf Part000.lookup)
 (.branch 256
 (.leaf Part001.lookup)
 (.leaf Part002.lookup)))
 (.branch 640
 (.branch 512
 (.leaf Part003.lookup)
 (.leaf Part004.lookup))
 (.branch 768
 (.leaf Part005.lookup)
 (.leaf Part006.lookup))))
noncomputable def lookup (i : Nat) : Nat := (dispatch.get i) i
noncomputable def test (i : Nat) : Bool := (List.finRange 45).all fun edge =>
  FastGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level09.entry (Fin.ofNat 883 i)) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level10.entry edge
    (choiceAt (lookup i) edge)
theorem checked : Interval test 0 883 := by
  intro i hlo hhi
  by_cases h0 : i < 384
  · by_cases h1 : i < 128
    · have hlocal := Part000.checked i (by omega) (by omega)
      simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, Part000.test] using hlocal
    · by_cases h2 : i < 256
      · have hlocal := Part001.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, Part001.test] using hlocal
      · have hlocal := Part002.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, Part002.test] using hlocal
  · by_cases h1 : i < 640
    · by_cases h2 : i < 512
      · have hlocal := Part003.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, Part003.test] using hlocal
      · have hlocal := Part004.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, Part004.test] using hlocal
    · by_cases h2 : i < 768
      · have hlocal := Part005.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, Part005.test] using hlocal
      · have hlocal := Part006.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, Part006.test] using hlocal
noncomputable def entry (i : Fin count) : Nat := lookup i.val

noncomputable def choices (i : Fin 883) (edge : Fin 45) :
    Choice 10 2024 24505 := choiceAt (lookup i.val) edge
theorem choices_checked (i : Fin 883) (edge : Fin 45) :
    extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level09.entry i) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level10.entry edge (choices i edge) = true := by
  have hi := checked i.val (Nat.zero_le _) i.isLt
  have he := List.all_eq_true.mp hi edge (List.mem_finRange edge)
  simpa only [choices, Fin.ofNat_val_eq_self, FastGraphCatalogueCheck.extensionCheck_eq] using he
theorem covers_step (hprevious : Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level09.entry i).edges) 9) :
    Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level10.entry i).edges) 10 :=
  covers_step_of_checks TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level09.entry Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level10.entry choices
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level09.entry_checked Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level10.entry_checked choices_checked hprevious

end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step09
