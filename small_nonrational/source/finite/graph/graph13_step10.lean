module
prelude
public import Graph13Step10Part000
public import Graph13Step10Part001
public import Graph13Step10Part002
public import Graph13Step10Part003
public import Graph13Step10Part004
public import Graph13Step10Part005
public import Graph13Step10Part006
public import Graph13Step10Part007
public import Graph13Step10Part008
public import Graph13Step10Part009
public import Graph13Step10Part010
public import Graph13Step10Part011
public import Graph13Step10Part012
public import Graph13Step10Part013
public import Graph13Step10Part014
public import Graph13Step10Part015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step10
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 2024
noncomputable def dispatch : Table (Nat → Nat) :=
(.branch 1024
 (.branch 512
 (.branch 256
 (.branch 128
 (.leaf Part000.lookup)
 (.leaf Part001.lookup))
 (.branch 384
 (.leaf Part002.lookup)
 (.leaf Part003.lookup)))
 (.branch 768
 (.branch 640
 (.leaf Part004.lookup)
 (.leaf Part005.lookup))
 (.branch 896
 (.leaf Part006.lookup)
 (.leaf Part007.lookup))))
 (.branch 1536
 (.branch 1280
 (.branch 1152
 (.leaf Part008.lookup)
 (.leaf Part009.lookup))
 (.branch 1408
 (.leaf Part010.lookup)
 (.leaf Part011.lookup)))
 (.branch 1792
 (.branch 1664
 (.leaf Part012.lookup)
 (.leaf Part013.lookup))
 (.branch 1920
 (.leaf Part014.lookup)
 (.leaf Part015.lookup)))))
noncomputable def lookup (i : Nat) : Nat := (dispatch.get i) i
noncomputable def test (i : Nat) : Bool := (List.finRange 45).all fun edge =>
  FastGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level10.entry (Fin.ofNat 2024 i)) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11.entry edge
    (choiceAt (lookup i) edge)
theorem checked : Interval test 0 2024 := by
  intro i hlo hhi
  by_cases h0 : i < 1024
  · by_cases h1 : i < 512
    · by_cases h2 : i < 256
      · by_cases h3 : i < 128
        · have hlocal := Part000.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_pos h3, Part000.test] using hlocal
        · have hlocal := Part001.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_neg h3, Part001.test] using hlocal
      · by_cases h3 : i < 384
        · have hlocal := Part002.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_pos h3, Part002.test] using hlocal
        · have hlocal := Part003.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_neg h3, Part003.test] using hlocal
    · by_cases h2 : i < 768
      · by_cases h3 : i < 640
        · have hlocal := Part004.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_pos h3, Part004.test] using hlocal
        · have hlocal := Part005.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_neg h3, Part005.test] using hlocal
      · by_cases h3 : i < 896
        · have hlocal := Part006.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_pos h3, Part006.test] using hlocal
        · have hlocal := Part007.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_neg h3, Part007.test] using hlocal
  · by_cases h1 : i < 1536
    · by_cases h2 : i < 1280
      · by_cases h3 : i < 1152
        · have hlocal := Part008.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_pos h3, Part008.test] using hlocal
        · have hlocal := Part009.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_neg h3, Part009.test] using hlocal
      · by_cases h3 : i < 1408
        · have hlocal := Part010.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_pos h3, Part010.test] using hlocal
        · have hlocal := Part011.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_neg h3, Part011.test] using hlocal
    · by_cases h2 : i < 1792
      · by_cases h3 : i < 1664
        · have hlocal := Part012.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_pos h3, Part012.test] using hlocal
        · have hlocal := Part013.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_neg h3, Part013.test] using hlocal
      · by_cases h3 : i < 1920
        · have hlocal := Part014.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_pos h3, Part014.test] using hlocal
        · have hlocal := Part015.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3, Part015.test] using hlocal
noncomputable def entry (i : Fin count) : Nat := lookup i.val

noncomputable def choices (i : Fin 2024) (edge : Fin 45) :
    Choice 10 4319 24505 := choiceAt (lookup i.val) edge
theorem choices_checked (i : Fin 2024) (edge : Fin 45) :
    extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level10.entry i) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11.entry edge (choices i edge) = true := by
  have hi := checked i.val (Nat.zero_le _) i.isLt
  have he := List.all_eq_true.mp hi edge (List.mem_finRange edge)
  simpa only [choices, Fin.ofNat_val_eq_self, FastGraphCatalogueCheck.extensionCheck_eq] using he
theorem covers_step (hprevious : Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level10.entry i).edges) 10) :
    Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11.entry i).edges) 11 :=
  covers_step_of_checks TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level10.entry Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11.entry choices
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level10.entry_checked Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11.entry_checked choices_checked hprevious

end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step10
