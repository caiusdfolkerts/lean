module
prelude
public import Graph13Step11Part000
public import Graph13Step11Part001
public import Graph13Step11Part002
public import Graph13Step11Part003
public import Graph13Step11Part004
public import Graph13Step11Part005
public import Graph13Step11Part006
public import Graph13Step11Part007
public import Graph13Step11Part008
public import Graph13Step11Part009
public import Graph13Step11Part010
public import Graph13Step11Part011
public import Graph13Step11Part012
public import Graph13Step11Part013
public import Graph13Step11Part014
public import Graph13Step11Part015
public import Graph13Step11Part016
public import Graph13Step11Part017
public import Graph13Step11Part018
public import Graph13Step11Part019
public import Graph13Step11Part020
public import Graph13Step11Part021
public import Graph13Step11Part022
public import Graph13Step11Part023
public import Graph13Step11Part024
public import Graph13Step11Part025
public import Graph13Step11Part026
public import Graph13Step11Part027
public import Graph13Step11Part028
public import Graph13Step11Part029
public import Graph13Step11Part030
public import Graph13Step11Part031
public import Graph13Step11Part032
public import Graph13Step11Part033

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step11
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 4319
noncomputable def dispatch : Table (Nat → Nat) :=
(.branch 2176
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
 (.branch 2048
 (.leaf Part015.lookup)
 (.leaf Part016.lookup))))))
 (.branch 3200
 (.branch 2688
 (.branch 2432
 (.branch 2304
 (.leaf Part017.lookup)
 (.leaf Part018.lookup))
 (.branch 2560
 (.leaf Part019.lookup)
 (.leaf Part020.lookup)))
 (.branch 2944
 (.branch 2816
 (.leaf Part021.lookup)
 (.leaf Part022.lookup))
 (.branch 3072
 (.leaf Part023.lookup)
 (.leaf Part024.lookup))))
 (.branch 3712
 (.branch 3456
 (.branch 3328
 (.leaf Part025.lookup)
 (.leaf Part026.lookup))
 (.branch 3584
 (.leaf Part027.lookup)
 (.leaf Part028.lookup)))
 (.branch 3968
 (.branch 3840
 (.leaf Part029.lookup)
 (.leaf Part030.lookup))
 (.branch 4096
 (.leaf Part031.lookup)
 (.branch 4224
 (.leaf Part032.lookup)
 (.leaf Part033.lookup)))))))
noncomputable def lookup (i : Nat) : Nat := (dispatch.get i) i
noncomputable def test (i : Nat) : Bool := (List.finRange 45).all fun edge =>
  FastGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11.entry (Fin.ofNat 4319 i)) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12.entry edge
    (choiceAt (lookup i) edge)
theorem checked : Interval test 0 4319 := by
  intro i hlo hhi
  by_cases h0 : i < 2176
  · by_cases h1 : i < 1024
    · by_cases h2 : i < 512
      · by_cases h3 : i < 256
        · by_cases h4 : i < 128
          · have hlocal := Part000.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, Part000.test] using hlocal
          · have hlocal := Part001.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_neg h4, Part001.test] using hlocal
        · by_cases h4 : i < 384
          · have hlocal := Part002.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_neg h3, if_pos h4, Part002.test] using hlocal
          · have hlocal := Part003.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_neg h3, if_neg h4, Part003.test] using hlocal
      · by_cases h3 : i < 768
        · by_cases h4 : i < 640
          · have hlocal := Part004.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_pos h3, if_pos h4, Part004.test] using hlocal
          · have hlocal := Part005.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_pos h3, if_neg h4, Part005.test] using hlocal
        · by_cases h4 : i < 896
          · have hlocal := Part006.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_neg h3, if_pos h4, Part006.test] using hlocal
          · have hlocal := Part007.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_neg h3, if_neg h4, Part007.test] using hlocal
    · by_cases h2 : i < 1536
      · by_cases h3 : i < 1280
        · by_cases h4 : i < 1152
          · have hlocal := Part008.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_pos h3, if_pos h4, Part008.test] using hlocal
          · have hlocal := Part009.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_pos h3, if_neg h4, Part009.test] using hlocal
        · by_cases h4 : i < 1408
          · have hlocal := Part010.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_neg h3, if_pos h4, Part010.test] using hlocal
          · have hlocal := Part011.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_neg h3, if_neg h4, Part011.test] using hlocal
      · by_cases h3 : i < 1792
        · by_cases h4 : i < 1664
          · have hlocal := Part012.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4, Part012.test] using hlocal
          · have hlocal := Part013.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_pos h3, if_neg h4, Part013.test] using hlocal
        · by_cases h4 : i < 1920
          · have hlocal := Part014.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, Part014.test] using hlocal
          · by_cases h5 : i < 2048
            · have hlocal := Part015.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, Part015.test] using hlocal
            · have hlocal := Part016.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, Part016.test] using hlocal
  · by_cases h1 : i < 3200
    · by_cases h2 : i < 2688
      · by_cases h3 : i < 2432
        · by_cases h4 : i < 2304
          · have hlocal := Part017.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, Part017.test] using hlocal
          · have hlocal := Part018.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_pos h3, if_neg h4, Part018.test] using hlocal
        · by_cases h4 : i < 2560
          · have hlocal := Part019.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_neg h3, if_pos h4, Part019.test] using hlocal
          · have hlocal := Part020.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_neg h3, if_neg h4, Part020.test] using hlocal
      · by_cases h3 : i < 2944
        · by_cases h4 : i < 2816
          · have hlocal := Part021.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_pos h3, if_pos h4, Part021.test] using hlocal
          · have hlocal := Part022.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_pos h3, if_neg h4, Part022.test] using hlocal
        · by_cases h4 : i < 3072
          · have hlocal := Part023.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_neg h3, if_pos h4, Part023.test] using hlocal
          · have hlocal := Part024.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_neg h3, if_neg h4, Part024.test] using hlocal
    · by_cases h2 : i < 3712
      · by_cases h3 : i < 3456
        · by_cases h4 : i < 3328
          · have hlocal := Part025.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_pos h3, if_pos h4, Part025.test] using hlocal
          · have hlocal := Part026.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_pos h3, if_neg h4, Part026.test] using hlocal
        · by_cases h4 : i < 3584
          · have hlocal := Part027.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_pos h4, Part027.test] using hlocal
          · have hlocal := Part028.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_neg h4, Part028.test] using hlocal
      · by_cases h3 : i < 3968
        · by_cases h4 : i < 3840
          · have hlocal := Part029.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4, Part029.test] using hlocal
          · have hlocal := Part030.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg h4, Part030.test] using hlocal
        · by_cases h4 : i < 4096
          · have hlocal := Part031.checked i (by omega) (by omega)
            simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, Part031.test] using hlocal
          · by_cases h5 : i < 4224
            · have hlocal := Part032.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, Part032.test] using hlocal
            · have hlocal := Part033.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, Part033.test] using hlocal
noncomputable def entry (i : Fin count) : Nat := lookup i.val

noncomputable def choices (i : Fin 4319) (edge : Fin 45) :
    Choice 10 8333 24505 := choiceAt (lookup i.val) edge
theorem choices_checked (i : Fin 4319) (edge : Fin 45) :
    extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11.entry i) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12.entry edge (choices i edge) = true := by
  have hi := checked i.val (Nat.zero_le _) i.isLt
  have he := List.all_eq_true.mp hi edge (List.mem_finRange edge)
  simpa only [choices, Fin.ofNat_val_eq_self, FastGraphCatalogueCheck.extensionCheck_eq] using he
theorem covers_step (hprevious : Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11.entry i).edges) 11) :
    Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12.entry i).edges) 12 :=
  covers_step_of_checks TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11.entry Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12.entry choices
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11.entry_checked Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12.entry_checked choices_checked hprevious

end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step11
