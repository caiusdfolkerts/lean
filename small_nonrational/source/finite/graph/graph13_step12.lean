module
prelude
public import Graph13Step12Part000
public import Graph13Step12Part001
public import Graph13Step12Part002
public import Graph13Step12Part003
public import Graph13Step12Part004
public import Graph13Step12Part005
public import Graph13Step12Part006
public import Graph13Step12Part007
public import Graph13Step12Part008
public import Graph13Step12Part009
public import Graph13Step12Part010
public import Graph13Step12Part011
public import Graph13Step12Part012
public import Graph13Step12Part013
public import Graph13Step12Part014
public import Graph13Step12Part015
public import Graph13Step12Part016
public import Graph13Step12Part017
public import Graph13Step12Part018
public import Graph13Step12Part019
public import Graph13Step12Part020
public import Graph13Step12Part021
public import Graph13Step12Part022
public import Graph13Step12Part023
public import Graph13Step12Part024
public import Graph13Step12Part025
public import Graph13Step12Part026
public import Graph13Step12Part027
public import Graph13Step12Part028
public import Graph13Step12Part029
public import Graph13Step12Part030
public import Graph13Step12Part031
public import Graph13Step12Part032
public import Graph13Step12Part033
public import Graph13Step12Part034
public import Graph13Step12Part035
public import Graph13Step12Part036
public import Graph13Step12Part037
public import Graph13Step12Part038
public import Graph13Step12Part039
public import Graph13Step12Part040
public import Graph13Step12Part041
public import Graph13Step12Part042
public import Graph13Step12Part043
public import Graph13Step12Part044
public import Graph13Step12Part045
public import Graph13Step12Part046
public import Graph13Step12Part047
public import Graph13Step12Part048
public import Graph13Step12Part049
public import Graph13Step12Part050
public import Graph13Step12Part051
public import Graph13Step12Part052
public import Graph13Step12Part053
public import Graph13Step12Part054
public import Graph13Step12Part055
public import Graph13Step12Part056
public import Graph13Step12Part057
public import Graph13Step12Part058
public import Graph13Step12Part059
public import Graph13Step12Part060
public import Graph13Step12Part061
public import Graph13Step12Part062
public import Graph13Step12Part063
public import Graph13Step12Part064
public import Graph13Step12Part065

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step12
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 8333
noncomputable def dispatch : Table (Nat → Nat) :=
(.branch 4224
 (.branch 2048
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
 (.branch 3072
 (.branch 2560
 (.branch 2304
 (.branch 2176
 (.leaf Part016.lookup)
 (.leaf Part017.lookup))
 (.branch 2432
 (.leaf Part018.lookup)
 (.leaf Part019.lookup)))
 (.branch 2816
 (.branch 2688
 (.leaf Part020.lookup)
 (.leaf Part021.lookup))
 (.branch 2944
 (.leaf Part022.lookup)
 (.leaf Part023.lookup))))
 (.branch 3584
 (.branch 3328
 (.branch 3200
 (.leaf Part024.lookup)
 (.leaf Part025.lookup))
 (.branch 3456
 (.leaf Part026.lookup)
 (.leaf Part027.lookup)))
 (.branch 3840
 (.branch 3712
 (.leaf Part028.lookup)
 (.leaf Part029.lookup))
 (.branch 3968
 (.leaf Part030.lookup)
 (.branch 4096
 (.leaf Part031.lookup)
 (.leaf Part032.lookup)))))))
 (.branch 6272
 (.branch 5248
 (.branch 4736
 (.branch 4480
 (.branch 4352
 (.leaf Part033.lookup)
 (.leaf Part034.lookup))
 (.branch 4608
 (.leaf Part035.lookup)
 (.leaf Part036.lookup)))
 (.branch 4992
 (.branch 4864
 (.leaf Part037.lookup)
 (.leaf Part038.lookup))
 (.branch 5120
 (.leaf Part039.lookup)
 (.leaf Part040.lookup))))
 (.branch 5760
 (.branch 5504
 (.branch 5376
 (.leaf Part041.lookup)
 (.leaf Part042.lookup))
 (.branch 5632
 (.leaf Part043.lookup)
 (.leaf Part044.lookup)))
 (.branch 6016
 (.branch 5888
 (.leaf Part045.lookup)
 (.leaf Part046.lookup))
 (.branch 6144
 (.leaf Part047.lookup)
 (.leaf Part048.lookup)))))
 (.branch 7296
 (.branch 6784
 (.branch 6528
 (.branch 6400
 (.leaf Part049.lookup)
 (.leaf Part050.lookup))
 (.branch 6656
 (.leaf Part051.lookup)
 (.leaf Part052.lookup)))
 (.branch 7040
 (.branch 6912
 (.leaf Part053.lookup)
 (.leaf Part054.lookup))
 (.branch 7168
 (.leaf Part055.lookup)
 (.leaf Part056.lookup))))
 (.branch 7808
 (.branch 7552
 (.branch 7424
 (.leaf Part057.lookup)
 (.leaf Part058.lookup))
 (.branch 7680
 (.leaf Part059.lookup)
 (.leaf Part060.lookup)))
 (.branch 8064
 (.branch 7936
 (.leaf Part061.lookup)
 (.leaf Part062.lookup))
 (.branch 8192
 (.leaf Part063.lookup)
 (.branch 8320
 (.leaf Part064.lookup)
 (.leaf Part065.lookup))))))))
noncomputable def lookup (i : Nat) : Nat := (dispatch.get i) i
noncomputable def test (i : Nat) : Bool := (List.finRange 45).all fun edge =>
  FastGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12.entry (Fin.ofNat 8333 i)) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level13.entry edge
    (choiceAt (lookup i) edge)
theorem checked : Interval test 0 8333 := by
  intro i hlo hhi
  by_cases h0 : i < 4224
  · by_cases h1 : i < 2048
    · by_cases h2 : i < 1024
      · by_cases h3 : i < 512
        · by_cases h4 : i < 256
          · by_cases h5 : i < 128
            · have hlocal := Part000.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, Part000.test] using hlocal
            · have hlocal := Part001.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_neg h5, Part001.test] using hlocal
          · by_cases h5 : i < 384
            · have hlocal := Part002.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_neg h4, if_pos h5, Part002.test] using hlocal
            · have hlocal := Part003.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_neg h4, if_neg h5, Part003.test] using hlocal
        · by_cases h4 : i < 768
          · by_cases h5 : i < 640
            · have hlocal := Part004.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_neg h3, if_pos h4, if_pos h5, Part004.test] using hlocal
            · have hlocal := Part005.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_neg h3, if_pos h4, if_neg h5, Part005.test] using hlocal
          · by_cases h5 : i < 896
            · have hlocal := Part006.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_neg h3, if_neg h4, if_pos h5, Part006.test] using hlocal
            · have hlocal := Part007.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, if_neg h3, if_neg h4, if_neg h5, Part007.test] using hlocal
      · by_cases h3 : i < 1536
        · by_cases h4 : i < 1280
          · by_cases h5 : i < 1152
            · have hlocal := Part008.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_pos h3, if_pos h4, if_pos h5, Part008.test] using hlocal
            · have hlocal := Part009.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_pos h3, if_pos h4, if_neg h5, Part009.test] using hlocal
          · by_cases h5 : i < 1408
            · have hlocal := Part010.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_pos h3, if_neg h4, if_pos h5, Part010.test] using hlocal
            · have hlocal := Part011.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_pos h3, if_neg h4, if_neg h5, Part011.test] using hlocal
        · by_cases h4 : i < 1792
          · by_cases h5 : i < 1664
            · have hlocal := Part012.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_neg h3, if_pos h4, if_pos h5, Part012.test] using hlocal
            · have hlocal := Part013.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_neg h3, if_pos h4, if_neg h5, Part013.test] using hlocal
          · by_cases h5 : i < 1920
            · have hlocal := Part014.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, Part014.test] using hlocal
            · have hlocal := Part015.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, Part015.test] using hlocal
    · by_cases h2 : i < 3072
      · by_cases h3 : i < 2560
        · by_cases h4 : i < 2304
          · by_cases h5 : i < 2176
            · have hlocal := Part016.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, Part016.test] using hlocal
            · have hlocal := Part017.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_pos h3, if_pos h4, if_neg h5, Part017.test] using hlocal
          · by_cases h5 : i < 2432
            · have hlocal := Part018.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_pos h3, if_neg h4, if_pos h5, Part018.test] using hlocal
            · have hlocal := Part019.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_pos h3, if_neg h4, if_neg h5, Part019.test] using hlocal
        · by_cases h4 : i < 2816
          · by_cases h5 : i < 2688
            · have hlocal := Part020.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_neg h3, if_pos h4, if_pos h5, Part020.test] using hlocal
            · have hlocal := Part021.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_neg h3, if_pos h4, if_neg h5, Part021.test] using hlocal
          · by_cases h5 : i < 2944
            · have hlocal := Part022.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_neg h3, if_neg h4, if_pos h5, Part022.test] using hlocal
            · have hlocal := Part023.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, if_neg h3, if_neg h4, if_neg h5, Part023.test] using hlocal
      · by_cases h3 : i < 3584
        · by_cases h4 : i < 3328
          · by_cases h5 : i < 3200
            · have hlocal := Part024.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4, if_pos h5, Part024.test] using hlocal
            · have hlocal := Part025.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4, if_neg h5, Part025.test] using hlocal
          · by_cases h5 : i < 3456
            · have hlocal := Part026.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_pos h3, if_neg h4, if_pos h5, Part026.test] using hlocal
            · have hlocal := Part027.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_pos h3, if_neg h4, if_neg h5, Part027.test] using hlocal
        · by_cases h4 : i < 3840
          · by_cases h5 : i < 3712
            · have hlocal := Part028.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_pos h5, Part028.test] using hlocal
            · have hlocal := Part029.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg h5, Part029.test] using hlocal
          · by_cases h5 : i < 3968
            · have hlocal := Part030.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, Part030.test] using hlocal
            · by_cases h6 : i < 4096
              · have hlocal := Part031.checked i (by omega) (by omega)
                simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, Part031.test] using hlocal
              · have hlocal := Part032.checked i (by omega) (by omega)
                simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, Part032.test] using hlocal
  · by_cases h1 : i < 6272
    · by_cases h2 : i < 5248
      · by_cases h3 : i < 4736
        · by_cases h4 : i < 4480
          · by_cases h5 : i < 4352
            · have hlocal := Part033.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, Part033.test] using hlocal
            · have hlocal := Part034.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_neg h5, Part034.test] using hlocal
          · by_cases h5 : i < 4608
            · have hlocal := Part035.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_pos h3, if_neg h4, if_pos h5, Part035.test] using hlocal
            · have hlocal := Part036.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_pos h3, if_neg h4, if_neg h5, Part036.test] using hlocal
        · by_cases h4 : i < 4992
          · by_cases h5 : i < 4864
            · have hlocal := Part037.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_neg h3, if_pos h4, if_pos h5, Part037.test] using hlocal
            · have hlocal := Part038.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_neg h3, if_pos h4, if_neg h5, Part038.test] using hlocal
          · by_cases h5 : i < 5120
            · have hlocal := Part039.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_neg h3, if_neg h4, if_pos h5, Part039.test] using hlocal
            · have hlocal := Part040.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, if_neg h3, if_neg h4, if_neg h5, Part040.test] using hlocal
      · by_cases h3 : i < 5760
        · by_cases h4 : i < 5504
          · by_cases h5 : i < 5376
            · have hlocal := Part041.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_pos h3, if_pos h4, if_pos h5, Part041.test] using hlocal
            · have hlocal := Part042.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_pos h3, if_pos h4, if_neg h5, Part042.test] using hlocal
          · by_cases h5 : i < 5632
            · have hlocal := Part043.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_pos h3, if_neg h4, if_pos h5, Part043.test] using hlocal
            · have hlocal := Part044.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_pos h3, if_neg h4, if_neg h5, Part044.test] using hlocal
        · by_cases h4 : i < 6016
          · by_cases h5 : i < 5888
            · have hlocal := Part045.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_neg h3, if_pos h4, if_pos h5, Part045.test] using hlocal
            · have hlocal := Part046.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_neg h3, if_pos h4, if_neg h5, Part046.test] using hlocal
          · by_cases h5 : i < 6144
            · have hlocal := Part047.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, Part047.test] using hlocal
            · have hlocal := Part048.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, Part048.test] using hlocal
    · by_cases h2 : i < 7296
      · by_cases h3 : i < 6784
        · by_cases h4 : i < 6528
          · by_cases h5 : i < 6400
            · have hlocal := Part049.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, Part049.test] using hlocal
            · have hlocal := Part050.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_pos h3, if_pos h4, if_neg h5, Part050.test] using hlocal
          · by_cases h5 : i < 6656
            · have hlocal := Part051.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_pos h3, if_neg h4, if_pos h5, Part051.test] using hlocal
            · have hlocal := Part052.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_pos h3, if_neg h4, if_neg h5, Part052.test] using hlocal
        · by_cases h4 : i < 7040
          · by_cases h5 : i < 6912
            · have hlocal := Part053.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_pos h4, if_pos h5, Part053.test] using hlocal
            · have hlocal := Part054.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_pos h4, if_neg h5, Part054.test] using hlocal
          · by_cases h5 : i < 7168
            · have hlocal := Part055.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_neg h4, if_pos h5, Part055.test] using hlocal
            · have hlocal := Part056.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, if_neg h3, if_neg h4, if_neg h5, Part056.test] using hlocal
      · by_cases h3 : i < 7808
        · by_cases h4 : i < 7552
          · by_cases h5 : i < 7424
            · have hlocal := Part057.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4, if_pos h5, Part057.test] using hlocal
            · have hlocal := Part058.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4, if_neg h5, Part058.test] using hlocal
          · by_cases h5 : i < 7680
            · have hlocal := Part059.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg h4, if_pos h5, Part059.test] using hlocal
            · have hlocal := Part060.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg h4, if_neg h5, Part060.test] using hlocal
        · by_cases h4 : i < 8064
          · by_cases h5 : i < 7936
            · have hlocal := Part061.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_pos h5, Part061.test] using hlocal
            · have hlocal := Part062.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg h5, Part062.test] using hlocal
          · by_cases h5 : i < 8192
            · have hlocal := Part063.checked i (by omega) (by omega)
              simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, Part063.test] using hlocal
            · by_cases h6 : i < 8320
              · have hlocal := Part064.checked i (by omega) (by omega)
                simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6, Part064.test] using hlocal
              · have hlocal := Part065.checked i (by omega) (by omega)
                simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, Part065.test] using hlocal
noncomputable def entry (i : Fin count) : Nat := lookup i.val

noncomputable def choices (i : Fin 8333) (edge : Fin 45) :
    Choice 10 13974 24505 := choiceAt (lookup i.val) edge
theorem choices_checked (i : Fin 8333) (edge : Fin 45) :
    extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12.entry i) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level13.entry edge (choices i edge) = true := by
  have hi := checked i.val (Nat.zero_le _) i.isLt
  have he := List.all_eq_true.mp hi edge (List.mem_finRange edge)
  simpa only [choices, Fin.ofNat_val_eq_self, FastGraphCatalogueCheck.extensionCheck_eq] using he
theorem covers_step (hprevious : Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12.entry i).edges) 12) :
    Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level13.entry i).edges) 13 :=
  covers_step_of_checks TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12.entry Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level13.entry choices
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12.entry_checked Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level13.entry_checked choices_checked hprevious

end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step12
