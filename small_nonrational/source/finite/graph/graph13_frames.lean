module
prelude
public import Graph13FramesPart000
public import Graph13FramesPart001
public import Graph13FramesPart002
public import Graph13FramesPart003
public import Graph13FramesPart004
public import Graph13FramesPart005
public import Graph13FramesPart006
public import Graph13FramesPart007
public import Graph13FramesPart008
public import Graph13FramesPart009
public import Graph13FramesPart010
public import Graph13FramesPart011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 24505
noncomputable def dispatch : Table (Nat → (Nat × Nat)) :=
(.branch 12288
 (.branch 6144
 (.branch 2048
 (.leaf Part000.lookup)
 (.branch 4096
 (.leaf Part001.lookup)
 (.leaf Part002.lookup)))
 (.branch 8192
 (.leaf Part003.lookup)
 (.branch 10240
 (.leaf Part004.lookup)
 (.leaf Part005.lookup))))
 (.branch 18432
 (.branch 14336
 (.leaf Part006.lookup)
 (.branch 16384
 (.leaf Part007.lookup)
 (.leaf Part008.lookup)))
 (.branch 20480
 (.leaf Part009.lookup)
 (.branch 22528
 (.leaf Part010.lookup)
 (.leaf Part011.lookup)))))
noncomputable def lookup (i : Nat) : (Nat × Nat) := (dispatch.get i) i
noncomputable def test (i : Nat) : Bool := TenGraphEdges.permutationCheck (lookup i).1 (lookup i).2
theorem checked : Interval test 0 24505 := by
  intro i hlo hhi
  by_cases h0 : i < 12288
  · by_cases h1 : i < 6144
    · by_cases h2 : i < 2048
      · have hlocal := Part000.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_pos h2, Part000.test] using hlocal
      · by_cases h3 : i < 4096
        · have hlocal := Part001.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_pos h3, Part001.test] using hlocal
        · have hlocal := Part002.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, if_neg h2, if_neg h3, Part002.test] using hlocal
    · by_cases h2 : i < 8192
      · have hlocal := Part003.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_pos h2, Part003.test] using hlocal
      · by_cases h3 : i < 10240
        · have hlocal := Part004.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_pos h3, Part004.test] using hlocal
        · have hlocal := Part005.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, if_neg h2, if_neg h3, Part005.test] using hlocal
  · by_cases h1 : i < 18432
    · by_cases h2 : i < 14336
      · have hlocal := Part006.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_pos h2, Part006.test] using hlocal
      · by_cases h3 : i < 16384
        · have hlocal := Part007.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_pos h3, Part007.test] using hlocal
        · have hlocal := Part008.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, if_neg h2, if_neg h3, Part008.test] using hlocal
    · by_cases h2 : i < 20480
      · have hlocal := Part009.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, Part009.test] using hlocal
      · by_cases h3 : i < 22528
        · have hlocal := Part010.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_pos h3, Part010.test] using hlocal
        · have hlocal := Part011.checked i (by omega) (by omega)
          simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, if_neg h3, Part011.test] using hlocal
noncomputable def entry (i : Fin count) : (Nat × Nat) := lookup i.val

theorem entry_checked (i : Fin count) :
    TenGraphEdges.permutationCheck (entry i).1 (entry i).2 = true :=
  checked i.val (Nat.zero_le _) i.isLt
noncomputable def vertexBijections (i : Fin count) : GrowthRenaming.Bijection (Fin 10) :=
  TenGraphEdges.checkedBijection (entry i).1 (entry i).2 (entry_checked i)
noncomputable def renamings (i : Fin count) : IncidenceRenaming TenGraphEdges.incidence :=
  TenGraphEdges.toRenaming (vertexBijections i)

end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames
