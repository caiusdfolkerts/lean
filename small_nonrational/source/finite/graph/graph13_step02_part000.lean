module
prelude
public import GraphCatalogueData
public import Graph13Frames
public import Graph13Level02
public import Graph13Level03
public import FastGraphCatalogueCheck

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step02.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
noncomputable def table : Table Nat :=
(.branch 1
 (.leaf 11374984462263922843884402421096896229068327205691928075608544923475884518086006146626711119132788929590327688196917873126758934311358149690513734782273418498083480354802549888351451331138265761278541878330540404964986356027562326756724483377388878256524422827888032732907969552666225171050952518156995291432937050416429508845369841158945055939909546621227814082237880708546259588370877106959545605990957464587966851552179364049584130)
 (.leaf 616639146386451627685239421746749633044361871973394386175933175666595072212348184936989870206185570594529361954517649066525099088377763447088916331167139424692435974560284235134853328146813195888002112263403284082818345516680205246206782437378610493892963207553328638473059970364723704434555718403599759941615448131547287187756624670777769705533518355932951251923068355188455877752090746877581430876503842157232134))
noncomputable def lookup (i : Nat) : Nat := table.get i
noncomputable def test (i : Nat) : Bool := (List.finRange 45).all fun edge =>
  FastGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level02.entry (Fin.ofNat 2 i)) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level03.entry edge
    (choiceAt (lookup i) edge)
theorem checked_0 : Interval test 0 2 :=
  interval_of_check test 0 2 (by decide +kernel)

theorem checked : Interval test 0 2 :=
  checked_0
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step02.Part000
