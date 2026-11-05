module
prelude
import GraphInputsRow24Part00096Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0212
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 25178373358080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record000_result⟩)
 (.leaf ⟨(24, 25185839513856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 25185843740672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 25185851803648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record003_result⟩)
 (.leaf ⟨(24, 25185973715200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 25185982103552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 25185983924224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record006_result⟩)
 (.leaf ⟨(24, 25186091141376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 25186493794368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 25190138445824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record009_result⟩)
 (.leaf ⟨(24, 25190251759872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(24, 25190260148224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 25190268404480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record012_result⟩)
 (.leaf ⟨(24, 25190788497928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(24, 25194420897792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 25194815162432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_result⟩)
 (.leaf ⟨(24, 25194831807040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(24, 25194949247496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 25215752995332), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record018_result⟩)
 (.leaf ⟨(24, 25215753126912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(24, 25222350700544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 25224360788224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record021_result⟩)
 (.leaf ⟨(24, 25261126975488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record022_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10838 + i))) 0 23 :=
  interval_of_check _ 0 23 (by decide +kernel)

public theorem complete : Block 10838 10861 :=
  block_of_table results 10838 23 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0212
