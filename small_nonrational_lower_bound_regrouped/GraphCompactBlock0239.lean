module
prelude
import GraphInputsRow24Part00123Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0239
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 29276936081664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record000_result⟩)
 (.leaf ⟨(24, 29284368449536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 29284463821056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record002_result⟩)
 (.leaf ⟨(24, 29287785177344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 29292802097280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record004_result⟩)
 (.leaf ⟨(24, 29322144383744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 29353284009984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 29357519142912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record007_result⟩)
 (.leaf ⟨(24, 29549426688000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 29550518110208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record009_result⟩)
 (.leaf ⟨(24, 29690343473408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 29690444124416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 29692489908480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record012_result⟩)
 (.leaf ⟨(24, 29692524499200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(24, 29696685248768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record014_result⟩)
 (.leaf ⟨(24, 29696782778624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record015_result⟩))
 (.branch 17
 (.leaf ⟨(24, 29725758603520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 29725760164096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record017_result⟩)
 (.leaf ⟨(24, 29726815174912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(24, 29757972418816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record019_result⟩)
 (.leaf ⟨(24, 29760118853888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record020_result⟩))
 (.branch 22
 (.leaf ⟨(24, 29764411724032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record021_result⟩)
 (.leaf ⟨(24, 29765500158208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 29826557677824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record023_result⟩)
 (.leaf ⟨(24, 29828836233472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 29829924667648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record025_result⟩)
 (.branch 27
 (.leaf ⟨(24, 29838783037440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record026_result⟩)
 (.leaf ⟨(24, 29894332399872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 29902133010496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record028_result⟩)
 (.leaf ⟨(24, 30031554447360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 30237933453568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 30237935014144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record031_result⟩)
 (.leaf ⟨(24, 30241154666752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(24, 30242246819840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record033_result⟩)
 (.leaf ⟨(24, 30249857847552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record034_result⟩))
 (.branch 36
 (.leaf ⟨(24, 30284217647104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record035_result⟩)
 (.branch 37
 (.leaf ⟨(24, 30305578914048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record036_result⟩)
 (.leaf ⟨(24, 30309874204672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00123.record037_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11462 + i))) 0 38 :=
  interval_of_check _ 0 38 (by decide +kernel)

public theorem complete : Block 11462 11500 :=
  block_of_table results 11462 38 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0239
