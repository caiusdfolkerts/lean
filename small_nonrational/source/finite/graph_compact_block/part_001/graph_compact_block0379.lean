module
prelude
import GraphInputsRow26Part00063Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0379
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 29689115119744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 29689131894912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record001_result⟩)
 (.leaf ⟨(26, 29691212269696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 29691261554816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 29696782778624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record004_result⟩)
 (.leaf ⟨(26, 29725758603520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 29760118853888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 29765500158208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record007_result⟩)
 (.leaf ⟨(26, 29828836233472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 29829924667648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 29838783037440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record010_result⟩)
 (.leaf ⟨(26, 29894332399872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 29902133010496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 30030464813184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record013_result⟩)
 (.leaf ⟨(26, 30031554414720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 30031554447360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 30236622524544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record016_result⟩)
 (.leaf ⟨(26, 30236725284880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 30236725544976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 30237782116368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record019_result⟩)
 (.leaf ⟨(26, 30241154666752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 30242211238144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record021_result⟩)
 (.leaf ⟨(26, 30305310410768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 30305578914048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record023_result⟩)
 (.leaf ⟨(26, 30309874204672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17114 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 17114 17139 :=
  block_of_table results 17114 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0379
