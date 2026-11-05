module
prelude
import GraphInputsRow30Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0737
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 6379377131520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record000_result⟩)
 (.leaf ⟨(30, 6379905483264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 6379913871360), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 6413204062208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record003_result⟩)
 (.leaf ⟨(30, 6425565003776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(30, 6425825018112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record005_result⟩)
 (.leaf ⟨(30, 6425837307904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record006_result⟩))
 (.branch 8
 (.leaf ⟨(30, 6426076645632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 6434398013696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record008_result⟩)
 (.leaf ⟨(30, 6434406402048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 6434414658304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record010_result⟩)
 (.leaf ⟨(30, 6442727901184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 6443017175040), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 6443256250888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record013_result⟩)
 (.leaf ⟨(30, 6451854573568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(30, 6516279083008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 6524600582144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record016_result⟩)
 (.leaf ⟨(30, 6602618929184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(30, 6603015290912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 6615900143648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record019_result⟩)
 (.leaf ⟨(30, 6637012221952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23897 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 23897 23918 :=
  block_of_table results 23897 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0737
