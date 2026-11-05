module
prelude
import GraphInputsRow25Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0294
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 6426076645632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record000_result⟩)
 (.leaf ⟨(25, 6434398013696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 6434406402048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record002_result⟩)
 (.branch 4
 (.leaf ⟨(25, 6434414658304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record003_result⟩)
 (.leaf ⟨(25, 6442727901184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(25, 6443017175040), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record005_result⟩)
 (.branch 7
 (.leaf ⟨(25, 6443256250888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record006_result⟩)
 (.leaf ⟨(25, 6451854573568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(25, 6516279083008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record008_result⟩)
 (.branch 10
 (.leaf ⟨(25, 6524600582144), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record009_result⟩)
 (.leaf ⟨(25, 6602618929184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(25, 6603015290912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record011_result⟩)
 (.branch 13
 (.leaf ⟨(25, 6637012221952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record012_result⟩)
 (.leaf ⟨(25, 6637144342528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(25, 6637210337536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record014_result⟩)
 (.branch 16
 (.leaf ⟨(25, 6674941788192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record015_result⟩)
 (.leaf ⟨(25, 6707409321985), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(25, 6711570071553), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record017_result⟩)
 (.branch 19
 (.leaf ⟨(25, 6727198113792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record018_result⟩)
 (.leaf ⟨(25, 6727206436864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(25, 6752966836480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record020_result⟩)
 (.branch 22
 (.leaf ⟨(25, 6791622623232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record021_result⟩)
 (.leaf ⟨(25, 6791630946304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(25, 6807055532288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record023_result⟩)
 (.leaf ⟨(25, 6823834877952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_result⟩))
 (.branch 26
 (.leaf ⟨(25, 6839899062272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record025_result⟩)
 (.branch 27
 (.leaf ⟨(25, 6840406802688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_result⟩)
 (.leaf ⟨(25, 6840419092480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(25, 6844835693312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record028_result⟩)
 (.branch 30
 (.leaf ⟨(25, 6851076817664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record029_result⟩)
 (.leaf ⟨(25, 6854969426176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(25, 6854981715968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_result⟩)
 (.branch 33
 (.leaf ⟨(25, 6855179896832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record032_result⟩)
 (.leaf ⟨(25, 6857598959616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(25, 6909937647616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record034_result⟩)
 (.branch 36
 (.leaf ⟨(25, 6912018022400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record035_result⟩)
 (.leaf ⟨(25, 6977465942016), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(25, 6982278905856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record037_result⟩)
 (.branch 39
 (.leaf ⟨(25, 6982287228928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record038_result⟩)
 (.leaf ⟨(25, 6983905247232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(25, 6986166960896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record040_result⟩)
 (.branch 42
 (.leaf ⟨(25, 6986447978496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record041_result⟩)
 (.leaf ⟨(25, 6988528353280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(25, 6999458709504), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record043_result⟩)
 (.branch 45
 (.leaf ⟨(25, 7003082653696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record044_result⟩)
 (.leaf ⟨(25, 7003355217920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12472 + i))) 0 46 :=
  interval_of_check _ 0 46 (by decide +kernel)

public theorem complete : Block 12472 12518 :=
  block_of_table results 12472 46 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0294
