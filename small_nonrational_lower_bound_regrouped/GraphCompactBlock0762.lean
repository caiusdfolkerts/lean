module
prelude
import GraphInputsRow30Part00034Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0762
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 19650280685568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record000_result⟩)
 (.leaf ⟨(30, 19701694464000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 19710412324864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record002_result⟩)
 (.leaf ⟨(30, 19718337462272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 19729745969152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record004_result⟩)
 (.leaf ⟨(30, 19733906718720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 19742228217856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record006_result⟩)
 (.leaf ⟨(30, 19742624579584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 19748328898560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record008_result⟩)
 (.leaf ⟨(30, 19901414670336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 20193195589632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record010_result⟩)
 (.leaf ⟨(30, 20199436713984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 20278893674496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record012_result⟩)
 (.leaf ⟨(30, 20381377265664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 20385670135808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 20393991634944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record015_result⟩)
 (.leaf ⟨(30, 20412123582720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(30, 20428152143872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record017_result⟩)
 (.leaf ⟨(30, 20688190636032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record018_result⟩))
 (.branch 20
 (.leaf ⟨(30, 20688198959104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record019_result⟩)
 (.leaf ⟨(30, 20688459038720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(30, 20688591159296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record021_result⟩)
 (.leaf ⟨(30, 20690279333888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record022_result⟩))
 (.branch 24
 (.leaf ⟨(30, 20694572204032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record023_result⟩)
 (.leaf ⟨(30, 20694638264320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(30, 20710366920832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record025_result⟩)
 (.leaf ⟨(30, 20711611564032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record026_result⟩))
 (.branch 28
 (.leaf ⟨(30, 20723514998784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record027_result⟩)
 (.leaf ⟨(30, 20724022804480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(30, 20727807868928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record029_result⟩)
 (.leaf ⟨(30, 20727915151360), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record030_result⟩))
 (.branch 32
 (.leaf ⟨(30, 20728072110080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record031_result⟩)
 (.branch 33
 (.leaf ⟨(30, 20728183554048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record032_result⟩)
 (.leaf ⟨(30, 20732612444672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00034.record033_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24663 + i))) 0 34 :=
  interval_of_check _ 0 34 (by decide +kernel)

public theorem complete : Block 24663 24697 :=
  block_of_table results 24663 34 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0762
