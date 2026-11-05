module
prelude
import GraphInputsRow26Part00053Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0369
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 25704976613952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record000_result⟩)
 (.leaf ⟨(26, 25705490417664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 25705556477952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record002_result⟩)
 (.leaf ⟨(26, 25705933447232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 25705934503936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record004_result⟩)
 (.leaf ⟨(26, 25705949962304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 25706654335744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 25707056988736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record007_result⟩)
 (.leaf ⟨(26, 25718365110336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 25718432211008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record009_result⟩)
 (.leaf ⟨(26, 25718435088384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 25735595311360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 25735597457408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record012_result⟩)
 (.leaf ⟨(26, 25735603699712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(26, 25735605520384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record014_result⟩)
 (.leaf ⟨(26, 25735997964352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record015_result⟩))
 (.branch 17
 (.leaf ⟨(26, 25736115390528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 25739873356032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record017_result⟩)
 (.leaf ⟨(26, 25739881744384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(26, 25740292653632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record019_result⟩)
 (.leaf ⟨(26, 25740410094088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record020_result⟩))
 (.branch 22
 (.leaf ⟨(26, 25769887940864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record021_result⟩)
 (.leaf ⟨(26, 25769890086912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(26, 25769896329216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record023_result⟩)
 (.leaf ⟨(26, 25769898149888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record024_result⟩))
 (.branch 26
 (.leaf ⟨(26, 25769964210176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record025_result⟩)
 (.branch 27
 (.leaf ⟨(26, 25770005367040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record026_result⟩)
 (.leaf ⟨(26, 25770357694528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(26, 25770360571904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record028_result⟩)
 (.leaf ⟨(26, 25770408020032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record029_result⟩))
 (.branch 31
 (.leaf ⟨(26, 25772085610752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 25772093999104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record031_result⟩)
 (.leaf ⟨(26, 25772102255360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 25772488263744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record033_result⟩)
 (.leaf ⟨(26, 25772504908352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 25772622348808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 25774174373888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record036_result⟩)
 (.leaf ⟨(26, 25774702723592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00053.record037_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16743 + i))) 0 38 :=
  interval_of_check _ 0 38 (by decide +kernel)

public theorem complete : Block 16743 16781 :=
  block_of_table results 16743 38 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0369
