module
prelude
import GraphInputsRow30Part00032Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0760
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 17636824023104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 17640010645568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record001_result⟩)
 (.leaf ⟨(30, 17672222900288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 17706686447616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 17721852960832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record004_result⟩)
 (.leaf ⟨(30, 17775403827200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 17783725326336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 17784129994816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record007_result⟩)
 (.leaf ⟨(30, 17786277470272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(30, 17856532119552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record009_result⟩)
 (.branch 11
 (.leaf ⟨(30, 18143071256960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record010_result⟩)
 (.leaf ⟨(30, 18143305605440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(30, 18181884313600), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 18248657600512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record013_result⟩)
 (.leaf ⟨(30, 18252281413633), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(30, 18253355155456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 18271933858048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record016_result⟩)
 (.leaf ⟨(30, 18272070205440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(30, 18272078528512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 18336033275905), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record019_result⟩)
 (.leaf ⟨(30, 18336503037952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(30, 18370393022464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record021_result⟩)
 (.leaf ⟨(30, 18384771153920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record022_result⟩))
 (.branch 24
 (.leaf ⟨(30, 18406082511104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record023_result⟩)
 (.leaf ⟨(30, 18406350979072), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00032.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24605 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 24605 24630 :=
  block_of_table results 24605 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0760
