module
prelude
import GraphInputsRow30Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0741
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 7186831016192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record000_result⟩)
 (.leaf ⟨(30, 7186831081472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 7187371917313), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record002_result⟩)
 (.leaf ⟨(30, 7187371982848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 7190333702144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record004_result⟩)
 (.leaf ⟨(30, 7190335197440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 7190458927120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record006_result⟩)
 (.leaf ⟨(30, 7191532666881), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 7203478048768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record008_result⟩)
 (.leaf ⟨(30, 7217986699520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 7225825361920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record010_result⟩)
 (.leaf ⟨(30, 7234146861056), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 7234415263744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record012_result⟩)
 (.leaf ⟨(30, 7235678273792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 7235690303488), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record014_result⟩)
 (.leaf ⟨(30, 7276492488704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(30, 7286575599872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record016_result⟩)
 (.leaf ⟨(30, 7293417054208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record017_result⟩))
 (.branch 19
 (.leaf ⟨(30, 7293468936208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record018_result⟩)
 (.leaf ⟨(30, 7294542675969), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(30, 7301658314768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record020_result⟩)
 (.leaf ⟨(30, 7301790435344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record021_result⟩))
 (.branch 23
 (.leaf ⟨(30, 7301856495632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record022_result⟩)
 (.leaf ⟨(30, 7302732054529), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(30, 7302864175105), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record024_result⟩)
 (.leaf ⟨(30, 7304275562496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record025_result⟩))
 (.branch 27
 (.leaf ⟨(30, 7424142479616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record026_result⟩)
 (.leaf ⟨(30, 7428963831808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(30, 7433124581376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record028_result⟩)
 (.leaf ⟨(30, 7478343369344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record029_result⟩))
 (.branch 31
 (.leaf ⟨(30, 7525072437248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record030_result⟩)
 (.branch 32
 (.leaf ⟨(30, 7533641206016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record031_result⟩)
 (.leaf ⟨(30, 7533657850624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00013.record032_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23971 + i))) 0 33 :=
  interval_of_check _ 0 33 (by decide +kernel)

public theorem complete : Block 23971 24004 :=
  block_of_table results 23971 33 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0741
