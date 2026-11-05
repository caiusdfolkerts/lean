module
prelude
import GraphInputsRow29Part00036Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0470
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 7191532732416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record000_result⟩)
 (.leaf ⟨(29, 7200122634240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 7203466019072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record002_result⟩)
 (.leaf ⟨(29, 7203478048768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 7217986699520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record004_result⟩)
 (.leaf ⟨(29, 7225825361920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 7227088371968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record006_result⟩)
 (.leaf ⟨(29, 7234146861056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 7234415263744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record008_result⟩)
 (.leaf ⟨(29, 7235678273792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 7235690303488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record010_result⟩)
 (.leaf ⟨(29, 7276479906560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 7276492488704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record012_result⟩)
 (.leaf ⟨(29, 7286575599872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 7286707720448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record014_result⟩)
 (.branch 16
 (.leaf ⟨(29, 7286971961600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record015_result⟩)
 (.leaf ⟨(29, 7291512881408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(29, 7293411266816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record017_result⟩)
 (.leaf ⟨(29, 7293417054208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record018_result⟩))
 (.branch 20
 (.leaf ⟨(29, 7293468936208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record019_result⟩)
 (.leaf ⟨(29, 7294542675969), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(29, 7301658314768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record021_result⟩)
 (.leaf ⟨(29, 7301790435344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record022_result⟩))
 (.branch 24
 (.leaf ⟨(29, 7301856495632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record023_result⟩)
 (.leaf ⟨(29, 7302732054529), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(29, 7302732120064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record025_result⟩)
 (.leaf ⟨(29, 7302864175105), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record026_result⟩))
 (.branch 28
 (.leaf ⟨(29, 7304275562496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record027_result⟩)
 (.leaf ⟨(29, 7340904416000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(29, 7340916998144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record029_result⟩)
 (.leaf ⟨(29, 7345201545216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record030_result⟩))
 (.branch 32
 (.leaf ⟨(29, 7424142479616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record031_result⟩)
 (.branch 33
 (.leaf ⟨(29, 7428963831808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record032_result⟩)
 (.leaf ⟨(29, 7433124581376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00036.record033_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20989 + i))) 0 34 :=
  interval_of_check _ 0 34 (by decide +kernel)

public theorem complete : Block 20989 21023 :=
  block_of_table results 20989 34 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0470
