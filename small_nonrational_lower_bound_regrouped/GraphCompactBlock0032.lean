module
prelude
import GraphInputsRow16Part00032Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0032
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 30477243449344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record000_result⟩)
 (.leaf ⟨(16, 30897797660672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 30897805983744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record002_result⟩)
 (.branch 4
 (.leaf ⟨(16, 30899413532672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record003_result⟩)
 (.leaf ⟨(16, 30901822062848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(16, 30901826289664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record005_result⟩)
 (.branch 7
 (.leaf ⟨(16, 30901958410240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record006_result⟩)
 (.leaf ⟨(16, 30901966733312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(16, 30902164914176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record008_result⟩)
 (.branch 10
 (.leaf ⟨(16, 30903708483584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record009_result⟩)
 (.leaf ⟨(16, 30904236965888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(16, 30904245288960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record011_result⟩)
 (.branch 13
 (.leaf ⟨(16, 30904748670976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record012_result⟩)
 (.leaf ⟨(16, 30910147788800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(16, 30913334411264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 30916727537664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record015_result⟩)
 (.leaf ⟨(16, 30917495160832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(16, 30917627281408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record017_result⟩)
 (.branch 19
 (.leaf ⟨(16, 30936222679040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record018_result⟩)
 (.leaf ⟨(16, 30945039630336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(16, 30963703775488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record020_result⟩)
 (.branch 22
 (.leaf ⟨(16, 30981915443456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record021_result⟩)
 (.leaf ⟨(16, 30981926952960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(16, 31007626559488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record023_result⟩)
 (.leaf ⟨(16, 31008096264192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record024_result⟩))
 (.branch 26
 (.leaf ⟨(16, 31010944262144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record025_result⟩)
 (.branch 27
 (.leaf ⟨(16, 31016212299776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record026_result⟩)
 (.leaf ⟨(16, 31016682004480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(16, 31016979275776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record028_result⟩)
 (.branch 30
 (.leaf ⟨(16, 31016980316160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record029_result⟩)
 (.leaf ⟨(16, 31031433437184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(16, 31031697678336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record031_result⟩)
 (.branch 33
 (.leaf ⟨(16, 31042422440960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record032_result⟩)
 (.leaf ⟨(16, 31050537566208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(16, 31050743029760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record034_result⟩)
 (.branch 36
 (.leaf ⟨(16, 31050743940096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record035_result⟩)
 (.leaf ⟨(16, 31051338482176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(16, 31073393197056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record037_result⟩)
 (.branch 39
 (.leaf ⟨(16, 31109728501760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record038_result⟩)
 (.leaf ⟨(16, 31109992742912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(16, 31110001065984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record040_result⟩)
 (.branch 42
 (.leaf ⟨(16, 31110768689152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record041_result⟩)
 (.leaf ⟨(16, 31384971280640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(16, 31384982790144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record043_result⟩)
 (.branch 45
 (.leaf ⟨(16, 31385239748608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record044_result⟩)
 (.leaf ⟨(16, 31385248071680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00032.record045_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1794 + i))) 0 46 :=
  interval_of_check _ 0 46 (by decide +kernel)

public theorem complete : Block 1794 1840 :=
  block_of_table results 1794 46 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0032
