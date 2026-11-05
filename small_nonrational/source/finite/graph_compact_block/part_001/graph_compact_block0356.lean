module
prelude
import GraphInputsRow26Part00040Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0356
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 21921915996416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record000_result⟩)
 (.leaf ⟨(26, 21922318649408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 21925963300864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record002_result⟩)
 (.leaf ⟨(26, 21926076614912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 21926085003264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record004_result⟩)
 (.leaf ⟨(26, 21926093259520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 21926613352968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record006_result⟩)
 (.leaf ⟨(26, 21930245752832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 21930640017472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record008_result⟩)
 (.leaf ⟨(26, 21930656662080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 21930774102536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record010_result⟩)
 (.leaf ⟨(26, 21951577850372), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 21951577981952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record012_result⟩)
 (.leaf ⟨(26, 22034866323712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 22043456225536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 22077546512640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record015_result⟩)
 (.leaf ⟨(26, 22077550674176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(26, 22077550723136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record017_result⟩)
 (.leaf ⟨(26, 22077816012832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record018_result⟩))
 (.branch 20
 (.leaf ⟨(26, 22111050580224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record019_result⟩)
 (.leaf ⟨(26, 22111051677728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 22146535473184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record021_result⟩)
 (.leaf ⟨(26, 22146538586176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 22181968888064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record023_result⟩)
 (.leaf ⟨(26, 22181975179328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(26, 22242094285056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record025_result⟩)
 (.leaf ⟨(26, 22250684186880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record026_result⟩))
 (.branch 28
 (.leaf ⟨(26, 22250694656000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record027_result⟩)
 (.leaf ⟨(26, 22259274153984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(26, 22283705991200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record029_result⟩)
 (.leaf ⟨(26, 22283709104192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record030_result⟩))
 (.branch 32
 (.leaf ⟨(26, 22283974393888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 22379264803072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record032_result⟩)
 (.leaf ⟨(26, 22379543674880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record033_result⟩)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf ⟨(26, 22396444672000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record034_result⟩)
 (.leaf ⟨(26, 22396981477376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record035_result⟩))
 (.branch 37
 (.leaf ⟨(26, 22443689312512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record036_result⟩)
 (.leaf ⟨(26, 22443968184320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(26, 22448252666112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record038_result⟩)
 (.leaf ⟨(26, 22448261054464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record039_result⟩))
 (.branch 41
 (.leaf ⟨(26, 22456846794752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record040_result⟩)
 (.leaf ⟨(26, 22457042878528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record041_result⟩))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf ⟨(26, 22464895664384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record042_result⟩)
 (.leaf ⟨(26, 22465029931008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record043_result⟩))
 (.branch 45
 (.leaf ⟨(26, 22465038254080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record044_result⟩)
 (.leaf ⟨(26, 22465498595328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(26, 22482619744256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record046_result⟩)
 (.leaf ⟨(26, 22584628363520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record047_result⟩))
 (.branch 49
 (.leaf ⟨(26, 22594493354048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record048_result⟩)
 (.branch 50
 (.leaf ⟨(26, 22617591980288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record049_result⟩)
 (.leaf ⟨(26, 22686579892288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record050_result⟩))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(26, 22686579900448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record051_result⟩)
 (.leaf ⟨(26, 22687704432896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record052_result⟩))
 (.branch 54
 (.leaf ⟨(26, 22697371242560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record053_result⟩)
 (.leaf ⟨(26, 22722056880384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(26, 22730646782208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record055_result⟩)
 (.leaf ⟨(26, 22730657251328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record056_result⟩))
 (.branch 58
 (.leaf ⟨(26, 22732863504384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record057_result⟩)
 (.branch 59
 (.leaf ⟨(26, 22732871827456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record058_result⟩)
 (.leaf ⟨(26, 22732995624960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record059_result⟩)))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf ⟨(26, 22739236749312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record060_result⟩)
 (.leaf ⟨(26, 22800509239296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record061_result⟩))
 (.branch 63
 (.leaf ⟨(26, 22804405747712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record062_result⟩)
 (.leaf ⟨(26, 22804942553088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record063_result⟩)))
 (.branch 66
 (.branch 65
 (.leaf ⟨(26, 22835378552832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record064_result⟩)
 (.leaf ⟨(26, 22850394161408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record065_result⟩))
 (.branch 67
 (.leaf ⟨(26, 22851929800960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record066_result⟩)
 (.branch 68
 (.leaf ⟨(26, 22851954411648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record067_result⟩)
 (.leaf ⟨(26, 22859506270208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00040.record068_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16131 + i))) 0 69 :=
  interval_of_check _ 0 69 (by decide +kernel)

public theorem complete : Block 16131 16200 :=
  block_of_table results 16131 69 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0356
