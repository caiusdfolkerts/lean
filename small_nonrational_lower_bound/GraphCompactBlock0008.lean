module
prelude
import GraphInputsRow16Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0008
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 31
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 14676197998592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 14676201054464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record001_result⟩)
 (.leaf ⟨(16, 14676721141792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 14678868623361), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record003_result⟩)
 (.leaf ⟨(16, 14680412129536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 14680755109888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record005_result⟩)
 (.leaf ⟨(16, 14699659952384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(16, 14699664179200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record007_result⟩)
 (.leaf ⟨(16, 14699672372224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record008_result⟩))
 (.branch 10
 (.leaf ⟨(16, 14699804492800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record009_result⟩)
 (.leaf ⟨(16, 14700465095168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(16, 14701744553984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record011_result⟩)
 (.leaf ⟨(16, 14701752747008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record012_result⟩))
 (.branch 14
 (.leaf ⟨(16, 14701950017536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record013_result⟩)
 (.leaf ⟨(16, 14701950927872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record014_result⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨(16, 14726119047168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record015_result⟩)
 (.leaf ⟨(16, 14729693135104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record016_result⟩))
 (.branch 18
 (.leaf ⟨(16, 14729697361920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record017_result⟩)
 (.leaf ⟨(16, 14729763422208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record018_result⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨(16, 14729770704896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record019_result⟩)
 (.leaf ⟨(16, 14729895542784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record020_result⟩))
 (.branch 22
 (.leaf ⟨(16, 14729902825472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record021_result⟩)
 (.leaf ⟨(16, 14729993527552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record022_result⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨(16, 14730530398208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record023_result⟩)
 (.leaf ⟨(16, 14730531438592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record024_result⟩))
 (.branch 26
 (.leaf ⟨(16, 14776995512320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record025_result⟩)
 (.leaf ⟨(16, 14779277189120), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record026_result⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨(16, 14783834300416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record027_result⟩)
 (.leaf ⟨(16, 14939273101568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record028_result⟩))
 (.branch 30
 (.leaf ⟨(16, 14939553013760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record029_result⟩)
 (.leaf ⟨(16, 14939809972224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record030_result⟩))))))
 (.branch 47
 (.branch 39
 (.branch 35
 (.branch 33
 (.branch 32
 (.leaf ⟨(16, 14939818295296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record031_result⟩)
 (.leaf ⟨(16, 14986797654272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record032_result⟩))
 (.branch 34
 (.leaf ⟨(16, 15003977523200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record033_result⟩)
 (.leaf ⟨(16, 15004234481664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(16, 15004242804736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record035_result⟩)
 (.leaf ⟨(16, 15011490045952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record036_result⟩))
 (.branch 38
 (.leaf ⟨(16, 15036290433024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_result⟩)
 (.leaf ⟨(16, 15051202330624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record038_result⟩))))
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf ⟨(16, 15075386654976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record039_result⟩)
 (.leaf ⟨(16, 15075395043328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record040_result⟩))
 (.branch 42
 (.leaf ⟨(16, 15075897778176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record041_result⟩)
 (.leaf ⟨(16, 15076484644864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record042_result⟩)))
 (.branch 45
 (.branch 44
 (.leaf ⟨(16, 15076955259904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_result⟩)
 (.leaf ⟨(16, 15123968172288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record044_result⟩))
 (.branch 46
 (.leaf ⟨(16, 15132826542080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record045_result⟩)
 (.leaf ⟨(16, 15133083500544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record046_result⟩)))))
 (.branch 55
 (.branch 51
 (.branch 49
 (.branch 48
 (.leaf ⟨(16, 15133091823616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record047_result⟩)
 (.leaf ⟨(16, 15145297281280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record048_result⟩))
 (.branch 50
 (.leaf ⟨(16, 15145308790784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record049_result⟩)
 (.leaf ⟨(16, 15145440911360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record050_result⟩)))
 (.branch 53
 (.branch 52
 (.leaf ⟨(16, 15180597592320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record051_result⟩)
 (.leaf ⟨(16, 15180733939712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record052_result⟩))
 (.branch 54
 (.leaf ⟨(16, 15180742262784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record053_result⟩)
 (.leaf ⟨(16, 15180874383360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record054_result⟩))))
 (.branch 59
 (.branch 57
 (.branch 56
 (.leaf ⟨(16, 15180965150720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record055_result⟩)
 (.leaf ⟨(16, 15181138624512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record056_result⟩))
 (.branch 58
 (.leaf ⟨(16, 15188372848640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record057_result⟩)
 (.leaf ⟨(16, 15196149612544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record058_result⟩)))
 (.branch 61
 (.branch 60
 (.leaf ⟨(16, 15212825575680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record059_result⟩)
 (.leaf ⟨(16, 15212829802496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record060_result⟩))
 (.branch 62
 (.leaf ⟨(16, 15212837085184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record061_result⟩)
 (.leaf ⟨(16, 15213332537344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record062_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (658 + i))) 0 63 :=
  interval_of_check _ 0 63 (by decide +kernel)

public theorem complete : Block 658 721 :=
  block_of_table results 658 63 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0008
