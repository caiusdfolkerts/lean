module
prelude
import GraphInputsRow26Part00030Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0346
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 18406359302145), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 18406627770368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record001_result⟩)
 (.leaf ⟨(26, 18406631801856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 18406891913216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 18406900236288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record004_result⟩)
 (.leaf ⟨(26, 18411052662784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 18411060985856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 18411325227008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record007_result⟩)
 (.leaf ⟨(26, 18452409532672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 18455082336384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record009_result⟩)
 (.leaf ⟨(26, 18457162711168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 18458202898560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record011_result⟩)
 (.leaf ⟨(26, 18471993769984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(26, 18472253816960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 18473933635840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record014_result⟩)
 (.leaf ⟨(26, 18473942024192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(26, 18474069983232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record016_result⟩)
 (.leaf ⟨(26, 18474074144768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record017_result⟩))
 (.branch 19
 (.leaf ⟨(26, 18474334191744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record018_result⟩)
 (.leaf ⟨(26, 18474470506496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(26, 18478234894336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record020_result⟩)
 (.branch 22
 (.leaf ⟨(26, 18481355456512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record021_result⟩)
 (.leaf ⟨(26, 18481454546944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(26, 18495816351872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record023_result⟩)
 (.leaf ⟨(26, 18513567711232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record024_result⟩))
 (.branch 26
 (.leaf ⟨(26, 18519987372288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record025_result⟩)
 (.leaf ⟨(26, 18522185042176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record026_result⟩))))))
 (.branch 40
 (.branch 33
 (.branch 30
 (.branch 28
 (.leaf ⟨(26, 18522210140160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 18522342260736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record028_result⟩)
 (.leaf ⟨(26, 18522606436608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(26, 18522606501888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 18522610630784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record031_result⟩)
 (.leaf ⟨(26, 18522612711552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record032_result⟩))))
 (.branch 36
 (.branch 34
 (.leaf ⟨(26, 18529047887872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 18529052016768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record034_result⟩)
 (.leaf ⟨(26, 18531043311872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(26, 18531051700224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record036_result⟩)
 (.leaf ⟨(26, 18531320070145), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record037_result⟩))
 (.branch 39
 (.leaf ⟨(26, 18537424881792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record038_result⟩)
 (.leaf ⟨(26, 18537635676288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record039_result⟩)))))
 (.branch 47
 (.branch 43
 (.branch 41
 (.leaf ⟨(26, 18537637757056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record040_result⟩)
 (.branch 42
 (.leaf ⟨(26, 18537637789696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record041_result⟩)
 (.leaf ⟨(26, 18543798288384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record042_result⟩)))
 (.branch 45
 (.branch 44
 (.leaf ⟨(26, 18544058335360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record043_result⟩)
 (.leaf ⟨(26, 18547959037952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record044_result⟩))
 (.branch 46
 (.leaf ⟨(26, 18548487357056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record045_result⟩)
 (.leaf ⟨(26, 18577992220672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record046_result⟩))))
 (.branch 50
 (.branch 48
 (.leaf ⟨(26, 18578091311104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record047_result⟩)
 (.branch 49
 (.leaf ⟨(26, 18591447517312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record048_result⟩)
 (.leaf ⟨(26, 18593527892096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record049_result⟩)))
 (.branch 52
 (.branch 51
 (.leaf ⟨(26, 18599769079808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record050_result⟩)
 (.leaf ⟨(26, 18616948883456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record051_result⟩))
 (.branch 53
 (.leaf ⟨(26, 18617477365760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record052_result⟩)
 (.leaf ⟨(26, 18618888814592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00030.record053_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15616 + i))) 0 54 :=
  interval_of_check _ 0 54 (by decide +kernel)

public theorem complete : Block 15616 15670 :=
  block_of_table results 15616 54 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0346
