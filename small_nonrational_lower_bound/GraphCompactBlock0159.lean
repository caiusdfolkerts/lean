module
prelude
import GraphInputsRow24Part00043Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0159
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 18411325227008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 18455082336384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record001_result⟩)
 (.leaf ⟨(24, 18456894275840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 18457162711168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 18461055025408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record004_result⟩)
 (.leaf ⟨(24, 18471993769984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 18472253816960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 18473933635840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record007_result⟩)
 (.leaf ⟨(24, 18473942024192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 18474065756416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 18474069983232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record010_result⟩)
 (.leaf ⟨(24, 18474074144768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 18474334191744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 18474470506496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record013_result⟩)
 (.leaf ⟨(24, 18474534453376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 18478234894336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 18481355456512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record016_result⟩)
 (.leaf ⟨(24, 18481454546944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 18489377046656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 18495816351872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record019_result⟩)
 (.leaf ⟨(24, 18496856539264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(24, 18513567711232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 18522338033920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record022_result⟩)
 (.leaf ⟨(24, 18522342195456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(24, 18522342260736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 18522606436608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record025_result⟩)
 (.leaf ⟨(24, 18522606501888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(24, 18522610630784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 18528783646720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record028_result⟩)
 (.leaf ⟨(24, 18528834947328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(24, 18529047887872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 18529052016768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record031_result⟩)
 (.leaf ⟨(24, 18529103382656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(24, 18531043311872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record033_result⟩)
 (.branch 35
 (.leaf ⟨(24, 18531051700224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record034_result⟩)
 (.leaf ⟨(24, 18537420687616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(24, 18537424881792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 18537637789696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record037_result⟩)
 (.leaf ⟨(24, 18543798288384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(24, 18543802319872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 18544058335360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record040_result⟩)
 (.leaf ⟨(24, 18547950649600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(24, 18547959037952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_result⟩)
 (.branch 44
 (.leaf ⟨(24, 18548487357056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record043_result⟩)
 (.leaf ⟨(24, 18577992220672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(24, 18590927454464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record045_result⟩)
 (.branch 47
 (.leaf ⟨(24, 18591447517312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record046_result⟩)
 (.leaf ⟨(24, 18593527892096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record047_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9519 + i))) 0 48 :=
  interval_of_check _ 0 48 (by decide +kernel)

public theorem complete : Block 9519 9567 :=
  block_of_table results 9519 48 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0159
