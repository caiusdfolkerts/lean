module
prelude
import GraphInputsRow30Part00033Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0761
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 18406359302144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record000_result⟩)
 (.leaf ⟨(30, 18406887653888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 18406896041984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record002_result⟩)
 (.leaf ⟨(30, 18522338033664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 18527159320576), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record004_result⟩)
 (.leaf ⟨(30, 18531039052544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 18531320070144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record006_result⟩)
 (.leaf ⟨(30, 18540033769472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 18544330801152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record008_result⟩)
 (.leaf ⟨(30, 18548491550720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 18593115046144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record010_result⟩)
 (.leaf ⟨(30, 18778875265280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 18817531052032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record012_result⟩)
 (.leaf ⟨(30, 18920014618624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 19093952397312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record014_result⟩)
 (.leaf ⟨(30, 19294748442624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(30, 19366825426944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record016_result⟩)
 (.leaf ⟨(30, 19435410685952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record017_result⟩))
 (.branch 19
 (.leaf ⟨(30, 19504260186112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record018_result⟩)
 (.leaf ⟨(30, 19512581685248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(30, 19564259704832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record020_result⟩)
 (.leaf ⟨(30, 19573914992640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record021_result⟩))
 (.branch 23
 (.leaf ⟨(30, 19586326233344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record022_result⟩)
 (.leaf ⟨(30, 19588947443712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(30, 19611625980480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record024_result⟩)
 (.leaf ⟨(30, 19611627044864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record025_result⟩))
 (.branch 27
 (.leaf ⟨(30, 19619574188032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record026_result⟩)
 (.leaf ⟨(30, 19623982532608), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(30, 19624510882312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record028_result⟩)
 (.leaf ⟨(30, 19633109204992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record029_result⟩))
 (.branch 31
 (.leaf ⟨(30, 19637261860864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record030_result⟩)
 (.branch 32
 (.leaf ⟨(30, 19645987815424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record031_result⟩)
 (.leaf ⟨(30, 19649752203264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00033.record032_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24630 + i))) 0 33 :=
  interval_of_check _ 0 33 (by decide +kernel)

public theorem complete : Block 24630 24663 :=
  block_of_table results 24630 33 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0761
