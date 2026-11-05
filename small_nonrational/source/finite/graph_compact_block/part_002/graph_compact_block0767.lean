module
prelude
import GraphInputsRow30Part00039Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0767
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 24663986012160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 24666066386944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record001_result⟩)
 (.leaf ⟨(30, 24666198507520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 24681635643392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 24740171972608), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record004_result⟩)
 (.leaf ⟨(30, 24741314891776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 24741322690576), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 24741339465744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record007_result⟩)
 (.leaf ⟨(30, 24742413205505), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 24757838839808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record009_result⟩)
 (.leaf ⟨(30, 24777943287824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 24778228924416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record011_result⟩)
 (.leaf ⟨(30, 24779557961728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(30, 24783718711296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record013_result⟩)
 (.branch 15
 (.leaf ⟨(30, 24783842508800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record014_result⟩)
 (.leaf ⟨(30, 24894918098944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(30, 24895510560768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 24896583778304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record017_result⟩)
 (.leaf ⟨(30, 25031270994048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(30, 25117262610432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record019_result⟩)
 (.branch 21
 (.leaf ⟨(30, 25117774317568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record020_result⟩)
 (.leaf ⟨(30, 25126095685632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 25142738551300), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record022_result⟩)
 (.leaf ⟨(30, 25152471466240), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 25154688188416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record024_result⟩)
 (.leaf ⟨(30, 25154960752640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record025_result⟩))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ⟨(30, 25155357114368), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record026_result⟩)
 (.branch 28
 (.leaf ⟨(30, 25158081314816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record027_result⟩)
 (.leaf ⟨(30, 25161061433344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(30, 25161598238720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record029_result⟩)
 (.branch 31
 (.leaf ⟨(30, 25169919737856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record030_result⟩)
 (.leaf ⟨(30, 25177132908544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record031_result⟩))))
 (.branch 35
 (.branch 33
 (.leaf ⟨(30, 25178241236992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record032_result⟩)
 (.branch 34
 (.leaf ⟨(30, 25178373357568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record033_result⟩)
 (.leaf ⟨(30, 25190276792320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(30, 25190788759552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record035_result⟩)
 (.leaf ⟨(30, 25194297098240), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record036_result⟩))
 (.branch 38
 (.leaf ⟨(30, 25194833903616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record037_result⟩)
 (.leaf ⟨(30, 25194949509120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record038_result⟩)))))
 (.branch 46
 (.branch 42
 (.branch 40
 (.leaf ⟨(30, 25215753125888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record039_result⟩)
 (.branch 41
 (.leaf ⟨(30, 25226767237120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record040_result⟩)
 (.leaf ⟨(30, 25329179557888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(30, 25329303355392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record042_result⟩)
 (.leaf ⟨(30, 25332927234304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record043_result⟩))
 (.branch 45
 (.leaf ⟨(30, 25333464104960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record044_result⟩)
 (.leaf ⟨(30, 25333472428032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record045_result⟩))))
 (.branch 49
 (.branch 47
 (.leaf ⟨(30, 25341785604096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record046_result⟩)
 (.branch 48
 (.leaf ⟨(30, 25341793927168), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record047_result⟩)
 (.leaf ⟨(30, 25363472187392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(30, 25364735262720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record049_result⟩)
 (.leaf ⟨(30, 25367360372736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record050_result⟩))
 (.branch 52
 (.leaf ⟨(30, 25367756734464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record051_result⟩)
 (.leaf ⟨(30, 25367765057536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00039.record052_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24838 + i))) 0 53 :=
  interval_of_check _ 0 53 (by decide +kernel)

public theorem complete : Block 24838 24891 :=
  block_of_table results 24838 53 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0767
