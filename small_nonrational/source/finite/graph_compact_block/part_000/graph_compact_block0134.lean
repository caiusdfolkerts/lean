module
prelude
import GraphInputsRow24Part00018Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0134
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 10905727271680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record000_result⟩)
 (.leaf ⟨(24, 10909359671424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 10909760095240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record002_result⟩)
 (.leaf ⟨(24, 10922512875520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 10940088123392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record004_result⟩)
 (.leaf ⟨(24, 10956805505024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 11035186659584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record006_result⟩)
 (.leaf ⟨(24, 11036333801488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 11039347409152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record008_result⟩)
 (.leaf ⟨(24, 11047937343616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 11125244592384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record010_result⟩)
 (.leaf ⟨(24, 11125376712960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 11125380939776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record012_result⟩)
 (.leaf ⟨(24, 11125385101312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 11125645148288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record014_result⟩)
 (.leaf ⟨(24, 11125845409920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 11139211690000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record016_result⟩)
 (.leaf ⟨(24, 11151013412992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 11181087588352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record018_result⟩)
 (.leaf ⟨(24, 11189677490176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 11190269919360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record020_result⟩)
 (.leaf ⟨(24, 11193970360320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 11197551231104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record022_result⟩)
 (.leaf ⟨(24, 11205112512640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 11237945540864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record024_result⟩)
 (.leaf ⟨(24, 11237945606144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 11238077726720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record026_result⟩)
 (.leaf ⟨(24, 11238197168384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 11238341967872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record028_result⟩)
 (.leaf ⟨(24, 11238348177536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 11238465603712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record030_result⟩)
 (.leaf ⟨(24, 11242894786561), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record031_result⟩))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf ⟨(24, 11244438292736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record032_result⟩)
 (.leaf ⟨(24, 11244781273088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record033_result⟩))
 (.branch 35
 (.leaf ⟨(24, 11247055536129), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record034_result⟩)
 (.leaf ⟨(24, 11253028227200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(24, 11276778569744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record036_result⟩)
 (.leaf ⟨(24, 11307984191488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record037_result⟩))
 (.branch 39
 (.leaf ⟨(24, 11310064566272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record038_result⟩)
 (.leaf ⟨(24, 11310070775936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record039_result⟩))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf ⟨(24, 11331400925312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record040_result⟩)
 (.leaf ⟨(24, 11331405119488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record041_result⟩))
 (.branch 43
 (.leaf ⟨(24, 11331601186944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record042_result⟩)
 (.leaf ⟨(24, 11334525681664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(24, 11334591741952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record044_result⟩)
 (.leaf ⟨(24, 11334721749120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record045_result⟩))
 (.branch 47
 (.leaf ⟨(24, 11342283030656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record046_result⟩)
 (.leaf ⟨(24, 11366733742208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record047_result⟩)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf ⟨(24, 11375512485888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record048_result⟩)
 (.leaf ⟨(24, 11401129263104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record049_result⟩))
 (.branch 51
 (.leaf ⟨(24, 11401265415168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050_result⟩)
 (.leaf ⟨(24, 11410862014720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(24, 11410862080000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record052_result⟩)
 (.leaf ⟨(24, 11410866208896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record053_result⟩))
 (.branch 55
 (.leaf ⟨(24, 11410996281344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_result⟩)
 (.leaf ⟨(24, 11411000410240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record055_result⟩))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf ⟨(24, 11411066470528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record056_result⟩)
 (.leaf ⟨(24, 11413142716416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record057_result⟩))
 (.branch 59
 (.leaf ⟨(24, 11413146845312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058_result⟩)
 (.leaf ⟨(24, 11414217494528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record059_result⟩)))
 (.branch 62
 (.branch 61
 (.leaf ⟨(24, 11417301319936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record060_result⟩)
 (.leaf ⟨(24, 11417301385216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record061_result⟩))
 (.branch 63
 (.leaf ⟨(24, 11417303465984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record062_result⟩)
 (.leaf ⟨(24, 11422568317184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record063_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8693 + i))) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

public theorem complete : Block 8693 8757 :=
  block_of_table results 8693 64 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0134
