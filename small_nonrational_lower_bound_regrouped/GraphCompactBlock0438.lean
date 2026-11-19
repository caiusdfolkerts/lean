module
prelude
import GraphInputsRow29Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0438
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 1587196002560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record000_result⟩)
 (.leaf ⟨(29, 1689411191040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 1689679593728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 1689679659008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record003_result⟩)
 (.leaf ⟨(29, 1693972463872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 1697195757824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record005_result⟩)
 (.leaf ⟨(29, 1702289801472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 1702293963008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 1702294028288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record008_result⟩)
 (.leaf ⟨(29, 1723972223232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 1723972288512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record010_result⟩)
 (.leaf ⟨(29, 1725247262976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 1727864570112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 1728265093376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record013_result⟩)
 (.leaf ⟨(29, 1728265158656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(29, 1729408012544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 1736454471936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record016_result⟩)
 (.leaf ⟨(29, 1736454537216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(29, 1736582430976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 1736586592512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record019_result⟩)
 (.leaf ⟨(29, 1736586657792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record020_result⟩))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(29, 1736850833664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record021_result⟩)
 (.leaf ⟨(29, 1736850898944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record022_result⟩))
 (.branch 24
 (.leaf ⟨(29, 1737729511680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record023_result⟩)
 (.branch 25
 (.leaf ⟨(29, 1774639382529), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record024_result⟩)
 (.leaf ⟨(29, 1805171851520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record025_result⟩))))
 (.branch 29
 (.branch 27
 (.leaf ⟨(29, 1859322446080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record026_result⟩)
 (.branch 28
 (.leaf ⟨(29, 1859330834432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record027_result⟩)
 (.leaf ⟨(29, 1861402820864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(29, 1874285592832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record029_result⟩)
 (.branch 31
 (.leaf ⟨(29, 1875436961792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record030_result⟩)
 (.leaf ⟨(29, 1876774879232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record031_result⟩)))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf ⟨(29, 1877718663168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record032_result⟩)
 (.leaf ⟨(29, 1894638485760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record033_result⟩))
 (.branch 35
 (.leaf ⟨(29, 1894646874112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record034_result⟩)
 (.branch 36
 (.leaf ⟨(29, 1894886211840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record035_result⟩)
 (.leaf ⟨(29, 1907368460544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record036_result⟩))))
 (.branch 40
 (.branch 38
 (.leaf ⟨(29, 1907521257728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record037_result⟩)
 (.branch 39
 (.leaf ⟨(29, 1907525484544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record038_result⟩)
 (.leaf ⟨(29, 1907636863232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(29, 1907649153024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record040_result⟩)
 (.branch 42
 (.leaf ⟨(29, 1912065753856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record041_result⟩)
 (.leaf ⟨(29, 1912090918912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00004.record042_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20523 + i))) 0 43 :=
  interval_of_check _ 0 43 (by decide +kernel)

public theorem complete : Block 20523 20566 :=
  block_of_table results 20523 43 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0438
