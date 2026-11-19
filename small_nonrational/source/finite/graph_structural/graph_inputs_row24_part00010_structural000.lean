module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00010Data
public import GraphInputsRow24Part00010Frames
public import GraphInputsRow24Part00010Leaves
public import GraphInputsRow24Part00010Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008
def vertexColumn : Fields := ⟨10, hexnat% "f0ba2788da4eb46b1b26a996639b1655936a38ce2b85e0fbc1e85e136539d16c5c96a5594e5c55554d68d334ad1743de0f43b0dc3c8ea368d6338f1334d33a2ccb4ad1b26c5b0ef07a1e4751cc789d2729c6785d170de0f23c4f548aa1582e079512a4550b41dc0e8350cc348ca344c5322c2b06e0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6d36d24db6db6db69b692492492492492492492492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000475afefbbc000000", 3458764513820540928, hexnat% "180000000000000000000", 622904123460681728, hexnat% "2000040000010440000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280005ecdc3dbbc000000", hexnat% "100002000040040000000", 61572651155456, 85568392920039424, hexnat% "2000040000002400000000", 562949953421312]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1152921504539738112, hexnat% "200004000000000000000", hexnat% "2000040000000000000000", 3458764513820540928, hexnat% "180000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000493a23fffc000000", hexnat% "2000040000040000000000", 162349488910893056, 325684140240273408, 3458764513820540928, hexnat% "180000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "210004280615fffc000000", 5764609722057490432, hexnat% "280000000000000000000", 338086631401586688, 164601288724578304, 72057594037927936]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1152921504539738112, hexnat% "200004000000000000000", hexnat% "80001000000000000000", hexnat% "2000040000000000000000", hexnat% "100002000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000040f2205fffc000000", hexnat% "200004000220000000000", 20486100648722432, 3458764513820540928, hexnat% "180000000000000000000", 41957363715932160]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "210004279f45fdf4000000", 603623087556001792, 63771808628736, hexnat% "80001000000000000000", hexnat% "200004000000200000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22000444fd23fffc000000", 593736278999040, 792844640649740288, 3458764513820540928, hexnat% "180000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200004ffde2ffa8000000", hexnat% "2000040000010040000000", 593736278999040, 3458764513887649792, hexnat% "180000000000000000000", 268435456]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000040fffc5f5c4000000", hexnat% "100002000000020000000", 63771808628736, hexnat% "200004000000200000000", 34628173824, hexnat% "80001000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000412022f788000000", hexnat% "2000040002040040000000", hexnat% "100002000400004000000", hexnat% "80001000000030000000", 330187739867643904, 594476284684271616, 146516521470918656]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016
def vertexColumn : Fields := ⟨10, hexnat% "16c4f0f2d2aca5aa9a3687a598e62db0ea394e3392e1b89e0fbc13c749b2569a64d94e479e15c5594e54d4b5c368d534cd4b46d4749d0f743b0f2358ce3a4cd32cc73c2e8b92d4b32d2b1ae1b26c5b0ef07a1d4731d2729c6783d0f23c4f0bc960d81e5870952525254354341da0cc318c930ce0b12c1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db4db6da4da69b6db4d24d34d24d34924924934924d3492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000b082fce92f1000000", hexnat% "180000000000000000000", 18004670676992, hexnat% "1000a000200004000000", hexnat% "4000080000800800000", 216172782113783808]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81000103279a72ff800000", 2322718313676800, hexnat% "a0800000000000000", hexnat% "1000a000240000000000", hexnat% "84000080000800000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "810001012fdef2bb000000", hexnat% "1000a000200004000000", hexnat% "a0800000040000000", hexnat% "84000080000800800000", 144115188075855872]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "940aaa8c428856800000", hexnat% "10100000000000000", hexnat% "8100000000000000000000", 48722260000768, 9992372947517440, 17729624997888]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80100ba82ffe7aff000000", hexnat% "100000100000000000000", hexnat% "84000080008000800000", 144115188075855872]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8100010927f27ab2000000", hexnat% "84000080008000800000", hexnat% "80008000040000000", hexnat% "20200000000000000", hexnat% "1000a000040004000000", 8796244017152]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8180000804820002000000", hexnat% "30380000000000000", hexnat% "4080008000000000000", 9869364547289088, hexnat% "1000a000240004000000", 70370631614464, 9723956953088]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00010.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00010.record016
