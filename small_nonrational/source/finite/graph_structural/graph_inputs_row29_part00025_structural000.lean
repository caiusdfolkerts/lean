module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00025Data
public import GraphInputsRow29Part00025Frames
public import GraphInputsRow29Part00025Leaves
public import GraphInputsRow29Part00025Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00025.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001
def vertexColumn : Fields := ⟨10, hexnat% "b6394d52d4cd2cccb392d4ad2b2a9a968da2e87ae1b46b1b16a599695956359362d876c3a8e938ce4b8ae1bb91d46d1b2699964d92e479e1745b1715a559595555355352d475c368d934cd4b4ad1b59354cd32cc7332d2b2ac6b26c5b0ed8751cc729c6745c9715c3743e8c931324988e1382e4c5252344d0b52344c9314c3322c4b0ad0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6db6db6db6db6da6da4924db6db6db6db6da6da492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000104000010413f93e000000", 7177611906121728, hexnat% "198000000000000000000", 28991029248, 118747255799808, hexnat% "20000002000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10100001017fb8bc000000", 31172067328, hexnat% "8000000804000000000", hexnat% "20000002000000000000", hexnat% "100000140000014000000000000", hexnat% "80000008000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1008000100ff787c000000", 32245809152, hexnat% "10000001008000000000", hexnat% "20000002000000000000", hexnat% "1000000c000000c000000000000", hexnat% "100000010000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10100001010ff8be000000", 123145302310912, hexnat% "20000002000040000000", 30064771072, hexnat% "100000140000014000000000000", hexnat% "88000008800000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000400000047ebffe000000", hexnat% "1000000100010000000000", hexnat% "8000000804000000000", hexnat% "20000002000000000000", 7036874417766400, hexnat% "190000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10780000027fbffe000000", 72057594037927936, 141012366262272, hexnat% "100000015000000000000", hexnat% "100000080000008000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10780001026f81fe000000", 515396075520, 25769803776, hexnat% "100000015000000000000", hexnat% "80000008800000000000", hexnat% "100000000000000100000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c7 c5
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10200001000f8124000000", hexnat% "10000004000001c000000000000", hexnat% "198000000000000000000", 515396075520, 985162452041728, 29393682432, 123145302310912]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c10 c4
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c11 c3
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c12 c2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c13 c1
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c14 c0
  c15
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00025.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00025.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008
def vertexColumn : Fields := ⟨10, hexnat% "b5334e334cb30dc2f07cb4b32e2b4ab28da2e87ae1b46b1b26c5a96958d68d9362d876c3a8e63a4e538ce4b8ae1b89e1783eb44d92e479e1745b1715a5655355352d4756354d334ad1b49d1743de0f43b0f13a4e5334d332cc7362d4b32cab1ac9b16c3bc1e8761e4751cc749ca719e1745c9715c3743c8f13c2f07e949512ca4a524a92949495154354348d1342d48c9314c3342c8b12c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "136db6d36db6db6da4db6db6db4db6db6db6d24924924926db49249249249b6db4db692492649249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨35, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨87, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨113, by decide⟩, ⟨121, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2020000000003f270ec800070000000", 4508032050397184, hexnat% "1800800000000000000e000000", hexnat% "d8000000000000000", 976366325465088]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2020000000003b200fc9c0070000000", hexnat% "401000000801000000", hexnat% "1800800000000000000e000000", 949978046398464, hexnat% "de000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f1703c640070000000", hexnat% "200000000000000c0000000000000", hexnat% "2000000000000020000800000000000", hexnat% "1800800000000000080f000000", hexnat% "c8000000000000000", 870813209198592]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f0f03c640070000000", hexnat% "200000000000000c0000000000000", hexnat% "2000000000000020000800000000000", hexnat% "1800800000000000080f000000", hexnat% "d0000000000000000", 870813209198592]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f00030000811000000", hexnat% "2000000000003000000000000000000", hexnat% "200000000000000c0000000000000", hexnat% "1800800000000000006e000000", 1121501860331520, 3377699720527872, hexnat% "ff000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00025.record008
