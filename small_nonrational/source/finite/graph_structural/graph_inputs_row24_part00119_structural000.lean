module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00119Data
public import GraphInputsRow24Part00119Frames
public import GraphInputsRow24Part00119Leaves
public import GraphInputsRow24Part00119Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010
def vertexColumn : Fields := ⟨10, hexnat% "1f1aa96a3a2e87a69a56358b61d94e4b86e1783e6a5998e4b91e5a565655354755352d1b51d1743d68e9394cd38ccb31cf0b62d4b8ad2b2ac6b86c9b16c3b91d4731d2719e1725c570dd0f13c2f07e582d24a618a6944b19261916439614a5254550d58390ca382d0b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4db4da6db6db4924926db4934da6924924d24924d2492649249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e70c97f3f9f0000000", hexnat% "8100000000080200000000", hexnat% "800100200000000000000", hexnat% "80000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400e87f2f970000000", hexnat% "250000000000000000", hexnat% "800000090000000000", hexnat% "1a0000000200000000", hexnat% "900000000000000000000", hexnat% "8000000010000080000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bb0007fbfbf0000000", hexnat% "400410000000000000", hexnat% "800000200000000000000", hexnat% "40880000000000000", hexnat% "8100000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81007b0690bbfbf0000000", hexnat% "800800000000000000", hexnat% "800000000400000000000", hexnat% "40000000000000000", 1970324836974592]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800310217fbfbf0000000", hexnat% "a0000000000000000", hexnat% "c00400000000000000", hexnat% "8100000080000000000000", hexnat% "40800000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8100210097fbfbf0000000", hexnat% "60800000000000000", hexnat% "180000000000000000", hexnat% "c00400000000000000", hexnat% "800000200000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80003b0014b0fbf0000000", 144748506773454848, hexnat% "40880020000000000", hexnat% "c00400010000000000", hexnat% "900000000000000000000", 290271069732864]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bf0c80022b70000000", 282299610431488, hexnat% "400002200000000000", hexnat% "8100000010090080000000", hexnat% "800000200401000000000", 1284229581242368]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b0800000a20000000", hexnat% "40080028100000000", hexnat% "e00400010000000000", hexnat% "800100200003000000000", hexnat% "8100000010080080000000", 844700881780736, 1389782965944320]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c2
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019
def vertexColumn : Fields := ⟨10, hexnat% "7a338751b4731ac4f16a8e93a558d64d8b65392e8791e0f9e1746b16c5c96a5693a6394e5c569595554d54d4b56354d3352d2b61d4743d38cd32ce4b1ae1b0ecc729e1725c570de0f0bc1f6c1c46514c8ca2a13a312c629314951362384c3382c4b0ac4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4936d36db4db6da4db69a69a69a4db6db49249a492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨67, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20080000180000000000", hexnat% "2000040000180400000", 25794969600, 1729452660014186496, hexnat% "c0000004000000000000", 503316480, 4785075677822976]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021
def vertexColumn : Fields := ⟨10, hexnat% "7c1e8751b4731accc9aa8e9a6559366394e4b8ae8785e0f9e1745b15c4f1aa4e9966391e5c569595554d54d4b52b61d1743d68d534ccab86c5b0ed8751d2729e1745c570de0f23c4f0bc1f71154332324ca2a45a31326292a4c51548d1362384c3382c2b05c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4d34d349b6db6db6d269a6d26d34db4934db692492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0000011000000000000", 216208241363779584, hexnat% "8400000008008000000", hexnat% "800002000030000000", hexnat% "2000040082800400000", 125829120, 1073741824]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record021
