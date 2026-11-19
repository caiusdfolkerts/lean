module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00018Data
public import GraphInputsRow29Part00018Frames
public import GraphInputsRow29Part00018Leaves
public import GraphInputsRow29Part00018Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000
def vertexColumn : Fields := ⟨10, hexnat% "7ce4b8aa5996358b61da8e63b89c6659566394e479a5595354b5a358d8751d1743dc4e9364e5354cd38cd332cc73a2d8b92d4b8ad2ba1d8731ca785d1725c570de0f43c8fe40741b382c286a1984e0bb81c469164471c246919495154351342dc0e8360c6382d0b12c2b21c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "249b6d36936da4926db4924db6da49249249b492489249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1002100c000000000000000", hexnat% "c040002000000000000000", 4433351142277120, hexnat% "f00000008000000000", hexnat% "200001810006000000000", 65970697666560]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002
def vertexColumn : Fields := ⟨10, hexnat% "398e529c9723c1f38ac6a5a8e87ac5a5655a364d876a3a4e33a2e2b86e8785e0fb91e2719a6599e1715a559555535a34cd2b46d8749d1743de0f1354d331cf0ba2d8b32cab86d1b16c3bc1e8751cc749ca785d1715c3783c8f13c2f07c78e13141d382a286ac1a86618661c4691643961465454550d58318c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "d36d26da4db6936da6db6db49a49b69b4936d34926d249249a49a499249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5c00000fddc0000000", hexnat% "20080000800000000000000000", hexnat% "100000000020c000000000000", 897201488265216, hexnat% "2002100004c00000000000000", hexnat% "104000000020000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20184000dc00203bdc00000000", hexnat% "100000000020c040000000000", 844432446324736, hexnat% "2002100004c00000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3002100004e0f07d1c0000000", hexnat% "20000000d00000080000000000", hexnat% "c0000000c00000000", hexnat% "184000000020300000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1840000c482333ddc0000000", hexnat% "2002100000400000000000000", hexnat% "20000000d00000080000000000", hexnat% "100000000020c040000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3002100004e0f0619c0000000", hexnat% "5c0000000000000000", hexnat% "20080000800000080000000000", 1941325217792, hexnat% "104000000020300000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100200000020c061900000000", hexnat% "20000000d00000080000000000", hexnat% "c0c00000000000000", 897201488265216, 1927366574080, hexnat% "2104100004020000000000000", hexnat% "80000000000000400000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004
def vertexColumn : Fields := ⟨10, hexnat% "398e507ce2b1a96a3a1eb86c59564d876338ae1b85e0fb91e2719a659996639e1715a559555535334ad1b49d1743dc4e5354e334cc73c2d8b92ccb8acab86d1b16c3bc1e8751cc749ca785d1715c3723c4f0bc1f1e074e0a8a1a98619b81c4471a2469864590e5851951515435c0e8360c6382c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "da4db49b69b4da4934926926d34936da492493492492692493249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108480c02e13ec07e00000000", hexnat% "1700000000000000000", hexnat% "1e0000080000000000000", hexnat% "840000000040100000000000", 51677046505472, hexnat% "2000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108480032e102cf7e00000000", hexnat% "103400000200000000000", hexnat% "6c000000000000000000", hexnat% "840000000040100000000000", 52917295621603328, hexnat% "80000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100080172c07cdf7e00000000", hexnat% "6c000002000000000000", hexnat% "840000000000000000000000", hexnat% "84000002100000000000000", hexnat% "100000080200000000000", hexnat% "82000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100080172c13ccf7e00000000", hexnat% "6c000002000000000000", hexnat% "84000002000000000000000", hexnat% "840000000040100000000000", hexnat% "100000080200000000000", hexnat% "82000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c4003702142ff7c00000000", hexnat% "1e0000080000000000000", hexnat% "100080002c000000200000000", hexnat% "c000000000000000000", 16888498602639360]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8401e30020fef07c00000000", hexnat% "c00c000000000000000", 16501264351232, hexnat% "1084800020100000000000000", hexnat% "700000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18849ee32e1c2d07e00000000", hexnat% "40001000000200000000000", 16888498602639360, hexnat% "4000000a0000000000", 5497558138880]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18849ed32e1c2c07e00000000", 16888498602639360, hexnat% "40002000000300000000000", hexnat% "4000000a0000000000", 5497558138880]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10848cc32e182c07e00000000", hexnat% "840000000040100000000000", hexnat% "20000028000000000000", 51677046505472, hexnat% "103400000000000000000", 5629499534213120]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c41c300a1c2f07c00000000", hexnat% "1000800024000000200000000", hexnat% "700000000000000000", hexnat% "2c000000000000000000", 16492674416640, 16888498602639360]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8401c370a0c0f07c00000000", 16501264351232, hexnat% "2c000002000000000000", hexnat% "1084800020100000000000000", 16888498602639360, 4611686018427387904]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18409cf72e1c0f07e00000000", hexnat% "84000000002000000000000", 16492674416640, hexnat% "20000028000000000000", 5629499534213120]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108480f32e182c07e00000000", hexnat% "840000000040100000000000", hexnat% "120400000000000000000", 51677046505472, 16888498602639360, hexnat% "c0000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "170e080c07c00000000", hexnat% "6c000002000000000000", hexnat% "840000000040100000000000", hexnat% "1084800020100000000000000", hexnat% "182000000000000000000", 51677046505472, 16888507192573952]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c19 c10
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c22 c3
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c23 c2
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c24 c1
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c25 c1
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c26 c0
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00018.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00018.record004
