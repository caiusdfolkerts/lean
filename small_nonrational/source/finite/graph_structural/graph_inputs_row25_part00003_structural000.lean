module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00003Data
public import GraphInputsRow25Part00003Frames
public import GraphInputsRow25Part00003Leaves
public import GraphInputsRow25Part00003Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020
def vertexColumn : Fields := ⟨10, hexnat% "358e52b4d331c4f0bcd4ab2d2b1a9695a2eb46b1aa6c5a968d8b6c3a4e538ae1ba1e4789e0fb91d45594e4b9e1745b1715a55954d4b54b4ad1b51d2743dd0ec3c4e9394d5352cab1ad1b26c5bc1e8791d4731c6785d1725c3743c8f07f44532922c83aa1a462984e0b8b1525190e5452950d1342d28c930cc4b0ac1b21c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db4db69b6d249a69a4936d369269b6da49269b69b49249a4926d2491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨94, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41d50200114449b360000000", hexnat% "20040100400000000000000", hexnat% "600800000000000000", hexnat% "8000080040000004000000000", 197914240483328, hexnat% "20000200000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "425462100404491340000000", 1242993497691127808, hexnat% "810000000000a000000000", hexnat% "8010080040000004000000000", 197914240483328, hexnat% "600800000000000000", 144115188075855872]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d16000060061f3e0000000", hexnat% "8010080040000000000000000", hexnat% "600900000000000000", 162727720910848, hexnat% "420000000004080000000000", hexnat% "101040000000000000", hexnat% "402000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e0600f40b452e0000000", hexnat% "8010000040000000000000000", hexnat% "810000000000a000000000", hexnat% "402001000400100000000", hexnat% "405000000000000000000000", hexnat% "20000100000080000000000", 1126999418470400]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3c160100e006df3e0000000", hexnat% "401400000004000000000000", hexnat% "8000080040000000000000000", hexnat% "600100100000000000", 140737488355328, hexnat% "2001040000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "425462001340601360000000", 864691130602618880, hexnat% "300000180000000000", hexnat% "40004018000000000", hexnat% "8010180000000004000000000", hexnat% "400000840000000000", hexnat% "8000000000002000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80100c2040200005240000000", hexnat% "120000000008000000000", hexnat% "405400000000000000000000", hexnat% "600900000000000000", hexnat% "8000000000012000000000", hexnat% "20000000004080000000000", 197914777354240, hexnat% "101440400100000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record038
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038
def vertexColumn : Fields := ⟨10, hexnat% "3b0da338b92b44f0bce8b62b8b92d2b2a9a96ac6a5ab1aa6998e6a5a564b8ae1b91e2785ee8761b8791cc6b16c5694e4b9395352d52d2b51d2745d0f783d0ec3c8ea368e6358ce3c4e9364e5352d2b2ac6b26c5b31d2729c6745c5743c8f0bc6cc4a92468961381e4a469464a5194951342d0751324d0b12c1b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db69b6d36db4db4926db6da4d34924936db6db49349a493492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨85, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d00014002dcfe000000", hexnat% "42000000000080000000000", hexnat% "82000000040000000000", 2882303770107052032, hexnat% "18420000000000000", 180143985094819840]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2012ee0000efe000000", hexnat% "8000000005000000000", hexnat% "40080000000060000000000", 9223372586610589696, hexnat% "5000000000000000000", 72057594037927936, hexnat% "2000000000080000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40080000200060400000000", hexnat% "2004000000080020000000", 2882303772254535680, hexnat% "1800000c000000000", hexnat% "9000040000002000000", hexnat% "2000080000814000000", 69793218560, 369295169578598400]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00003.record038_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00003.record038
