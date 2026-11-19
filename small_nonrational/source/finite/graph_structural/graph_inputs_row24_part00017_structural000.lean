module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00017Data
public import GraphInputsRow24Part00017Frames
public import GraphInputsRow24Part00017Leaves
public import GraphInputsRow24Part00017Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00017.record037
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037
def vertexColumn : Fields := ⟨10, hexnat% "3586e19c2f07cd49b26a99a5693a2e87a65a562d876638ce2b86e4789e1783ed47496a719965594e47995475634cd1b51d1743de0f4368f1394d538cd331cd8b52ccb4acab1ad1b16c3b61e4731c6785d1715c3743c8f13c2f07cac1703cc4a52298560d9892a4a52344d0b70360e4328c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d24db6db6926d36d26d36db6d24d24924db69b69b6d249b49a499249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80723001b18441cdc00000", hexnat% "30000000000000000000000", 3377699720527872, hexnat% "20200000000000000", 562958543355904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "23203a00441cdc00000", hexnat% "30000000000000000000", 2814758357041152, hexnat% "8040000000800000000000", hexnat% "30000000010000000000000", 1407374883553280]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300023203bf84420dc00000", 7516192768, hexnat% "30000000000000000000", hexnat% "8040000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3232023f8442cdc00000", 108086391056891904, hexnat% "40000000000100000000", hexnat% "8000000000000000000000", hexnat% "30000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1807232029f84424dc00000", hexnat% "20000000000000000000000", 6442450944, 81064793292668928]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3807232029204424dc00000", 72057596185411584, 3659174697238528, 140741783322624, 9007199254740992]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100123203bf84420dc00000", hexnat% "20020000000000000000000", 7516192768, hexnat% "8040000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1232023f044205c00000", 72057596185411584, hexnat% "20020000000000000000000", hexnat% "10000000080000040000000", hexnat% "8040000000800000000000", 4429185024]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300723001b184404dc00000", hexnat% "8000000004000000000000", hexnat% "20200000000000000", 6442450944, 2814758357041152]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100723000358441cdc00000", hexnat% "8000000000000000000000", hexnat% "20000000080000000000000", 2814758357041152, hexnat% "20300000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3007230003004400dc00000", hexnat% "20002000000000000", hexnat% "8000000005800000000000", 7516192768, 2251808403619840, 252201579132747776]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2203020443cdc00000", 3659174697238528, hexnat% "8040000000800000000000", hexnat% "20022100000000000000000", hexnat% "100000000b0000000000000", hexnat% "10000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000200005804080800000", hexnat% "40000000000108000000", 2819156403552256, hexnat% "20300000001000000", hexnat% "20022100000000000400000", hexnat% "100000000b0000000000000", hexnat% "10000000000044000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c23 c2
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00017.record037_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00017.record037
