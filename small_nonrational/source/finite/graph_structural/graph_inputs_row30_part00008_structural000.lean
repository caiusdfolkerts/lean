module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00008Data
public import GraphInputsRow30Part00008Frames
public import GraphInputsRow30Part00008Leaves
public import GraphInputsRow30Part00008Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013
def vertexColumn : Fields := ⟨10, hexnat% "3d13c2f07ce8b62b8b92d4ad26c9723cb2aaaa6ac6a9a9693a2e87ab18e6359362d876a3a4e4b8ae1b91e2785e0fba1d86e1e4751b45b15c4f1ca6a99a719a66594e4b91e6c5394d54d4b51d68d9352d2b46d4749d1743de0f43b0f23a8da398d6338f13a4d9394d5334d332cc73c2e8b92e2b4acab1ae1b46c9b16c3ba1e4731d2729c6745c9715c3783d0f23c4f0bc1fc292a468a6198961582e07b094a51929465254550b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6da6d369b69349b4924936db6db4da6d36d26936924926db6db6db6db6d36d36d36db6d26936db489249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨114, by decide⟩, ⟨117, by decide⟩, ⟨120, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "201e0092104f00002220360c0000", hexnat% "1240080000000000000000000000000", hexnat% "26300000000000000000", hexnat% "4c60000000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40c020092367f00002220000c0000", hexnat% "201c000000000000000000000000", hexnat% "40e0000000000000000000000000", hexnat% "1200000000000000000000000000000", 905969664]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12400900092004900002220360c0000", hexnat% "26300000000000000000", hexnat% "10060000000000000000", hexnat% "4c62000000000000000000000000", hexnat% "200c000000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42c0e000236370000020026040000", hexnat% "9000480000000000000000", hexnat% "4060000000000000000010080000", hexnat% "1200000000000000000202000000000", hexnat% "90000000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42c0e000236370000020016040000", hexnat% "9000480000000000000000", hexnat% "4060000000000000000020080000", hexnat% "1200000000000000000202000000000", hexnat% "90000000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6ce20000367100000200300c0000", hexnat% "60000000006000000", hexnat% "1c000000000000000000000000", hexnat% "1240000000000000000202000000000", hexnat% "9200080000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12440900092064900002220360c0000", hexnat% "10060000000000000000", hexnat% "20300000000000000000", hexnat% "2c0e000000000000000000000000", hexnat% "60000000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1244cea0092162f00002220360c0000", hexnat% "20500000000000000000", hexnat% "2014000000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4cea0000267500002220300c0000", hexnat% "1240010000000000000000000000000", hexnat% "10020000000006000000", hexnat% "9200080000000000000000", hexnat% "2004000000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12440480092062500002220360c0000", hexnat% "2000000030000000000000000000", hexnat% "90000000480000000000000000", hexnat% "24000000120000000000000000", hexnat% "c02000000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4040009206490000222000040000", hexnat% "1240090000000000000000000000000", hexnat% "10060000000006000000", hexnat% "20300000000030080000", hexnat% "2c0e000000000000000000000000", hexnat% "20000000000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record013
