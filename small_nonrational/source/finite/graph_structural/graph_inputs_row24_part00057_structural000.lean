module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00057Data
public import GraphInputsRow24Part00057Frames
public import GraphInputsRow24Part00057Leaves
public import GraphInputsRow24Part00057Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013
def vertexColumn : Fields := ⟨10, hexnat% "7cb8ad29caaa3aa9a36a3a1e9c68d876638ce4b86e4785e0fae1b4671aa4e9a64d98e479716351d58d3352d1b51d1743de0ec370ea398ce3a4e5334e331ce8b32e2b4acab1ae1b46c9b16c3b61d4731e2749e1745c3723c4f628661590e0b81e624651550d0b41da0d8330e2318e1314d0b22c2b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6934924db6db6db49a492492492492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "250004affffffff0000000", hexnat% "15000000000000000", hexnat% "4080080000000000000000", hexnat% "a00000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50000afeffbee70000000", hexnat% "55000000000000000", hexnat% "4000080000001000000000", hexnat% "2a80000000000000000000", 4508004116332544]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4d8009bdb7ecfff0000000", hexnat% "2000040000020000000000", 164381386399023104, hexnat% "200004000000000000000", 18691697672192]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4080081fff4cdf40000000", hexnat% "50000a000800010000000", 56075629887488, hexnat% "54000000000000000", hexnat% "2a00000000000000000000", 139586437120]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4080081fb7ffc570000000", hexnat% "2000040000002800000000", hexnat% "1e000000000000000", hexnat% "f00000000000000000000", 20266267042643968, 10737418240]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60800c1edf88faf0000000", 81064814767505408, hexnat% "1e000000000000000", hexnat% "f00000000000000000000", 130841883705344]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50000af7fbfe9f0000000", hexnat% "55000000000000000", hexnat% "4000080000001000000000", hexnat% "2a80000000000000000000", 36099191532945408]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c8 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1152358336415399936, hexnat% "2000040000002000000000", hexnat% "1f000000000000000", hexnat% "f80000000000000000000", hexnat% "4000080002001040000000", 10737418240]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000081fe7ddfd0000000", hexnat% "4080081000000000000000", hexnat% "16000000000000000", hexnat% "b00000000000000000000", 1009228666971881472, hexnat% "2000040000020000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1152883971156082688, hexnat% "4080081000000040000000", hexnat% "2000040000222020000000", 6917529029788565504, hexnat% "18000000200000000", hexnat% "f00000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2c0005808c7bfff0000000", 8070450532247928832, hexnat% "4080080002000000000000", hexnat% "300000000000000000000", 85572790966550528, 1027242927505539072]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "230004601c3ffff0000000", hexnat% "19000000000000000", hexnat% "4080080002000000000000", hexnat% "c00000000000000000000", 117163959055810560, 1027242927505539072]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [143974243892199424, 1008947191458299904, hexnat% "2000040000000000000000", hexnat% "4000080000001010000000", hexnat% "1f000000000000000", hexnat% "f80000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [413304009256861696, hexnat% "2000040000222020000000", 739012551353827328, hexnat% "1f000000010000000", hexnat% "4000080002001040000000", hexnat% "f80000000000000000000", 4402341478400]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c22 c10
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c23 c9
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c24 c7
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c25 c6
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c26 c5
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c27 c2
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record013
