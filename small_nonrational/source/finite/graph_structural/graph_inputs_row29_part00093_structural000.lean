module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00093Data
public import GraphInputsRow29Part00093Frames
public import GraphInputsRow29Part00093Leaves
public import GraphInputsRow29Part00093Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00093.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000
def vertexColumn : Fields := ⟨10, hexnat% "3cb2aaa8ea96a3a1e9a6c5956359362db0e4b8ae8785e0f8f1ca6a93a6598e47969715554d54d4b5c352d2b61d1743dc8ea368ce3c4e5354cd38cd332cc73c2e8b92ccb8ad2b2ac6b86c5b0ef0761d4731d2729e1745c9715c3783d0f23c4f0bc1fcc0ccc8b128c93232a2a2a8c6458562384ec87118c531326292a4c5454552344d"⟩
def kindColumn : Fields := ⟨3, hexnat% "69269b4926da69b4934da4936d34d36d36d26db6934db6db4db4d36d26c9249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44d1089a222306808a30000000", hexnat% "600000000000000000000", hexnat% "204000000000000000000000", hexnat% "30000000000000000000000000", hexnat% "4080000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d1001a222100000800000000", hexnat% "10000200000004800020000000", hexnat% "40000800000202000000000000", hexnat% "200004000000008210000000", hexnat% "20000400000000000000000000", hexnat% "4004080080000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "64904c920a2306808a30000000", hexnat% "c000000000000000000", hexnat% "10010000000000000000000000", hexnat% "600000000000000000000000", hexnat% "200200000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "64104c800a2202000000000000", hexnat% "800010000100000800000000", hexnat% "200004000000008210000000", hexnat% "400008000000000000000000", hexnat% "10000200000004800020000000", hexnat% "10002200000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "343146062a2306808a30000000", hexnat% "40000800000000000000000000", hexnat% "18000000000000000000", hexnat% "80000000000000000000", hexnat% "c00000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "34914e922a2306808a30000000", hexnat% "40000000000000000000000000", hexnat% "c000000000000000000", hexnat% "600000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "34114e822a2206808020000000", hexnat% "40000000000000000000000000", hexnat% "200004000000000210000000", hexnat% "800010000100000800000000", hexnat% "400008000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "34110682200004808020000000", hexnat% "40000800020202000000000000", hexnat% "c080000000200000000", hexnat% "800010002100000800000000", hexnat% "604000000000000000000000", 268435456]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1411021a222306808a30000000", hexnat% "c00000000000000000000000", hexnat% "60000000000000000000000000", hexnat% "200004000000000000000000", hexnat% "c80000000000000000000", hexnat% "4000080000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44910890022306808a30000000", hexnat% "30000000000000000000000000", hexnat% "c080000000000000000", hexnat% "2200000000000000000", hexnat% "600000000000000000000", hexnat% "604000000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14d1021e2a2306808a30000000", hexnat% "204000000000000000000000", hexnat% "60000000000000000000000000", hexnat% "c80000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4d1001e0a2104000a20000000", hexnat% "600200000800000000000", hexnat% "204000000000008010000000", hexnat% "30000000000000000000000000", hexnat% "40000800000202000000000000", hexnat% "80000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "64114c880a0206000000000000", hexnat% "200200000800020000000", hexnat% "200004000000008210000000", hexnat% "c00000000000000800000000", hexnat% "10000000000000000000000000", hexnat% "12002100000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44110888020206000000000000", hexnat% "10000200000000800020000000", hexnat% "4080000008210000000", hexnat% "2200000000000000000", hexnat% "800010002100000800000000", hexnat% "604000000000000000000000", hexnat% "20000400000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c23 c12
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c24 c5
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c25 c2
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00093.record000
