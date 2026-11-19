module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00267Data
public import GraphInputsRow29Part00267Frames
public import GraphInputsRow29Part00267Leaves
public import GraphInputsRow29Part00267Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00267.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000
def vertexColumn : Fields := ⟨10, hexnat% "c729a598e6558d64d8b6538ce4b8ae4789e785d16c5c96a719a659939715554d54d4b5c354d3352d2b49d58e9354cd34ccb3a2d4b32d2b2ad1b91d4731e2749ca745c9715c3743c8f13c2f5921c470e28689a19a168381e584e1865192654549465855158350d074c328c6384c9382c8b06e0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "4926db6db4936da4924d349a69269a4d3492492492492249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f00c03807407fff000000000", hexnat% "204000000000000000000", hexnat% "18000000000000000000", 119345390125318144, hexnat% "2d0000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400e1d805487fff000000000", hexnat% "800000080000000000000000", hexnat% "300002002000000000000000", 83316593106354176, hexnat% "250000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e07803403fff000000000", hexnat% "400008000084000000000000", hexnat% "800010084000000000000000", 83316593106354176, hexnat% "250000000000000000", hexnat% "300000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c4 c0
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f00c03207107fff000000000", hexnat% "204000000000000000000", hexnat% "18000000000000000000", 335518172239101952, hexnat% "8d0000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400e1d205187fff000000000", hexnat% "800000080000000000000000", hexnat% "300002002000000000000000", 299489375220137984, hexnat% "850000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e07203103fff000000000", hexnat% "400008000084000000000000", hexnat% "800010084000000000000000", 299489375220137984, hexnat% "850000000000000000", hexnat% "300000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c10 c6
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e00e040060052b8000000000", hexnat% "18000000000000000000", hexnat% "100002000000944000000000", hexnat% "1ad0000000000000000", 633524856029184, 1560497270883876864]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f00c020c60a7fff000000000", hexnat% "204000000000000000000", hexnat% "18000000000000000000", 1515461274610171904, hexnat% "1a10000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400e1c0c50a7fff000000000", hexnat% "800001000000000000000000", hexnat% "300002002000000000000000", 362539770003324928, hexnat% "a10000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e060c20a3fff000000000", hexnat% "400008001004000000000000", hexnat% "800011004000000000000000", 362539770003324928, hexnat% "a10000000000000000", hexnat% "300000000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d00e06004004976000000000", hexnat% "18000000000000000000", hexnat% "200000002001288000000000", 633387417075712, 1560497270883876864, hexnat% "1ad0000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e04000000032000000000", hexnat% "400008001084000000000000", hexnat% "800011084000000000000000", hexnat% "300002002000000000000000", 686163975208960, 371692379670839296, hexnat% "a50001088000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c21 c12
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c22 c11
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c23 c5
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00267.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00267.record000
