module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00215Data
public import GraphInputsRow29Part00215Frames
public import GraphInputsRow29Part00215Leaves
public import GraphInputsRow29Part00215Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00215.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000
def vertexColumn : Fields := ⟨10, hexnat% "7915c2f1e2568ba719a6598e6c5a96659562da4e53a2e2b86e8791e2785e0f9e1564b9715a5594e5c5695554b59354d8b4ad4749d1743d70da358ce3c4e9354cb392d4b8acab46c9b16c3bc1e8761e4751cc789d2729c6785d1725c570de0f43c8f13c2f07d941b21c6486a869911a6196154529465855152560d1342d0758350ca318e1344c9382c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db4db6da4db6db4924924924924924924924926d34db4924da6d2449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "feff22ff2811380000000", 13835060804061233152, hexnat% "d1000000000000000", hexnat% "10000000080000000000", hexnat% "8180000000000040000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ef6fffff28d9380000000", hexnat% "9000000000000000000", hexnat% "100000000000000000000", hexnat% "8180000000000020000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "eeff13ff2811380000000", hexnat% "e0000000000000000", 13835060804061233152, hexnat% "110000000080000000000", hexnat% "8180000000000040000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ee4eb2e22810000000000", hexnat% "b100000000100000000", hexnat% "110000000080000000000", 15046526355044827136, hexnat% "40100000000000000", hexnat% "8180000000000069280000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffbfff08f8380000000", hexnat% "40002000000000000", hexnat% "800000000000000000000", hexnat% "8180000000000001000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fbf8f5f00f8180000000", hexnat% "70000000000000000", 720576017688690688, hexnat% "804000000800000000000", hexnat% "8180000000002000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffbf4f1f00f8180000000", 720576017688690688, hexnat% "b0400000000000000", hexnat% "4000000800000000000", hexnat% "8180000000002000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3ff0c1400c0100000000", hexnat% "c0000000038080000000", hexnat% "d1000000000000000", 1058345912432066560, hexnat% "22000800000000000", hexnat% "8180000000002001200000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "311ff5f2088000000000", hexnat% "f00000000000000000000", 720576024131141632, hexnat% "c0c00000030000000000", hexnat% "8180000000000840000000000", hexnat% "e200000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81800ebf7dbf28f9380000000", hexnat% "d10000000000000000000", hexnat% "82400000000000000", hexnat% "204000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4fffbfff0878280000000", hexnat% "b00000000000000000000", hexnat% "40002080000000000", hexnat% "8180000000000001100000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "25cf3ff0840280000000", 13835061903572860928, hexnat% "a300000001100000000", hexnat% "f00000000000000000000", hexnat% "d0000000000000000000", hexnat% "8180000000002080000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21001f70000080000000", 16176930961026449408, hexnat% "f0000000000000000", hexnat% "eb00000000000000000", hexnat% "d0400000008000000000", hexnat% "f00000000000000000000", hexnat% "81800000000028e1300000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c23 c6
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00215.record000
