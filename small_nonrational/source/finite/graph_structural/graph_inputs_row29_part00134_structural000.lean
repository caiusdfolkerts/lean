module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00134Data
public import GraphInputsRow29Part00134Frames
public import GraphInputsRow29Part00134Leaves
public import GraphInputsRow29Part00134Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00134.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005
def vertexColumn : Fields := ⟨10, hexnat% "bcd2aaaa68bab1a8e9392e2b86e4789e17b49aa6992e6c5a364d4b4ad1b51d2745dd0ec3a8e93c2e8b8ad2b2ac6b86d1b26c5ba1d8791cc749c6745c5783c8f2d14c0f0b29294a0e946298960d90e1382e078b1925490e545294950d50d1342d0768390d4328c930ce0b42c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9369b4924926d3692492492492492492492492249249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80040f4cfff00000000000", hexnat% "200100008000000000000000", 3674937295934324736, hexnat% "3f00000000000000000", hexnat% "7e00000000000000000000", hexnat% "440020000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20ff0288ffcb300000000000", hexnat% "4500000000000000000", hexnat% "440021200000000000000000", hexnat% "70024000000000000", 4714705859903488]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20ff0218ffca700000000000", hexnat% "4c00000000000000000", hexnat% "440021200000000000000000", hexnat% "70024000000000000", 4925812092436480]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "72038ffffff00000000000", hexnat% "200100000000000000000000", hexnat% "8800000000000000000000", hexnat% "4500000000000000000", hexnat% "440420200000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44fe23f0ffcbf00000000000", hexnat% "104000000000000000000", hexnat% "200000080000000000000000", hexnat% "30034000000000000", hexnat% "40000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "56023ffffff00000000000", hexnat% "200100000000000000000000", hexnat% "8800000000000000000000", hexnat% "4c00000000000000000", hexnat% "442021000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5e0267fffff00000000000", hexnat% "208000000000000000000000", hexnat% "100080000000000000000", hexnat% "4900000000000000000", hexnat% "442021000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20530228ffcbf00000000000", hexnat% "30034000000000000", hexnat% "8800000000000000000000", hexnat% "40000000000000000", hexnat% "4d00000000000000000", hexnat% "442421000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20ff00c8ffc9b00000000000", hexnat% "6100000000000000000", hexnat% "440021200000000000000000", hexnat% "70024000000000000", 5136918324969472]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20ff0058ffc8f00000000000", hexnat% "6800000000000000000", hexnat% "440021200000000000000000", hexnat% "70024000000000000", 5348024557502464]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3a01cffffff00000000000", hexnat% "200100000000000000000000", hexnat% "c000000000000000000000", hexnat% "6100000000000000000", hexnat% "440420200000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44fe23f0ffcbb00000000000", hexnat% "104000000000000000000", hexnat% "200000080000000000000000", 14707067533131776, hexnat% "70000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e017ffffff00000000000", hexnat% "200100000000000000000000", hexnat% "6800000000000000000", hexnat% "442020000000000000000000", hexnat% "c000000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7a0347fffff00000000000", hexnat% "208000000000000000000000", hexnat% "100080000000000000000", hexnat% "4900000000000000000", hexnat% "440420200000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "201b0148ffcbf00000000000", hexnat% "30034000000000000", hexnat% "c000000000000000000000", hexnat% "40000000000000000", hexnat% "6900000000000000000", hexnat% "442420200000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c23 c16
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c24 c15
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c25 c14
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200100089548000000000000", hexnat% "30034100000000000", hexnat% "46200200000000000", hexnat% "6d00000000000000000", hexnat% "442421200880000000000000", hexnat% "da00000000000000000000", 1055531162664960]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c28 c13
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c29 c0
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00134.record005
