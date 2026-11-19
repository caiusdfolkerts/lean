module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00227Data
public import GraphInputsRow29Part00227Frames
public import GraphInputsRow29Part00227Leaves
public import GraphInputsRow29Part00227Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016
def vertexColumn : Fields := ⟨10, hexnat% "7c1e8761b85e0f85d0f45b0ec570dc4f0bc1f362b89e2749ca6a96a3a99a568da9996639a56558d6538ce8b92e2b86e4789e17b61b85e1745b15c4f16a5994e4b99956539655554d54d4b51d62d4b4ad4749d0f743b0dc3c8ea368e6358ce364e5354cd362e2b4acab91d4731e2749ca719e1745c9715e0f43c8f0be64548d24689a91856079292a519266250b41d44c9342c8b06e0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6db4db6924da49b6db4936db6d24936db6da4924db6db6d349349369b692492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨103, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "879c02032000002e2408000000", hexnat% "c00000000000000000000", 1946157056, 2053641430089334784, hexnat% "c00300000000000000", 824684052480]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "870c0e02e01e802ce03a800000", hexnat% "1000100000000000000", hexnat% "800000000000000400000000", 2199107141632, hexnat% "100000000000000040000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "860c0803e01f802ee47f800000", hexnat% "900000000000000000000000", hexnat% "1000600000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "868c0802e01e802ce43e800000", hexnat% "1000000020000000000", hexnat% "1000600000000000000000000", 72057594054705152, hexnat% "100000000000000040000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80880802e01e800ce422800000", hexnat% "4000001000000220000000000", hexnat% "40400000100000011000000", hexnat% "100200000000000048000000", hexnat% "3000000000000000000000000", 67108864]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80040400601d8002c457800000", hexnat% "1800200000000000000", hexnat% "900000000000002000000000", hexnat% "4000002000000200000000000", hexnat% "3080a00000000000000000000", 13194810621952]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "839c0e02e01f800ce43b800000", hexnat% "4000001000000220000000000", 1140850688]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "839c0a03c00f800ec42b800000", hexnat% "200000002000000000", hexnat% "4000400000000000000000000", 35185714266112, 1152921504673955840]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "839c0a03a01e002ee47f800000", hexnat% "4000400000000000000000000", hexnat% "400180000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "839c0a03a00e000ee46b800000", hexnat% "4000000000000200000000000", hexnat% "400180000000000000", 1152921504673955840, hexnat% "400000000000010000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "831c0e00000f000cc03b000000", hexnat% "800000200000002400000000", hexnat% "4000003000000220000000000", 1149239296, 1188950301625810944, hexnat% "c00000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800c0403c01f8000c011800000", hexnat% "800000200000002400000000", 2199123918848, hexnat% "100200000000000048000000", hexnat% "7000800000000000000000000", 48379048493056]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "87880003200c002e2479000000", hexnat% "e00000000000000000000", hexnat% "140000000000000000000000", 1188950301701308416, hexnat% "c00300000000000000", 824667275264]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "871c0e03c00f802e803b800000", 155759673344, hexnat% "800000000000004000000000", hexnat% "201000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800c0803c00f8022c023800000", 1152921521853825024, hexnat% "900000000000002000000000", hexnat% "7000600000000000000000000", 1476395008, hexnat% "2000000c0000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840c0403c01f8022c011800000", 1711276032, hexnat% "800000200000002400000000", hexnat% "100200000000000008000000", hexnat% "3000800000000000000000000", 13194139533312]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80080002201e00200401000000", hexnat% "1c00180000000000000", hexnat% "900000000000002000000000", 3023698919424, hexnat% "7000e00000000000000000000", 2080374784, hexnat% "400000000000c0000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c26 c19
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c27 c18
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c28 c17
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c29 c8
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c30 c7
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c31 c0
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record016
