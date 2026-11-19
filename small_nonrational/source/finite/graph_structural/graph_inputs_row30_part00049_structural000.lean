module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00049Data
public import GraphInputsRow30Part00049Frames
public import GraphInputsRow30Part00049Leaves
public import GraphInputsRow30Part00049Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003
def vertexColumn : Fields := ⟨10, hexnat% "1b8cd2745d1ac3b23c4f07ccc9b29c9726a8ea66a3a4e8ba1eb26a99a69996639b16959568d9361d98e33a2e4b8ae1ba1e4785e0fb316c6715c5a93a5998e5392e479c96a569665594e5c5655556354d475634cd8b52d2b46d8751d1743dc4d9394d5362ccb86d1b26f07a1e4751cc785d1715e0f43c1f1e1a42b06c169862384e165852344d60e1344c5322c4b06e0741c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db69369b6db6db4da6db6db69369369b6db6db69b4db6db6d26d26d3492492492492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩, ⟨110, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000020400000102fffff000000", hexnat% "4000000000040001000000000000", hexnat% "9000600000000000000000000", hexnat% "40000004000008022000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000000204000001020ffff000000", 16492674416640, hexnat% "4000000000040001000000000000", hexnat% "9000600000000000000000000", hexnat% "40000004000008022000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000066400000130f7fff000000", hexnat% "40000000000000020008000000000", hexnat% "4008000000040000200000000000", hexnat% "1000000008000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2400800664004003328c7ff000000", hexnat% "40001000000008000000000000000", 7937099563008]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240080066400400132847ff000000", hexnat% "40001000000008020000000000000", 7937099563008, 549755813888]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24008006640040013284247000000", hexnat% "40001000000008020000000000000", 24561844224, 5050881540096, 3435973836800]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000026000000332f7fff000000", hexnat% "40000004000000000008000000000", hexnat% "4008000040040000000000000000", hexnat% "1000000008000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000100660000803328c7ff000000", hexnat% "4008000040040000000000000000", 7937099563008]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240080026400400332847ff000000", hexnat% "40001004000008000000000000000", 7937099563008, 549755813888]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24008002640040033284247000000", hexnat% "40001004000008000000000000000", 24561844224, 5050881540096, 3435973836800]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6400100660000803300d242000000", hexnat% "8000040040000200000000000", 16664473108480, 24645730304]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000000600000803200c7ff000000", hexnat% "9000600000000000000000000", 16733192585216, hexnat% "4000000040040001200000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240090066400480132f7c79000000", 15133048832, hexnat% "40000000000000020008000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "62000000110f7fff000000", hexnat% "40000000000000020008000000000", hexnat% "4008000040040000200000000000", hexnat% "20000000400000002000000000000", hexnat% "1000000008000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c21 c19
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240090066400480132f7979000000", 28017950720, hexnat% "40000000000000020008000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "640090066400480332eda53000000", 1237621669888, 23689428992]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400010062000080310eda53000000", hexnat% "20000000400000002000000000000", 1237621669888, 23689428992, hexnat% "4008000040040000200000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c28 c26
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400010060000080300ac040000000", hexnat% "20000000400000002000000000000", 5738076307456, hexnat% "4008000040040000200000000000", hexnat% "200000001000000000000", 33269219328]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c31 c25
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c32 c22
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c33 c18
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c34 c17
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c35 c16
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c36 c9
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c37 c2
  c38
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record003
