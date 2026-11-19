module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00034Data
public import GraphInputsRow26Part00034Frames
public import GraphInputsRow26Part00034Leaves
public import GraphInputsRow26Part00034Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00034.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014
def vertexColumn : Fields := ⟨10, hexnat% "6d2cc670bc1f1b2b299a2e87ae1ac6a99a665a56559362d876a398e938ce2b86e4789e1783e1e785a95a5955554d475a358d934ad1b51de0ea368e5354d331ce8b62e4b2ac6b46f07a1d8791d4789d2729c6785d1715c3783d0f23c4f0bc1f2b05c0f0aa1683a1643991515154351342d0764344c530cc4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6936d26db6db6db6d36d24db4926d249b6924da4936d36db6926da489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6300021893c08c0001c00000", 1143630068711424, 6917529028983259136, 846623953387520, hexnat% "200000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21000008f2c7860070400000", 17729641775104, hexnat% "2100100080000800000", hexnat% "200000000000000000", hexnat% "420000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "230f2c3822071c00000", 1147890139398144, hexnat% "600000000100000000000000", hexnat% "10000080000000000000000", hexnat% "20000000000080000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2100023893c49e2071c00000", 844424930131968, 6917529027641081856, hexnat% "420000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21000038f2c6962071c00000", 281474976710656, hexnat% "2000100080000000000", hexnat% "420000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "63000238f3c28e2071c00000", 1143492092887040, 281474976710656]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "63000238d1c08e2071c00000", 144132780261900288, 2306124484190404608, 1688849860263936]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "61000038f2c6962071c00000", 281474976710656, hexnat% "2000100080000000000", hexnat% "20000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "61000038d2c0962071c00000", 2306124484190404608, hexnat% "2000100080000000000", hexnat% "20000000000000000000000", 1688849860263936]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4200023813801c2071c00000", hexnat% "210000000000800000000000", 2306124484190404608, 13853072453791645696, 1691048883519488]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "420002381380182071c00000", 2306124484190404608, hexnat% "210000000000840000000000", 13853072453791645696, 1691048883519488]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2100021811879e0070c00000", 16158915463005339648, hexnat% "200000002001000000", hexnat% "420000000000000000000000", 144115188075855872]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208d287962061800000", hexnat% "100100080000000000", 2323857407995805696, hexnat% "420000000000000000000000", hexnat% "210000200000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600002181184800040800000", hexnat% "300000000000c0000000000", 144132918254501888, 846624226017280, 16158915463005339648, hexnat% "200000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c23 c2
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c24 c1
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c25 c0
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00034.record014
