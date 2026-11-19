module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00127Data
public import GraphInputsRow29Part00127Frames
public import GraphInputsRow29Part00127Leaves
public import GraphInputsRow29Part00127Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00127.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006
def vertexColumn : Fields := ⟨10, hexnat% "9d2aca723c1f1726a99a4e87aa99a6a59968d9361d8ce2b89e0fba1e47319c571aa5a9a65998e5391e6a569665a5595956354d475a34cd8b4ad8749d0f6a368d63a4d9354e334cc7362ccb4acab46c9b0ee8761cc789d2729e1745c970dc6c1706a168661588e1382e078691668589465854552344d0b41d60d2318d1314c8b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6d36da6db6d24936db6db6d269349a49249349a4d2492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨100, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101000365fe41fffd800000000", hexnat% "800000002000000000", hexnat% "e0000000000000000000000", hexnat% "200200000000020000000000000", 684547143360315392]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "16d3e40617d800000000", hexnat% "c0000000000000000", hexnat% "1e0000000000000000000000", 579002823186841600, 108297634728378368, hexnat% "210200020000030200000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10100032dfe09ffef800000000", hexnat% "4000000010000000000", hexnat% "e0000000000000000000000", hexnat% "200200000000020000000000000", 936748722493063168]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "16d3e08496f800000000", hexnat% "c0000000000000000", hexnat% "1e0000000000000000000000", 74388558688813056, 865536652896894976, hexnat% "210200020000030200000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800140b0d8bdff800000000", hexnat% "280c000000000000000", hexnat% "160000000000000000000000", hexnat% "20040004000000000000", hexnat% "210200000502030200000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000288cd8bdff800000000", hexnat% "14030000000000000000", hexnat% "1a0000000000000000000000", hexnat% "20040004000000000000", hexnat% "210200000502030200000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4020db3eff800000000", 3377699720527872, hexnat% "1e0000000000000000000000", hexnat% "12c08000000000000000", hexnat% "d4000100000000000", hexnat% "210200020102000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2103e0024d6a03027d800000000", 972777519512027136, 79302276153344, hexnat% "94000100000000000", 4362862139015168, hexnat% "12000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "908db3eff800000000", 3377699720527872, hexnat% "1e0000000000000000000000", hexnat% "16420000000000000000", hexnat% "210200020002000000000000000", hexnat% "d4000100000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e000010000003f000000000", hexnat% "16c00000000000000000", 981784718766768128, 2282586139262976, hexnat% "fe000000000000000", 2216615441596416, hexnat% "210200020000010000800000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c17 c2
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00127.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00127.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007
def vertexColumn : Fields := ⟨10, hexnat% "1f3a2e4b329c972aa9aaa699a8e93a1eaa669a9665a364d876338ae2783ee8791cc6715c6a96a699666394e479a95a5a55958d5351d4cd2b49d0f783c8ea368e6358f13a4d9394d538cd331ce8b62ccb8ad2b2ae1b46c9b0ee8761cc789d2729e1745c970dc6c1706a168661588e1382e07869164651548d1342d0768360e2348c6384d1314c8b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "4db6db6db4db6da4926db6db6da6db6d2492492492492492492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨80, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨103, by decide⟩, ⟨115, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e00000000000000000", hexnat% "f00000000000000000000000", hexnat% "80081000102000380200800000000", 8935634722948644864, hexnat% "f800e038000000000", hexnat% "1000701c0000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00127.record007
