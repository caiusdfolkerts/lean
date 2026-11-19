module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00281Data
public import GraphInputsRow29Part00281Frames
public import GraphInputsRow29Part00281Leaves
public import GraphInputsRow29Part00281Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00281.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000
def vertexColumn : Fields := ⟨10, hexnat% "3d13c2f07c3ca3a2e87aa9a6639996558d62d876c3a2e2b86e4789e1783e8e5392e479a966565555355352d475c352d2b46d4749d1743da8e6338d9354e332cc73c2e2b2ac6b86c9b16c3bc1e8761e4751e2729c6745c9715c3723c4f0bc1f3c0e48b0d2468c68390e384d12c4718a5190e4c5894a51960d4342d30d1324c5382d0b06e0741c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "136d36db4da6d26d36d24926d349249369b4934926d24924924924d2489249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩, ⟨105, by decide⟩, ⟨109, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "303c03e46f3e13bc00000000", 540959720865792, hexnat% "200102002c000000000000000000", hexnat% "300000000000000000000", hexnat% "208000000008000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220932002fe48f161fbc00000000", hexnat% "300000000000000000000", hexnat% "3c00000000000000000000", 527765581332480, 6928788026709508096]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "303c03e4ef3e13bc00000000", 540959720865792, hexnat% "200102002c000000000000000000", hexnat% "300000000000000000000", hexnat% "208000000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2209300223e4ef3fffbc00000000", hexnat% "10c000000000000000000", hexnat% "20000000000000000000000", hexnat% "3c00000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2209300023e4ef3fffbc00000000", hexnat% "2000c000000000000000000", hexnat% "300000000000000000000", hexnat% "3c00000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220932032fe4cf1f1fbc00000000", 246290604621824, 2314850208468434944, hexnat% "3c00000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2209323023e4cf3f1c3c00000000", hexnat% "30c000000000000000000", 250138895319040, 2305843009213693952, hexnat% "c00000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200303c03e4ef3e93bc00000000", 400222232510464, hexnat% "200102002c000000000000000000", hexnat% "8000000000000000000000000", hexnat% "300000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c7 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208303003e4c33e103c00000000", hexnat% "3000000000c0000000000", 531613872029696, 3170534137668829184, hexnat% "c0c000000000000000000", hexnat% "2001020020000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c17 c0
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200122002e24ea1bebbc00000000", hexnat% "3000000024000000000000", hexnat% "c00000400000000000000", hexnat% "301c00000000000000000", hexnat% "208100000000100140000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200803806e3fffbc00000000", hexnat% "30c440000000000000000", hexnat% "3400000000000000000000", hexnat% "2001020020200000000000000000", hexnat% "208100000008100000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220932002e248c000fac00000000", 6934417526243721216, hexnat% "3c00000000000000000000", 216172782113783808, hexnat% "301c00000000000000000", 1108376440274944]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200423406e3fffbc00000000", hexnat% "30c840000000000000000", hexnat% "3800000000000000000000", hexnat% "2001020000200000000000000000", hexnat% "208100000008100000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220932102f248f07ffbc00000000", hexnat% "300c00000000000000000", hexnat% "2c00000000000000000000", 6933291626336878592]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220932102f248f061fbc00000000", hexnat% "300c00000000000000000", hexnat% "2c00000000000000000000", 527765581332480, 6933291626336878592]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220132122f240207ffbc00000000", hexnat% "100c00000000000000000", hexnat% "8000000008d00000000000000", 6933291626336878592, hexnat% "2c00000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220932102f248f071fbc00000000", hexnat% "300c00000000000000000", 246290604621824, hexnat% "2c00000000000000000000", 6933291626336878592]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220932182fa46e3f03bc00000000", hexnat% "2400400000000000000000", 9295460417218281472, hexnat% "300000000000000000000", 246290604621824]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220932102f24021703bc00000000", 6928788026709508096, hexnat% "2c00000000000000000000", 10160151545673416704, hexnat% "300c00000000000000000", 246290604621824]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c29 c26
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c30 c25
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c31 c24
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c32 c23
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208103c2620ed3c1db800000000", hexnat% "200000000202000400000000", 529964604588032, hexnat% "2001020008040000000000000000", hexnat% "301c00000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f2fe4041c1d3800000000", hexnat% "220000000200000400000000", 1093464313823232, hexnat% "208100000008900000000000000", 6926536226895822848, hexnat% "2001000000000000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200122002ea40603ffbc00000000", 6934417526243721216, hexnat% "301400000000000000000", hexnat% "208100000008900000000000000", hexnat% "3c00000000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220922002ea4860203bc00000000", hexnat% "301400000000000000000", hexnat% "3c00000004000000000000", 6933291626336878592, 558551906910208, hexnat% "100000000900000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2208320c2aa0ef1e1d3c00000000", hexnat% "3000000020000000000000", 530514360401920, hexnat% "301440000000000000000", hexnat% "1000004000000000000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000003f2fe40c1e1d3800000000", hexnat% "220000000200000400000000", 530514360401920, hexnat% "208100000008100000000000000", hexnat% "1000000000000000000000000", 6926536226895822848]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000220222e00e03ffbc00000000", hexnat% "101040000000000000000", 6934417526243721216, hexnat% "208100000008100000000000000", hexnat% "100000c000000000000000000", hexnat% "3c00000000000000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000220022e00e03013400000000", hexnat% "301040000000800000000", hexnat% "3c00000004000000000000", 6933291626336878592, 277076930199552, hexnat% "208100000008100000000000000", hexnat% "100000c000000028000000000"]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c42 c39
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c43 c38
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨109, by decide⟩ c44 c37
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c45 c36
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c46 c35
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c47 c34
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c48 c33
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c49 c22
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c50 c21
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c51 c20
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c52 c19
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c53 c18
  c54
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00281.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00281.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002
def vertexColumn : Fields := ⟨10, hexnat% "3d0bc1f0f22e87aa9a6639996558d62d876c3a2e4b8ae1ba1e4789e1783e3c4b91e6a599595554b51d70d4b4ad1b61d2745d0f6a398d9354cb31cf0b4acab1ae1b26c5b0ef07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f390d48b11c388d28a91a384d18a5193162529465454951560d4342d074c388ca318d1324c5382d0b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "1369b6d369b69b6d36d36924924924924924924924db6d269349349b489249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩, ⟨89, by decide⟩, ⟨94, by decide⟩, ⟨98, by decide⟩, ⟨101, by decide⟩, ⟨106, by decide⟩, ⟨109, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24000027e6e78782440400000000", hexnat% "183800000800000000", hexnat% "1900000000c000000000", 4611686018427387904, hexnat% "244200000000012a0000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24000027e6e78782220400000000", hexnat% "183800000800000000", hexnat% "1900000000c000000000", 4611686018427387904, hexnat% "244200000000014c0000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2400002060018002000000000000", hexnat% "181e00000000400000000", hexnat% "60e000000000800000000", hexnat% "1000400000c000000000", hexnat% "60780000000000000", hexnat% "183800000000000000", hexnat% "244200000000016e0000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00281.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00281.record002
