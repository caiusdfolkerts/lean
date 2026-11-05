module
prelude
public import GraphInputsRow29Part00213Data
public import RawFrameSupport
public import SharedFrameGroups066Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xe9672db889b2cd7367eb36991ec8263db0c97e4bc95d2ae396a0b27581abb15aaac755caa9953ea104f0a61d2ca931490a43d1a88b243f21b90b884b41f20dd0627d93cf9d9ce8273137a9af4d2e68733a99a0cb465332198f4b7e5992b01510a4c51728393e49a64b724c92288f446c23291708ae4512008eec7203811af8d3867e32f18f8bfc5d42d915f0ab453c28e13f0978492238118888c438216103077836a1780b5856027813009204541fe0f307383601a405e02c813409604102000dc06c029013008804201d00c805c02200f00700300140090030014002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record000_frame001_links_0000 (interval_append _ 64 128 137 record000_frame001_links_0064 record000_frame001_links_0128))
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xd4f69f3405978ca962eb10d7c4bbc5d32df16c0b3b5912c555e8acc559aaa1516a7453028b14329bf4d1256926e905478236913e87c426a0e904a8073f01f28f6c78a3b41d00e547253809b48d706b234c99f0cc26563151864b965b42c595bcab054429994949f44dc26212c093e491241118c8a84402088f747823be1cd8e2c6f636b1b10cf864a31317a0b885a62c115c0a544fa26b12c88d04442120fe87783821940c385dc2a214109884782020f3073035419205e02c813409604102000dc06c029013008804201d00c805c02200f00700300140090030014002000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record000_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record000_frame002_links_0000 (interval_append _ 64 128 137 record000_frame002_links_0064 record000_frame002_links_0128))
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1cb0de468831e989ac3b5f9adfd556a154f4275937099d4c7a6312fc9784ada555292947495249122a90f48423f11ea8ec472236512a8113961974c8a5f52dc1644b185612a713e09b44d524411d888e43620e0fc07c23cb1c30d2464431d1790b7c51226b133086440e1d80e386b43021720ae055c2a01470a104e4268128090846821e10b08183f81f00ee07503901b80d906802a014c09c048824011808504181e40dc06d03480d405c02c013009004201e00e006402e0110078030012007 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6e76c468e66b65e65a64661c5df5b95ac5a759257255c55b5495415255185055034e64de4cd4c04b54a549e49649248846b4313d739e39a37d35c3463453313273062f92f82d82ce2b72af2a329729428e27425023a23922521d1f21e41e21c01b819b19218617517116a16415b14b14913913812611a10f0fd0f80ec0e80e40d30ce0c50bc0ba0ad09909809108b08a08607f07d07506c06b06703502e02c02602402101e01c01901701100f00c009007 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x293d0d9c52e6564a492f1fe2942983505202bf57d6fa9efbd8786ef1d7bae730e45c237d6eeda5b2b5f6b2d45a43295f2b015daab52aa1d42a7a4ea969292514668b10c2124047d0f79e53b2714da9b3346670bd96c2d6550a793e2724c09011c226444851021fc3d87a0eb1cc3806a8d319832c638bc1742d4578ae14a230458861001fc3e0760e81bc348680ca0cc1602b04a08c1001d0360640b81101e03004807 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x34b5a30d0a66eb30995ec8362ab0ed6c2b3758f2bd5590aaf545aa154e8a6e5302941484a24508a7a536e99a4b7258929693f496a4712168ed46ba2c113088d43aa1c50be84341a207ced27463981c08db26bf34c9a38cf86713309958c9463231097e4ba65bc2cd1644afc5752b3156ca9c53929594209e64ea26a93489884ab251125073637b1b10d4865231717a0b4c5702a814089bc4b223411108383dc1d10dc86ac30c1760b2050026011f04c025812605902b81580aa02100f807803a011007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record002_frame001_links_0000 (interval_append _ 64 128 131 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x33c99c2cd3645b1c58c6c29603aff95e4ad2562aa3d4dea6151d28a5424a084f8a7893b09c14daa5f52ae94748da4291de8e446522e115a893443217508083240d203cffc7e63ed9f48dfe6d83641a38cd265a3191890c1c6042f79784bae5c22db1610abe5502951470a0a4fc27513689a24bf259924c8f647122f115c892436217909867431517b8ba05942bf14e89e04c025211d08c44441ff0f9079438c1a80c806142da1640aa84bc24411604c025812605902b81580aa02100f807803a011007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record002_frame002_links_0000 (interval_append _ 64 128 131 record002_frame002_links_0064 record002_frame002_links_0128))
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x11c2364688bd16229c4b88b0fe003f67def89ecbd4796f25e13c0774ed5d9bad752e75c9b8c704df5b9b6e6cad81adb5269cd059c334656c9d91b1a62cc49652bd56caad51a9e52aa4544a854fa9e53aa6d4d29792aa4f48a9011c2334568a111a1b43083101a003ee7d0f89e83ca788c41762ca580a794b2824d494925232454869031f83d4738da19a3285e8ba16429c5089b0d219c328430821001f81e03806c0d01101e0380680c0140240400600800c01000 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record002_frame003_links_0000 (interval_append _ 64 128 131 record002_frame003_links_0064 record002_frame003_links_0128))
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x3aa5cf2e566f4b6e5b2cd5b6a334e18a6c105f42e516b6b3b5802bd15b6ace559aa81526a7b534a8a13de9cf4ca26212de9624a3a4d124e90f47ea39d1bc8d9468232d1888bb45b22bcfe27b53c89cfce186ec35b9ab4d2868a33a9988cac63c31597a8b6e5972b11560a7e5352901434a024e726b130096e4b2255129493c49524812246d434118c8c105b42c71548a284d625b11e08b44361fe0f8078838c1a70c405e02b214a09c046c21a0ff04c025812605902b81580aa02100f807803a011007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record002_frame004_links_0000 (interval_append _ 64 128 131 record002_frame004_links_0064 record002_frame004_links_0128))
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x82e81880c7e97d77cb7b179f79472b7116ff6e36c36b269769068167c67266865d64d64162860a5f85dd5d85cc5c55b75ad5a259258757456a56655c55955454b54653f4e04c44af48a46945743a43442441d4104063fb3e83dd3bd39f38d36f36835935334333932e31b3102ff2f52f12e72e42df2d62d12ca23221a2041f51de1d41c31b51a81a118f18617a16715e15614313512812110d1070fa0e50e00d609609409105905705605502101f01e01d01100f00e00d00c00a009008006004003002000 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record002_frame005_links_0000 (interval_append _ 64 128 131 record002_frame005_links_0064 record002_frame005_links_0128))
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x7086fc6f26d16c16b369a69068961a6085ff5dd5cd5c35ab5a359358e57e57456e55d55654052f5215095014f14eb4da4d24cd4bd4b44a649e49a49048c48647c47847241a4033f73d43bf3b439a39337f37936c36035b34f34432b3163052eb2e42d02cb2bf2b12ab29e29528727f27a27126d26725e25a2551dc1c81b61ad19b19518717616e16815d15815213e1391321251121071020fa0f60f00dc0d40d109409208f05705505405302101f01e01d01100f00e00d00c00a009008006004003002000 } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record002_frame006_links_0000 (interval_append _ 64 128 131 record002_frame006_links_0064 record002_frame006_links_0128))
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
def record002_frame007_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x404dfbcfb578a3b5dd5ee3b6fc3725842be15dbad5d632af455a2a9d518a7f5312941484a27509a73532c97049aa4a121e904475235d1968b044ea1d90bc85241e20c103e8073fd9fa4dda6ad341988cbca5c02c015ccab054b2971470a1c4f326f92648c443c2008fd07b63d01db0e8c72e37c1b48d0865431e1840bf05d62d31638ad44101fa0f607943ae1d00e106d034c19f0c886283021730b605942b214b09e84d825012108c04282060fc04c025812605902b81580aa02100f807803a011007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record002_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record002_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 7)
      (record002.inverseMaps 7) record002_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record002_frame007_links_0000 (interval_append _ 64 128 131 record002_frame007_links_0064 record002_frame007_links_0128))
theorem record002_frame007_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 7 :=
  of_group record002 7 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame007_indices record002_frame007_graph record002_frame007_links
def record002_frame008_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x72f7297237066fc6f26d96d16c764162a61e5fe5e95de5ce5c75bb5b55a859d59758657d55f54753a52351a50a5024f54e84e04ce4c44b34a449f49549248847b47546e4043f03e23c03af3a239238b37e37836735d35734a34132230b2fe2e72de2cc2c42b22a729f29228827726826225524f24623c2392321bb1ae19e19618617f17916b15d15514714013c13312e12711e1141071000f30ed0e90de0d90d309609409105805605505402101f01e01d01100f00e00d00c00a009008006004003002000 } : Fields).get c.val)
theorem record002_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record002_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record002) (record002.maps 8)
      (record002.inverseMaps 8) record002_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record002_frame008_links_0000 (interval_append _ 64 128 131 record002_frame008_links_0064 record002_frame008_links_0128))
theorem record002_frame008_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 8 :=
  of_group record002 8 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record002_frame008_indices record002_frame008_graph record002_frame008_links
def record002_frame009_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1045.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1045.count (({ width := 11, code := 0xfbdf63ea7c2f79edbd37a0f31cc39271ce01bc3726ccd89ac355698d19a1b3966aca18fb17614c197e2f85deba572ad95a8b2560abb56aac155aa453ca65362664c494d26a454708d11522643485508a084047ccf61e43b0750e51c737a6e0da9ac34e674ca98f310608bf1782e65b49c1332564a09011c230438831011f23d0770e61c43706b0cc1882fc5b8b21582904f89a0e81c83804808c1142202103e0780e81101e0380680c0140240400600800c01000 } : Fields).get c.val)
theorem record002_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record002_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1045.localPairCheck (smallEmbedding record002) (record002.maps 9)
      (record002.inverseMaps 9) record002_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record002_frame009_links_0000 (interval_append _ 64 128 131 record002_frame009_links_0064 record002_frame009_links_0128))
theorem record002_frame009_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 9 :=
  of_group record002 9 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1045
    Papers.RationalityTen.SharedFrameCatalogue.group1045_facts record002_frame009_indices record002_frame009_graph record002_frame009_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (Fin.cases (record002_frame007_supported hcells) (Fin.cases (record002_frame008_supported hcells) (Fin.cases (record002_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x19bacc2657b2118b0c3e5b0acdd63ca8b53a29814a0a24508a7a536e99a4b7258929693f496a4712168ed46ba2c111a87142fa0d103e7673a09cace026d735e9a64cf866132b18c8c425f72e696d8b5259a2c295f8ad25662ad9500a7252b28413e09d44da26913109604a224a10487c43c61cd8e246f63691b10d4867432918b8bd05a62b81540a044de25911a088841c1ee0ee87443801b90d5865430c1760b2054c28013008f81640ae05602a811c08a04201700b005202100f807803a011007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record003_frame001_links_0000 (interval_append _ 64 128 130 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1916c71631b0ad812bff5792b4958aa3a50927c53c49c14daa5f52ae94748da4291de8e446522e115a893443217506480f3ff1f6cfa46f93691b18d1666632c98c8c1c5ef2f09708b6c57e2ac9538a7c52a28694149de4ea26d131097e4b324992008e246322b912487642f2130e846f236819d0c8462a30317b8ba05ac2ca15f8a744f026012908e84622220ff87c83ca1c60d906a03321900c285d82da1640aa851825e12208b01640ae05602a811c08a04201700b005202100f807803a011007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record003_frame002_links_0000 (interval_append _ 64 128 130 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x22f4588a713223440800fd9f7bcb784ee9dabad752e75c9b8c704df5b9b6e6cad81adb5269cd059a327646c59892c8576ad1552a253aa5544a7d4f29b534a5c4a693525a454748e116a2b4508750da18418815001f93e87c4f51e53c46a8cd9933105f0bb16a2ca580aa14f2965049a92924a4648a90d2063f07a8e71be368690cd1943085e8ba1642b4538a113610c2084007e0e01b0340500981201e03806c0d01101e0380680c0140240400600800c01000 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record003_frame003_links_0000 (interval_append _ 64 128 130 record003_frame003_links_0064 record003_frame003_links_0128))
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0xb5ad2b3ecbb22c5a468aa126196e5594a4c926428f2388be2c8a2258861e86e178520c81a007f9f87d9d4731c76f5b56c1ab699a167d9a6618f625856117f5ed7a5d9755cd6f5b96c5916057559559545414d52d2b4751543103400f73d0f13a0e5388dc34cca320bf2f4ba2d4b12b4a52809d2609524c8e22c89214821f87b1e0400f83d0f0350cc31098250901e0701b0681103c0e0340c02809020060100300800 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record003_frame004_links_0000 (interval_append _ 64 128 130 record003_frame004_links_0064 record003_frame004_links_0128))
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0917.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0917.count (({ width := 9, code := 0x2a14fa7536994b9b4ce612792c8e431f8ec6229118743215088341205007f3edf2f77b3d1e6e26f36db2d76ab4da2cf66b2d92c35faf176b95b2d564b157ab156a95329146a15027d3a9c4da310e84409f4f8783b9d8e471381b8d46632984c05e2e16cb457299489c4d261208e46229108642208c8602f170b0562a12890461d0d8683211078381a0c0502410060200c0400 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0917.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0917.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0917.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0917.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0917.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record003_frame005_links_0000 (interval_append _ 64 128 130 record003_frame005_links_0064 record003_frame005_links_0128))
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0917
    Papers.RationalityTen.SharedFrameCatalogue.group0917_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xb5f598ac615e8ac6556aa2d4e8a6052828914229e84da265d2dc94b496a4711da8d745822350e285f41a207cece7413959c04dae6bd34c99f0cc26563191884bf05d12dd1668afc5662ad94e4a5650827513489884a224a10447be3c31d68e6c6f63621a90ca462e2f41710b4c5822b81540a4c50226f12c88d044420e0f7077c3a21c20dc86ac32e1860bb059028013008f81fc0fa07a02c815c0ac055023811408402100f807803a01900b8050022010007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0xaed566ab0d518a6c53028e94249f14f1270536a97b4aaa5192368ef46522e112688642ea0c901e7fe3ed9f48df26d23631a2cccc6593191838bde5e12e116d8b0455d2a794a8a0a4ea26d12fc966493238915c89242f2130e746ea3671a80ce862a2f71740b2857e29d14489e04d8260129091847423111107fc3e41e50e306d035019b0c806142f016d0b2055425e12208b01fc0fa07a02c815c0ac055023811408402100f807803a01900b8050022010007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x3fe7e8fb5f0bd87a6f2de13ba76aeb5d4b9c724e2dc13736cad81a934e682cd193b2362cc49642bb568aa95129d52aa253ea794da9a52ea5449c9151c22b45086d0c20c4007d0f89e53c46a4cd192320620bb1652c053ca59412784d49812924a4808c91521a40c7e0f51ce3806d0d319a328618bd1742c8538a113616c2c8570861042003f0700d81a01e03806c0d0160280480881001e0380680c0140240400600800c01000 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0x28fa22829da6d9a26196e5594a4c926418ee378be288861e85e1483206801fe7e1f6751cc71dbd6d5b06ada66859f669986418a6197f5e9755cd6e5b164575565514d52d2a471144490c400f43c4e5388dc360d333cca320c42fcbd2e8b52c4ad294a1274992549323c8b224851f87b1e057154531003e0f43c0d4330c41e0701b06816050120441003c0e0340c02809020060100300800 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame004_links_0000 record004_frame004_links_0064)
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc1a5ed2ec16a8b16578aad1518a62528289d4269ca4c9a5b526a90f475235d16089d43b214906081f3fd9fa4dcc6a633e1880bc45bd2c01560a5c51c279937c92c45f21c90047b63b61d18df06d234218f0bf05d62c715a88f845221b10788203f41ec0f2875c3a01c20dd06d03581a60cf865c32218a0c085cc2d81650ac854429614309e84d825c128090846021410307e01fc0fa07a02c815c0ac055023811408402100f807803a01900b8050022010007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame005_links_0000 record004_frame005_links_0064)
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
def record004_frame006_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6706566446306146005eb5db5ce5c65af5a258756b55954753452651f5084fb4e84d94c94c04a749a43641c40c3f63d93c83b03a239438c37236834d33032130b2fc2ec2e52cb2c22ad29d28f28626a25f20e1f81e91e11d91c81b91b61a81a019018717f17617016c16515f15714d14013713012812111c11511010d1071010f90f10e60df0d807d07b07805705505405304704504202101f01e01d01901701401101000f00e00d00c00a009008006004003002000 } : Fields).get c.val)
theorem record004_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 6)
      (record004.inverseMaps 6) record004_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame006_links_0000 record004_frame006_links_0064)
theorem record004_frame006_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 6 :=
  of_group record004 6 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record004_frame006_indices record004_frame006_graph record004_frame006_links
def record004_frame007_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x63c62661c5fc5e75dd5ce5bb5a859d58657d55e54653952350a4f54e84ce4c44b349f49248847546e4003eb3e03be3ad3a139237e36735d34a34132130a2fd2e72cc2b22a729228827726224f2462392321e31cf1c81c11bb1ae19e19618617f17917116b16415d15514e14714013c13312e12711e11911410c1071000f80f30ed0e90de0d90d307e07c07905805605505404704504202101f01e01d01901701401101000f00e00d00c00a009008006004003002000 } : Fields).get c.val)
theorem record004_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record004) (record004.maps 7)
      (record004.inverseMaps 7) record004_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame007_links_0000 record004_frame007_links_0064)
theorem record004_frame007_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 7 :=
  of_group record004 7 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record004_frame007_indices record004_frame007_graph record004_frame007_links
def record004_frame008_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0938.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0938.count (({ width := 9, code := 0x17cbc5dae56fb6daecf63b0d76b756a953e93429dce6653095ca24b2490c821b0983c0e00fe7e3e1e8f2773b1cee370369a6cc6530d82bc5cad96ab258a853a9b4d261268e46a210e83401fcf87b3d1dcec75391b8d86a3318cc45f2f174b4592c154a04e2611086421a0c86230170b4581e0e06c34160a0482210078381a0c0502410060200c0400 } : Fields).get c.val)
theorem record004_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0938.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record004) (record004.maps 8)
      (record004.inverseMaps 8) record004_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame008_links_0000 record004_frame008_links_0064)
theorem record004_frame008_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 8 :=
  of_group record004 8 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0938
    Papers.RationalityTen.SharedFrameCatalogue.group0938_facts record004_frame008_indices record004_frame008_graph record004_frame008_links
def record004_frame009_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0961.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0961.count (({ width := 9, code := 0x18cc3e0eff7bbc5dae972b85bad967b258ac15cac55aa550a6d2a8f46a1d0a612b93c8e3f1c8d4622d148944217088341200fc7d3d9e8f1773add4e77335198c863b0d78b559ab154a65127d36984b2491e8d462250c833f9ecf275399c4da6b34994c6612f93094481d0e06e36180b8581e0e06c34160a0482210078381a0c0502410060200c0400 } : Fields).get c.val)
theorem record004_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0961.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0961.localPairCheck (smallEmbedding record004) (record004.maps 9)
      (record004.inverseMaps 9) record004_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame009_links_0000 record004_frame009_links_0064)
theorem record004_frame009_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 9 :=
  of_group record004 9 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0961
    Papers.RationalityTen.SharedFrameCatalogue.group0961_facts record004_frame009_indices record004_frame009_graph record004_frame009_links
def record004_frame010_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xc4d604af85722b5859c2c015b6ab355029ed4d2a254f6273132896f4a3a4d121e8fd473a3651968c445b22bcfd47ae3c51cf0e126e935b9a50cea66231e18acbce5b42ca1588a7e520286939c9ac4c0259129493c49024490607a23a61bf8da86823191820b6858e2a914c0a284f226b12d892c47822d10d87f83e01e20e306d434e1960c405e02d01590a504e023610d07f81fc0fa07a02c815c0ac055023811408402100f807803a01900b8050022010007803801a00c0050024010006002000c004000 } : Fields).get c.val)
theorem record004_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 10)
      (record004.inverseMaps 10) record004_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame010_links_0000 record004_frame010_links_0064)
theorem record004_frame010_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 10 :=
  of_group record004 10 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record004_frame010_indices record004_frame010_graph record004_frame010_links
def record004_frame011_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x72970e6fc6e26c16b069768167266864d6416276085f65dd5cc5b75ad59258757456655955454653f4de4bf4aa48946745543a4244104063e83dd3bc39d38b36f35934333931b3102ff2f12e42df2d12ca28726324c23c23221a2041f51de1d41c31bb1b51ad1a81a119618f18617a16715e15614313b13512d12812111610d1070fa0e50e00d607f07d07a05905705605504704504202101f01e01d01901701401101000f00e00d00c00a009008006004003002000 } : Fields).get c.val)
theorem record004_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 11)
      (record004.inverseMaps 11) record004_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame011_links_0000 record004_frame011_links_0064)
theorem record004_frame011_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 11 :=
  of_group record004 11 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record004_frame011_indices record004_frame011_graph record004_frame011_links
def record004_frame012_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x6186065fd5db5cc5c25ab59357e57455d55653f52d5205094f14da4d24bd4b44a649a48c4864784724163ff3f53d23bd3b339a37f36c36034f3443293143042eb2d02bf2b129e29528727a26d26725a2552171fe1f31e81dc1c81b61ad19b19518717b17617116e16816215d15815213e13913212511911210c1071020fd0fa0f60f00dc0d40d107b07907705705505405304504304002101f01e01d01901701401101000f00e00d00c00a009008006004003002000 } : Fields).get c.val)
theorem record004_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record004_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record004) (record004.maps 12)
      (record004.inverseMaps 12) record004_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record004_frame012_links_0000 record004_frame012_links_0064)
theorem record004_frame012_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 12 :=
  of_group record004 12 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record004_frame012_indices record004_frame012_graph record004_frame012_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (Fin.cases (record004_frame006_supported hcells) (Fin.cases (record004_frame007_supported hcells) (Fin.cases (record004_frame008_supported hcells) (Fin.cases (record004_frame009_supported hcells) (Fin.cases (record004_frame010_supported hcells) (Fin.cases (record004_frame011_supported hcells) (Fin.cases (record004_frame012_supported hcells) (fun j => Fin.elim0 j))))))))))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x695b441a04cdb65bb29190cc63624b08182ac065fdafc17cebd35dd2e915e6ac35552a354eca61529a8994269e74d8264d2e094d497247d1de8d9462a2cd13289043b21c90c484441ba08902a7ea3ea1ef8e046d935f9a58cf266032998bcc3c5f92e996f0b2e57b2b29560a6c52828594049da4e3269931c9744a524b91fc8b844d21e904c7c83c81cf0df86c63551960c685e82de1698af45702a81470a044de25711908804181ee0ed074437a1b90d5864830c1760b104f825c11d08784141e40e506b03280ea07303801980c806101a80cc064031013009004602200600280120080030010006002 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record005_frame001_links_0000 (interval_append _ 64 128 144 record005_frame001_links_0064 record005_frame001_links_0128))
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x67533659a2c846353185866c11600af6d78ebb45d3ae45700b735aead45514a6a52fa8f54289f34f2270d36c9774a8a51523c8f146622e912a88743c218108283540da0490027e73ef1f4cf9a7a03c41dd8d1c66932d18bcc165ec2ef16fcb6a5842af9540a4e502273935c9784b224b12288e846b22d113088643221390507e43e51ec8e886f436919e8c5c5f22ea1660b0053a28413c09a04c025212108e84622200fe87c43c81c60d786a032e1900c285d02da1640a984b424211508383fc1d20de06a03240ea07303801980c806101a80cc064031013009004602200600280120080030010006002 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record005_frame002_links_0000 (interval_append _ 64 128 144 record005_frame002_links_0064 record005_frame002_links_0128))
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x8dd1aa3345c8ad146274488850ea1ac3285b0aa1342183d069f03d77a4f35e23bb76eeb9d539b722e29c23756ccd89a9b4f696d099cb35658ca19231b62ec4d882fd5e8bad55aa353ca4d43a7c4ee9b13425e4aa93d21a364548990d21741a825009fd3ea7c8f71e63c6760e69c73826acce1943145e0b31622a0530a093a26a4b89492523c4648a90c2043ec7a0e71ba368680cd1943005e8ba1602985009a12222c428800f61cc2a8540a61342584905e0b41602b0460841001f0180280480800c01001802 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record005_frame003_links_0000 (interval_append _ 64 128 144 record005_frame003_links_0064 record005_frame003_links_0128))
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0962.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0962.count (({ width := 10, code := 0xb86dfb76d5b46ceb36cab1ec0af6b9adab2abeacaa2a59d66c99e629725694e4d92a408ea368c22988a1f862158460d8220780a017fdfa7e5f77d5ed7ade96f9b66c5aa695a06799965d9162d875f9795d1725b56b595635795c55d5554d4e53147509404f92c47916435013d4f2398e3370d634ccd328c8308bf2f4b92d0b02b0a527c9d25c9524c8d22c8920c7d1e8771cc701b46b1a4661445013c4811c460b02a0a42808c210801f0300a024080180400c02 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0962.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record005_frame004_links_0000 (interval_append _ 64 128 144 record005_frame004_links_0064 record005_frame004_links_0128))
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0962
    Papers.RationalityTen.SharedFrameCatalogue.group0962_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x74fb9bdc96ddf6d7b62dabcd4b69eb499a40d186893429a06cfd67ab3b971cb5459a2c0d5bcab6551a9f94d8a224f4272132e9724a524dd224900477a3a11be8da468a33118a8bc45ba2c115689d44b223ce7e70c3761ad0d2267232f98e4c505ea2db965cabe53c28e94289c84d326092ec9664ae253127c93249124512048ea46f23490787b03ac1b68d1063830716e8b2855229414509d44d625b12388f045a2190fe07b83c01c60d8869c3241880bc05902b214a09b04642160fd07b83c81d20e206d83540ea07303801980c806101a80cc064031013009004602200600280120080030010006002 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record005_frame005_links_0000 (interval_append _ 64 128 144 record005_frame005_links_0064 record005_frame005_links_0128))
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
def record005_frame006_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x82c8118087e77d37c47b37a379878778277c77777276d7677607596e16be6ad69968267366b64f6426266055f35de5ce5b85b059358957c57556b56755d55b55554c54754053b52d52651f48a46945743842140f4033e63db3bd39f38d36c35734233631930e3002fb2f22ed2e62e02da2d22cb2c32b52af2aa28926825123421c2051f81e01d61c31b91b51aa1a81a119218f18617816615d15414313813512b12812111210d1070f80e40df0d40ce0cb0c30c00bd0b807507307006606406103503303203102602402302200c00a009008006004003002 } : Fields).get c.val)
theorem record005_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record005_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record005) (record005.maps 6)
      (record005.inverseMaps 6) record005_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record005_frame006_links_0000 (interval_append _ 64 128 144 record005_frame006_links_0064 record005_frame006_links_0128))
theorem record005_frame006_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 6 :=
  of_group record005 6 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record005_frame006_indices record005_frame006_graph record005_frame006_links
def record005_frame007_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0957.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0957.count (({ width := 8, code := 0xf7f6f5f4f3f2f1f0efeeedecebeae8e7e6e4dcd9d7d6d5d4d2d1cfcac7c5c4c3c2c0bfbdbbbab8b7b5b4b2b0afadaba9a8a7a19e9c9a9998979695928f8d8b8a89888786858382807f7d7b7a78757473726f6c6a68666462605e5b59585655545251504e4d4c4b494746444342403f3e3c3b3a393837363534332f2e2d2928271e1d1c1b1a1918170a09080705040302 } : Fields).get c.val)
theorem record005_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0957.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0957.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0957.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0957.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem record005_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0957.localPairCheck (smallEmbedding record005) (record005.maps 7)
      (record005.inverseMaps 7) record005_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 144 record005_frame007_links_0000 (interval_append _ 64 128 144 record005_frame007_links_0064 record005_frame007_links_0128))
theorem record005_frame007_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 7 :=
  of_group record005 7 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0957
    Papers.RationalityTen.SharedFrameCatalogue.group0957_facts record005_frame007_indices record005_frame007_graph record005_frame007_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (Fin.cases (record005_frame006_supported hcells) (Fin.cases (record005_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x336d96eca461030197e0be75dd2e915e8ac6556aa354eca61529a8994269e74d8264d2e094d497247d1de8d9459a2410e486241ba08902a7ea3ea1ef8ed07443971c04dae6bd34b19e4cc06533179878bee5cd2db165cb1257b2b69594ab054429b14a0a164ed269931c94a49723f917089a43d2088f7c78639e1bf0d8c6aa32c18d0bd05c42d31608ae055029314089bc4ae23211008303fa1ee0e886e43561860bb058827c12e08e843c1e40e506b03280cc06403080d406603201880b8058029013009004602200c805c02800c00500240100060028010006002 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record006_frame001_links_0000 (interval_append _ 64 128 135 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x32118d4c615edaed1722b805aead45518a6c53028f54289f34f2270d36c9774a8a51523c8f146622e912a88743020d50248013ef1f4cf9a7a03c41dd8df86d53639a2cccc659317982cbd85de2df96d4afc5592a7149ca22502279939c9ae4c825e12c892c47422d113086442720a0fc87ca3d91ce8dd46ce33d18b8be45d42cc1600a7451227813609804a424611d08c44401fd0f887903ac1c60d4064030a16d0b2054c25a12108a841c1d20de06a03240cc06403080d406603201880b8058029013009004602200c805c02800c00500240100060028010006002 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record006_frame002_links_0000 (interval_append _ 64 128 135 record006_frame002_links_0064 record006_frame002_links_0128))
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x11722b4518750ca1542683d069f0bd87a6f35e23bb76eeb9d539b722e29c23756ccd89a9b4f684cd59432462ec4d882fd5e8bad64abc56aaa95129d526a1d3e2774d89a12e25349a90d1e23645e8a91321f43485d06a013ea7c8f31e33b0734e39c1352668c918a2f0598b11502985049e1352604a492920232454861021f63d0778e71b4334650bd1742c0530a0134244428800f61cc2684b0920bc1682c0560a0130240460841001f02c0500900c0140240400600a01001802 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record006_frame003_links_0000 (interval_append _ 64 128 135 record006_frame003_links_0064 record006_frame003_links_0128))
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x1746df5b0ae95a6b0d5aa9d5227dce89b5336614ba96729e50c898f11b62ec4f8870f216c26831029ff3f77d0f85ee3d47a0f31dcba8734e1dbb3686b0d39a233e662ca9862f45cab41642c357aaed59aa8544a6d45a7b4e29a52a24a47c8cd172284187d0f29d13826dcd799a3205f4ba9702d45a0b015529e5209f13325c4a09191c21e4087e0ee1ce380690ce1903085a0b015429c2e85b0b00d4198320620b81602904c0901182203205c0a00c0140240400600a01001802 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record006_frame004_links_0000 (interval_append _ 64 128 135 record006_frame004_links_0064 record006_frame004_links_0128))
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x147287d069ad326604bb95f29e3345d8a91161ec308570720bc037eefb5ef3d078ef09dabad73ee5dc43836eadbdb3b606b4d4d9c328640c39812f85d0b6d67aca57cae555a985149e93aa6f4d49a1302574aa93921a3545488508a093f87c8f61e63b2720dc1a5332634c21732d456cab15429e530a213b26c4cc9511d234450881091fa3c8768e31ba358668c81882f4598b015629c310600ba0cc1883005e0b01582804a08c1102103205c0a00c0140240400600a01001802 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record006_frame005_links_0000 (interval_append _ 64 128 135 record006_frame005_links_0064 record006_frame005_links_0128))
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
def record006_frame006_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0x13b672cdb95527e4a48c9031ee1d42d843056043fd7f0fb5f33d278aef5d83a2726e25beb756d4d69a7348672cbd9532263cc5d7faf65d6b6d69ac7570ac152aa052aa45422764d2965292504969212023a4688c91421a418818fc1f23ce76ceb9d13886e0d51993165f4bb1682c655ca814a2884f89e1372684c09411c22a4488790a1fe3c8758de1b0348630c217a2dc558a614427c2f85d0b40d4198320620b81602904c0901182203205c0a00c0140240400600a01001802 } : Fields).get c.val)
theorem record006_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record006) (record006.maps 6) (record006.inverseMaps 6) record006_frame006_indices (Fin.ofNat record006.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record006_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record006) (record006.maps 6)
      (record006.inverseMaps 6) record006_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record006_frame006_links_0000 (interval_append _ 64 128 135 record006_frame006_links_0064 record006_frame006_links_0128))
theorem record006_frame006_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 6 :=
  of_group record006 6 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record006_frame006_indices record006_frame006_graph record006_frame006_links
def record006_frame007_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0929.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0929.count (({ width := 9, code := 0x47e3b1b8cc5a271187432130782c0e00fd7dbe1ecf479bc9e0ed753a1cae370375b4d86ab4da2ce6632990c66230980be5d2d964b0562a950a652289409e4e26932974aa51248f462290e85411fcfa7b3c9dcea73381b4d6683318cc25f2e96cb4582b154a65027130964a241188a4321104803f1f0f4783b1d0e46e361a8904622108803e1e0e86c341909848220b048200e06028100602 } : Fields).get c.val)
theorem record006_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0929.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (smallEmbedding record006) (record006.maps 7) (record006.inverseMaps 7) record006_frame007_indices (Fin.ofNat record006.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record006_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (smallEmbedding record006) (record006.maps 7)
      (record006.inverseMaps 7) record006_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record006_frame007_links_0000 (interval_append _ 64 128 135 record006_frame007_links_0064 record006_frame007_links_0128))
theorem record006_frame007_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 7 :=
  of_group record006 7 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0929
    Papers.RationalityTen.SharedFrameCatalogue.group0929_facts record006_frame007_indices record006_frame007_graph record006_frame007_links
def record006_frame008_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0953.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0953.count (({ width := 8, code := 0xa7a4a2a1a09f9e9d9c9592908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a7978777573716f6d6b6a6866656362605e5c5b5a595857565554535251504f4e4d4c4b4a494745434241403f3e3d3c3b3a393837363534333231302f2e2c2a2927262524232221201f1e1d191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record006_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0953.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0953.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0953.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0953.localPairCheck (smallEmbedding record006) (record006.maps 8) (record006.inverseMaps 8) record006_frame008_indices (Fin.ofNat record006.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record006_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0953.localPairCheck (smallEmbedding record006) (record006.maps 8)
      (record006.inverseMaps 8) record006_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record006_frame008_links_0000 (interval_append _ 64 128 135 record006_frame008_links_0064 record006_frame008_links_0128))
theorem record006_frame008_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 8 :=
  of_group record006 8 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0953
    Papers.RationalityTen.SharedFrameCatalogue.group0953_facts record006_frame008_indices record006_frame008_graph record006_frame008_links
def record006_frame009_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0913.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0913.count (({ width := 8, code := 0xadaba9a8a7a6a5a4a3a19f9d9c9b9a999897969594939291908f8e8d8c8b8a89888786858483817f7d7b7975726f6d6a6866646261605e5d5b5a5957565554535251504f4e4d4c4a48464544434241403f3e3c3b3938373534333231302f2e2d2c2b2a292827262524232221201f1e1d161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record006_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0913.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0913.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0913.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0913.localPairCheck (smallEmbedding record006) (record006.maps 9) (record006.inverseMaps 9) record006_frame009_indices (Fin.ofNat record006.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record006_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0913.localPairCheck (smallEmbedding record006) (record006.maps 9)
      (record006.inverseMaps 9) record006_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record006_frame009_links_0000 (interval_append _ 64 128 135 record006_frame009_links_0064 record006_frame009_links_0128))
theorem record006_frame009_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 9 :=
  of_group record006 9 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0913
    Papers.RationalityTen.SharedFrameCatalogue.group0913_facts record006_frame009_indices record006_frame009_graph record006_frame009_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (Fin.cases (record006_frame006_supported hcells) (Fin.cases (record006_frame007_supported hcells) (Fin.cases (record006_frame008_supported hcells) (Fin.cases (record006_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x19b6cb765232118b0c3e60eb00d7dcbe25da2e796c0b3458dabd158caad545a9d14c0a5051228453d49c04d1a5c92c694f4a024bd24490c479237116e8a844a22150e886842a20f104e8163f59f54f7e7683a21cb8e026d735e9a64cf866132b18c8c425f72e696d8b2e5892bd95b4aca5582a214d8a5050827c13a89b44d226212c0944494241117c8a04402088f7c78639b1c58dec6d63621a90cf065231717a0b885a62c115c0aa0526281137896446822210708003e21db0ea06f83741ae0c986242f21610aa04f425a11c08604101de0e2069832c05c02c0148098048023011008403e01e00e806402e014008803c01c00d0060028012008 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame001_links_0000 (interval_append _ 64 128 154 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1908c6a630b0ad812bff5eaaec571ab7d5acad3d5deacf5622a314d8a6051d28493e29e24e0a6d530695d4a424852168f3472a3391788ae44ba2210cc85241ca0a902c8053fb1f88faa7ce3d09e24eee6fc36a9b1cd1666632c98c8c1c5ef2f09708b6c57e2ac9538a4e51128113cc9ce4d726412f096449324011c48c645722490ec85e42620b8fd47ce3db1ce8dd46ce33a1918c5460a2f71740b605942bf14e8a244f026c130094848c23a11888883fe1f20f287643921b00d506603241870ba85bc2ca1520a384b024011408203f81cc0db068832805c02c0148098048023011008403e01e00e806402e014008803c01c00d0060028012008 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame002_links_0000 (interval_append _ 64 128 154 record007_frame002_links_0064 record007_frame002_links_0128))
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x22e4568a3132234408710c214424839061ffbf57dcf85ec3d3796f09dd3b575aea5cf39471ae15bf3766ded9db1b5c6a8d41a233f66ecc995326642c658ab115fcbd5762c9578ad5552a253aa5544a7d4f29b534a5c4a693521a3c46c8bd1522643e8690ba0c40a800fc9f43e27a8f29e23b273ce49c3352668c91882fc5d8b61652c0558a794b2824f09a9302524949011922a434818fc1ea3c4740de1b6344670cb1822f85d8af15c2944f89911c2284187e0f21d01402604808c1082003e0780e01b0340580a01202203c0700d01802804808 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame003_links_0000 (interval_append _ 64 128 154 record007_frame003_links_0064 record007_frame003_links_0128))
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1c32de86e135c1a7ad1566f32ed920c7d629b0fd768b835aeac2d5b0ab053ca959456a184f727693709a34caa5f92f09704b525892b69554a6a5192709324952491238915487a41d2008fb476a3991be8444059f94f147503921b9cd866993421964c885f52df165cac254e29e94a8a3050527993849a24ac24c92208ec46722a91088644232080fbc7be3cf1c30d3c6502f216f8b385762a914b0a104e426211e88a84322070fc07983a61c30da06843001700b0055c2a01470a104e426812d092047c23010f085840c1f80f507703a81c40dc06b034805c02c0148098048023011008403e01e00e806402e014008803c01c00d0060028012008 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame004_links_0000 (interval_append _ 64 128 154 record007_frame004_links_0064 record007_frame004_links_0128))
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x6035f55ec5d25c55bb5ab5a059558a57e5775545435375205125064f64e94dd4d44c94c24aa49948f48047a47246b46345a45344b44443843242b42541e41741140a4044003f23eb3e43bf3b13a939038237736535a34b34333432d30e2f92f12d92ce2c82c12bb2b02a729f29828927d27627026c26525d2572522472342302292091f61ec1d41c91c11b81b01a71a019a19318417816f16716115b15515114d14212f12a12311d11710f10a1020ff0f90f10ee0ea0e20df0d70d10cc0c70c40bc0b80b50b202e02c02902602402302202101f01e01d01901701401100f00e00d00c00a009008 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame005_links_0000 (interval_append _ 64 128 154 record007_frame005_links_0064 record007_frame005_links_0128))
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
def record007_frame006_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0916.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0916.count (({ width := 8, code := 0x999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record007_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0916.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0916.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0916.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0916.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0916.localPairCheck (smallEmbedding record007) (record007.maps 6)
      (record007.inverseMaps 6) record007_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame006_links_0000 (interval_append _ 64 128 154 record007_frame006_links_0064 record007_frame006_links_0128))
theorem record007_frame006_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 6 :=
  of_group record007 6 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0916
    Papers.RationalityTen.SharedFrameCatalogue.group0916_facts record007_frame006_indices record007_frame006_graph record007_frame006_links
def record007_frame007_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1b78d916b7348d9f0cd5658b29192cc8f640b1e97e4bc25cf2d41640afc56aab1d572ab25522a754aaa124f1a68131e97e4b6a56d290936491a4451da8dc465a2e9150895441a1c10bc84e42020e506479f3b61d18dea6c234e19d4cd065a3299914c7e5f72e0966cad855e2a89508a6a52628b94289f84df268931096a4a824c92288fa46f232916c8ac4512008ef872635f1a70cfc65e31f1870bf45dc2dd15f0ab453c28e13f09b44b824d11e08c444621c10a88243ea1db0e786c834a1910bb85b42b414409e84b424211408384001e00e406b834c05c02c0148098048023011008403e01e00e806402e014008803c01c00d0060028012008 } : Fields).get c.val)
theorem record007_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record007) (record007.maps 7)
      (record007.inverseMaps 7) record007_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame007_links_0000 (interval_append _ 64 128 154 record007_frame007_links_0064 record007_frame007_links_0128))
theorem record007_frame007_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 7 :=
  of_group record007 7 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record007_frame007_indices record007_frame007_graph record007_frame007_links
def record007_frame008_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6da6d06ca6b66a269b68c67f6756706666636196075ff5e15c75bc5ac59e59558f58658256955254552c52151750e5034f84f24eb4e34d54ca4bf4b94b24aa4a149648c48947b47446f41a4073fe3e03c03b23a439939038b38237e35c34133732331831430b3062fd2f62f22ed2df2d42ce2c72c32bd2b42af2a92a529b29629326824423621920b2031fb1f31ea1e21dc1d61c11b31ac1a419e19618e18617e17916b16516115b15114213e12e12911f10f10a1020f70f20e40e00da0d10cc0be0b80b40b102e02c02902602402302202101f01e01d01901701401100f00e00d00c00a009008 } : Fields).get c.val)
theorem record007_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record007) (record007.maps 8)
      (record007.inverseMaps 8) record007_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame008_links_0000 (interval_append _ 64 128 154 record007_frame008_links_0064 record007_frame008_links_0128))
theorem record007_frame008_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 8 :=
  of_group record007 8 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record007_frame008_indices record007_frame008_graph record007_frame008_links
def record007_frame009_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0931.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0931.count (({ width := 9, code := 0x2633097cba5b2c94c9e4b24914863d1c8dc622d15894421d0d85c2a130681bf9f8f97bbd1e4f076badcee571381badb6cb59a8d26632990c4613057cbc5dae16cb459ac560ae562a94ea55228942a04f27538994ba592893492411e8e46225108742209027d3d9e8f0773b1d0e672371b0d6693419cca6431984be5e2e970b2552a1409e4d249208c42208f87a3c1c8e06a34198c842200f878381b0d0642e160a84c2411080381a0c058241007 } : Fields).get c.val)
theorem record007_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0931.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0931.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0931.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0931.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0931.localPairCheck (smallEmbedding record007) (record007.maps 9)
      (record007.inverseMaps 9) record007_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame009_links_0000 (interval_append _ 64 128 154 record007_frame009_links_0064 record007_frame009_links_0128))
theorem record007_frame009_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 9 :=
  of_group record007 9 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0931
    Papers.RationalityTen.SharedFrameCatalogue.group0931_facts record007_frame009_indices record007_frame009_graph record007_frame009_links
def record007_frame010_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x2e8dbeb6168ac7d83ae75a2b0559a9b51e98d1ea253ee744da9993065ccb294d28246c7d8e117a2bc508971121ec3785d09e0cc12817019ffbf87e4fa5f13dd7aaf45e6bb9750e69c3b766d0d65a7b4567ecc995b0c5e8b95682c8586af55dab3550a894da895029e93a2704ce96d29a494808d117a294187d0f29cf38e700dd1b635a684cc98f2fa5d4b816a2d0580aa94f2905009a12f2524908e914220420818fd1e83bc740df1b6344668c71822f4598af1522a01702c052098120230440840f81e03a0640b81402203c0700d01802804808 } : Fields).get c.val)
theorem record007_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 10)
      (record007.inverseMaps 10) record007_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame010_links_0000 (interval_append _ 64 128 154 record007_frame010_links_0064 record007_frame010_links_0128))
theorem record007_frame010_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 10 :=
  of_group record007 10 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record007_frame010_indices record007_frame010_graph record007_frame010_links
def record007_frame011_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0x276ce59b733660cb79532764948a8ff1ea2dc5288f0ea16c2182901dfe3f67d6f95ea3c777eec5d53a3738e51c53856fcdddb5b646b8d5da8349684ce998b2b646c7d8c2ff5ecbad6dad358eae558aa6542a5949a844ec9a52ca524a092d242404748d11922643c8610820a4087f0fb1f03d2774ec1d33886e0d519731e624c097b2e85b0b31612ae540a514427c4f09b9342604a88f117226440859052003dc798ec1c637c6d0d119e314608bc16c2d0550a41422801702c052098120230440840f81e03a0640b81402203c0700d01802804808 } : Fields).get c.val)
theorem record007_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record007) (record007.maps 11) (record007.inverseMaps 11) record007_frame011_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record007) (record007.maps 11) (record007.inverseMaps 11) record007_frame011_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record007) (record007.maps 11) (record007.inverseMaps 11) record007_frame011_indices (Fin.ofNat record007.n i)) 128 154 :=
  interval_of_check _ 128 26 (by decide +kernel)
theorem record007_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record007) (record007.maps 11)
      (record007.inverseMaps 11) record007_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 154 record007_frame011_links_0000 (interval_append _ 64 128 154 record007_frame011_links_0064 record007_frame011_links_0128))
theorem record007_frame011_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 11 :=
  of_group record007 11 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record007_frame011_indices record007_frame011_graph record007_frame011_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (Fin.cases (record007_frame006_supported hcells) (Fin.cases (record007_frame007_supported hcells) (Fin.cases (record007_frame008_supported hcells) (Fin.cases (record007_frame009_supported hcells) (Fin.cases (record007_frame010_supported hcells) (Fin.cases (record007_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x74973e6c16b66aa6a269468c5f15dd5d25c65bb5ad55354753d52e52150b5024fa4ea4dd4d54ce4c44bc4b54ae4a94a147945744740e4043fa3f13e73dd34b33f33530c3062f12e62df2cc2a729d29728727f2081fc1f01d11c31af1a519a18e17115f15914a13d11d1101040f60f00e30de0d70d10c30bf0ba0ae09308a08607907106c05c05b05705605303703602802602402101f01d01201100e00c009008006002001000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x153ea2d3da6736a60c96923019ffbf37a6f1dda3a5726dfdbb3706d8d919bb2060ab856b2c9584ae9392654b4941272394628ad0e21240e804fb9f13d4790f09bf340640c49842f65d8b195d2aa53ca393d2624ac9391f20a3fc7c8ed1c2344658c416c2c8570a411c1b42e85c0b215c2984708a0f41b82c04e098128230420800e8130240440780e0180280400600600800800 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00213
