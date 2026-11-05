module
prelude
public import GraphInputsRow31Part00023Data
public import RawFrameSupport
public import SharedFrameGroups029Checked
public import SharedFrameGroups030Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6d86cc6a86966716635bf59458a58156b52850f5094d04b74a949949449046144343840f3f43de3ae37336a35433a33031730e3002fd2eb2d72c82bf2b12a729a29729428b28227826726124b21e2081e81b91b118a17517116315714512811f11610b0f60e70cc0c409e09b08607606e06a06706105a05805405305204f04d04103803403102f02d02b02a02402201e01d01c01601401000f00d00b009008007004003002001000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x76d76774f7256f06e06d56cd6af6a368668067866a65e65263e63c63762761a60e5f75e45cf5ba5a85a559858f55753d5235024fd4df4c74a449f48347947346644c44143e43042a4144043ff3fd3ed3e73ce3bd39b39538037536135935531d2f22e92cd2bc29428d26f25c24924223222c2132071fe1ef1e61e01da1c91ba1b51af1a519d19719118017116b16615c15414814313a13012c12911d1111020fa0e50de0d90c60be0b90b40af0ab0a609909108207706d05b05a05605504c04003602502302001e01b01501000d00b008005001000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame001_links_0000 (interval_append _ 64 128 142 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1d40e6570f3551976caa64eb251906c7c61a306580abe35e8aed5702b775b1ad0565eb1356fab39576aab5512a7951aa674e5a61929a917488234d13486442ea11107a8384181fa0f787b33c79e10eaa72b3891c24dca6da3559a04cc265b3261918c7a6213091648a8653028893e096c4a324211ac8c045d22b11488483eb1e70e9470c36c1b10d0064a30d17f0ba45b42cb1608a7c50826c12e892047222a112887442a2050fb073435216f0ac84b024411707783941b40d2066030817209f04a82180f206f02e81700b0057026010006c025011808003c01b00a804001a00b0040014002000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame002_links_0000 (interval_append _ 64 128 142 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0994.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0994.count (({ width := 11, code := 0x2794ee9c33265b4ad9512964cc948fb1de3a4678bb15625c4a88b0e21942b83503601bf37d4fa5f1bde778ea5cd386708dc5b134c696ce599b30654c4d85b095fabdd74adf5b8b65662c8578ac14da99512a153da764e894919a2f43a844fd9f53c876ce79cb384700d89a834265cc918b30c5ecb916a2c4564a994e2965009a92d24a4748b10f2164147f8fc1f63c4738db1a830c5e0b91522985089c132254490881041d0348630a814c2784e0860e8198250460800f01b02a0400680b01001400800 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record003_frame003_links_0000 (interval_append _ 64 128 142 record003_frame003_links_0064 record003_frame003_links_0128))
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0994
    Papers.RationalityTen.SharedFrameCatalogue.group0994_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x7056c769867666766263562d6205f95f25db5ce5b65a459358458157555e54853a5094fd4e84e14af49c49048a47747146c43e4314213f83f23d73c73ac39e38e38037d37135633b33130c3032f32ec2c42b52ac2a829a29729429228827026424c23a22d22b21f2122071fe1ee1e01d81d31c71ba1a219a19118118016f16816716315f14113512c12211610d0ff0ec0eb0df0de0c60c50bc0b30ae0aa08908308007e07c07606d06a06905d05b05905605305204f04c04a04804203703403302702502302001d01c } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame001_links_0000 (interval_append _ 64 128 134 record004_frame001_links_0064 record004_frame001_links_0128))
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x8077c279177175f75873973572f6f76f06d66c76a868967064964063161b5fc5ed5be5b559158355a54d54553e52952251c4f34ea4e34a449e47d46c44d42e40e3e43dc3ca3b039038034d34131a30c2e52d82d02c92b62b02ab2a729c28b28326c25524424323722721f20f2011e41da1d01c51be1a91a619a18a18916b16416315c15013713012912611a1101020eb0ea0dd0dc0c60c50c20ba0b40b208d08708408308207c06f06c06b05f05d05b05805505405104e04c04a04403703403302702502302001d01c } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame002_links_0000 (interval_append _ 64 128 134 record004_frame002_links_0064 record004_frame002_links_0128))
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0948.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0948.count (({ width := 9, code := 0x26d359a4c25d2d9349647208fc7a39198ac4a210f87436170881c05fefe7cbddeaf4793c5e0ec75ba5cce572389bedb6c359aad469b459cc963b1588bf5eaed74b75b2d568b2572b150a4512853c9b4c255229047231128641a04fc7a3c9d4e873389bcd86933190c25e2d960ae552a1409e4d2592892411f0f0763a1c8e06c351a0c8622f170b45428138984a2411084401e0e86c3419 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0948.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0948.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame003_links_0000 (interval_append _ 64 128 134 record004_frame003_links_0064 record004_frame003_links_0128))
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0948
    Papers.RationalityTen.SharedFrameCatalogue.group0948_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0927.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0927.count (({ width := 9, code := 0x27f3e9ece66f36964ae532692c92451f8dc622d158a44e230e84c1e0b047fbf5f6fa7c3ddecef773b1d2e873b95c4de6db65b0d76b351a2cc653218ec2602f97aba5cae16eb457ab550a4512853c9b4c255229047231128641a04fc7a3c9d4e873389bcd86933190c25e2d960ae552a1409e4d2592892411f0f0763a1c8e06c351a0c8622f170b45428138984a2411084401e0e86c3419 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0927.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame004_links_0000 (interval_append _ 64 128 134 record004_frame004_links_0064 record004_frame004_links_0128))
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0927
    Papers.RationalityTen.SharedFrameCatalogue.group0927_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0911.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0911.count (({ width := 9, code := 0x2b754a7d2e9348a15067d389bcd2652d9448a411f8f476311487c36150981bfdfafb7c3ddecf077bb1cce571381b6d768b3d9ccd6631d86bf5eae972b3582b958a95429d4ca551a853e9c4d265309549a451a8c452210e85411fcfa7a3c9d0e471371b0d66933994c4602e164b0562a944a04e25124903f1e0e872381b8d86833190c05e2d160ac50261289046221007c3c1c0d8643017 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0911.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0911.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0911.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0911.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0911.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame005_links_0000 (interval_append _ 64 128 134 record004_frame005_links_0064 record004_frame005_links_0128))
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0911
    Papers.RationalityTen.SharedFrameCatalogue.group0911_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
def record004_frame006_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0468.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0468.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0468.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0468.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0468.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0468.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0468.localPairCheck (smallEmbedding record004) (record004.maps 6)
      (record004.inverseMaps 6) record004_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame006_links_0000 (interval_append _ 64 128 134 record004_frame006_links_0064 record004_frame006_links_0128))
theorem record004_frame006_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 6 :=
  of_group record004 6 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0468
    Papers.RationalityTen.SharedFrameCatalogue.group0468_facts record004_frame006_indices record004_frame006_graph record004_frame006_links
def record004_frame007_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0465.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0465.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0465.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0465.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0465.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0465.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0465.localPairCheck (smallEmbedding record004) (record004.maps 7)
      (record004.inverseMaps 7) record004_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame007_links_0000 (interval_append _ 64 128 134 record004_frame007_links_0064 record004_frame007_links_0128))
theorem record004_frame007_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 7 :=
  of_group record004 7 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0465
    Papers.RationalityTen.SharedFrameCatalogue.group0465_facts record004_frame007_indices record004_frame007_graph record004_frame007_links
def record004_frame008_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0461.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0461.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0461.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0461.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0461.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0461.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0461.localPairCheck (smallEmbedding record004) (record004.maps 8)
      (record004.inverseMaps 8) record004_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame008_links_0000 (interval_append _ 64 128 134 record004_frame008_links_0064 record004_frame008_links_0128))
theorem record004_frame008_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 8 :=
  of_group record004 8 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0461
    Papers.RationalityTen.SharedFrameCatalogue.group0461_facts record004_frame008_indices record004_frame008_graph record004_frame008_links
def record004_frame009_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0457.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0457.count (({ width := 8, code := 0xc6c5c4c3c2c1c0bfbebbbab9b7b6b4b3b0afaeadabaaa8a7a5a3a2a1a09f9e9d9c9b9a9996959492918f8e8b8a898886858382807e7d7c7b7a79787776757473716f6e6d6c6a686664615f5d5c5a58565451504e4c4b4a48474543413f3d3b393836353332302e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f } : Fields).get c.val)
theorem record004_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0457.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0457.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0457.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0457.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0457.localPairCheck (smallEmbedding record004) (record004.maps 9)
      (record004.inverseMaps 9) record004_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame009_links_0000 (interval_append _ 64 128 134 record004_frame009_links_0064 record004_frame009_links_0128))
theorem record004_frame009_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 9 :=
  of_group record004 9 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0457
    Papers.RationalityTen.SharedFrameCatalogue.group0457_facts record004_frame009_indices record004_frame009_graph record004_frame009_links
def record004_frame010_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0455.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0455.count (({ width := 8, code := 0xd0cfcecdcccbc9c8c7c4c3c2c1bebdbbb9b7b6b5b4b3b2b0afadacaaa8a7a5a3a19f9e9d9a9998979493918f8d8c8b8a898886858382807e7d7b79777675747372706e6d6c6b6a686562605e5d5c59575552514e4d4c4a4845444341403f3d3c3b38373534322f2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f } : Fields).get c.val)
theorem record004_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0455.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0455.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0455.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0455.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0455.localPairCheck (smallEmbedding record004) (record004.maps 10)
      (record004.inverseMaps 10) record004_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame010_links_0000 (interval_append _ 64 128 134 record004_frame010_links_0064 record004_frame010_links_0128))
theorem record004_frame010_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 10 :=
  of_group record004 10 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0455
    Papers.RationalityTen.SharedFrameCatalogue.group0455_facts record004_frame010_indices record004_frame010_graph record004_frame010_links
def record004_frame011_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0454.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0454.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0454.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0454.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0454.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0454.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0454.localPairCheck (smallEmbedding record004) (record004.maps 11)
      (record004.inverseMaps 11) record004_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame011_links_0000 (interval_append _ 64 128 134 record004_frame011_links_0064 record004_frame011_links_0128))
theorem record004_frame011_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 11 :=
  of_group record004 11 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0454
    Papers.RationalityTen.SharedFrameCatalogue.group0454_facts record004_frame011_indices record004_frame011_graph record004_frame011_links
def record004_frame012_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f42e986de34c19ccccc62c3115860b985c62d0564ead754ea96d444a124f7a6e12f695647d239115e8984192034ff07e83da1e98f2a7243889bf0cc865830697ccb4656929393b89bc4bb242111c8443c61d80dec6c82fe16c8b1056828013909844b025112208f045e22110988444142020fe07d03d21da0e9872c3881bc0d4868433218e0c605e42e41700b4058829a14509f84e026012a08f044021c10207f83b41d60e306c034819c08f044821810808203e01bc0d806b02f81740b605802a81500a204e026012808803701a00cc04e025011808003a01c } : Fields).get c.val)
theorem record004_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 12)
      (record004.inverseMaps 12) record004_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame012_links_0000 (interval_append _ 64 128 134 record004_frame012_links_0064 record004_frame012_links_0128))
theorem record004_frame012_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 12 :=
  of_group record004 12 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame012_indices record004_frame012_graph record004_frame012_links
def record004_frame013_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1040.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1040.count (({ width := 11, code := 0x20ec11810fd9f73ea79ef2de33b175ee95d038d704dd5b43656bed51a3b3b652c8d8cb145febcd75ae75aeb51682b6564ab54a292510a0d3a2694b493d262464768b91120c4087e8fa1df3ae744e71be3746dcda9b0348674c89873005f8bc1712d8594ac950296518a013925849c90114226420821031fe3ec778e71c43706a0cf18c2e85c8b015e2804f8991242384607d0ee1d0390700d8194310610ac1502904f09812c240450861041e8360660c8138250460800e81c } : Fields).get c.val)
theorem record004_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record004) (record004.maps 13) (record004.inverseMaps 13) record004_frame013_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record004) (record004.maps 13)
      (record004.inverseMaps 13) record004_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame013_links_0000 (interval_append _ 64 128 134 record004_frame013_links_0064 record004_frame013_links_0128))
theorem record004_frame013_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 13 :=
  of_group record004 13 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1040
    Papers.RationalityTen.SharedFrameCatalogue.group1040_facts record004_frame013_indices record004_frame013_graph record004_frame013_links
def record004_frame014_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x2744d596d28649c8d8ed1ca37c5b8af12e21c2c83f041febf77def85e5bbf748e79c437c6b4d2da1b3b656c958f30760ac0576ae95b4b495c2a852e9f93ba6e4c69412222e450851069ec3ba750e69bc36c6c0d69a733c66cca18c30a610c017a2e85b8b295f2b4554a814b27a4e09912624a4508790e2104087a8f01d43946f8d9196304600b616a2ac548a31382644c0790e61c03786e0d41802e85c0a81482804d094124230430841041e8340620c0138250460800e81c } : Fields).get c.val)
theorem record004_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record004) (record004.maps 14) (record004.inverseMaps 14) record004_frame014_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record004) (record004.maps 14)
      (record004.inverseMaps 14) record004_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame014_links_0000 (interval_append _ 64 128 134 record004_frame014_links_0064 record004_frame014_links_0128))
theorem record004_frame014_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 14 :=
  of_group record004 14 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record004_frame014_indices record004_frame014_graph record004_frame014_links
def record004_frame015_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0947.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0947.count (({ width := 8, code := 0xc6c5c4c2c1c0bfbebdbcbbbab9b8b5b4b3b2b1b0afaeabaaa9a8a6a4a3a2a1a09f9e9d9c9b9a99989794939291908f8e8d8a89888785838281807f7e7d7c7b7a797877767472706e6c6b69676563615f5d5b5a5857565452504e4c4a4846444342403f3d3c3a38373634333231302f2e2c2b2a28272524232221201f1e1d1b1a191716141312 } : Fields).get c.val)
theorem record004_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0947.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0947.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0947.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0947.localPairCheck (smallEmbedding record004) (record004.maps 15) (record004.inverseMaps 15) record004_frame015_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0947.localPairCheck (smallEmbedding record004) (record004.maps 15)
      (record004.inverseMaps 15) record004_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame015_links_0000 (interval_append _ 64 128 134 record004_frame015_links_0064 record004_frame015_links_0128))
theorem record004_frame015_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 15 :=
  of_group record004 15 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0947
    Papers.RationalityTen.SharedFrameCatalogue.group0947_facts record004_frame015_indices record004_frame015_graph record004_frame015_links
def record004_frame016_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0926.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0926.count (({ width := 9, code := 0x2472290c76371a89c4a210d8642e130681c01fcfd7e3edf2f6793c1dced74b9dcae471385c0d96c359a6d268b3d98c96331186c260afd78b85b2d166af56aad54a853a994aa35027936984b255269046a290c8541a04fe7c3c9dce870379b4d86b3499cca622f974b4572a14ca45027934984a2411c8c411f0f0763a1c8e06c351a0c8622f170b45428138984a2411084401e0e86c3419 } : Fields).get c.val)
theorem record004_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0926.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record004) (record004.maps 16) (record004.inverseMaps 16) record004_frame016_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record004) (record004.maps 16)
      (record004.inverseMaps 16) record004_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame016_links_0000 (interval_append _ 64 128 134 record004_frame016_links_0064 record004_frame016_links_0128))
theorem record004_frame016_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 16 :=
  of_group record004 16 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0926
    Papers.RationalityTen.SharedFrameCatalogue.group0926_facts record004_frame016_indices record004_frame016_graph record004_frame016_links
def record004_frame017_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0910.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0910.count (({ width := 8, code := 0xc6c5c4c2c1c0bfbebdbcbbbab9b8b5b4b3b2b1b0afaeabaaa9a8a6a4a3a2a1a09f9e9d9c9b9a99989794939291908f8e8d8a89888785838281807f7e7d7c7b7a797877767472706e6c6b69676563615f5d5b5a5857565452504e4c4a4846444342403f3d3c3a38373634333231302f2e2c2b2a28272524232221201f1e1d1b1a191716141312 } : Fields).get c.val)
theorem record004_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0910.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record004) (record004.maps 17) (record004.inverseMaps 17) record004_frame017_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0910.localPairCheck (smallEmbedding record004) (record004.maps 17)
      (record004.inverseMaps 17) record004_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame017_links_0000 (interval_append _ 64 128 134 record004_frame017_links_0064 record004_frame017_links_0128))
theorem record004_frame017_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 17 :=
  of_group record004 17 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0910
    Papers.RationalityTen.SharedFrameCatalogue.group0910_facts record004_frame017_indices record004_frame017_graph record004_frame017_links
def record004_frame018_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0467.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0467.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0467.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0467.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0467.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0467.localPairCheck (smallEmbedding record004) (record004.maps 18) (record004.inverseMaps 18) record004_frame018_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0467.localPairCheck (smallEmbedding record004) (record004.maps 18)
      (record004.inverseMaps 18) record004_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame018_links_0000 (interval_append _ 64 128 134 record004_frame018_links_0064 record004_frame018_links_0128))
theorem record004_frame018_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 18 :=
  of_group record004 18 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0467
    Papers.RationalityTen.SharedFrameCatalogue.group0467_facts record004_frame018_indices record004_frame018_graph record004_frame018_links
def record004_frame019_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0464.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0464.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0464.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0464.localPairCheck (smallEmbedding record004) (record004.maps 19) (record004.inverseMaps 19) record004_frame019_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0464.localPairCheck (smallEmbedding record004) (record004.maps 19) (record004.inverseMaps 19) record004_frame019_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0464.localPairCheck (smallEmbedding record004) (record004.maps 19) (record004.inverseMaps 19) record004_frame019_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0464.localPairCheck (smallEmbedding record004) (record004.maps 19)
      (record004.inverseMaps 19) record004_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame019_links_0000 (interval_append _ 64 128 134 record004_frame019_links_0064 record004_frame019_links_0128))
theorem record004_frame019_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 19 :=
  of_group record004 19 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0464
    Papers.RationalityTen.SharedFrameCatalogue.group0464_facts record004_frame019_indices record004_frame019_graph record004_frame019_links
def record004_frame020_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0460.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0460.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0460.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0460.localPairCheck (smallEmbedding record004) (record004.maps 20) (record004.inverseMaps 20) record004_frame020_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0460.localPairCheck (smallEmbedding record004) (record004.maps 20) (record004.inverseMaps 20) record004_frame020_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0460.localPairCheck (smallEmbedding record004) (record004.maps 20) (record004.inverseMaps 20) record004_frame020_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0460.localPairCheck (smallEmbedding record004) (record004.maps 20)
      (record004.inverseMaps 20) record004_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame020_links_0000 (interval_append _ 64 128 134 record004_frame020_links_0064 record004_frame020_links_0128))
theorem record004_frame020_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 20 :=
  of_group record004 20 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0460
    Papers.RationalityTen.SharedFrameCatalogue.group0460_facts record004_frame020_indices record004_frame020_graph record004_frame020_links
def record004_frame021_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0456.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0456.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0456.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0456.localPairCheck (smallEmbedding record004) (record004.maps 21) (record004.inverseMaps 21) record004_frame021_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0456.localPairCheck (smallEmbedding record004) (record004.maps 21) (record004.inverseMaps 21) record004_frame021_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0456.localPairCheck (smallEmbedding record004) (record004.maps 21) (record004.inverseMaps 21) record004_frame021_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0456.localPairCheck (smallEmbedding record004) (record004.maps 21)
      (record004.inverseMaps 21) record004_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame021_links_0000 (interval_append _ 64 128 134 record004_frame021_links_0064 record004_frame021_links_0128))
theorem record004_frame021_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 21 :=
  of_group record004 21 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0456
    Papers.RationalityTen.SharedFrameCatalogue.group0456_facts record004_frame021_indices record004_frame021_graph record004_frame021_links
def record004_frame022_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0453.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0453.count (({ width := 8, code := 0x8584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0453.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0453.localPairCheck (smallEmbedding record004) (record004.maps 22) (record004.inverseMaps 22) record004_frame022_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0453.localPairCheck (smallEmbedding record004) (record004.maps 22) (record004.inverseMaps 22) record004_frame022_indices (Fin.ofNat record004.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record004_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0453.localPairCheck (smallEmbedding record004) (record004.maps 22) (record004.inverseMaps 22) record004_frame022_indices (Fin.ofNat record004.n i)) 128 134 :=
  interval_of_check _ 128 6 (by decide +kernel)
theorem record004_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0453.localPairCheck (smallEmbedding record004) (record004.maps 22)
      (record004.inverseMaps 22) record004_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 134 record004_frame022_links_0000 (interval_append _ 64 128 134 record004_frame022_links_0064 record004_frame022_links_0128))
theorem record004_frame022_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 22 :=
  of_group record004 22 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0453
    Papers.RationalityTen.SharedFrameCatalogue.group0453_facts record004_frame022_indices record004_frame022_graph record004_frame022_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (Fin.cases (record004_frame006_supported hcells) (Fin.cases (record004_frame007_supported hcells) (Fin.cases (record004_frame008_supported hcells) (Fin.cases (record004_frame009_supported hcells) (Fin.cases (record004_frame010_supported hcells) (Fin.cases (record004_frame011_supported hcells) (Fin.cases (record004_frame012_supported hcells) (Fin.cases (record004_frame013_supported hcells) (Fin.cases (record004_frame014_supported hcells) (Fin.cases (record004_frame015_supported hcells) (Fin.cases (record004_frame016_supported hcells) (Fin.cases (record004_frame017_supported hcells) (Fin.cases (record004_frame018_supported hcells) (Fin.cases (record004_frame019_supported hcells) (Fin.cases (record004_frame020_supported hcells) (Fin.cases (record004_frame021_supported hcells) (Fin.cases (record004_frame022_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x690343199cc5c5fcae81726b6c5afad3d658b16582abdd5caad75652af9566aa154aaa054eaa6652d28854049ea4e926e936a9944b725352808db462229111a8854102034fd87d93e91ea4f2877d3b59cf4e507163831bbcdbe6cd3601accd4869433f99bccbe65330e97fcbce5d22dd16d8b345752aa15289e84e426492e496446422a10f08584262038fe47ce3db1eb0f0074c3981bf0dc06c835c1a20cac63830b1780bbc5bc2c31610ae855029214009c84b625a12608d446821d10507e43d81de0d6068032a1890be85c82cc13c09c84782240f407903681a00cd04482180f807903901bc0ba05b02d01600ac055028813808804101d00dc04a023011008003c01d } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record005_frame001_links_0000 (interval_append _ 64 128 160 record005_frame001_links_0064 record005_frame001_links_0128))
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x838c131f44e926dcb50da66cfc67633358eec58622b0c1812bf05e52e6d718b795b12d0564eb0456caa814eea5a51da87d4269ef4dc26012b68fa472230515489a42120b501a7f83f49f18f727a53c99d0ce4871137e1b54d786963339960c8a62e30697ccba05a52b6150ca4c507275937c976484226109c78c3b01c68dd86cc30e17c8b645882b51490a144e225f12c094448823c117889c43221110508083f81f40f4879c3be1d40e8872c3881bc0db06b83461a10cc863831617f0bc05c42d41620a6851427e13809804a824411008704081f60ed075837c1b00d604482180f807903901bc0ba05b02d01600ac055028813808804101d00dc04a023011008003c01d } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record005_frame002_links_0000 (interval_append _ 64 128 160 record005_frame002_links_0064 record005_frame002_links_0128))
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x73f73771e6eb6c46a169b68768167865f65664e64463762f6236166126096015f65ee5e25d65c45b25a259258057d56e55653f5334fd4f04d94c94c349949047f47346e45945344643b42341a4114093fd3f33e73da3d63cd3c53ba3b23a639a38837336135434434133131a3032f72bd2ad29a28d28725924d24023723221d2172071fe1fb1f51e91e11d51cd1c71c31bd1b51b11a819a19919018218117e17a17316e16715915815114314213b13613212b12411710f10a1030fb0f60ef0e30e20d70d10c70c60bb0b50b408708507b07807106e05c05a05905705505405104e04404103a03702502302202001e01d } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record005_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 128 160 :=
  interval_of_check _ 128 32 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 160 record005_frame003_links_0000 (interval_append _ 64 128 160 record005_frame003_links_0064 record005_frame003_links_0128))
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x6e3b6e1a60c8a610b055818c065eeaf4d74eb9d5b4ad91576a5b52128f546a9fd4bb244520a8ff47b21e509c83c4182038ff87f03f39f24f6c79d3be9da8ea272a38e9c54e1469f33518f8c125fe2fc17ccb764f427713a490046522810d884241a1fa0f7877a3af1c68df86d835d1a78cb463c30c17e8bdc5e02e116789ec49423d108080c3f41dc0db063c2ec1690a284e024c10907b03a414a09f04902380e006c02f816c0aa054028812808803801b80d006602b014009c04802300f807403801b00c0050024010007002c0100070018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record006_frame001_links_0000 (interval_append _ 64 128 132 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x36d1b48d936bc359da88d34685322183ec14606301d7babd35d3ae756d2b64596aab949ca4351ea8d14069cc4e1a67d3049674af24e923a90447fa3dd1a48a243da14107882e4081ff0fdc7e73951c74e2a5ff2fc17c8bd25c72c09548a584fd27993b89d447e233913887041f20d0fec7ce37e1b60c786182fd17b8bc04ec25a12508804201fa0f387843761940b4857c27012e09304281ec0e805c02cc12408e03701a80d006102e81540a804a02200e806e03601980c8052028012809003e01d00e005002401000700240100070028008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record007_frame001_links_0000 (interval_append _ 64 128 131 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1d3ce8471cb6bdaf6cfd646318d89ec3c60faf51694b1654c289d3fc9ea4eba73538c9b94d826a534298e4c325c52d29634a8253928c939495a46121e90348023cd1d68e046c9f44e166953349954c82634310180cb80584295945c9c04d1221108c8023f11e28ec472835118a8af0550271131074c3681920c105602a21490a184ec26412408e846021210507e03d41d40e206e03581a00ac04e825412408d04602240f407203781a80d204201d00dc06403101580a4050025011808803e01e00e807002c014009804001c00d0050024010007 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record008_frame001_links_0000 (interval_append _ 64 128 130 record008_frame001_links_0064 record008_frame001_links_0128))
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6fb6f56e96d36c669d67666b66666265463d62060a5da5b05a65a259e59c59258257a56c56155054a53352852050e50c5084f94e24c74b84a34a148c48246f46842a3e03b33a93a63a239f39738c37035f33d33732c32a2db2ce2bc2b62a329628726424d22421b20a2061a519117e17415e15014413b12f12411210a1070f20ef0e40df0cc0ba0ae0a609e09008708308107f07e07b07206c06906406304203a03703203102b02902802502302201f01e01d01c01601401301000e00d00a009008007 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record008_frame002_links_0000 (interval_append _ 64 128 130 record008_frame002_links_0064 record008_frame002_links_0128))
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6fb6d369d67666666265463d62060a5da5b05a65a259e58454c51c51050b50749e47f45f44942a4123e03b33a93a63a238d35f33732e32c32a2ce2b629d29027726c26424d24522c22421b20a2061ec1d01a519117e17414b1361151060f50ee08308107f07e07b07206c06906406305d05a05505405105004f04e04b04203a03703203102b02802302201f01e01d01c01b01a01801601401301000e00d00a009008007004003002001000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0497.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0497.count (({ width := 9, code := 0x34ba1cde672992c86330f82be5dee972b859ebd56a95429d3295c7231138742207007f3f1ecf1763a5d0e66933582bf5dae56eb2582b154a751a813a9b4ba4d228f43204ec6e351989248229108642209007a3c1c0d86431180bc5c2d160ac542913094421f0d86832180b8582a1409848221007030160a048200e04018080200 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0497
    Papers.RationalityTen.SharedFrameCatalogue.group0497_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0475.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0475.count (({ width := 9, code := 0x2813d9d4e66d359a4ce652d94c96452190462230a8341608f074b85c0df6d359a4cf6733590c4602f578bb56aa1429f4da652e9549a451e8d44a1d0a833f9f0f478381acc25b2b94c7a3c1d8e872381b8d86a34180b8582b150a45027130944823110843a1b0c8602e160a8502612088401e0e06830160a048200e04018080200 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0475.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0475
    Papers.RationalityTen.SharedFrameCatalogue.group0475_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c76d7b698b4219e6ced666b1dd7a2b9e5902abd50ca7753328c936894348d242d1f48af44d21ad01a77c3a41b54ce264931c18a0be658028e13d09c64d324491d88b24422010fa47a63911bf0d0065831816c8b1c55028912588b441a2000e286982d014a095047412a092046823011207a03901bc0d406903181800b605a02b81580aa054028810807403701900c4056028011808803e01e00e807003601a00c0058028013008003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record009_frame004_links_0000 record009_frame004_links_0064)
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x28e4f598d2924b48f90f1e62ac48851021fe3f97e6f95e03a5732e51c7b5b690cc18b2ec5b4ae1492855049f53523f4428550820c3ac70cd89aa334650c717c2f059cb095a29c5249f9342444708790b1ee3b46c0cf18a308438840fe1f83e8700d219c318620ba16c2b8560a61482885009a1001c8360620c0158280460880f81e03a0700d81a0300580a0130200380680a0120200380400600800800 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record009_frame005_links_0000 record009_frame005_links_0064)
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
def record009_frame006_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f2ce8f6d9349d9c0cca651311573eb6256ca97946aa23508275d2ae8e645f22b11347e93db9db8e2266b3171694a5450127793709464231d90e286f036615a8a0c4a624c11c08c445621410707e43e61eb0eb07403821b30cb86282f61750ac052825c121089043012a092046823011207a03901bc0d406903181800b605a02b81580aa054028810807403701900c4056028011808803e01e00e807003601a00c0058028013008003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record009_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record009_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 6)
      (record009.inverseMaps 6) record009_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record009_frame006_links_0000 record009_frame006_links_0064)
theorem record009_frame006_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 6 :=
  of_group record009 6 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record009_frame006_indices record009_frame006_graph record009_frame006_links
def record009_frame007_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8ba87f84482180e8087f87dd7947737216e36c56bb6af68862b5e55c25b55a554c5345154fa4b148e4313eb3c83bb3ab3853332f52d72cd2c126925123a23321f2192131fe1f91e51df1d71c21bd1af1a018017116115b13d12e10e0ff0ef0e909509208d08c08907a07206f06a06906306005b05a05705605505405104203a03703203102b02802302201f01e01d01c01b01a01801601401301000e00d00a009008007004003002001000 } : Fields).get c.val)
theorem record009_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record009) (record009.maps 7) (record009.inverseMaps 7) record009_frame007_indices (Fin.ofNat record009.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record009_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record009) (record009.maps 7)
      (record009.inverseMaps 7) record009_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record009_frame007_links_0000 record009_frame007_links_0064)
theorem record009_frame007_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 7 :=
  of_group record009 7 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record009_frame007_indices record009_frame007_graph record009_frame007_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (Fin.cases (record009_frame006_supported hcells) (Fin.cases (record009_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1910bc65722a65468a004faa7b51888ad445212106881f3f99f78f906f235298f8c226052fd946ca0a4e72581288928470230914885e4202000eb06082a81498a044de25b12408d84481fc0f687803a01c30c305d8284132088040416809d04a823011207a03b01d00e406903181840ba05a02b81580aa054028810807c03c01d00c4056029012808803e01e00e807003601a00c00580280100068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x19fcc125812a89482a2450727d11ce8cb44f21410828314082004fe26bf32f17f4bcc5d32dd93849904a223391748a243821710888123f41de8d745c026812d093447c22e110084c4081ec0ed072036c1a40b6058027612f08d042817c09d04a823011207a03b01d00e406903181840ba05a02b81580aa054028810807c03c01d00c4056029012808803e01e00e807003601a00c00580280100068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0x2f97ab95bad368b3d96b759ab5429b49a3d1283248ec5a2b14893fdfafa7a3c1d8eb73b91bcdc6b33578ab54299449f4e2692e9046a290e853d1d8dc6b3298ca853289389a4a2311488411f8f8783a1b8d86a34198c0582a14898482210078361a0c8602e160a85026100683014090401c0a04018080200 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame003_links_0000 record012_frame003_links_0064)
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0478.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0478.count (({ width := 9, code := 0x22b1488c3a170a84c2205007f3edf0f579bc1dadf6d355a8d3693198ac3602f172b85a2c55cac542953c9247a35148742208fe7b3c1d8e6713519cc05d2c95c90472291086401e0ec74391b8d86a34188c05e2e168a84c251208c42200f878361a0c8602e160a85026100683014090401c0a04018080200 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0478.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0478.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0478.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0478.localPairCheck (smallEmbedding record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame004_links_0000 record012_frame004_links_0064)
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0478
    Papers.RationalityTen.SharedFrameCatalogue.group0478_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
def record012_frame005_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0488.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0488.count (({ width := 7, code := 0x3cf8efdbaf4e7cb8f0dfb75e9d19b262c382fdebb72ddab15aa53a33e6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record012_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0488.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0488.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0488.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0488.localPairCheck (smallEmbedding record012) (record012.maps 5)
      (record012.inverseMaps 5) record012_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame005_links_0000 record012_frame005_links_0064)
theorem record012_frame005_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 5 :=
  of_group record012 5 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0488
    Papers.RationalityTen.SharedFrameCatalogue.group0488_facts record012_frame005_indices record012_frame005_graph record012_frame005_links
def record012_frame006_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1c9acf65a02b1946a9ff4f7a75d114873427a030ff67e93e39edcf4e60c2c914049964bb2518d5867e31b16c0b1c56a29314189cc4a624c11c083838e19f0cb86443141830bd85d42dc15f0ac0548294144094048421810507b03c018009d04a823011207a03b01d00e406903181840ba05a02b81580aa054028810807c03c01d00c4056029012808803e01e00e807003601a00c00580280100068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record012_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record012_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 6)
      (record012.inverseMaps 6) record012_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record012_frame006_links_0000 record012_frame006_links_0064)
theorem record012_frame006_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 6 :=
  of_group record012 6 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame006_indices record012_frame006_graph record012_frame006_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (Fin.cases (record012_frame005_supported hcells) (Fin.cases (record012_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x412e03af8f7b1bc81d10e6070b3795b78d8b6acb4c19b6cc75c7adb95aea5b506a7c93c495647222a910487d42ba0c901a7f83f41f20f687a632d98e8b4652726c92f895c4221d80dd869c3491918bf85b22c415a0a505002720dd86903301890be05b428813c097849c22610b07403881860b004d826811808203e01e40f006f03581a40be05b02d01600aa054025011008204001b80cc062027011808804001d00e0058026012007803801a00b005002000e0050018008002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x10037bc3cc9dfee57717b835bd2da46c63549a2acfb652b121822b6a5a3ac9160eacd55b2a0d4a4a3a4c8a3e917e8304061fa4f8e7b73ca9dc4e286dd31b184cbe05d32cc9608a9e51e283117478c38b17e0b6056a29314189844561f30ee069832e18a0bd85d42ce1520a204f424210c07f03c017a0b504902340de06a03081800ba05b02b81580aa05401b80c8052028012808c03e01e00e80700280130080038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x397722e29c23666bcd55a8b4567ecc59231c60cbfd7cadb5a6b29632ba568a994ca914d694d242324568990fa1d42e84905a053ce77ceb1d238c700d91a533a5dcaf95427c4dc9912b25248c870f61d6354670c91843005d0b51662c8570ab15229c5089f10c204348640b61682b8550a21402784e06e0c81482804a08c0f81e03a0700a0130200380500901001c0280400600800800 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record014_frame002_links_0000 record014_frame002_links_0064)
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6f76eb6e066c6576406335a855d5245114c94b149e48547f46b45b4454394143f73e93d03c23b13ab39d39538f37e37537036a35635134233d33532f2ec2db2ce2bc2b62a92a129428a27526a26425b24323e22a2242182101b91a519117e17416414212d1251060ee0e00c908107f06906405b05a05705505105004f04e04904804604503703202902802502301f01e01d01c01401301000e00a009008007005004003002001000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x743b8f1c1ec686112f5d754a034d025a12a291b48623fd1e08ea46e22ed0cc82a3cd1d74e746e635e9a0ccdc63130e9828bc05cf2e016b8ae256329d14aca0e4f223391088464011f88f447843ae1cd8dc46c035119f8c085e82cb15e0a605061f80e986d03241820b1052027413308b84101ec0e904902340de06a03081800ba05b02b81580aa054027813809204601b80c8052028012808c03e01e00e80700280130080038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x830c009fdaf7877e3b9dd76e7b735395dc64e1d6feb685b18d5268c33e99c4ca5607afed79ab8f5be2da9692b3458bab2956ca8352aa8e544a99146022b113486442120c10167f93e41edcf2877136d9b1cd3265b32418d8c2a6002f19658b0454f29094149e245d1c60de06cc3301870bf05ae2c514a0a0c4c022b0ee87583a01bb0d6869832c18f0be05d42cc1520a204f4242113086036c16a08d03501840c005b02d01600ae05602a00c8052028011808804001f00f0070028013007003401600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
def record016_frame002_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1112.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1112.count (({ width := 11, code := 0x732e59ca391706dfdbd3706d6d99afb5a6a8d119fb3164ac6d8ab065f0bd177ae55c0b6d6a2cf592ae55a2a6534a414526b4929192223b46a8c9152274408750b212408800fd9f13d879cf01db3aa714e01b234c670cb1772aa548a81472824f89b1332584a49110e1d83a4738de1b0354668ca1863005c8b51662c8570ac1562904f8810c816c2d0550a81482885009c0c8148280460881001f03c0700a01301c0340580a01201c0280400600800800 } : Fields).get c.val)
theorem record016_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1112.localPairCheck (smallEmbedding record016) (record016.maps 2)
      (record016.inverseMaps 2) record016_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record016_frame002_links_0000 record016_frame002_links_0064)
theorem record016_frame002_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 2 :=
  of_group record016 2 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1112
    Papers.RationalityTen.SharedFrameCatalogue.group1112_facts record016_frame002_indices record016_frame002_graph record016_frame002_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (Fin.cases (record016_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x102378e3891c1ede26d03621aaecfe671b2957beb7c59cacc960ea7451b28993be9be4cea60d1ce8c3455a23d0f684c40ca028ff47e93e29ed8f2a7713559920c0a5fe2e99500a044f225592288d244f1d98e3c6ee35b1a38c605ca2d61630ad452228213088ac4021f30f607703aa1ad0c806282e816709e84b824211207f03bc1d20be054825c12808d03801b00d406002e016c0ac05502a00e0068032014009004601e00e8070028013008003c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3a1dbd2d686ab34ad8d0c526112e11606af1563280d3da9a04bb25a12c29514a5243120a8ff47823a51b88bb43ea1a90ac80c3b89d70e6c6fa3729afccdc6583189874c145e02e79700b5c54f29594609e44df26012b890a45222110c48464011f80f447843ae1cd8dc46c035119f8b805782a914189c04a223f10b078c3a61c20da06483021620a404e826611707b03a41c608d03501840c005d02e016c0ac05502a013c09c03c01c80c8052028012809004601e00e8070028013008003c01c009004001c00a0040018008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x67f338d93ec58622b0d57beb7959e2c114e8a36513277133e980473a30d15680a3fd1fa4f8a7b63ca9dace487113809aacc8a6082e81500a044f225411ac8983b31c78ddc5ac2c615a8a44504261129893048a22b111083840e2010fc87cc3d81dc0ea87203661ad0cf06403141740b3856029413d09a84b824211207f03bc1d208d04382180e006c03501800b805b02b01540a804f02700e0068032014009004601e00e807003601a00c0054028013008003c01c00b004802000e0040018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x71370d6fd6ed6e56e06c66a169268163d61b6125f45e05d658c57456852852251d50e5074fb4f04dc4d64d24b649347e46c4223ff3f93d73bf3b336334b33e2ff2f92f42e62e02d52ce2c22b829428426425825124823d23221720a1f11d71d01bc1a819f17d16915414313512811e10b0f20d50c60c108708308206e06a06805e05a05905405305204d04c03703303102802402301e01d01c01b01a01801501401301000f00e00b009008007004003002001000 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x9091f636c658c51822b44b8850ee0c4017f6fa1efbd8754e71c83596a4d3da033865ac898d31762cc2d7faf55d8b1156aa6526a254225b49690906a074087d0f69e23b8758e81bb36c6acd219f336658c89822f45bcaf1582964fc9d92523242c7f8f21d83986e0ce1742bc5407b0ec1d4320610be15c2985209a1302584708c0d8190300500901181e03a0700d81a0300540a01302003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record020_frame003_links_0000 record020_frame003_links_0064)
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record020_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023
