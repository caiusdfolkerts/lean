module
prelude
public import GraphInputsRow31Part00027Data
public import RawFrameSupport
public import SharedFrameGroups008Checked
public import SharedFrameGroups011Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups034Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1d12dc96b0b535a46c355c22db9670b175812b19530a8650c28093989ab4cb256925891a472a30916c8af45322691267d23979c6cdd26cc35c9a0ccb26492ed1718b285772b214b8a084f425f127092048924011d88e041a1d30ca84f224b11e08b441a2000f906582d01590a504a823a10f06402c813c09904a825012008c03d01c80d206302d015c0ac05502a0108074031015808803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0555.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0555.count (({ width := 8, code := 0xd5d3d1cfcdcac8c7c5c2c1bfbbb9b6b5b3b0afada9a7a39f9d9b9997959391908e8b8a8884827f7e7c79787672706c68666462605e5c5a58544f4e4d494847433e3d3c383736333231302f2e2c2a29282726252221201f1e1d1c1b1a171615141312110f0d0a0908070403020100 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0555.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0555.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0555.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0555.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0555
    Papers.RationalityTen.SharedFrameCatalogue.group0555_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
def record000_frame003_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1b9ed4d680b3458d0b815842be558eaa854ca99d48ea414ea271131c96f4afa4a5212903464217108283140e2004fe27343629ad0d026643299880c025fd2d1964caca54e29f14409ec4f226291bc8ba45122010b88443cf1be0c7051825a12688f8440213102068c2ec16c0b0051427612f06302c813c09904a825012008c03d01c80d206302d015c0ac05502a0108074031015808803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record000_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 3) (record000.inverseMaps 3) record000_frame003_indices (Fin.ofNat record000.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record000_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record000) (record000.maps 3)
      (record000.inverseMaps 3) record000_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record000_frame003_links_0000 record000_frame003_links_0064)
theorem record000_frame003_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 3 :=
  of_group record000 3 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record000_frame003_indices record000_frame003_graph record000_frame003_links
def record000_frame004_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0534.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0534.count (({ width := 8, code := 0xc8c4c3c0beb7b2b1aeadacaaa7a5a09f9c9b9a989593928f8e8d8c8b8a85807f7c7b7a7875736e6d6a6968666361605d5c5b5a59585653504c4a494847464542403f3e3d3c3b3937353432312f2d2b2a2726232221201f1d1c191815141312110f0e0d0b09080706050403020100 } : Fields).get c.val)
theorem record000_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0534.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0534.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0534.localPairCheck (smallEmbedding record000) (record000.maps 4) (record000.inverseMaps 4) record000_frame004_indices (Fin.ofNat record000.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record000_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0534.localPairCheck (smallEmbedding record000) (record000.maps 4)
      (record000.inverseMaps 4) record000_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record000_frame004_links_0000 record000_frame004_links_0064)
theorem record000_frame004_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 4 :=
  of_group record000 4 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0534
    Papers.RationalityTen.SharedFrameCatalogue.group0534_facts record000_frame004_indices record000_frame004_graph record000_frame004_links
def record000_frame005_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0531.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0531.count (({ width := 9, code := 0x2f573b85b2cb54a75369347a350e7d3c9a4c65f2c95c9e47218c43a19088340e02f778bbdd8e974391c0de69b499acb6532186c15e2c55eac54a994a9e4c245027a3c9d4e4703718cb85b2c150a451219047c3d1d0e46e35190bc562a138984a2411884401d0d0582a14098481e0e0682c1208038180a04018080200 } : Fields).get c.val)
theorem record000_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0531.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (smallEmbedding record000) (record000.maps 5) (record000.inverseMaps 5) record000_frame005_indices (Fin.ofNat record000.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record000_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (smallEmbedding record000) (record000.maps 5)
      (record000.inverseMaps 5) record000_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record000_frame005_links_0000 record000_frame005_links_0064)
theorem record000_frame005_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 5 :=
  of_group record000 5 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0531
    Papers.RationalityTen.SharedFrameCatalogue.group0531_facts record000_frame005_indices record000_frame005_graph record000_frame005_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (Fin.cases (record000_frame003_supported hcells) (Fin.cases (record000_frame004_supported hcells) (Fin.cases (record000_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x6a6b3558d8c195c0ab1d4cea414ea271131c96f4afa4a5212903420a0c50027f13ed9ac4d026503101808bfa5d22de9660b185652a194dca204f226511cc8ba45122210b884440d1e78eec76037c1ad8d40638303146096849a23e110084c4081ef0ec068c3001760b6058029e14509d84bc18c09e04a82300f4072034818c0b405702b01540a804f024810c08403a01880bc05602a013008803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x728e0db9b5a684cb18bb045debb1712dc5b2b39622c0510a093826a4c28bd12a1c418804fd9e73cc780ee1d1392714dc1a93305fcbb9722d6590b01572a2534a593d26c4d49211c1e8398718de1a6340660c41822cc558a814e2904f09a1302503f0730de1a4328610b615c2704b0941242404708a10c2103a0620bc1582a04c0880f81e03a0700b8160280400680a0120200380400600800800 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
def record001_frame003_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0xb355deaed3ba2137e61cad9031e22e4508910ca0d412790ef9d239b720cd58fb115fabb5742d65a0b15612b454ea8147a734c08e916224434825009f43ca774ed1bf3686c8d09942c2524a113825047c8c90e2103d8760e51c236c690cd19030c4d0891081f03a06f0ce1842c0550a814c2904d09010c2103a0620bc1582a04c0880f81e03a0700b8160280400680a0120200380400600800800 } : Fields).get c.val)
theorem record001_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record001) (record001.maps 3) (record001.inverseMaps 3) record001_frame003_indices (Fin.ofNat record001.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record001_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record001) (record001.maps 3)
      (record001.inverseMaps 3) record001_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record001_frame003_links_0000 record001_frame003_links_0064)
theorem record001_frame003_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 3 :=
  of_group record001 3 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record001_frame003_indices record001_frame003_graph record001_frame003_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (Fin.cases (record001_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x13064747e8dd17a2844785b07e05bf67c4f5dc63856d6d89abb1d620c0d7a2e65bcb115a2a552aa093c23f4748990fa15424841069fc3d0754e019730a5e4b79672bc548a494026e49c8b1092023e8788e51b4344620840ee1b83686b0d21a0310590aa1302484808e1182284307e0f81c02f0560880f81e03a0700d81a02e0580a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x2fe55ecac754b299d490a414e0a6392b8929485240d0828314009fc4fb66b13409940c406022fe9640aca53b28813dc9e445d22890b88444091fa8f8479e3ac1be0d306382cd146099c4b424d11f08b444021310207683461820bb05b02c01510a284ec25e0c604a823010e08103d81e80e406903181680ae05602a815009e0490218108074031015808803e01e00e807003601a00b805802a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x106df73e47bef51e43c3750e5dc5b7d6dad9d8b30c5eabb971aab53ea6547a824fa9b12fa5749a9051e9ff3ee790ef9d2398710df1b3344650c31632904e89892e2484708a90d2123dc720d91a6340650c317c2e45a0810f21d03886e0d61a83205f0b21402684c096128238440821001c0310560880f81e03a0700d81a02e0580a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x33816d6b3857fab19534a864ffa73132695a497246916c8af44d224d1007183749ad8d0665c324970cb28561297141c9e849024491d88e045922190b48343e81d30da06542a813c896849623c116887041a2000f9071432c1770b40564294139095047421e0c804a823010e08103d81e80e406903181680ae05602a815009e0490218108074031015808803e01e00e807003601a00b805802a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0xfc5e1bb5750e51c2b7e6c2d51a3b3664ac6d73ae25a2b3161a814e699d29a4547e879092043e8794ee1a9348650c81853045f8bd1702c65589f92322a43c851062023ec7a0f11ce364680c81842f45d0b315a2985107e0e61b0358690ce198308590ac1382584a092120218410760e81a82d0540880f81e03a0700d81a02e0580a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame005_links_0000 record002_frame005_links_0064)
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0246.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0246.count (({ width := 9, code := 0x57ea74da5d1a8b439fcea7133984be4f2591c8a3d128642a0b04813f9f2f7793bddce672389c2db6bb51a0c85fae15a9f4b2451c8c44a1906813f1d8d6663197cb85a2c154a642209007e3d1d8e87035198c05e2e168b056291389848210f870361a0c8602e160984822100703416090401c0c04018080200 } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0246.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame006_links_0000 record002_frame006_links_0064)
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0246
    Papers.RationalityTen.SharedFrameCatalogue.group0246_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
def record002_frame007_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32dd658af1559a9d9494a354d225b52688fc468a2f8ff67e93db9e9cf065f82de95fca8451628091c08724001e40e747142c715a8a0c4e6253126891848023010d88183e21c10d6067832e1910c506082f61750b7056028613509704a0242119089043020a0c804a823010e08103d81e80e406903181680ae05602a815009e0490218108074031015808803e01e00e807003601a00b805802a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record002_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 7)
      (record002.inverseMaps 7) record002_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame007_links_0000 record002_frame007_links_0064)
theorem record002_frame007_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 7 :=
  of_group record002 7 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame007_indices record002_frame007_graph record002_frame007_links
def record002_frame008_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6cc63461c5fb5e25cc5c658456e54f53752051a4ba4b249448a47c3e23c93a839037c3763313192fa2e42d02ca26425a24123922922321c2172041ec1d31bb19718217416c16415b15114914113812811810b1050ff0f90f10eb0e50df0af09508c08708107b07a07206906305a05705605505404f04904304203a03102b02201f01e01d01c01b01a01701601501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record002_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record002) (record002.maps 8)
      (record002.inverseMaps 8) record002_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame008_links_0000 record002_frame008_links_0064)
theorem record002_frame008_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 8 :=
  of_group record002 8 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record002_frame008_indices record002_frame008_graph record002_frame008_links
def record002_frame009_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1074.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1074.count (({ width := 10, code := 0x38bd6f51d1f40cdb33c5b0cbf6f3b9ee3ab6a7a6692a1a5492a3b8c625886057f9f179ddd769aa68d93635815fd7d5ed7058d5652530481174450d421003ecf73c8e0340c7308be2e4b02a8a62847d1bc681946217c5e15c50134481144410c420fc3c0e4380cc2e0a42207c1e0741c06c1a05c1605414044100340a0240801c0400c0200400 } : Fields).get c.val)
theorem record002_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1074.localPairCheck (smallEmbedding record002) (record002.maps 9)
      (record002.inverseMaps 9) record002_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame009_links_0000 record002_frame009_links_0064)
theorem record002_frame009_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 9 :=
  of_group record002 9 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1074
    Papers.RationalityTen.SharedFrameCatalogue.group1074_facts record002_frame009_indices record002_frame009_graph record002_frame009_links
def record002_frame010_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x76a6f46e16d06b269d69365a63e6276035e85dc56e56354053352049947c45d44642b4203e13c83b03a639238a31930b2f12e72d22c92c02b92a52822642452061e61d31c81c41ba1ac1a219818c17015113d13012611a10d1060fd0f50b008f08608207d07707606f06606005705405305205104d04704204103903002b02201f01e01d01c01b01a01701601501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record002_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record002) (record002.maps 10)
      (record002.inverseMaps 10) record002_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame010_links_0000 record002_frame010_links_0064)
theorem record002_frame010_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 10 :=
  of_group record002 10 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record002_frame010_indices record002_frame010_graph record002_frame010_links
def record002_frame011_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0245.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0245.count (({ width := 10, code := 0x1f3781d7749ca721c56f5b66c9ab699a464d9163d8c61d725a5645755855950521434f1374d129495224851a45d15449093f8f63a4d4324c32f8bb2d8b22b4aa2989b238882107e1e4761cc6e1ac501244811c4510c421003c0e8360cc320c4300bc2d0ac2a098220801c06c1a0641805c1604c12044100380d02c09020070180400c0200400 } : Fields).get c.val)
theorem record002_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (smallEmbedding record002) (record002.maps 11)
      (record002.inverseMaps 11) record002_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame011_links_0000 record002_frame011_links_0064)
theorem record002_frame011_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 11 :=
  of_group record002 11 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0245
    Papers.RationalityTen.SharedFrameCatalogue.group0245_facts record002_frame011_indices record002_frame011_graph record002_frame011_links
def record002_frame012_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0239.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0239.count (({ width := 8, code := 0xa19996959291908d8a898685848281807f7d7572716e6d6c6966656261605e5d5c5b59575654514e4c494845434241403f3e3d3c3b38363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a19181716151413120f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record002_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0239.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0239.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0239.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0239.localPairCheck (smallEmbedding record002) (record002.maps 12)
      (record002.inverseMaps 12) record002_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame012_links_0000 record002_frame012_links_0064)
theorem record002_frame012_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 12 :=
  of_group record002 12 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0239
    Papers.RationalityTen.SharedFrameCatalogue.group0239_facts record002_frame012_indices record002_frame012_graph record002_frame012_links
def record002_frame013_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0237.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0237.count (({ width := 8, code := 0xa19996959291908d8a898685848281807f7d7572716e6d6c6966656261605e5d5c5b59575654514e4c494845434241403f3e3d3c3b38363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a19181716151413120f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record002_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0237.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0237.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0237.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record002_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0237.localPairCheck (smallEmbedding record002) (record002.maps 13)
      (record002.inverseMaps 13) record002_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record002_frame013_links_0000 record002_frame013_links_0064)
theorem record002_frame013_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 13 :=
  of_group record002 13 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0237
    Papers.RationalityTen.SharedFrameCatalogue.group0237_facts record002_frame013_indices record002_frame013_graph record002_frame013_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (Fin.cases (record002_frame007_supported hcells) (Fin.cases (record002_frame008_supported hcells) (Fin.cases (record002_frame009_supported hcells) (Fin.cases (record002_frame010_supported hcells) (Fin.cases (record002_frame011_supported hcells) (Fin.cases (record002_frame012_supported hcells) (Fin.cases (record002_frame013_supported hcells) (fun j => Fin.elim0 j)))))))))))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x45d8870b60ec007eef51e8bad71ee09b836c6bed3d9f339664c5d88b075fcbb9742e1580ae5482784de9452524546a8c915a224247d4f29da386700dc1b134e688cc194318610bf97c2cc578aa94327a4d8989131f43c8758e71c0364658c41822fc5e0b815a28c4f87b0f21b8320620ba16c2a05209c134260470800f41b83405a0ac148280480881001c0360680b81602803c0680b0120200380400600800800 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x4027e6f71e53b874ae79c23736d4d6daab5167ccb990b1761ec0d75ae85b4b355e2b755ca4d4626e4b894d2123c47088908a043f47ccf41d139c704da9a6344658c918c30c5e0b21592884d8991272244307d8f71e43b4750de1a2324610bd16e2c0528961241c0368680cc18c3085b0ae1402704a0921202183e0780e01b02f0560901101e03a0700d81a02e0580a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x550a6b43675cda96d2c64847d8e315e27449855072033f37d6f8de1bbc760e91c938b704d61a9b28626c1971ad95acab94da834d69912f23d46c8ad1020f4127fcfc1f13d877ce59bc33062cc31792ac544a193a26a4b8929121fc3b4730e01b0344618b21581f03c8750e21b4350640c01682c0540a6148268460820e81b8300560901101e03a0700d81a02e0580a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0328.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0328.count (({ width := 8, code := 0xbab9b8b7b6b5b4b2b0afacabaaa9a6a5a3a2a19f9e9d9c9b9a9998979593928f8e8d8c89888685848281807f7e7d7b797775716d6b6562605e585653514f4d4b4844403e3c3a383532302c2b2a292827262524232221201f1e1d1c1b1a19181716151413120f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0328.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0328.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0328.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0328.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0328
    Papers.RationalityTen.SharedFrameCatalogue.group0328_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0405.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0405.count (({ width := 8, code := 0xbab9b8b7b6b5b4b2b0afacabaaa9a6a5a3a2a19f9e9d9c9b9a9998979593928f8e8d8c89888685848281807f7e7d7b797775716d6b6562605e585653514f4d4b4844403e3c3a383532302c2b2a292827262524232221201f1e1d1c1b1a19181716151413120f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0405.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0405.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0405.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0405.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame004_links_0000 record004_frame004_links_0064)
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0405
    Papers.RationalityTen.SharedFrameCatalogue.group0405_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0167.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0167.count (({ width := 8, code := 0xbab9b8b7b6b5b4b2b0afacabaaa9a6a5a3a2a19f9e9d9c9b9a9998979593928f8e8d8c89888685848281807f7e7d7b797775716d6b6562605e585653514f4d4b4844403e3c3a383532302c2b2a292827262524232221201f1e1d1c1b1a19181716151413120f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0167.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0167.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0167.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0167.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame005_links_0000 record004_frame005_links_0064)
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0167
    Papers.RationalityTen.SharedFrameCatalogue.group0167_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
def record004_frame006_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0242.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0242.count (({ width := 9, code := 0xd66ab51a6d26733592c76330d84c1602f578ba5cae16cb55a2cd64b1582b156a752a9142a04fa79369a4c25d2c9449a49229047a2d1083401ecea733519cca632d160aa532893c9a4a221007c3c1d0e06a32180b0562a148a04e26128904622108803e1e0e870361a0c8602e160a8502612078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record004_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0242.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0242.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0242.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0242.localPairCheck (smallEmbedding record004) (record004.maps 6)
      (record004.inverseMaps 6) record004_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame006_links_0000 record004_frame006_links_0064)
theorem record004_frame006_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 6 :=
  of_group record004 6 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0242
    Papers.RationalityTen.SharedFrameCatalogue.group0242_facts record004_frame006_indices record004_frame006_graph record004_frame006_links
def record004_frame007_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0117.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0117.count (({ width := 9, code := 0x182c05f6f77abadd2db67b2d82bf5dadd5aa94ea6d2a8b43a0cfe7b3c9ccd2672c934923f1e8e46a2b1386c32130481401fcfc7dbd5e4ed75389b2d3602f572b3502752c934823916833c1cce06c3499cc2572a9289246221047c3c1d0e06c34198c8622e160a44c24110803c1c0d86832180a850261208038180a0401c0c04018080200 } : Fields).get c.val)
theorem record004_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0117.localPairCheck (smallEmbedding record004) (record004.maps 7)
      (record004.inverseMaps 7) record004_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame007_links_0000 record004_frame007_links_0064)
theorem record004_frame007_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 7 :=
  of_group record004 7 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0117
    Papers.RationalityTen.SharedFrameCatalogue.group0117_facts record004_frame007_indices record004_frame007_graph record004_frame007_links
def record004_frame008_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xffd7723741a54cb7601afc5678aed563a985494a374d225b525e8e5468a2b507e82f4051fa4f6c7a73c19b3cd7a6082dc964ca5a51628191c08723fb1d88e746f230b17d8b5856a282139894c49a24612008c043620d0f507743ae1c80d286783141820be05d02dc1580a184d425c128090846420a0ef074823010e08003d81cc0e006903181700b405602a815009e04802180ec070031015809004401e00e807003601a00b805802a014008803c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record004_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 8) (record004.inverseMaps 8) record004_frame008_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 8)
      (record004.inverseMaps 8) record004_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame008_links_0000 record004_frame008_links_0064)
theorem record004_frame008_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 8 :=
  of_group record004 8 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame008_indices record004_frame008_graph record004_frame008_links
def record004_frame009_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x422824fe9f23d4776ed5cc3866fada9b1b5d698cf598326640c5d7e2f75d4b8167acb580a814c27f4e29a52b24f4948d91521841680cfc9e43c2758e61ba36c69cd099b32a624ba96a2a05109f13122e448800f91e63ac730da1963085e8b81622a84f89211e1c0368680cc18c300590aa1382604808e1182183e0760dc1a82f0560901101e03a0700d81a02e0580a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record004_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record004) (record004.maps 9) (record004.inverseMaps 9) record004_frame009_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record004) (record004.maps 9)
      (record004.inverseMaps 9) record004_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame009_links_0000 record004_frame009_links_0064)
theorem record004_frame009_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 9 :=
  of_group record004 9 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record004_frame009_indices record004_frame009_graph record004_frame009_links
def record004_frame010_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0840.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0840.count (({ width := 11, code := 0x4768a70c20e40b7eefc9eabc5776e95ceb9b6f6db9aeb48680cdd8eb16622c217c2f15ccb45672b0538a413d2704d69351fa2e43e861089f73e47a4ee9d0396700dd9b6364698ca1892d6584ad95126c4c09091a22c43c838f41ca3606a0cc18a2f4570a01321a8338640c21702d0540a012c2484508810c2003d0740d41982d0540901101e03a0700d81a02e0580a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record004_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record004) (record004.maps 10) (record004.inverseMaps 10) record004_frame010_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record004) (record004.maps 10)
      (record004.inverseMaps 10) record004_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame010_links_0000 record004_frame010_links_0064)
theorem record004_frame010_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 10 :=
  of_group record004 10 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0840
    Papers.RationalityTen.SharedFrameCatalogue.group0840_facts record004_frame010_indices record004_frame010_graph record004_frame010_links
def record004_frame011_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0404.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0404.count (({ width := 8, code := 0xbab9b8b7b6b5b4b2b0afacabaaa9a6a5a3a2a19f9e9d9c9b9a9998979593928f8e8d8c89888685848281807f7e7d7b797775716d6b6562605e585653514f4d4b4844403e3c3a383532302c2b2a292827262524232221201f1e1d1c1b1a19181716151413120f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0404.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0404.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0404.localPairCheck (smallEmbedding record004) (record004.maps 11) (record004.inverseMaps 11) record004_frame011_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0404.localPairCheck (smallEmbedding record004) (record004.maps 11)
      (record004.inverseMaps 11) record004_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame011_links_0000 record004_frame011_links_0064)
theorem record004_frame011_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 11 :=
  of_group record004 11 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0404
    Papers.RationalityTen.SharedFrameCatalogue.group0404_facts record004_frame011_indices record004_frame011_graph record004_frame011_links
def record004_frame012_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0241.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0241.count (({ width := 8, code := 0xd4d3d2d1d0cccbc7c5c4c1c0bfbebbbab8b7b6b4b3b2b1b0afaeaaa9a5a3a29f9e9d9c99989695949291908f8e8d8986817e7a74726966646259575452504e4c4943403e3c3a383532302c2b2a292827262524232221201f1e1d1c1b1a19181716151413120f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record004_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0241.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0241.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0241.localPairCheck (smallEmbedding record004) (record004.maps 12) (record004.inverseMaps 12) record004_frame012_indices (Fin.ofNat record004.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record004_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0241.localPairCheck (smallEmbedding record004) (record004.maps 12)
      (record004.inverseMaps 12) record004_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record004_frame012_links_0000 record004_frame012_links_0064)
theorem record004_frame012_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 12 :=
  of_group record004 12 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0241
    Papers.RationalityTen.SharedFrameCatalogue.group0241_facts record004_frame012_indices record004_frame012_graph record004_frame012_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (Fin.cases (record004_frame006_supported hcells) (Fin.cases (record004_frame007_supported hcells) (Fin.cases (record004_frame008_supported hcells) (Fin.cases (record004_frame009_supported hcells) (Fin.cases (record004_frame010_supported hcells) (Fin.cases (record004_frame011_supported hcells) (Fin.cases (record004_frame012_supported hcells) (fun j => Fin.elim0 j))))))))))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x11762642d853041ffbf77a8f15dd39671ce09b836c6bed499fb3965ac6988307608bbd73ae159ab25602a7540a594828a4de9a52b2504949151aa32456889092053f87d8ef9da3a4718df9b83626b4d1199326630c217f2f8598af1582925109e9362564788c1122003c8760e61c0364658c41822fc5e0b816428c4d8790dc1882e85b0a61482784d09811c1e83405a0ac148280480841001d0360680b8160280380680b0140200380400600800800 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8c687182180e7e67c07b57b174b74572f7207116f46df6b469569368767163e62c61d6005eb5d75d55c05b15aa59759357b57757055554d52b5235064fc4ec4bd4b548d47d44a42e4223c73b53ad38537536535933532431b3093002fc2ca2b529128827225d23923021320d2031fb1ce1ca1bb1b31a71a018917f17616d16513813411610c1020fa0ee0e70e00ce0ca0c60c20b90b50ad09f09609508608007b07906f05c05805704304003b03602c02302001e01b01501100d00b008005001000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record006_frame001_links_0000 (interval_append _ 64 128 129 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0525.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0525.count (({ width := 10, code := 0x27799a5694e4c916408fa2e8b22889a2487a1a84606816017f5f37bded79de376dda755cf731c670dbb6e1b46b9ac69da567d9b65d946498c6217f5d971599625815a5595052d424ed384c12d4a91b4590b42105400f53c8e8394e4384d4344cb31cc22fcb32b8a929ca425c94218811e8761c46e1b0631845f17058158551485013c4b1284911c430f0380dc2f0b02b0a0250841e07019054110340b0200500400 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record006_frame002_links_0000 (interval_append _ 64 128 129 record006_frame002_links_0064 record006_frame002_links_0128))
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0525
    Papers.RationalityTen.SharedFrameCatalogue.group0525_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0519.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0519.count (({ width := 10, code := 0x22084a0580dfb7d1f07b9df775d9761d7749d0729bf6f9bb6ddb16bdae6a1a56759c65d8f635876117e5ed775c9705b16a58d5e56d5755550535475013b4d5334c52e4ad26485184450e41903400f13bce8398e437cd7350c8310c3300b52ccb02b4a92989c25c922408e220851f0781d4731b86b1a45e16c59158521404f1384c12c47118431083f0e0340cc2b0a0250841e06c19060150440f02c090180400400 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0519.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0519.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record006_frame003_links_0000 (interval_append _ 64 128 129 record006_frame003_links_0064 record006_frame003_links_0128))
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0519
    Papers.RationalityTen.SharedFrameCatalogue.group0519_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x38fdb9adb46a5b4c19eeca9643b10183cc0f6042ded6cab5358c2c0d5e2ac9556aa8d522a69526a929476a36512279d39e9bc4c825d52d4957495a4412188fd47c22e912e881429a0f50708133fe9fe0fd07b53d21da4eb07323921c60d806b533f19a0cbe65430e981cc085fa2f91678b285622a89524a7e50d27e13e49e04e924712248d446222690ec86641e20d8ef075037f1ba0d7069031f18a0c105f02f11708b48512280133896c49023b116888441c2010fd07b03be1a00cc06082ee1670ae854428c13609604982100fd07583701a40b8059829413e08604001bc0d606002e00ec06c032016009c04601b00a80440160080038014004001 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record007_frame001_links_0000 (interval_append _ 64 128 155 record007_frame001_links_0064 record007_frame001_links_0128))
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0525.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0525.count (({ width := 10, code := 0x2789ae6796e579524f92e48912418fe358c22c8a2268921e86a1985e1383a0d82204805fd7edf97d5f07bded79de3789dd765d6749ce721c5711bd6e9b96d5ae6b1a7695a267199651926318861d866017c5e9755c96e5b56758d625815a5595453d4c515444fd3c4dd344c52c4ad1b4590b42105400f53c8ee3a4e6390e1350d132cc7308bf2e8b62c0ab2a8a7290972508d224831f87a1d8711b86d19c641885e16c55150531484b128431043e0f02b0a02709424084190541102c0801c0500801 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 128 155 :=
  interval_of_check _ 128 27 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 155 record007_frame002_links_0000 (interval_append _ 64 128 155 record007_frame002_links_0064 record007_frame002_links_0128))
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0525
    Papers.RationalityTen.SharedFrameCatalogue.group0525_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1d22e79733b819b7ed5067f3281918c2c60a3009742b5a575aa65476a274e6a71537c9b64d8a6a93349944c6a6192ca9634ae2551284939492246122c90747e23cd1d68e046ca0c4fce7623889accd3463b31697f4bc25d02ce9628ae652428e14109e84cb25591ec8c045421910748023f11ed8ef871c3721b08cb863630415a8ab452a28512e08f04181f10f2870c35c1920c105b02aa14e0a484f426c12b093047c23211108484141fe0f507803a81c40df06b034015e0a004d825412208d04601f40f007203701a80d203101800bc054025011007c03a01c00d806802a0100068028010007 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record008_frame001_links_0000 (interval_append _ 64 128 142 record008_frame001_links_0064 record008_frame001_links_0128))
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x75a75475173c71f7026e36cc6c86ae6a56a268766063e6175fd5f95e15da5d15c95c65bc5aa59e5905845515505485365125084e94d64d44b849e49548f48447d45a43d4173fa3dd3d93c13bd3aa39e39237c37136334334233532d3153082f62e82e02cf2c02b82b42ad2a429028427825d25124422121d2112091ef1e31cb1bf1b61a519418b18717f16e16316014c14012912211610d0fd0f00ec0e60d40cf0c60bb0b80a60a109408e08b08808508108007206f06b06806406303103002f02a02502201f01d01c01b01a01501000d00a008007 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record008_frame002_links_0000 (interval_append _ 64 128 142 record008_frame002_links_0064 record008_frame002_links_0128))
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x2f8de9bcd746db59cafb57aad53ea6f4ce905019cb32e56ca791921e41c808fd1e236c678c316e1cc388650a609c0a7e8fa9f43d8792f09ddbb375ee55bf35f68cca992b0b60cbd5762e45a4b215f2a654aa694b2824e49852aa4c47a8b111a1e42c82cfd1f13d6758e69bf342680c898a2e2598ac9502924f89892624446c8710720a3ec7b0ed1d23886e0d519a330630bc1702cc550a913e268468851041fc3e87a0f21c43786c0d2198328310600bc1502504407c0e81c0360680a81001a02804007 } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record008_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record008_frame003_links_0000 (interval_append _ 64 128 142 record008_frame003_links_0064 record008_frame003_links_0128))
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x704b54d9e8ce0652b1d1748aee547a9ed480a0f4daa5992a692148323fd1e08ea471a34d05a7aa3cb9d78dea6e235718c4bee5e52ea15c4ac652928113d09804a923b114886442320790047e23e11e10e206ec3651810bd057429314289444742070f1870c3681a00c906082e4148092847822e10407e83a416409504601c80d206403181740b405702b01540a804902180f807403901a80c405802b012808803e01e00e807002e0160080034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027
