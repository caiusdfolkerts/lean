module
prelude
public import GraphInputsRow29Part00143Data
public import RawFrameSupport
public import SharedFrameGroups034Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143
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
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0562.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0562.count (({ width := 11, code := 0x86108e1140e7f8fddf6bc9736e59c43826d4d81acb46686d019b30f608ba9692cf588ae5552824e89b13124b4888e517227438860f91e13a46e4d51a333660cbc9672be568aa13f2684989010c20a4007c8f51d43846b0d019a31c610bc1662b04f89912c23c4286e0da18c310590ac1442784e08a1041e83c0640c01502904e0780d81601e0380400700800c01000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0562.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0562
    Papers.RationalityTen.SharedFrameCatalogue.group0562_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd616a6b48d6dcb385812b19530a86501273132c95a49624691ca8c245b22bd14c89a4499c6cdd26b93419964c925c62ca1590a5c50427a12f893849024492008ec47020d0e9865427912588f045a20d10007c832c1680ac852825411d08782c813c09904a825012008c03d01c80d206302d015c0ac05502a0108074031015808803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0555.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0555.count (({ width := 8, code := 0xd1cfcdc7c5c1bfbbb9b5b3afada9a7a39f9d9b999795908e8a8884827e7c787672706c68666462605e5c5a58544f4e4d494847433e3d3c3837363231302f2e2c2a29282726252221201f1e1d1c1b1a171615141312110f0d0a0908070403020100 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0555.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0555.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0555.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0555.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0555
    Papers.RationalityTen.SharedFrameCatalogue.group0555_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xd01668b1a15f2ac754ca99d48ea414e226392be929484a40d19085c420a0c50388013f89ad0d026533101804bfa5932b294f8a204f627913148de45d228910085c4221e78df063828c12d093447c22010988103461760b6058028a13b09782c813c09904a825012008c03d01c80d206302d015c0ac05502a0108074031015808803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0534.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0534.count (({ width := 8, code := 0xc3c0beb1aeacaaa7a59f9c9a989593928f8e8d8c8b8a7f7c7a7875736d6a68666361605d5c5b5a59585653504c4a494847464542403f3e3d3c3b37353432312f2d2b2a2726232221201f1d1c191815141312110f0e0d0b09080706050403020100 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0534.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0534.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0534.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0534.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record003_frame004_links_0000 record003_frame004_links_0064)
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0534
    Papers.RationalityTen.SharedFrameCatalogue.group0534_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0531.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0531.count (({ width := 9, code := 0x170b65969b49a350e7d3c98cbe572791c86310e864220d0380bbdd8e872381bcd266b2990c360af162af562a54ca54f26122813d1e4ea72381b8c65c2d960a852289047c3d1d0e46e35190bc562a138984a2411884401d0d0582a14098481e0e0682c1208038180a04018080200 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0531.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record003_frame005_links_0000 record003_frame005_links_0064)
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0531
    Papers.RationalityTen.SharedFrameCatalogue.group0531_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x19aac6c60cab1d4cea414e226392be929484a40d0828314009fc4e6c6b13409940c406022fe96f4b1856529b94409e44ca23991748a2444217108879e3b01be0d40638303146096849a23e110084c4081d80d186002ec16c0b0053c28a13b097827812a08c03d01c80d206302d015c0ac05502a010c08403a01880bc05602a013008803e01e00e807002e01600a004001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x1c1b736b4cb18bb045d8b896cace588b01442824e09a927a2f44a871062013f6798ee1d138a6e0d49982fe5dcb916b2c8580a894b27a4d49211c1e8398718de1a6340660c11662ac540a71482784d0981281cc378690ca1842d85709c12c2504909010c2103a0620bc1582a04c0880f81e03a0700b8160280400680a0120200380400600800800 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0x2bbd5da7737e61cad8f117224432835049e43be748e6db6b3563ec457eaed5d0b41612b4540a3d39a604748b11221a412804f29da37e6c8d09942c2524a113825047c8c9081ec3b0728e11b6348668c81862244207c0e81bc338610b01542a0530a410c2103a0620bc1582a04c0880f81e03a0700b8160280400680a0120200380400600800800 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xb8357b2b1d52ca67524290538298e4ae24a5214903420a0c50027f139b1ac4d026503101808bfa5902b294eca204f727911748a242e2110f8479e3be1d60df06bc34c18e0b3451826712d093447c22d110084c4081da0d186082ec16c0b0054428a13b097825411807b03d01c80d206302d015c0ac05502a010c08403a01880ac04401f00f007403801a00b805802a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x4b391d1fa3745e8a111e16c1f816fd9f13d7718e15b5b6268cc75883035e8b996f2c4568a954aa824f08fd1d22643e84106a083f87a0f09d538065cc29792de59caf1522925009b92722c424808fa1e23946d0d11881dc370690d01882c8550981242404708c0fc1f03805e0ac1101f03c0740e01a02e0580a8140220400680a0120200380400600800800 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xc3a5b5ace15feac654d2a193fe9cc4c9a56925c91a45b22bd1348933ec1c60dd26b63419970c925c32ca1584a5c50727a124091247623810b48344031f40e986fe3681950aa04f225a12588f045a21c10688003e41c50cb05dc2d01590a504e425411d087825411807b03d01c80d206302d015c0ac05502a010c08403a01880ac04401f00f007403801a00b805802a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x7707166f26d16b96a469d65b6436225fe5e65df59859157c5755104b149046f4524384313ec3cf3a938836f36832231c3073012e22da2cc2b928e2742612361f81d11bb1b21ac1a319718f18717e16213b12411c11410b1020f90f30ea09508c07b07a07206906305a05705605505404304203a03102b02201f01e01d01c01a01701601501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record005_frame004_links_0000 record005_frame004_links_0064)
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc075962bc5566a7652528d534896d49a23f11a28be3fd9fa4f6e7a736997e0b7a57f2a11458a0247021c900079039d1c50b1c56a2831398918480239118086c41e2060f8870435819e0cb86443141820bd85d42dc1580a184d425c128090846422410c082825411807b03d01c80d206302d015c0ac05502a010c08403a01880ac04401f00f007403801a00b805802a014008804001a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record005_frame005_links_0000 record005_frame005_links_0064)
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
def record005_frame006_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x7c47507307106ef6d16c565f63b6185f35d05c255554c53452c4e146544141e3f93d63c83623423223012e32d727226925124922d2272202182051fa1f11dd1af19818718017917116816115b15313d12611510e1070ff0f60ef0e90e109508c07b07a07206906305a05705605505404304203a03102b02201f01e01d01c01a01701601501401101000d00a009008007004003002001000 } : Fields).get c.val)
theorem record005_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record005_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record005) (record005.maps 6)
      (record005.inverseMaps 6) record005_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record005_frame006_links_0000 record005_frame006_links_0064)
theorem record005_frame006_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 6 :=
  of_group record005 6 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record005_frame006_indices record005_frame006_graph record005_frame006_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (Fin.cases (record005_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x44383b001fbbd175ae3dc136c6bed3d9f339664c5d88b075fcbb9742b94f094525245464889091f53ca70ce01b836269cd1198328610be1662aa50c9e93626244c7d0f21d639c6c8cb1883045f8bc1702b45189f0f61e4370640c41742d8540a41382684c0800f41b83405a0ac148280480881001c0360680b81602803c0680b0120200380400600800800 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1dc8dd06952fc55daa6152528dd34896d497a3951a28ad41fa0bd0147e93db1e9cd7a5b92969458a0647021c8fec76239d1bc8c2c5f62d615a8a084e624612008e446021b0f507743ae1a50cf062830417c0ba05b82b014309a84b825012108c84141de0e904602000f607303801a40c605c02d01580aa054024010c07603801880ac04802200f007403801a00b805802a014008803c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x1f9bdc794e79b9b5b6aad459f32e642c5d87b035d6ba16d2cd578add4625c4848f11c222422810fd1f33d0744e71c136a698d118c30c600bc1642884d8991122183ec7b8f21da3a86f0d11923085e8b71602944b0920e01a0330630c216c2b85009c1282484807c0f01c03605e0ac1202203c0740e01a02e0580a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0550.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0550.count (({ width := 11, code := 0x2093fa7c8ed5c336a6c6d75a633d660c99903175f8bdd752e059eb2d4c2714ac93d2523645486105a033f2790f09d63986e8db19b32a63cc49752a05109f1172244007c8f31d63986d0cb1842f45c0b115427c4908f0e01a0330630c01642a84e0981202384607c0ec1b83505e0ac1202203c0740e01a02e0580a81402203c0680b0120200380400600800800 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0550.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0550
    Papers.RationalityTen.SharedFrameCatalogue.group0550_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record007_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143
