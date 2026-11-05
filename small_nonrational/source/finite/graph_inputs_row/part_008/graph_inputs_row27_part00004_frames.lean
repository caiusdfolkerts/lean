module
prelude
public import GraphInputsRow27Part00004Data
public import RawFrameSupport
public import SharedFrameGroups005Checked
public import SharedFrameGroups008Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups107Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34c1998b8c56e296d4249db4dba4cd1c8898444a1dd06480a3f41ed0f4c79532c16a0a4e4de253920c7fe3b01b20d546862fe16b0ad0500272130894c48c23810e885440e1ce0e407043761a40c886242f816d0b385782ae14b09e04d825c11a08583f81ee0ef07403880f8070035817c0b605502a0110070033013808c03a01c00d806802c014009003c01c00b005002000e0060018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1c4cdf66d7b4059dcc3c5e0ae45694a9c544a75d39a9be4d4a63930e9804b8258d2b694e4a3250124691d48724212008fa47923811b27d13879904c685842bc9598a2e4e026891dc8cc443218908c8043c518a8c285ee2a813889884101f70ea07083681930ac054429213b099049823a118089042c20a0fc07a83a01c80dc06b034011a08c03501a406403101580a0046022010007803a01c00b004c01c00d0058024010007 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x6085f95e85b75af5765585485335024fa4c14bc4ae49d48c48948247246445a44c44443f42441f41040b4043ff3f73e53de3a437332c3272ec2e72dd2ba29e29827126b25e25625223f2221e71e21d81af19919316816015615014d13a11e1181111050fc0f40eb0ea0e50df0d90d10cc0c20be0b80b50b008308206706603203102b02802302202001e01d01c01601300e00d00b009008007 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe8f669ae7d6ccb2b56ea8413fe95747322b11348454081fb0f967a23c819acc645f72d493709964231d90de06cc31116e0ae052e26e12e094c48c23110a07ac3ac1d00e006d035a1a50cf866032018a0c185f02be1580a9051025e12108984301dc0e006c834c0ee06a034818c0c005b02d00fc06403101580a004602200d806802c013007003401800b004802000e005002000c004001 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0xb9d726e2db0b37646c6d88af95d6b7d60ab5456834fc9f13ce62cbe9712a651c608a712e1bc2a84505e09c0f7f8fc5f5b8c710dfdb3b5e6a0cfd9b3285d6b9145a844f89e93824b48a8f91b1c738065cc818830c5f09c13225648c7a0ef1cc36c6b0cd1922f05b8a41461542a0530861001381e01c02401800 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xc20c1cc15be2bb1b99b91b8bb7cb70b65b47b3ba91a65a4ca42a3c9df9d09c19a399490b8e98d98a98898798598458317f77d47c06bb6ad6a067466764f63162360b5925844e74d94bf4b94aa46b45e44f43b37135e3002f02d42cd2bd23622921920118c17d16714a13a1231160f10e40b70b605805705604304002701e00e009003000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0840.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0840.count (({ width := 11, code := 0x4858eb1ae34c5289711a1d4368550960cc0e810fc1f3be47a8f4de337f6ced2d9d33465aca98ab0c60eb6d65ac2580a7d4a27f4dc9911b22d440821031d83a4728d19973205fcb996e2c8578ab93f2584a08f8df1722c8560a0132208408800f01682c04504808c0f00b01201001800 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0840
    Papers.RationalityTen.SharedFrameCatalogue.group0840_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcca6042acd4209ff4a424d118089a4182030ff67e93db9b50afe4dc265905080038c1b30bf05b02c715a8a0c4a623810688183f41e50ee87403821a60cb86443141820ba857c2b01520a204f425012108c844c2180f004682300d4069030816c0b405702b01540a803201880a404602200f807803a01c00d80680280110070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record017_frame001_links_0000 record017_frame001_links_0064)
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
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xce3650b15d7ecb745a0ac55608ac754f2a2d49ea264e5260121c8d6455a19907e7fa3f49ed8f4e7953b69c8cd846403069784ba05932b5155ca364f224b11307b43a21bb8cc86162c615a8a084e626112b892c48623c11988b444e212104880c3fa1e80ed072c37c1b60d506843321930c586142fa1770b785a02a814d0a304f8270125091047021210607f83c81d40df06c034811407303001700ac05502a0148076028012007803a01c } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
def record037_frame002_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xc0d5f4aecd6fab3a581ab8d5acaa3541a9d9494a3c4f1a68127690c47ea2e510e840418a000fe27e73e41df0e606f13601a80d2265f31f98c0c085f92d695d0a3e4f927712e892045c22890b484441a20a8fb87b43c71da8e9472e3671aa8d1466e30717c8bac5882ae14289bc4c025312188d444c21910487f03a41c00d706643121660b1856026a13209404441fe0e206c033811407303001700ac05502a0148076028012007803a01c } : Fields).get c.val)
theorem record037_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record037_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record037) (record037.maps 2)
      (record037.inverseMaps 2) record037_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record037_frame002_links_0000 record037_frame002_links_0064)
theorem record037_frame002_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 2 :=
  of_group record037 2 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record037_frame002_indices record037_frame002_graph record037_frame002_links
def record037_frame003_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6d96c069f67e65764062a6226065f15e95ce5c259857453e5225154f14da4b94b249348a48146f45142e4073ed3d83d03b439e39637e3723483202ea2d22c52a128a26325a24023923122d2212192132082001fa1e21d71cf1c91b11a91a119418c18017816f16715d15514c14413a13312512011b11410f0fc0fb0f50e20e10db0d20ca0c00b90b208a07306005c05605505405203b02802401e01d01c } : Fields).get c.val)
theorem record037_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record037) (record037.maps 3) (record037.inverseMaps 3) record037_frame003_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record037) (record037.maps 3) (record037.inverseMaps 3) record037_frame003_indices (Fin.ofNat record037.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record037_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record037) (record037.maps 3)
      (record037.inverseMaps 3) record037_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record037_frame003_links_0000 record037_frame003_links_0064)
theorem record037_frame003_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 3 :=
  of_group record037 3 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record037_frame003_indices record037_frame003_graph record037_frame003_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (Fin.cases (record037_frame002_supported hcells) (Fin.cases (record037_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19ccc1e588a8893d29b74b6a42d15e7f83da1e98f2a6ea2ee93b896a48321c8f5c6f62c414009c84c225411f08e04362000fc87c83d81d50dd065c2da1670af050c26c12e093848423410b07f03dc1d00e204502140de06b032816c0aa054029013406e033016808c03a01c00d806403001700a004c01e00e005002000e0060018008002000 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x4899011c229c5189f12a22c4085f08a09c0a7c4f81eabcf77aee1d9baf744e69b83676c6d69ab34d678ce199b2863cc3d852ff5eebc95aa814c897928a194187c8f21cb3846f0d419f3305e0b015428c4e89910a1f23bc738c817c2ec588a8134258410710c0130210260440680900900e00800800 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x22d451806d1da032862ec0977ae25beb696a2d059ab2964ac7582ae95b2b1558a4136a644b094121a3f446875052003d4780d499e322600b996f2ac5349e12c22e41c790ec1b033c5e8b314a2744b88f1142143e0640a00f41d83a0700c015025044084100160260380680a01200800800 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
def record044_frame002_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0x2ff7ebb562af52a7522853c9d4e26b33994c25f2c95ca64f2591c6a210e85c260f057dbe5eaf175395a2cf6631982bf5b2cd58a54ea591688401e4e26a32188c05d2d15ca4441d0b4562a1489446200f0743814090381a0a048080200 } : Fields).get c.val)
theorem record044_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record044_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (smallEmbedding record044) (record044.maps 2)
      (record044.inverseMaps 2) record044_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record044_frame002_links_0000 record044_frame002_links_0064)
theorem record044_frame002_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 2 :=
  of_group record044 2 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record044_frame002_indices record044_frame002_graph record044_frame002_links
def record044_frame003_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0271.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0271.count (({ width := 8, code := 0x6e6d6a646361605f5e5c5b5a59585756555453504f4c4b494745444341403e3d3b3a39383635343231302e2d2b2a29282625232221201f1e1d1c1b1a1918171412110f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record044_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0271.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0271.localPairCheck (smallEmbedding record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0271.localPairCheck (smallEmbedding record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record044_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0271.localPairCheck (smallEmbedding record044) (record044.maps 3)
      (record044.inverseMaps 3) record044_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record044_frame003_links_0000 record044_frame003_links_0064)
theorem record044_frame003_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 3 :=
  of_group record044 3 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0271
    Papers.RationalityTen.SharedFrameCatalogue.group0271_facts record044_frame003_indices record044_frame003_graph record044_frame003_links
def record044_frame004_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0128.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0128.count (({ width := 8, code := 0x6e6d6a646361605f5e5c5b5a59585756555453504f4c4b494745444341403e3d3b3a39383635343231302e2d2b2a29282625232221201f1e1d1c1b1a1918171412110f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record044_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0128.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0128.localPairCheck (smallEmbedding record044) (record044.maps 4) (record044.inverseMaps 4) record044_frame004_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0128.localPairCheck (smallEmbedding record044) (record044.maps 4) (record044.inverseMaps 4) record044_frame004_indices (Fin.ofNat record044.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record044_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0128.localPairCheck (smallEmbedding record044) (record044.maps 4)
      (record044.inverseMaps 4) record044_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record044_frame004_links_0000 record044_frame004_links_0064)
theorem record044_frame004_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 4 :=
  of_group record044 4 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0128
    Papers.RationalityTen.SharedFrameCatalogue.group0128_facts record044_frame004_indices record044_frame004_graph record044_frame004_links
def record044_frame005_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0067.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0067.count (({ width := 7, code := 0x28d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record044_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0067.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0067.localPairCheck (smallEmbedding record044) (record044.maps 5) (record044.inverseMaps 5) record044_frame005_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0067.localPairCheck (smallEmbedding record044) (record044.maps 5) (record044.inverseMaps 5) record044_frame005_indices (Fin.ofNat record044.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record044_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0067.localPairCheck (smallEmbedding record044) (record044.maps 5)
      (record044.inverseMaps 5) record044_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record044_frame005_links_0000 record044_frame005_links_0064)
theorem record044_frame005_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 5 :=
  of_group record044 5 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0067
    Papers.RationalityTen.SharedFrameCatalogue.group0067_facts record044_frame005_indices record044_frame005_graph record044_frame005_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (Fin.cases (record044_frame002_supported hcells) (Fin.cases (record044_frame003_supported hcells) (Fin.cases (record044_frame004_supported hcells) (Fin.cases (record044_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x83505e0940e816fd1f3be07b4e6dc93886e6d159f32362abf576ae85c4b7d6d2d45a0abd51a9a5269852d25348a8950fa093fc7a4ef1da3ac740e39c13766d8d81ab342674c998e31260cb415e2aa4dc9a92f240448851031e83b86e8dc19a330608bb1622c0550a2134248438820ce18c308590ac1442584a07a0dc1982b05008c0e81c } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
def record046_frame002_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0270.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0270.count (({ width := 9, code := 0xa9546a14fa752a8f419ecce5f2b934863f1b8c44e210f8642e15098441200fb7c3b1d2e67036db2d468b3996c963b0974b5582b552a65127d36984aa451888429f4f8793a9c4de6c3318cb65a2a950a04d249208c43200f472371a0cc5e2e158a450271208c421e0e8643017 } : Fields).get c.val)
theorem record046_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0270.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (smallEmbedding record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (smallEmbedding record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record046_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (smallEmbedding record046) (record046.maps 2)
      (record046.inverseMaps 2) record046_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record046_frame002_links_0000 record046_frame002_links_0064)
theorem record046_frame002_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 2 :=
  of_group record046 2 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0270
    Papers.RationalityTen.SharedFrameCatalogue.group0270_facts record046_frame002_indices record046_frame002_graph record046_frame002_links
def record046_frame003_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x65b32858fec4560eacf562aac454526012ae92047321990a881c3fd1f14f4c7953c11db4e967113749824bc25902ab11308463ec1d90cc86402e81630a444e426112b894449024211e08cc45a22710c88444081fc0fa07b838c1be0db86703321930c205e42e01680aa0534274138092848822a10d08103fc1f20f2075038c1b00d203b81c40d8063030016c0aa05401f80e406802b014008c03a01c } : Fields).get c.val)
theorem record046_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record046) (record046.maps 3) (record046.inverseMaps 3) record046_frame003_indices (Fin.ofNat record046.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record046_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record046) (record046.maps 3)
      (record046.inverseMaps 3) record046_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record046_frame003_links_0000 record046_frame003_links_0064)
theorem record046_frame003_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 3 :=
  of_group record046 3 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record046_frame003_indices record046_frame003_graph record046_frame003_links
def record046_frame004_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0xa8f50e9ed31a513fa78cdd9991ea37c5f88b0620abfc7e4f65e3bc0772ec9d43a173adbdad343668b8d6aac856ea294126b4b69111ba3245c8950c210412804fb1ef3c0768e59c33786c4c51802f0570ad15327e4c49291c21c4207b8f61cc3906c8d218e318610bc16c2bc5209f0de1a83305d0b41542784e07a0e01a02b05008c0e81c } : Fields).get c.val)
theorem record046_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record046) (record046.maps 4) (record046.inverseMaps 4) record046_frame004_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record046) (record046.maps 4) (record046.inverseMaps 4) record046_frame004_indices (Fin.ofNat record046.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record046_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record046) (record046.maps 4)
      (record046.inverseMaps 4) record046_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record046_frame004_links_0000 record046_frame004_links_0064)
theorem record046_frame004_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 4 :=
  of_group record046 4 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record046_frame004_indices record046_frame004_graph record046_frame004_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (Fin.cases (record046_frame002_supported hcells) (Fin.cases (record046_frame003_supported hcells) (Fin.cases (record046_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34a996cb795a9ad05608a9e530a6011ca8ad43320bcfd27b63d39e08c8a61f3069740ad452d2260ec46f233217d8ad450427312a093048e23f11b88884001ea0f2075c3901b90d986b434a19e0cc06282f81740b70544294135094048420a0ef07482300d206302e01680ac05502a00c4056024011007803a01c00d806403001600a803c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32d97aeadd530a8e944c9b74ada51d1d28c3457a144fd27a73ca9e08d465a929694189e4483213904c76a38f1bd8c7456a273130895049824711f88e042820e0f507703aa1b30d2865c32018a0bd85d02dc1670af04f026c12e093848423411208584141fc0f704281fc0ca05602a815009a047016807803a01c00d806403001600a004c02000f004802000e0060018008002000 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
def record051_frame002_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x2fe16e8ab652b290d4789ce4bea5a523090547f22810627f13f39f68e5067030797fcbf259d2ac1520a064f427792908a242220d10287e83e21e70ef46da35d1868bf45ec2a213c096849823e11008484081fa0f586443061760b585802a414509d04bc24c11b04281fc0ca05602a815009a047016807803a01c00d806403001600a004c02000f004802000e0060018008002000 } : Fields).get c.val)
theorem record051_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record051_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record051) (record051.maps 2)
      (record051.inverseMaps 2) record051_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record051_frame002_links_0000 record051_frame002_links_0064)
theorem record051_frame002_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 2 :=
  of_group record051 2 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record051_frame002_indices record051_frame002_graph record051_frame002_links
def record051_frame003_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6cb6756125d65c85c258c56555852c51c5164e54b248a48147b4253bd38637837233a30e3022db2cc2c629525a23923122a22221d21620e1e51dd1b41ab1a718917c16c16315b14914013813112c11210c1050fe0f90f20eb0e40df0d90d608507f06505605505404d04702d01e01d01c01b01901801601401301000f009008007006003002001000 } : Fields).get c.val)
theorem record051_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record051) (record051.maps 3) (record051.inverseMaps 3) record051_frame003_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record051) (record051.maps 3) (record051.inverseMaps 3) record051_frame003_indices (Fin.ofNat record051.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record051_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record051) (record051.maps 3)
      (record051.inverseMaps 3) record051_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record051_frame003_links_0000 record051_frame003_links_0064)
theorem record051_frame003_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 3 :=
  of_group record051 3 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record051_frame003_indices record051_frame003_graph record051_frame003_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (Fin.cases (record051_frame002_supported hcells) (Fin.cases (record051_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
def record053_frame001_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32d988ac1d588aa7d4c0a3a4dba56d28e90b461a0c8ff07a63ca9e08e226e92ee95aca58506241909c8263d71c78bf8588272130895049824711f88e042820e0ff87e43e61eb0ee06e83481970bd85d42da1670af04f026c12e093848423411207f03dc1d00e204281bc0ca05b02a815009a037016808c03a01c00d806403001600a004c02000e005002000e0060018008002000 } : Fields).get c.val)
theorem record053_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record053_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record053) (record053.maps 1)
      (record053.inverseMaps 1) record053_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record053_frame001_links_0000 record053_frame001_links_0064)
theorem record053_frame001_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) : Supported record053 1 :=
  of_group record053 1 (smallEmbedding record053) (small_cells_exact record053 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record053_frame001_indices record053_frame001_graph record053_frame001_links
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSmall.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (Fin.cases (record053_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSmall.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
def record055_frame001_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x65b2c4153ca264dba56d2168e4457a2250147a63ca9e08bb856a279120c84e3d71d80dec6aa2d613909844a824c12388fc47021410007e43aa1c80dc86402f81740b6859c2bc13c09b04b824e12108d042c1fc0f7077838810a07c03801940b605502a0134088038016808c03a01c00d806403001600a004c01e00e005802000e0060018008002000 } : Fields).get c.val)
theorem record055_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record055_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record055) (record055.maps 1)
      (record055.inverseMaps 1) record055_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record055_frame001_links_0000 record055_frame001_links_0064)
theorem record055_frame001_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) : Supported record055 1 :=
  of_group record055 1 (smallEmbedding record055) (small_cells_exact record055 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record055_frame001_indices record055_frame001_graph record055_frame001_links
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSmall.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (Fin.cases (record055_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSmall.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSmall.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSmall.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
def record059_frame001_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x50b9ab34a65c8c8ff1be33c5e89b0e601bff7e4fb1f0bcd756e89acb56698c297f2ec5c4b61622b14f29d5362674ba93518a2643c865089f83c0708d8196320624c217b2e6598b114426a4ac8f9112164147e0ef1c8374680b61602a4510840da19c2d85a0aa1501b8310460880e81c0360640c0160260380680c0140200380500600800800 } : Fields).get c.val)
theorem record059_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record059_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record059) (record059.maps 1)
      (record059.inverseMaps 1) record059_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record059_frame001_links_0000 record059_frame001_links_0064)
theorem record059_frame001_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 1 :=
  of_group record059 1 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record059_frame001_indices record059_frame001_graph record059_frame001_links
def record059_frame002_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcb65cfae2d6d0a8a530288d3de9c94c9256d13488a432a1510647f83d31e08cd665731a1558a584ef25d92548bc4271b30d5866232017f0b104e4254126091c47e22a10a07e43d61d60e8071c3841ba0d9069033e1830ba85b42be1500a5051027812f09384842260f607803a01c408c03781a40b605a02a815006e031011808803a01c00d8064030016009803801a00c005002000e0050018008002000 } : Fields).get c.val)
theorem record059_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record059_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record059) (record059.maps 2)
      (record059.inverseMaps 2) record059_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record059_frame002_links_0000 record059_frame002_links_0064)
theorem record059_frame002_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 2 :=
  of_group record059 2 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record059_frame002_indices record059_frame002_graph record059_frame002_links
def record059_frame003_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x76971570f7056bf6a768d67766664f6345c45bc5a65a058756c53251f4cb4c24b344e4394144013f33d73bc37a37235a34e33d3172e62d32c82c12b829827924e23b22021820e2071fa1f01db1d41ad19818b17816315915214613112511a1070e30dc0d20ca08606c06605805705205103603002302201d01c01b01901801601300e00d00c00a008007005003002001000 } : Fields).get c.val)
theorem record059_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record059) (record059.maps 3) (record059.inverseMaps 3) record059_frame003_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record059) (record059.maps 3) (record059.inverseMaps 3) record059_frame003_indices (Fin.ofNat record059.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record059_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record059) (record059.maps 3)
      (record059.inverseMaps 3) record059_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record059_frame003_links_0000 record059_frame003_links_0064)
theorem record059_frame003_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) : Supported record059 3 :=
  of_group record059 3 (smallEmbedding record059) (small_cells_exact record059 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record059_frame003_indices record059_frame003_graph record059_frame003_links
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSmall.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (Fin.cases (record059_frame001_supported hcells) (Fin.cases (record059_frame002_supported hcells) (Fin.cases (record059_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSmall.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSmall.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x87285784b84782a81c81381177f7747657266f36e86ba69b68766264b6476155ed5c858856a56553b52b5024df49146745544a4254183d23ab3a538838433e3212f32e32e129f2551ef1dd1c11b11881831621471351210f20ed0d10c80c20ba0b00a60a409c09507106e06c05d03102d02502300a009004003 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (smallEmbedding record062) (small_cells_exact record062 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSmall.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x10820ec1781d026034057caf71e03bd736e21b1b5d65cc317aadf5a8b35652c9540a553d2774c294d1da374247dcf21d63a06ecdb1b0356674c998e3125f8bc9742e0574aa14327e4a49391a2204107f8f41dc3846e0cd1983045d8b1158250460871041dc3a8740c41802f8560a21402684c0961281a8320620a01182203e0780e81c } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
def record063_frame002_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3381994ca1622b0257babca5822a7d446a104c0248115889a4181fa4f6e76d3889b54d526962e815ac9de4dc2260fb06f036617e0ad450625712888f046622d11388444081fc0fa079c3be1d90e886f436c1a70d0863831617e0bb05ac2c81540a684f8270125091045421a10207d83981be0d8069024811a08c03781a80d206002d81680ae05602a815006e03201880a004602200f807803a01c } : Fields).get c.val)
theorem record063_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record063_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record063) (record063.maps 2)
      (record063.inverseMaps 2) record063_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record063_frame002_links_0000 record063_frame002_links_0064)
theorem record063_frame002_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) : Supported record063 2 :=
  of_group record063 2 (smallEmbedding record063) (small_cells_exact record063 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record063_frame002_indices record063_frame002_graph record063_frame002_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSmall.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (Fin.cases (record063_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
def record064_frame001_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6653115812bca5822a7d42098049022690607fb3f49edce226d534b1740ad64dc2260fb06cc2fc1638ad450625412608dc44420e0ff87e43e61e40ef07403741b30d3067832218a0bd85d42a214a09e84d4250121089043011a08c03501a40b605a02b81580aa05401900c404602200f807803a01c00d8064030015008003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record064_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record064_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record064) (record064.maps 1)
      (record064.inverseMaps 1) record064_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record064_frame001_links_0000 record064_frame001_links_0064)
theorem record064_frame001_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) : Supported record064 1 :=
  of_group record064 1 (smallEmbedding record064) (small_cells_exact record064 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record064_frame001_indices record064_frame001_graph record064_frame001_links
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSmall.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (Fin.cases (record064_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSmall.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
def record066_frame001_indices (c : Fin record066.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1920bd756f2a6936e97d4a3a30d15e8513fe9f9cf687a73ae1a8cb54566241912482638f1bd8c745922b314009cc4a824c11c088c43a21610707703aa1ba0d9869831e1880bd85b82bc136097049c23411208584141fc0f7074036c10a07f03581940be05602a013408e033016809c03c01c00d8064030014009804802000f005002400e0060018008002000 } : Fields).get c.val)
theorem record066_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record066.data.requiredEdges q = true := by decide +kernel
theorem record066_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record066_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record066) (record066.maps 1) (record066.inverseMaps 1) record066_frame001_indices (Fin.ofNat record066.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record066_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record066) (record066.maps 1)
      (record066.inverseMaps 1) record066_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record066_frame001_links_0000 record066_frame001_links_0064)
theorem record066_frame001_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) : Supported record066 1 :=
  of_group record066 1 (smallEmbedding record066) (small_cells_exact record066 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record066_frame001_indices record066_frame001_graph record066_frame001_links
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSmall.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (Fin.cases (record066_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSmall.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSmall.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record068_frames_supported
theorem record069_frame000_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) :
    Supported record069 0 :=
  of_identity record069 0 (by decide +kernel)
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSmall.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
def record070_frame001_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xd8c69bb3298a4b2756929953da9cc4e326c133a9784b8a58929e940499a4ad24690a48424011e48ec4702374eaa658319979cb7453c28c137c98449f24390f48624231f80f447883781a58b3455227012988c04301ce0e106d03021620ac854029414009a04b424e11d08c04442060fc07b83c01d60e406e03581a00a8049823410a07003500c805a028012008c03c01d00e006002600f0070024010007 } : Fields).get c.val)
theorem record070_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record070_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record070) (record070.maps 1)
      (record070.inverseMaps 1) record070_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record070_frame001_links_0000 record070_frame001_links_0064)
theorem record070_frame001_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) : Supported record070 1 :=
  of_group record070 1 (smallEmbedding record070) (small_cells_exact record070 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record070_frame001_indices record070_frame001_graph record070_frame001_links
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSmall.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (Fin.cases (record070_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSmall.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
def record072_frame001_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x60730196c6b5256aa9d5476a3550726c52988fe47b239d1708a341f20c0ffc7f03f39c5ce1269031797e0be65d32c114b49de4e927092e494e45a22810ac84241a2050fd073a38d1b78cf465a30f17b0bc05c02ce15c0a844d023d117080c3f41ec0e306d83481770b5851827412608d04281f00e903781ac0be05b02a815006e033013808c03a01c00d8064030013009003c01c00c005002000e0050018008002000 } : Fields).get c.val)
theorem record072_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record072) (record072.maps 1) (record072.inverseMaps 1) record072_frame001_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record072) (record072.maps 1) (record072.inverseMaps 1) record072_frame001_indices (Fin.ofNat record072.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record072_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record072) (record072.maps 1)
      (record072.inverseMaps 1) record072_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record072_frame001_links_0000 record072_frame001_links_0064)
theorem record072_frame001_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) : Supported record072 1 :=
  of_group record072 1 (smallEmbedding record072) (small_cells_exact record072 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record072_frame001_indices record072_frame001_graph record072_frame001_links
def record072_frame002_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x7fafddeabd2772e61bcb746dcd71a0b1861ec2d81b005ccb85682cb58ea5949a774b08e91aa2f4327fcec9d0398710e09a834664cc798b30c604b69692c2540a493a2564a09292423a464881001f8398710dd1a8348688c31782b85289a12a244468890bc16c2984f0921201902f04e08c0e81c0360640c01302403c0700c0140200380500600800800 } : Fields).get c.val)
theorem record072_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record072) (record072.maps 2) (record072.inverseMaps 2) record072_frame002_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record072) (record072.maps 2) (record072.inverseMaps 2) record072_frame002_indices (Fin.ofNat record072.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record072_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record072) (record072.maps 2)
      (record072.inverseMaps 2) record072_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record072_frame002_links_0000 record072_frame002_links_0064)
theorem record072_frame002_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) : Supported record072 2 :=
  of_group record072 2 (smallEmbedding record072) (small_cells_exact record072 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record072_frame002_indices record072_frame002_graph record072_frame002_links
def record072_frame003_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xa2543e6b4d295f2323746b8cf13615408804ffdf93ec79af15d83ab74cd69ab32e614bad742e2588a813f2784ea9b133a4d48e8d518a2c44c878fc1f13c2728e11b132a638c49842f65ccb114d2884ac9291f22242c828ef1c8340638bb16c2c0548a20da1a42f05b0aa1501b83304e08c0e81c0360640c01302403c0700c0140200380500600800800 } : Fields).get c.val)
theorem record072_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record072) (record072.maps 3) (record072.inverseMaps 3) record072_frame003_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record072) (record072.maps 3) (record072.inverseMaps 3) record072_frame003_indices (Fin.ofNat record072.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record072_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record072) (record072.maps 3)
      (record072.inverseMaps 3) record072_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record072_frame003_links_0000 record072_frame003_links_0064)
theorem record072_frame003_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) : Supported record072 3 :=
  of_group record072 3 (smallEmbedding record072) (small_cells_exact record072 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record072_frame003_indices record072_frame003_graph record072_frame003_links
def record072_frame004_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6733331740b8b581aa29444a124f7a64923e8af44c22290ca8543fc1fa0f687a63ca99b0cae5cf2ab13b89bc4bb22f0fac6f63641ab0cc46402c415a0a004e426112a093045422310b08003f21ec0ea873838e1c20dd06c833e1890c185b42ce15f0a8052828812f093844c2160fe07b03c01d00e203781ac0be05b02a815006e033013808c03a01c00d8064030013009003c01c00c005002000e0050018008002000 } : Fields).get c.val)
theorem record072_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record072) (record072.maps 4) (record072.inverseMaps 4) record072_frame004_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record072) (record072.maps 4) (record072.inverseMaps 4) record072_frame004_indices (Fin.ofNat record072.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record072_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record072) (record072.maps 4)
      (record072.inverseMaps 4) record072_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record072_frame004_links_0000 record072_frame004_links_0064)
theorem record072_frame004_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) : Supported record072 4 :=
  of_group record072 4 (smallEmbedding record072) (small_cells_exact record072 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record072_frame004_indices record072_frame004_graph record072_frame004_links
def record072_frame005_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x6da6d266765f6215e85c15bb5ae57b54651650e5074f04e74b74b149148948141740f3cf39537136b35e3282f12c62be2b72a029726125923e23823122a2221fc1f51e71cb1c41b61a71a319d19819018817515a15213713112d12111d1191060fe0ec0e40d90d50d00c80c306f06b05f05b05505403703302702301d01c01b01901801301200f00e00c00a008007005003002001000 } : Fields).get c.val)
theorem record072_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record072) (record072.maps 5) (record072.inverseMaps 5) record072_frame005_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record072) (record072.maps 5) (record072.inverseMaps 5) record072_frame005_indices (Fin.ofNat record072.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record072_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record072) (record072.maps 5)
      (record072.inverseMaps 5) record072_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record072_frame005_links_0000 record072_frame005_links_0064)
theorem record072_frame005_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) : Supported record072 5 :=
  of_group record072 5 (smallEmbedding record072) (small_cells_exact record072 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record072_frame005_indices record072_frame005_graph record072_frame005_links
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSmall.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (Fin.cases (record072_frame001_supported hcells) (Fin.cases (record072_frame002_supported hcells) (Fin.cases (record072_frame003_supported hcells) (Fin.cases (record072_frame004_supported hcells) (Fin.cases (record072_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSmall.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSmall.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSmall.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSmall.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSmall.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSmall.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSmall.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSmall.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSmall.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSmall.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
def record083_frame001_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x34a98aec085ef2de1680af1530a93538a9934b6a39515a82f3f49f58f6c7a73919b50d5464430616f4a5a519248917c8723b11bc8bec56a2a214109cc4ae25011e88ec45c22010908244061ef0f307803b01cc0da86bc3501a00cd062c3001770b785902a814609d04c425212208e042420c0fb07c83a81be0d8069023011006d034818c0b805a02b01540a805001a80c4056024011007803a01c } : Fields).get c.val)
theorem record083_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record083) (record083.maps 1) (record083.inverseMaps 1) record083_frame001_indices (Fin.ofNat record083.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record083_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record083) (record083.maps 1)
      (record083.inverseMaps 1) record083_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record083_frame001_links_0000 record083_frame001_links_0064)
theorem record083_frame001_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) : Supported record083 1 :=
  of_group record083 1 (smallEmbedding record083) (small_cells_exact record083 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record083_frame001_indices record083_frame001_graph record083_frame001_links
def record083_frame002_indices (c : Fin record083.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x67163f62d61d6085f75e05bf5b958e5775615285094d04a94a049449046044742d40e3f83d33ae3a837c36334d3172fd2c82a729f29729428d28427227025c24623322622120a2051f61e91dc1c11bc1b31ae19f18b17f17617216915414213512511910e1040eb0e90db0da0c60bb0b10ac08608206b06706105a05805405305204e03503102b02402201e01d01c } : Fields).get c.val)
theorem record083_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record083.data.requiredEdges q = true := by decide +kernel
theorem record083_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record083) (record083.maps 2) (record083.inverseMaps 2) record083_frame002_indices (Fin.ofNat record083.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record083_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record083) (record083.maps 2) (record083.inverseMaps 2) record083_frame002_indices (Fin.ofNat record083.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record083_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record083) (record083.maps 2)
      (record083.inverseMaps 2) record083_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record083_frame002_links_0000 record083_frame002_links_0064)
theorem record083_frame002_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) : Supported record083 2 :=
  of_group record083 2 (smallEmbedding record083) (small_cells_exact record083 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record083_frame002_indices record083_frame002_graph record083_frame002_links
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSmall.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (Fin.cases (record083_frame001_supported hcells) (Fin.cases (record083_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSmall.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSmall.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
def record086_frame001_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x6f4362dac2d15647ae0d64cafc55828a93989c54d926c13469954bc25912aa94d4a0a4a924891d48aa43d2008f947623911b2698319987cbe25e72e29678a2c4e124411988aa4232090fc07c23c41d80e086f03561978a9c4e42190fb87983681a30c085c82b21500a50508278132096849c23e118088840c1fc0f507703901b80d606802ac11808803480c4056024011008403c01d00e005801e00d0060024010007 } : Fields).get c.val)
theorem record086_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record086_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record086) (record086.maps 1)
      (record086.inverseMaps 1) record086_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record086_frame001_links_0000 record086_frame001_links_0064)
theorem record086_frame001_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) : Supported record086 1 :=
  of_group record086 1 (smallEmbedding record086) (small_cells_exact record086 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record086_frame001_indices record086_frame001_graph record086_frame001_links
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSmall.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (Fin.cases (record086_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSmall.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSmall.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSmall.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSmall.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSmall.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSmall.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSmall.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSmall.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSmall.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
def record096_frame001_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x18aeb7856ea98549aa214e226492b694848fa3a515488a4209fa4fac7a73919910b5252d28c93b492045e21390507d63b51bb0d5861a2b515109cc4ae25011e88b4432212104880c3de1e60ea073036a1af0d4068032618b0c005dc2de1640b1055428213f09804a824411c08a043820c0fb07c83c41be0d8069023011007903681a40c805a02b01540a805002080d406202c011007803a01c } : Fields).get c.val)
theorem record096_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record096_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record096) (record096.maps 1)
      (record096.inverseMaps 1) record096_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record096_frame001_links_0000 record096_frame001_links_0064)
theorem record096_frame001_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) : Supported record096 1 :=
  of_group record096 1 (smallEmbedding record096) (small_cells_exact record096 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record096_frame001_indices record096_frame001_graph record096_frame001_links
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSmall.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (Fin.cases (record096_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSmall.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSmall.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSmall.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004
