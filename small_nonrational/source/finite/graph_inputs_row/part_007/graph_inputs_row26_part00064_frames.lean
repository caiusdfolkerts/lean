module
prelude
public import GraphInputsRow26Part00064Data
public import RawFrameSupport
public import SharedFrameGroups043Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064
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
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd7268ab331796a9f525a8492388fa46b22610c681c3fd9fa0fac7c73db9e98f2a6972b5945c9bc3e81e30e886c832f1740b1c5682a21498a0c4e4261112083c3fe1fa0f9878c39c1c20dd064431217b0ba85b42ce14409e84d425e12808c84301fc0f607803880e206d033017c0ba05b02b81540a803901a80b804e025011807c03a01c00c8054024011008003801800a004001c00a0040018008002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3461996b05524a8451a289942120c10427e73eb1f20f6e7a73ca1744a2a4dd1ce8d9461c2fc1768acc54429414189cc4c02240e787243841b40d6869833a1880be05d42dc1660a204f426a12f094046422610c08283d81b609803d81d40da06602f81680b005702b015008603d01a80b804e022010007c03c01c00c8054024011006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xaf0ab5a0497e94f8618237d47c07ae76c75574272b7146fd64f5de5ba4ee4c348247746b43b42841d40f3fe3ef3972d72c72b72a12932862732442252152031f11b51a81971871781561451351251030cd09607b07506d06605f05a05805705605404303d03502e02702202001f01e01c01901501201100d00c00b00a009007005004003002001000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a36ccd546292142691c47d234518289a431a0c10387fb3f49f6cf4a7932ac14509be3e81e30e7471a3661978bf05d02c715a8a9c4e225f10787fc3f41f30ef07403841ba0da069832218a0c085b02ca14409e84d425e12809084642180f607803540f607103301740b605a02b81580aa04301c80b804a023011007c03c01d00c8054022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6c66b46055f45e656c55553d5305194f84da4c94b24a549b4874803e13d23c435734833332d31b3022ed2de2cf2c62bd2af2aa2452382302262091f41e41dd1d51c41a519918f18117a14613a12d11f1131070fb0eb0cd0c50a207106a06005905705605305205104103902e02502302201f01e01d01901501101000e00d00c00a009008005004003002001000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x20ec0f75ce81c835f6aed29a3b3c65ac798ab09606bf9762e750e9e534a364568790c20c3fe7ccf51e13b875ce29c0320618c117b2cc560a69472864d49011922841c818ed1cc3806c8d119a3145d8a8148234360650b41482804f09812c2503f06e0b41282304407c0f01d0320540881001c0340600a0120200280400600800800 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x17e6fa5f3b8f6dec54ff9bd33238c4286107e0a3f87ccf7de53886fedddab34e68ecf59bb3065cca59231b62ac3d71ad357eac956aaa524a4540a7e4cc98124a373d0738dd1ab33e610be1672c2570aa1452744c0820ff1d438c6c0d3196310600b616429c5189412220c4106a0d21742383d04c0941180c01402403003 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7c17b97b178c78477974372c71d6f26dd67467364c63b6365d05c25a159558a5425205185034e24b645c45b4123ff3f93ab39c35934b33e3092f62ef2d62b52952812762511cd1c91b01aa1a217d13d13212011310e0f20be0b70b00a40a309909707106a06105a03703302802401000f00b007004001 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x73973172b7117076fd6cb6ae69465c6405da5d95bc5ae5a753b53050b4fe4f14a347046a44a4203ef39e39d35e3503492ff2f42a829b28e24a23422e2021e61d21c91c61b416215e14c14814113410e1050fa0f10ee0e50c00ba0b10a90a80a40a207206b06205b03803402802401000f00b007004001 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6bf6ba6af69e69366666362761f5f25d95c25a558b57f54e53a51d4fe4ec4e049048a47847547346143942541b4073c63b339237e37136431b3102ed2e72dd2c02bb2b726e26124c2051f81ef1c61ab1a518f18917916815412e11b10d0ff0f90e20d80c40a908707c06f06105505405204104003402501f01c01300d00a007004001000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0585.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0585.count (({ width := 8, code := 0xc4c2c1beb8b7b5b0afa9a7a39f9a9491908d8c87807f7b7a7877757372706f6c6a676661605f5e5c5b585352504f4d4b48473d3b383634312f2b2a262421201e1d1c1b1a19171513110c0b0605020100 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0585.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0585
    Papers.RationalityTen.SharedFrameCatalogue.group0585_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0583.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0583.count (({ width := 7, code := 0x9f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0583.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0583.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0583.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0583.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0583
    Papers.RationalityTen.SharedFrameCatalogue.group0583_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1032.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1032.count (({ width := 9, code := 0x3017ebd5e2ed75b9dbed364add62ad54a95469145994b63d1b8943e1b09843fdf8f8783b9cce36f36db0cf65b1988c05ead96ab057a91449d4ca591a8c42a11007b3b1d4d06530978ae552812c92431d8d4622e160ac502712888381a0b844200b038080200 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1032.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1032
    Papers.RationalityTen.SharedFrameCatalogue.group1032_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x2825009db3aa714df9a52ca50c958f317a2bc4e8970fe15421770e99b736266ec6187ae85cab4566ac8514a01352654b894122a2d442845051fc3e8798f11a934e628c297b2dc580a21422644b49111521a4246e8d619e3205e0b21542884c08c0ee1882b85309c12c228440820e41802904a06c0a00b00e00800800 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0582.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0582.count (({ width := 7, code := 0x31e2c382fdebb72ddab362bd6ab529d2a3427ce9b325ca93223c5890e0c07ef9ebc76e9cb86ed9ab466c98b05eb962b54a54274c952234280f9e3a70d9a3260b962a50992224070d18244060808080 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0582.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0582.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0582.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0582.localPairCheck (smallEmbedding record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record015_frame003_links_0000 record015_frame003_links_0064)
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0582
    Papers.RationalityTen.SharedFrameCatalogue.group0582_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7ce7cd7cb7c27bb7b47a979f78d78677c77476774474173d6dc6c765063a6245a558957153e53a53552b5254cf4b54274163fe36835d33d31330e3052ff2f92b529525123822d2162091cd1c91b01aa18617716a13d1321201130ea0e30d60c60c10ba0b508d08c07b07a07106105404003f03702801d01000f00b004000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x74173e73d73a73272c7267237127086fe6f76ec6cd6c96c363d62b5be5ac59850d4ef4d349c4974914834784053ec37936034e2b72aa28c25d25224323e2381e61d21b41a319b18b18316215e14c14813813112a10e1050fa0f10de0dc0d60c90c40bc0b609509207c07b07206205504204103802801d01000f00b004000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0819.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0819.count (({ width := 11, code := 0xa17426845039f73ce77cee9c93726b4d09992e25a4ad8d918a1241a81eefdd5b9e6ecdcdb53616aec51842be55aa8928a4b47886d082043fc7e8e19b632c620c09772dc54ca79402784988d1121ea3a4708da1822f0598a71422684a0750e61883085d0a41181c83806609c0e81001e02c02000 } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record017_frame003_links_0000 record017_frame003_links_0064)
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0819
    Papers.RationalityTen.SharedFrameCatalogue.group0819_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xed670b358daa0d4469b3451a16d05565aad1544a8b4afa52126c91f467231916a8aa44da25511a83737e1ba4daa68c33f19c4cc864e2d39650b005372949470a1e4f925a129094048f24512108ee46f23590747a632818d0bb84f626712588344001ef0f206603081680950474218101074838c1b60d405a82840de06002280e806e03201580a004601400980400140080038010004001 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x296516a1b22a3bc72845069f9bda736dfdacb51680ced9c32c638bcd742b4556a894fa6c4c89852624147686507a054007dcf49e53b6758d69a833c608bd9752de5a4a61402764a89091a22c3e4798e51c2370688c41642b84706d0b214c2904608a0e41b8350580a41282303a0700b01301c0280400700600800800 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0589.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0589.count (({ width := 11, code := 0x110a1fc3584f081f43dd756e95c4375642c71852e35b0b05532a1532a4940a7e4f69c135a684a49111fa044007e8f01d93a6744e21ad34e690b31602aa548a512f25c4808890c20a3b4740e11ae32c5e0bb16c2ac5109e13825c420830fc1b0340670aa1402083e0700d8160250440740a00d01602000800 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0589.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0589
    Papers.RationalityTen.SharedFrameCatalogue.group0589_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0xc9f61653ca393f20e3f4718d71222143585f06609bf97e4fb1ea3c3732df5a63055e8b6968acc54ca79452874b295d2123c43a808f71db3aa72cd41a031e610af15528a4ec920f81e639c708dd1ac340658c71822ec5b0b215e2a83f8640c21802a0340660b41602a0520941001c0300580a81301e0280380600600800800 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x65eacb92989474a0237d1928a844920910227f03ee9e94f1e74539f9ce4dfa6d6346199cc345982b9954ca9c54a27913a498e4be23111648744311fa0eac70636d1b40d8460e2f516d0b204dc25e12408e04201990c785d82d81640ab850426012408c04241f00ea070035811e06b03281880a803401980b405802a014809404001c00c005802a013007802800e0060018008002000 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0xa8d31613c22838ff5f93e67c2eddd639f734e15beb636bed71a734765ec95822d358eadd58aae512a113aa714868f916a2b410798ee1d239c718d219831c61caf95228e504950f61e03886f0d91a8334638c317a2d8578a91482783d0650be174280340660b41602a0520941001c0300580a81301e0280380600600800800 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
def record022_frame004_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x705b0f53d29da4dfa5a52aa93248ea2d914487f43521090788033f89f78f4076d37b1b0ccdc61f2f316bcb3658b2a094dca2c50c25a12a891247f22d105c7aa3a71cb8df066431d1800bb052227c12f892c4521b40d085e42d21570a404e426012508c042c1f80f3074036c11e06b03281880a803401980b405802a014809404001c00c005802a013007802800e0060018008002000 } : Fields).get c.val)
theorem record022_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record022_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record022) (record022.maps 4)
      (record022.inverseMaps 4) record022_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record022_frame004_links_0000 record022_frame004_links_0064)
theorem record022_frame004_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 4 :=
  of_group record022 4 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record022_frame004_indices record022_frame004_graph record022_frame004_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (Fin.cases (record022_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1922c7f636b07d7beb5558baa752f896d4ada3f11d28c3457a11106480f3fe9f14f6875d3a59ce4dd66ab310978cad244821c909c7903b51c78dec6202fe16d8b24522280127091c48023911908ac44421b10a08043e21ea0ee07543761ab0d2065831e14309e04b824e12108d044821610507f03dc1de0e8071036c0d806b03281880a803401980b405401c00c005c02c01500a004c02000f005802800e0060018008002000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1668b2e593abc15a0a8d536a8792989464a023751928a644920890227ee3ee9ea0f1e74539f9ce4dfa6d6346199cc345532a795289ec4e926592f88cc45921f10c480c3f41db8eac73e38f1c18ddc6da3671b08c906082f516b8b2051426b12f091447019b0c785e02d81640ab850c26012408c04241f40ea07003580d806b03281880a803401980b405401c00c005c02c01500a004c02000f005802800e0060018008002000 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x66566065b6406295fd5e85c153e5395334fe4f44da4cd49a49348047645844e42942441f4033ef3bf3ae3853022fd2f72be2b129b29125a25024123a21c2121f11ec1e51dd1d81d11cb1c81c51b41a419c18c18417216315b14d14510c1060f80f20ed0eb0e50df0db0d50ce0c90c30bf0b906b06a06406105303403302d02a01c01801701601501401301000f00b00a007006003002001000 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
def record023_frame004_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x189ec3d615afcd786b51590ab353d29d84dfa5992aa92f48ea2cd14487c435210d0788033f89f78f4076d37b1b0ccdc5af2cf962ca8a53728d14309704aa24691fc8be45a216905c8063ed1ea8f0074e3931be0d3c65c31d17e0bb055c28d13e096c4961b60d085ec2d21570a404ec26012508c042c1fc0f3074036c0d806b03281880a803401980b405401c00c005c02c01500a004c02000f005802800e0060018008002000 } : Fields).get c.val)
theorem record023_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record023_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record023) (record023.maps 4)
      (record023.inverseMaps 4) record023_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record023_frame004_links_0000 record023_frame004_links_0064)
theorem record023_frame004_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 4 :=
  of_group record023 4 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record023_frame004_indices record023_frame004_graph record023_frame004_links
def record023_frame005_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xa9fa99a95a81a64a2da0f9c08f68e68d688887884d8397d67c279878373f7286e86e36e06cb6ab67765961256955f5525105034e34d548447945b44c41a40c3d93cd3c63bd3ae3a439538637934d32f31d2f82e82ad2912842632531b41a718617716b1571441341251151040f60e90dc0cd06c06b06506205403403302d02a01c01801701601501401301000f00b00a007006003002001000 } : Fields).get c.val)
theorem record023_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record023) (record023.maps 5) (record023.inverseMaps 5) record023_frame005_indices (Fin.ofNat record023.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record023_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record023) (record023.maps 5)
      (record023.inverseMaps 5) record023_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record023_frame005_links_0000 record023_frame005_links_0064)
theorem record023_frame005_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 5 :=
  of_group record023 5 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record023_frame005_indices record023_frame005_graph record023_frame005_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (Fin.cases (record023_frame004_supported hcells) (Fin.cases (record023_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x3929c56e236bb337594ac9463e2e8d718b015752aed566aa454f29353c49684a6a4b92208b544d21ed0ba83d41c20c100a7b23a89d2ce6a7083539a84d166753351970ca264532017fcb505572a394bca3250226512e894448c23a91988b64582290c2c5fa2ee135097049a23211188543c017a09e045c1fe0da069031017609f04a81700ae04301c809003e01400780340140080028010002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x15329950c9d537669cc295b21e3d4688c11662844384d07a0ac017e0fb5f03c677eec1d0b92710e15bdb6669ac7988af85dcb956dacf54ea754a27d4d29992d2404728ad0ea0f40c80cf41b83225449d13525c478768e61c03445e0b215824c458800fa1a82d0530a40dc1201d0380540a01101e02c0400700800800800 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 91 :=
  interval_of_check _ 64 27 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 91 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0639.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0639.count (({ width := 9, code := 0x359a7ce66f1d89c35d6e96ab2d8abb58a7d228b3a99cc2592a9449a3b138642202fd77bb5d4e77238db0d06331580be5729934984aa491e8e43a19027d3b1ccd86631980b6582a948a04f2713082391c0dc52271288c42200e068260a040140802 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0639
    Papers.RationalityTen.SharedFrameCatalogue.group0639_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1c94e316c235b99d6cd5652b251920c8163d2ecd73cb1157e2b2156eab35522a754a09e34b6a53126c923488a2e913288343821790808394191ec8e106753351970ca26452ff955ca8e52f291945ca144ca25d128892c48a23e91988b6458228902468833318c8c2c5fa2ee1518a484f026a12e093446422310f08543c61c20d685dc2da13d09684a022810007803ac1ae0d304f82540f807202180e4052024011007c03a0140078034014008 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1e08ec96ec3709a56d156613221904c5361fadcd6baac65582975446a1d4f7276936c9954b525792aa94d4a3249123090f483a4011da8e646fa168f3a6e73669a90cf86592fe9510a5e51128113cc9c248f23d91808a444221910507de3e61e78e385aa2c01510a4c50827211008303e21e30e9870c34a1800bb858029213d09b049023e10b08183fc1ea0ea071037c1ac0d204f82540f807202180e4052024011007c03a0140078034014008 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
def record030_frame003_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0639.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0639.count (({ width := 9, code := 0x35ba9ce66f3398ca63f1b88c2dfafb75ba5c2d769b2586bd5aa9d3a9949a34fa73379a4c65b2b94c9a3b1487c2a0d027ebbddaea73b91c6dc6d355a6d167b298ec460af964b055aa54ea54d2612a9247a39168842a08fc793a9c0da6932990be5e2d164a8532612886411489c401c0d05c2a13078341408 } : Fields).get c.val)
theorem record030_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record030_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0639.localPairCheck (smallEmbedding record030) (record030.maps 3)
      (record030.inverseMaps 3) record030_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record030_frame003_links_0000 record030_frame003_links_0064)
theorem record030_frame003_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 3 :=
  of_group record030 3 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0639
    Papers.RationalityTen.SharedFrameCatalogue.group0639_facts record030_frame003_indices record030_frame003_graph record030_frame003_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (Fin.cases (record030_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1ba0d2a648b0d9608aed545a985494a374c025b521c8e5468a2b507e82f4051fa4f6c7a73ae9c08ba05b92ab94b4a2c50322610e47b43b11ce8de46162fb16b0ad4504273127892048223a11388804121fd0f787883c01d80db06a83501a10ca862c30a17d0bb85bc2c814d0a304e8270131094848823810908303ec1e40ea06f83601a408c03d81cc0e006903181700b405602a815008603b01c00c4056024011007803a01c } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
def record031_frame002_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0x286ceb9a33024247d8cb15e27449847071ff3f37d6f8de1bbc760e91c938b6f4d958e3135eab8d6cad6548a6d3da6b4c89791ea3645688107a093f67d0f71e93b4740dc9af33a638c69882dc578ae1532945109f1372624a08e10c2083c8788e91c436c698c61882e8598ad1462784c87c0e21b4350640c01682c0540a61482083a06e0c0158240440780e81c } : Fields).get c.val)
theorem record031_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record031_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (smallEmbedding record031) (record031.maps 2)
      (record031.inverseMaps 2) record031_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record031_frame002_links_0000 record031_frame002_links_0064)
theorem record031_frame002_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 2 :=
  of_group record031 2 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record031_frame002_indices record031_frame002_graph record031_frame002_links
def record031_frame003_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0840.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0840.count (({ width := 11, code := 0x21841c808ff5e53c5764e95ceb9b6e6db9aa348680cdd8eb16622c217c2f15c0b5d51a9c5089e93826b48e8fd1421f430844fb9f23d2774e81cb37a6e0da1b0340664c417c2e0594b195d28c4f09d1332564888e9192224207e8ee1d23706d8d619e318600b115e2945109b1262304286a0c21702d0540a012c2484508810c1d0350660b4150240440780e81c } : Fields).get c.val)
theorem record031_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record031_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (smallEmbedding record031) (record031.maps 3)
      (record031.inverseMaps 3) record031_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record031_frame003_links_0000 record031_frame003_links_0064)
theorem record031_frame003_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 3 :=
  of_group record031 3 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0840
    Papers.RationalityTen.SharedFrameCatalogue.group0840_facts record031_frame003_indices record031_frame003_graph record031_frame003_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (Fin.cases (record031_frame002_supported hcells) (Fin.cases (record031_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xef86593191850c035edae4965aaa4539289938293848323811668a14451e68f046e836f1970c665932c4941c9bc49724711f08e84441db8e7067e31e1800b80590278137097048422e10e08383f61e10ca862c2f215f0a584e425611807f039c1b40b004e024811c08c03581700b005702a0130086031011008003a01c00c005c02200b0038014002000 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x2544818bb0f21c421836fc1e93ce762eb1b2b5968cca587aec5c8b0157aa94fe9d52a23f474821021d434c5f0b31632a45349f9332584748c11121a3f87c0e81b6354630c01742d8580ab1081fc3a8740e219c2c85109a130228420820cc1282003a0700b01302403c0700800e00800800 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x5ceb5f612b5565a5f3da684c98f710e10c0c7faf91ef3b9768e5dc63756deda19fb3a63ac55802fb5eeae95027e48a83cf99ed3946fcd419831a5e4b89662ba4f0989172103f8758e41b434c648bf1082043b0720a2140248470861081b8340540941082003a0700b01302403c0700800e00800800 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
def record034_frame002_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xbcc5a72b314f4a684f1258121c8fc461227d1188443f61dd8ebc6f33741a48cfa63b3151824b3c59329e94a09cc4d5263925c90446a1dc8ca45b02c514609f04b023b116082c3fe1f10f206a43321750ac052425011c08704041ec0ef04a023c10407c02a815009804a0228110072034015009404202000e807002c013009003c01c0080038008002000 } : Fields).get c.val)
theorem record034_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 64 85 :=
  interval_of_check _ 64 21 (by decide +kernel)
theorem record034_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record034) (record034.maps 2)
      (record034.inverseMaps 2) record034_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 85 record034_frame002_links_0000 record034_frame002_links_0064)
theorem record034_frame002_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 2 :=
  of_group record034 2 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record034_frame002_indices record034_frame002_graph record034_frame002_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (Fin.cases (record034_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x33c958aab854fa9f52b294c499a44517a8b4450a2611188473fd9f18e7a6823371984c6e5e82969464a184e225c925c8f846a2220ee872a32b18b0c085b8278136896849823910e08383fa1f10f206543141770b4855827212b08d04382020e804902380fc05802a815008c04401b80cc050024010007c03a01c00c005c02a011007002c0100070028008002000 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xc1b6072c554769a34bea4f923090d47f22210ec85141f2044ffc7e73d19d5ce606d230217e0ba25702ac146ca064f827792449084732341168888439215906879e3901b68cc061a30517b0ae451627712d88843f41b40c886002ee16b0b0053c28c13a09784981f00e903781ac0c805802a815006e03301680b0054026010007403801700b004c01e00b005002000e0050018008002000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19ccc7f60fa8893da97c4ada3e11d28af4192078ff07c73da1e54e966eb27712e48904271e20ed46f62fe1750b10526280130893848e24011908884282010f887a83aa1a40cf05ec2ce16009e04bc24e12108d042c20a0fe07b83c01d00e203781ac0ca06403101740aa05401b80cc05a02c015009403a01c00c005c02c015009804001e00a004001c00c0050018008002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
def record040_frame002_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x306df4bd15a6ad529a313c2734d09211fe3444786d086073ff6e8d9da0b3562ec45802cd584ac54d28e4fc9d536a634aa91919a21420814f99b33545ecae958244448840ff1ec3906d8d31983085a8a90d01942f85e0b81642885006c0cc1682c0540940e81c03005c0b0150260400780a01001c0300500600800800 } : Fields).get c.val)
theorem record040_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record040_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record040) (record040.maps 2)
      (record040.inverseMaps 2) record040_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record040_frame002_links_0000 record040_frame002_links_0064)
theorem record040_frame002_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 2 :=
  of_group record040 2 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record040_frame002_indices record040_frame002_graph record040_frame002_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (Fin.cases (record040_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x188cb5552528e130090e47e234508882e3fd9f14f6e7123109458a0844c1ed0f2073a31017d0b1c522283127091c48022210787e03e21de0dd86ac34819e0cc06443041750a5050c26a128090846422410c08283bc1c408c03d81b00d206302d015c0aa05402180d006202b011007c03a01c00c005c02c015008804001a00b005002000e0040018008002000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record043_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00064
