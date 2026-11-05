module
prelude
public import GraphInputsSix0Part00015Data
public import RawFrameSupport
public import SharedFrameGroups004Checked
public import SharedFrameGroups005Checked
public import SharedFrameGroups008Checked
public import SharedFrameGroups014Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups030Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x88185e82f8168138097fd7f07e57cc7c67bb7ad7a179172a7287267247226686645a259e59858e58750b5074e84d14ca4b44a549f48848047146a42441b4143a63a239a39238e37734432c32a30e2f62ed2de2d22cf2bf2b72ad2a82a129428a20a2061dd1c11b91a619117f17415514a14213512d1251161060f60ee0c70bc0b00a80a006906406305a05505403703203103002f02d02802302201300e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (embedding record006) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a13c9a618f0b5823c0d5f96f336ffb3cd9bebf15bcad9c7fa3d51d18dc46b19dacd35c62de56cea2350827fd3de9dc45622690ce845419a040fec7ec3e59ee8f4479032c1914c664ef26e132c9764a81bc0d9866631117f8b705842b814b8a184dc25c129893048a2310fc87583a01c80e086ec3661ad0d3066031417c0ba857c2b01520a5051027a12f090844c2180ee07383801b20d303781a80d206002d816806e03201880a004602200d8068030013007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1576a6ed14287941fa05cfda75f3379744b464ef260926bf59f86fb97d33e5d9eccee5e0aec5746a77533295548aa37485a3e91c28d346622f916a8b0451226d12488b3b69d74e9a6383141860c105f8271934c9744ad253126091e48a23e91dc8de46922c91088583e91a00b6458e2b81540a6451227a135893045a20e100075438a1b60d3065c3101690a504ac23a0f007483881b60d403781a80d206002d816806e03201880a004602200d8068030013007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x87b85883782e81e8158067fa7ee7d07ca7b97b17ab72a72872672472266866461961160c5a259e59658c58650b5074e84d14ca4b44a549f48848047146a42441b4143a63a239d39538f32c32a30e2f62ed2de2d22cf2bf2b72ad2a829d29028926c22c20a2061fc1ec1dd1d01c11b91a619117f17415714b14213612d1251161060f60ee0c70bc0b00a80a006906406305a05505403703203102802302201b01a01801300e00d00b00a009008007005004003002001 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x6b9d2b9f73be6fcd59872ce3ec4f87f05dffbf15f6bd577ae95ca4c4918a1132253f97e6fb5f53e7728e3dc0b776e8d9dafb5d69cd299fb3b5ceb7d6da824fa9d93926b420830fe9f23dc788ec9d8394714dd9b73626a8d29942ce538a494327e4ec9a13025648c8e1102163f07b8f31da3a4720d919e318610b215a2a4530a30ce18c3105b0ae1581b0310600a0118220360680c01301c0340580a0120200380500800c01001 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record007_frame004_links_0000 record007_frame004_links_0064)
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (embedding record007) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6723373991c9c63ef139863c0e604efc579dbb5dbf6d5d67bb32d7eaae55699cece126c73539a2cc1a53d27f93547523771ae8a844e625ccc962c2de5470a0f4ee22b51327c53db1e9ce48645282136c9503791b28a44504273129893048a223107081c4021de0eb873c3901b30d686602e816e0ac052827a12808904141de0e904882300dc06c034817c0b805a02b01540a803601a00c404e024011007803a01c00d8068030012008003c01a00b004802000e0040018008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (embedding record014) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x9269259239209139048fb8e48de8dc8d98d38bd8b08a789788c87687284a84884083f83a83382181d81880a8058017ef7eb7e77066ed6a161d6075f456a55c50e5075024dc4934013ed3d73403342e62e02db2ce2c22b828526425825121920c1fb1f11d71d01b417d1751541431351170f20e10c60c108b08606c06a06705d05a05805405305203503303002702402201e01d01c01b01a01801201000f00d00b009008007004003002001000 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record014_frame002_links_0000 record014_frame002_links_0064)
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (embedding record014) hcells Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x664726990ac31e16b04781abf15e66edf6b8b5759e6cdf5beaba55825dd2d3962ca825032738cc46022e715389e44c198eb8c506a7fd3de9dc4322034ff67e83e41edcf4c65826c932c9764a81980b6458e2b414a0a0c4e425312609144461f90e407043761980c886242f81750b6857c2b01520a5051027a12f094044c2180e204d82300f006902f816c0b405802b81540a8040018809c046022010007c03a01c00d8068030012007003401600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xee3ed4ec5e88e7fe67e5be4de3ee2fdf2de9dd1dc5d85d69d56d05cfccf0ce0cd9cd0c95c8cc80c70c69c60ab1a3b94b94293692d7f779678176d74272b7136855b65af5a759e49b45944a43c41d40f3fd3e43d73cb3963402c62b62ad2652552452252152021e11d41cd1c31b51a81871781451350dc09908c07806905f05b05a05805705505404003102702302202001f01d01c01b01a01801200e00d00b00a008007005004003002001000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x83c83483281b81880e8098017f97f77e07dd7d37ce7ba7a779e76476175c75475274f73973272d7297237206155cd53b53552e52a48045544843d42a4204163c533332d32732327824a24023522021720e2001fa1f51dd1bb18e18818416615e15614d14513e13212b12712211d1161070ff0eb0e30be08f08006f06305905505405205104f04e03d03102702302202001f01d01c01b01a01801200e00d00b00a008007005004003002001000 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (embedding (N := 44310) record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (embedding (N := 44310) record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (embedding (N := 44310) record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
def record018_frame004_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x4f1e74337298dcc2a5a52c1945497e4691dc8e2c6362ed132876c31dee8f607a7bcc5e3af0c769bb0dd6ae9f747ba05808b53519a89141c9f945ba145082830408a004fe070a2f89798ba65c025c11a08ba45021c90b88424091fa0f8071a32d1708b3457225b12688f444221310187b03b41c80db06903241770b605182760e904d82300f006902f816c0b405802b81540a8040018809c046022010007c03a01c00d8068030012007003401600a004001c00a0040018008002000 } : Fields).get c.val)
theorem record018_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record018_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record018) (record018.maps 4)
      (record018.inverseMaps 4) record018_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record018_frame004_links_0000 record018_frame004_links_0064)
theorem record018_frame004_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 4 :=
  of_group record018 4 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record018_frame004_indices record018_frame004_graph record018_frame004_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (Fin.cases (record018_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x588af5572add52a894d699d28a0336e664ca97b2ca5349592323a4648a9051be2544285f04e06bd5770eb1d13936e0d69ab33c670ccd9430f614bfd7baf257c9f535a584a287d062033e4790eb1c23786a0cf9982c6580a69462744c88b10a1f23bc738c817c2ec588a81342584107d0f61c4360640c0130210260440680900900e00800800 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xaf6af5af4af3adaad6ad1ad08fc8f48e58e48e18e08d088d83d8188077e17bd7b976771c6f56e46a86a16286015f05ea5e35b25a85a158c5855705074b649348443c4353ae38b37c37336c33b33232b3173102fc2802281c51ab1a317612f0f20ea0e00c60c20ba0b90b20a409a09607905604101e01601300f00d009008003001000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x68cf465a30d17e6bb315929c8c45be26f0d6867427a12b07f7f83bbdcc8e236ccb479a0cbed5992bd15baa5652124e91fe8e946e232507882640a1f74f9a79735c97f8b805a9291143880c3cb1da8ea072a3081790b8055229913188503d41a50c806282ca13c08584141fa0da06a832018e0be052026812c07902b010403c016009803c01a009004000c002000 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 87 :=
  interval_of_check _ 64 23 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 87 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0840.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0840.count (({ width := 11, code := 0x131661cc29832fa5bcb59672b655ca894d28e4ec9b93325648c8f91722642c758a51021f43a855065fb3d478aef9d0b9a6c6d3da5343672cb58eb15608bf9752cd55aa794ba744da94116a1f438841031f23e078cec1c532c63cba16d2be5649e92d24245c7f0dd19a2cc570a611e220410811001e03005c0b41141c82a0480780680901000c00800 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (embedding (N := 44310) record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (embedding (N := 44310) record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0840.localPairCheck (embedding (N := 44310) record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (embedding record023) hcells Papers.RationalityTen.SharedFrameCatalogue.group0840
    Papers.RationalityTen.SharedFrameCatalogue.group0840_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xfcbe9fba75ce97c8f7fe99d1f9d710debba9706d5597b1961abed7a9872de3ac34831025ffbfb7d0f51e83c075ce9db8b606b2cd991afa5d2a4146a864fa9311822d40a6f0d319c30c578a914625a490838f11cc3305f8ba14e2804e09712223c460891021f03b8760dc1741d03705608c0f81e01a02000800 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
def record028_frame002_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0245.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0245.count (({ width := 10, code := 0x9565292e4590a408ea328c22d8a2208761a8520d8320981e05789de71db46a5a36859f6659665190635896057b5e57059d5a5553a4e1364c9284811d42ceb394e2358c22e8b329ca1240851fc721a8661745a15c531404d1304911c4510c420fc38098240801d06c1a02c0700400 } : Fields).get c.val)
theorem record028_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (embedding (N := 44310) record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (embedding (N := 44310) record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record028_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (embedding (N := 44310) record028) (record028.maps 2)
      (record028.inverseMaps 2) record028_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record028_frame002_links_0000 record028_frame002_links_0064)
theorem record028_frame002_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 2 :=
  of_group record028 2 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0245
    Papers.RationalityTen.SharedFrameCatalogue.group0245_facts record028_frame002_indices record028_frame002_graph record028_frame002_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (Fin.cases (record028_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xfcbe9fbbf74ed9d9bb175ce97c8381eb5d25a373ae42c3d7bee45c4b776d6d55a5b3565ec5d8aaff5f2b1d61ac156aab54fa6947675cc396f28243c778e916a2c43483104e05bd175eea19b323634bf57cab955ea4146a854b692d2523945e8b9029bc358688c315e2a45009492520e3ac710cc17e2ec550a31362584788c1021f03706b0c01741d0370640ac1402301001c01001 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0245.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0245.count (({ width := 10, code := 0x956529324b9264891a4590a3e8ee348c62f8b62a89a218721b866188521283a0d82e0a8220680a01801fe7f5fc7ddf57ade2779d472dc9719c06f9b46a5a7695956398a5c1675955b565495193a4e1354ad274992347d1e42ceb398e3358c22e8b0290a2240821f0721a8671785b158521344c11c450fc3d0e4380982408c2007c1d01c0600801 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (embedding (N := 44310) record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (embedding (N := 44310) record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0245.localPairCheck (embedding (N := 44310) record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group0245
    Papers.RationalityTen.SharedFrameCatalogue.group0245_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x14628a513a1f43684ce09b334666c708c115a26b6a6c2d75abb5269ed31a530760cbdd622b454ea5d462624a8925222374608a5112003d8770e39ba33261cbb96d2aa530a193a1f43c4658be13e258430800fe1ec3505509c1342384608a0ec1b8360560740b00800800c01000 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (embedding record058) hcells Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x293d0f9ef3d6754de9ab336634bf93d23a3bc6f8d11862a45389512222c4287f0e61541e82101e013ff78ae8dc7b8c6accc5963225f2b4165ac7586aed5a2ae552a193f26e4c494511a0f4167bcf71cc3746ccd69a0334654c89732cc570a2938242448869061fa3b0748ce1943005d0af150274468891001f03b8680b613c248480860d81a02b0500740b00a01000c01000 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
def record068_frame001_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x1322604b49672be574a494526e454878cb18e2343586509a1242284107a0e4027e6f71e53a16ecd6d8bb035d0b355e2b755ca4d4626e4b894d2123c47088908a043f47ccf41d139c704da9a63445e8b31542884f8991162244147d8ed1d42f45b8a51241c02d8570a01382504909010c1f03c0700d81782b0480880f01d0380580780d0120200380400600800800 } : Fields).get c.val)
theorem record068_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record068_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record068) (record068.maps 1)
      (record068.inverseMaps 1) record068_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record068_frame001_links_0000 record068_frame001_links_0064)
theorem record068_frame001_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) : Supported record068 1 :=
  of_group record068 1 (embedding record068) hcells Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record068_frame001_indices record068_frame001_graph record068_frame001_links
def record068_frame002_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x163abfd6ead759ab0d4aa8f4fa9652b9f73de6acc79832d2584ad9572a25245d88d076003d1760e3d9f332622bf9772e85c2b015ca904f09bd28a4a48a895092043ea7b8f29c33806c4d39983285f0b49552864f4989172264187d0eb1ce2fc5e0ad13e1b82e85b0a81482704d09811c2003d06e0d0168290440800e01b0340580780d0120200380400600800800 } : Fields).get c.val)
theorem record068_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record068_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (embedding (N := 44310) record068) (record068.maps 2)
      (record068.inverseMaps 2) record068_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record068_frame002_links_0000 record068_frame002_links_0064)
theorem record068_frame002_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) : Supported record068 2 :=
  of_group record068 2 (embedding record068) hcells Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record068_frame002_indices record068_frame002_graph record068_frame002_links
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (Fin.cases (record068_frame001_supported hcells) (Fin.cases (record068_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record068_frames_supported
theorem record069_frame000_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    Supported record069 0 :=
  of_identity record069 0 (by decide +kernel)
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
def record072_frame001_indices (c : Fin record072.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x921212344628bb15e1fc3085d0aa1141a815011f93f07d0f99f2be37baf65ec3d47a6eb1a8b4c672ca98931060ebe1762d657ca7d4ea8d4f69712b25049e8990f9fd3da768eb1c034866cc517d2ca588a911e230434831001f63e4710e01ba364640c517e2e8598a513e2704c08c1142184006a0c81882e85509c0fc1a02f0560a01181601e0380500800e00c01001 } : Fields).get c.val)
theorem record072_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record072.data.requiredEdges q = true := by decide +kernel
theorem record072_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record072) (record072.maps 1) (record072.inverseMaps 1) record072_frame001_indices (Fin.ofNat record072.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record072_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record072) (record072.maps 1) (record072.inverseMaps 1) record072_frame001_indices (Fin.ofNat record072.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record072_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (embedding (N := 44310) record072) (record072.maps 1)
      (record072.inverseMaps 1) record072_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record072_frame001_links_0000 record072_frame001_links_0064)
theorem record072_frame001_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) : Supported record072 1 :=
  of_group record072 1 (embedding record072) hcells Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record072_frame001_indices record072_frame001_graph record072_frame001_links
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (Fin.cases (record072_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
def record073_frame001_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0xa3b4668b508a053f273cde9a933a5bca794b26e474868ed1c22e4598a914e2945089911e23443883075e2b8f6accb17b2ef590b0d4928b4fc9912924e45c8ad07a033e27ace51b235867ccc98c2e659890918224434841061cc3886e0ce194318600ba14a2684b09210c2083e8780d016c278430780dc1b0340660bc1602b0520a01181601e0380500800e00c01001 } : Fields).get c.val)
theorem record073_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record073_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record073) (record073.maps 1)
      (record073.inverseMaps 1) record073_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record073_frame001_links_0000 record073_frame001_links_0064)
theorem record073_frame001_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 1 :=
  of_group record073 1 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record073_frame001_indices record073_frame001_graph record073_frame001_links
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (Fin.cases (record073_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
def record076_frame001_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x2aa553a3d4768c517a2744a60c6d8bb0b60fbb874ee69c9b6a6c2d75abb025e6b115a2624a89252222543c86d0ba14422839032053e2774e41b933c674c59752d6558a69452784d09611b21e434828fd1e83285e8bc1682ac510991182144007b0da1a8328610c01542704d08e118228400760dc1b02b04808c0e81c } : Fields).get c.val)
theorem record076_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record076_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (embedding (N := 44310) record076) (record076.maps 1)
      (record076.inverseMaps 1) record076_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record076_frame001_links_0000 record076_frame001_links_0064)
theorem record076_frame001_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 1 :=
  of_group record076 1 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record076_frame001_indices record076_frame001_graph record076_frame001_links
def record076_frame002_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0x2d76aadd6ab358abd5a9944a0cd263268ec662d0f864220afd7d3b5d4df6b3499ec862b057ebb5b2c95aac532913c9a49a49128542204fe7d3d1dce66a32990c25e2e160ae56299409a4a2290882401f8f87a3c1d8dc6833168b0562a148a04e231007c3218 } : Fields).get c.val)
theorem record076_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (embedding (N := 44310) record076) (record076.maps 2) (record076.inverseMaps 2) record076_frame002_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (embedding (N := 44310) record076) (record076.maps 2) (record076.inverseMaps 2) record076_frame002_indices (Fin.ofNat record076.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record076_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (embedding (N := 44310) record076) (record076.maps 2)
      (record076.inverseMaps 2) record076_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record076_frame002_links_0000 record076_frame002_links_0064)
theorem record076_frame002_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 2 :=
  of_group record076 2 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record076_frame002_indices record076_frame002_graph record076_frame002_links
def record076_frame003_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2a93530926c8d220b0ec85c428d96eab253aa6912da87842220710147b63d31e54f0657e2a091c08723441880ba05ac28213909844b0250124890446c23511008283ea1e90e3071436019c0ca86102fa1770b805a02b614609d04e026212909104242040ff07c83c81d40e306c034817c09f04381f00ee071038018c0b805b02a815009e04401f80e407002b012008c03a01c } : Fields).get c.val)
theorem record076_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record076) (record076.maps 3) (record076.inverseMaps 3) record076_frame003_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record076) (record076.maps 3) (record076.inverseMaps 3) record076_frame003_indices (Fin.ofNat record076.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record076_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record076) (record076.maps 3)
      (record076.inverseMaps 3) record076_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record076_frame003_links_0000 record076_frame003_links_0064)
theorem record076_frame003_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 3 :=
  of_group record076 3 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record076_frame003_indices record076_frame003_graph record076_frame003_links
def record076_frame004_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x8e2378a22789a258922381df47c5df765ba6b9a96959864d8d625725b1535413c4c12a495194550f4310840cff3e4f83bcea384db33cce308ba2dcb02b4aa294a02648d218852007b1e06d1a86918c5f16c571404b1284910c42104400fc390d8350bc2e0b42c0ac2a0a4250801f06418 } : Fields).get c.val)
theorem record076_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (embedding (N := 44310) record076) (record076.maps 4) (record076.inverseMaps 4) record076_frame004_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (embedding (N := 44310) record076) (record076.maps 4) (record076.inverseMaps 4) record076_frame004_indices (Fin.ofNat record076.n i)) 64 90 :=
  interval_of_check _ 64 26 (by decide +kernel)
theorem record076_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (embedding (N := 44310) record076) (record076.maps 4)
      (record076.inverseMaps 4) record076_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 90 record076_frame004_links_0000 record076_frame004_links_0064)
theorem record076_frame004_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 4 :=
  of_group record076 4 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record076_frame004_indices record076_frame004_graph record076_frame004_links
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (Fin.cases (record076_frame001_supported hcells) (Fin.cases (record076_frame002_supported hcells) (Fin.cases (record076_frame003_supported hcells) (Fin.cases (record076_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
def record094_frame001_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x2bbd74ac355eaa544a714ce98528a4144e86cde9b5356674c698526a4ac8f8fb1e235c678c918a2fc5d8b714623433806fc5ebba96fcd499cb2862ec0977ae359ab1d602bb56aac952a894da9992c2474868fd15a17414800f51e0364678c29802e65bcb09462784b08b9071f23986c0cf17a2cc5289d12e23c450850f8190280460860f41e0390700c015025044084100160260380680a01200800800 } : Fields).get c.val)
theorem record094_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record094) (record094.maps 1)
      (record094.inverseMaps 1) record094_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame001_links_0000 record094_frame001_links_0064)
theorem record094_frame001_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 1 :=
  of_group record094 1 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record094_frame001_indices record094_frame001_graph record094_frame001_links
def record094_frame002_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0907.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0907.count (({ width := 9, code := 0x34ba4d1e8b43a0cf677399bcce5f2b92c8e3f1d8dc5e230f85c1e07017fbf5f6f97bba56ea1449ccd653238cc42170982c01f8fa7739dcae370b79b2c55dae15ea551a81309247a2d0a813e9e8ee75399c4dc6a34198c65f2f174b6582993c9a4c259248e451a0b854261207c3c1d0e06830170b0542812088381a0a048080200 } : Fields).get c.val)
theorem record094_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0907.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0907.localPairCheck (embedding (N := 44310) record094) (record094.maps 2) (record094.inverseMaps 2) record094_frame002_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0907.localPairCheck (embedding (N := 44310) record094) (record094.maps 2) (record094.inverseMaps 2) record094_frame002_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0907.localPairCheck (embedding (N := 44310) record094) (record094.maps 2)
      (record094.inverseMaps 2) record094_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame002_links_0000 record094_frame002_links_0064)
theorem record094_frame002_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 2 :=
  of_group record094 2 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0907
    Papers.RationalityTen.SharedFrameCatalogue.group0907_facts record094_frame002_indices record094_frame002_graph record094_frame002_links
def record094_frame003_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0471.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0471.count (({ width := 9, code := 0x371b7da6bf5dacd2e873d9bcb6532587c360b0380bf5cee16db3592c762b0d82bf5eaed6eb156a752687389acaa4f2491476311487c36190b84c1a06fc78bc1d8e973b95b6d96b3519cca5dad95eac53a913c994a24110833d9d0de6b3217cb2572a9449a49230f4682e168ac54281388c421e0e06c3412080301609040080200 } : Fields).get c.val)
theorem record094_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (embedding (N := 44310) record094) (record094.maps 3) (record094.inverseMaps 3) record094_frame003_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (embedding (N := 44310) record094) (record094.maps 3) (record094.inverseMaps 3) record094_frame003_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (embedding (N := 44310) record094) (record094.maps 3)
      (record094.inverseMaps 3) record094_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame003_links_0000 record094_frame003_links_0064)
theorem record094_frame003_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 3 :=
  of_group record094 3 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0471
    Papers.RationalityTen.SharedFrameCatalogue.group0471_facts record094_frame003_indices record094_frame003_graph record094_frame003_links
def record094_frame004_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0271.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0271.count (({ width := 8, code := 0x99989795949291908f8e8d8b8a85848382817f7c7b7a77767574737271706f6d6c6b6a69686766656261605f5e5d575452514e4d4a484746444241403f3c3b3a39383735333231302f2c2b2a29282724232221201f1e1d1c1b1a19181716151413100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record094_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0271.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0271.localPairCheck (embedding (N := 44310) record094) (record094.maps 4) (record094.inverseMaps 4) record094_frame004_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0271.localPairCheck (embedding (N := 44310) record094) (record094.maps 4) (record094.inverseMaps 4) record094_frame004_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0271.localPairCheck (embedding (N := 44310) record094) (record094.maps 4)
      (record094.inverseMaps 4) record094_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame004_links_0000 record094_frame004_links_0064)
theorem record094_frame004_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 4 :=
  of_group record094 4 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0271
    Papers.RationalityTen.SharedFrameCatalogue.group0271_facts record094_frame004_indices record094_frame004_graph record094_frame004_links
def record094_frame005_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0128.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0128.count (({ width := 8, code := 0x99989795949291908f8e8d8b8a85848382817f7c7b7a77767574737271706f6d6c6b6a69686766656261605f5e5d575452514e4d4a484746444241403f3c3b3a39383735333231302f2c2b2a29282724232221201f1e1d1c1b1a19181716151413100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record094_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0128.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0128.localPairCheck (embedding (N := 44310) record094) (record094.maps 5) (record094.inverseMaps 5) record094_frame005_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0128.localPairCheck (embedding (N := 44310) record094) (record094.maps 5) (record094.inverseMaps 5) record094_frame005_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0128.localPairCheck (embedding (N := 44310) record094) (record094.maps 5)
      (record094.inverseMaps 5) record094_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame005_links_0000 record094_frame005_links_0064)
theorem record094_frame005_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 5 :=
  of_group record094 5 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0128
    Papers.RationalityTen.SharedFrameCatalogue.group0128_facts record094_frame005_indices record094_frame005_graph record094_frame005_links
def record094_frame006_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0219.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0219.count (({ width := 7, code := 0x38f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record094_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0219.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0219.localPairCheck (embedding (N := 44310) record094) (record094.maps 6) (record094.inverseMaps 6) record094_frame006_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0219.localPairCheck (embedding (N := 44310) record094) (record094.maps 6) (record094.inverseMaps 6) record094_frame006_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0219.localPairCheck (embedding (N := 44310) record094) (record094.maps 6)
      (record094.inverseMaps 6) record094_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame006_links_0000 record094_frame006_links_0064)
theorem record094_frame006_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 6 :=
  of_group record094 6 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0219
    Papers.RationalityTen.SharedFrameCatalogue.group0219_facts record094_frame006_indices record094_frame006_graph record094_frame006_links
def record094_frame007_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0113.count (({ width := 7, code := 0x38f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record094_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0113.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0113.localPairCheck (embedding (N := 44310) record094) (record094.maps 7) (record094.inverseMaps 7) record094_frame007_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0113.localPairCheck (embedding (N := 44310) record094) (record094.maps 7) (record094.inverseMaps 7) record094_frame007_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0113.localPairCheck (embedding (N := 44310) record094) (record094.maps 7)
      (record094.inverseMaps 7) record094_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame007_links_0000 record094_frame007_links_0064)
theorem record094_frame007_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 7 :=
  of_group record094 7 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0113
    Papers.RationalityTen.SharedFrameCatalogue.group0113_facts record094_frame007_indices record094_frame007_graph record094_frame007_links
def record094_frame008_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0068.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0068.count (({ width := 7, code := 0x38f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record094_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0068.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0068.localPairCheck (embedding (N := 44310) record094) (record094.maps 8) (record094.inverseMaps 8) record094_frame008_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0068.localPairCheck (embedding (N := 44310) record094) (record094.maps 8) (record094.inverseMaps 8) record094_frame008_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0068.localPairCheck (embedding (N := 44310) record094) (record094.maps 8)
      (record094.inverseMaps 8) record094_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame008_links_0000 record094_frame008_links_0064)
theorem record094_frame008_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 8 :=
  of_group record094 8 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0068
    Papers.RationalityTen.SharedFrameCatalogue.group0068_facts record094_frame008_indices record094_frame008_graph record094_frame008_links
def record094_frame009_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0050.count (({ width := 7, code := 0x38f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record094_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0050.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0050.localPairCheck (embedding (N := 44310) record094) (record094.maps 9) (record094.inverseMaps 9) record094_frame009_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0050.localPairCheck (embedding (N := 44310) record094) (record094.maps 9) (record094.inverseMaps 9) record094_frame009_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0050.localPairCheck (embedding (N := 44310) record094) (record094.maps 9)
      (record094.inverseMaps 9) record094_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame009_links_0000 record094_frame009_links_0064)
theorem record094_frame009_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 9 :=
  of_group record094 9 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0050
    Papers.RationalityTen.SharedFrameCatalogue.group0050_facts record094_frame009_indices record094_frame009_graph record094_frame009_links
def record094_frame010_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0065.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0065.count (({ width := 7, code := 0x38f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record094_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0065.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0065.localPairCheck (embedding (N := 44310) record094) (record094.maps 10) (record094.inverseMaps 10) record094_frame010_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0065.localPairCheck (embedding (N := 44310) record094) (record094.maps 10) (record094.inverseMaps 10) record094_frame010_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0065.localPairCheck (embedding (N := 44310) record094) (record094.maps 10)
      (record094.inverseMaps 10) record094_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame010_links_0000 record094_frame010_links_0064)
theorem record094_frame010_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 10 :=
  of_group record094 10 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0065
    Papers.RationalityTen.SharedFrameCatalogue.group0065_facts record094_frame010_indices record094_frame010_graph record094_frame010_links
def record094_frame011_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0049.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0049.count (({ width := 8, code := 0xb9b7b6b5b4b2b0aeadacabaaa9a5a4a2a1a09f9b9a989493908f8e8b8a89888785848381807e7d7b7877757371706d6b6a69676564625e5d5b575655524f4e4c4a48464443413f3e3d3a38363432312e2d2b29272625242322211f1d1c1a191716131211100e0d0c0b0a0906050403020100 } : Fields).get c.val)
theorem record094_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0049.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0049.localPairCheck (embedding (N := 44310) record094) (record094.maps 11) (record094.inverseMaps 11) record094_frame011_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0049.localPairCheck (embedding (N := 44310) record094) (record094.maps 11) (record094.inverseMaps 11) record094_frame011_indices (Fin.ofNat record094.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record094_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0049.localPairCheck (embedding (N := 44310) record094) (record094.maps 11)
      (record094.inverseMaps 11) record094_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record094_frame011_links_0000 record094_frame011_links_0064)
theorem record094_frame011_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 11 :=
  of_group record094 11 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0049
    Papers.RationalityTen.SharedFrameCatalogue.group0049_facts record094_frame011_indices record094_frame011_graph record094_frame011_links
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (Fin.cases (record094_frame001_supported hcells) (Fin.cases (record094_frame002_supported hcells) (Fin.cases (record094_frame003_supported hcells) (Fin.cases (record094_frame004_supported hcells) (Fin.cases (record094_frame005_supported hcells) (Fin.cases (record094_frame006_supported hcells) (Fin.cases (record094_frame007_supported hcells) (Fin.cases (record094_frame008_supported hcells) (Fin.cases (record094_frame009_supported hcells) (Fin.cases (record094_frame010_supported hcells) (Fin.cases (record094_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
def record096_frame001_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xa93a85a3a9f89d49ce9ae99e9659258f38ef8d38ac89c89788a8867ed7bf6d76b76a767867165463462d5fe5bf57b55a5525294c34af4a74944404393ec3e63bc3753363272f82df2a427924423b2112041e91db1d21a019818b18117b17414f14613a12511a1050eb0e50dd0c00b80ab09808107206e06c05f05804403603302c02502301601300e00a008007003002001 } : Fields).get c.val)
theorem record096_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record096_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record096) (record096.maps 1)
      (record096.inverseMaps 1) record096_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record096_frame001_links_0000 record096_frame001_links_0064)
theorem record096_frame001_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) : Supported record096 1 :=
  of_group record096 1 (embedding record096) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record096_frame001_indices record096_frame001_graph record096_frame001_links
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (Fin.cases (record096_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
def record097_frame001_indices (c : Fin record097.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x1f6be6fc4f7fecbd4f93f11e07bdf72ed7d83acf44e5fbab5ee9cd2d9c72f630bf9742e55b3b29626c3d7eaf7516974b89111fe2cc39832f79deba8746d51a3b4063ec017f2e05bab45642b15549cd2b2554888e9171ff3c06d8d81812dc598af93926a4ac9291c2043f07a8e41ba3345d8b716226c4b08f1181b42d84e08a0fc1f03906e0d01802c054094118160260380500800e00c01001 } : Fields).get c.val)
theorem record097_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record097.data.requiredEdges q = true := by decide +kernel
theorem record097_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record097_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record097) (record097.maps 1) (record097.inverseMaps 1) record097_frame001_indices (Fin.ofNat record097.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record097_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record097) (record097.maps 1)
      (record097.inverseMaps 1) record097_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record097_frame001_links_0000 record097_frame001_links_0064)
theorem record097_frame001_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) : Supported record097 1 :=
  of_group record097 1 (embedding record097) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record097_frame001_indices record097_frame001_graph record097_frame001_links
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (Fin.cases (record097_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
def record099_frame001_indices (c : Fin record099.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x2bc576ab155aa053fa774ea9b535a5d4b26dcd999932a3f47c8e91ca3746d8d51a6334658c318221c30836fd1f4be079ee8dc93786e6d419bb2362abf576ae85c6abd5329a51499d2d24848a8b90d2093fc7a4ef1da3ae73ce41c03766c4d099d30860cb41672984dc9a92f240448851031f63a06e8dc19a330608bb1622c0550a2134248438820e01b4338630c21642b0510961282304307a0dc1982b05008c0e81c } : Fields).get c.val)
theorem record099_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record099.data.requiredEdges q = true := by decide +kernel
theorem record099_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record099) (record099.maps 1) (record099.inverseMaps 1) record099_frame001_indices (Fin.ofNat record099.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record099_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record099) (record099.maps 1) (record099.inverseMaps 1) record099_frame001_indices (Fin.ofNat record099.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record099_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record099) (record099.maps 1)
      (record099.inverseMaps 1) record099_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record099_frame001_links_0000 record099_frame001_links_0064)
theorem record099_frame001_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) : Supported record099 1 :=
  of_group record099 1 (embedding record099) hcells Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record099_frame001_indices record099_frame001_graph record099_frame001_links
def record099_frame002_indices (c : Fin record099.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0270.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0270.count (({ width := 9, code := 0x32591c863f1d8dc662f1589c461f0983c1606fd7dbe5eef579bc5deed75ba5cec95aa9d2a91419dcd65f289348e3b1b8c44e210f86c1204fb7abbdd2e270375aed468b3996c96430576b4582a9449f49245188b411f4f8793a9c4de6c34980b65a2a950a04d249208c43200f472371b0d46833178b856291409c4c251208c421e0e8643017 } : Fields).get c.val)
theorem record099_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0270.graphBitCheck record099.data.requiredEdges q = true := by decide +kernel
theorem record099_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (embedding (N := 44310) record099) (record099.maps 2) (record099.inverseMaps 2) record099_frame002_indices (Fin.ofNat record099.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record099_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (embedding (N := 44310) record099) (record099.maps 2) (record099.inverseMaps 2) record099_frame002_indices (Fin.ofNat record099.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record099_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0270.localPairCheck (embedding (N := 44310) record099) (record099.maps 2)
      (record099.inverseMaps 2) record099_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record099_frame002_links_0000 record099_frame002_links_0064)
theorem record099_frame002_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) : Supported record099 2 :=
  of_group record099 2 (embedding record099) hcells Papers.RationalityTen.SharedFrameCatalogue.group0270
    Papers.RationalityTen.SharedFrameCatalogue.group0270_facts record099_frame002_indices record099_frame002_graph record099_frame002_links
def record099_frame003_indices (c : Fin record099.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0127.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0127.count (({ width := 9, code := 0x3a7d2e8f439fcee6f3395c9e371777badcee365b1d86bf5dadd5eab4fa6d2e9345a1cd61b0981be5c2d768b2d72ad54a7d2e9146a1cbe5b2a92c66291187415fefd7c3d1e2ef76b99c0d96ab2d84c058ac144a14c24d248e4521504803e9d0dc6d33194c45f2d164ae54289389448211047e3e1e0e06a33188c0582b148a04c220f874361a } : Fields).get c.val)
theorem record099_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0127.graphBitCheck record099.data.requiredEdges q = true := by decide +kernel
theorem record099_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (embedding (N := 44310) record099) (record099.maps 3) (record099.inverseMaps 3) record099_frame003_indices (Fin.ofNat record099.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record099_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (embedding (N := 44310) record099) (record099.maps 3) (record099.inverseMaps 3) record099_frame003_indices (Fin.ofNat record099.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record099_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0127.localPairCheck (embedding (N := 44310) record099) (record099.maps 3)
      (record099.inverseMaps 3) record099_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record099_frame003_links_0000 record099_frame003_links_0064)
theorem record099_frame003_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) : Supported record099 3 :=
  of_group record099 3 (embedding record099) hcells Papers.RationalityTen.SharedFrameCatalogue.group0127
    Papers.RationalityTen.SharedFrameCatalogue.group0127_facts record099_frame003_indices record099_frame003_graph record099_frame003_links
def record099_frame004_indices (c : Fin record099.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3459a26cc065d71db8dfc4ae1fb09d837bfd5fbaa93530a5b528a4992338f1c72a33b1858aa44f620d0ed85c428dc34d4865bacf564cac4538267d2ae8f747321e108881c3fd1f14f4c7953c19824be459029e11ac8463c31d90d106202e81630a444e426112c094049224111e08bc4322110f807b838c1c50d806703321930c205e42e01680ad8518274138092848822a10d08103fc1f20f2075038c1b00d204301f40ee071036018c0c005b02a815009c04501f80e406802b014008c03a01c } : Fields).get c.val)
theorem record099_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record099.data.requiredEdges q = true := by decide +kernel
theorem record099_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record099) (record099.maps 4) (record099.inverseMaps 4) record099_frame004_indices (Fin.ofNat record099.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record099_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record099) (record099.maps 4) (record099.inverseMaps 4) record099_frame004_indices (Fin.ofNat record099.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record099_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record099) (record099.maps 4)
      (record099.inverseMaps 4) record099_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record099_frame004_links_0000 record099_frame004_links_0064)
theorem record099_frame004_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) : Supported record099 4 :=
  of_group record099 4 (embedding record099) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record099_frame004_indices record099_frame004_graph record099_frame004_links
def record099_frame005_indices (c : Fin record099.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x3726e3da7b4b626c3d81aff5c6b7d53a9f34e67cb39570d617c1982b02e03bf17daf6debbc778ac856fa913fa7acdd97720637c4b88b08a05bfc7e4f65e3bc0774dbdaf343658bb56aabb56ea413fa6b4b69111ba3245e8910ca0f4127dcf01da3646c4c51892e0570ad15327e4c49291c22c4087b8f61cc3906c8d218e318610bc16c2bc5209f0f61d43786a0cc1742d05509e1382484307a0e01a02b05008c0e81c } : Fields).get c.val)
theorem record099_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record099.data.requiredEdges q = true := by decide +kernel
theorem record099_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record099) (record099.maps 5) (record099.inverseMaps 5) record099_frame005_indices (Fin.ofNat record099.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record099_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record099) (record099.maps 5) (record099.inverseMaps 5) record099_frame005_indices (Fin.ofNat record099.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record099_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record099) (record099.maps 5)
      (record099.inverseMaps 5) record099_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record099_frame005_links_0000 record099_frame005_links_0064)
theorem record099_frame005_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) : Supported record099 5 :=
  of_group record099 5 (embedding record099) hcells Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record099_frame005_indices record099_frame005_graph record099_frame005_links
def record099_frame006_indices (c : Fin record099.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0269.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0269.count (({ width := 8, code := 0xeeedecebeae9e8e7e6e5e4e3e0dfdedddad9d8d7d6d5d4d3d2d1d0cfcecdcbc3c2c0bebbb9b7b6b5b2b1b0afaeadaba3a2a09e9b999796959291908f8e8d8c857f7874706b6961605c5b555352504e4c4b4947413d3c3a3937353332302e2c2a2827262524232221201f1e1d1c1b1a19181716151413 } : Fields).get c.val)
theorem record099_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0269.graphBitCheck record099.data.requiredEdges q = true := by decide +kernel
theorem record099_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0269.localPairCheck (embedding (N := 44310) record099) (record099.maps 6) (record099.inverseMaps 6) record099_frame006_indices (Fin.ofNat record099.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record099_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0269.localPairCheck (embedding (N := 44310) record099) (record099.maps 6) (record099.inverseMaps 6) record099_frame006_indices (Fin.ofNat record099.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record099_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0269.localPairCheck (embedding (N := 44310) record099) (record099.maps 6)
      (record099.inverseMaps 6) record099_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record099_frame006_links_0000 record099_frame006_links_0064)
theorem record099_frame006_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) : Supported record099 6 :=
  of_group record099 6 (embedding record099) hcells Papers.RationalityTen.SharedFrameCatalogue.group0269
    Papers.RationalityTen.SharedFrameCatalogue.group0269_facts record099_frame006_indices record099_frame006_graph record099_frame006_links
def record099_frame007_indices (c : Fin record099.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0126.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0126.count (({ width := 9, code := 0x20d058240e0501803fdfcfd7e3edf4f97c3ddecf57a3cde4f1783bddced763add4e973b7dbcdc6c351a2cf6733594c963b1988c360ae570b6592b956a95429d48a350a813c9d4e259248c44208f87a381bcd66a32188c25e2e164ae552993494492291084401e8f074381b0d06431168b05429138984a23110843e1e0e06c32180b8542813 } : Fields).get c.val)
theorem record099_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0126.graphBitCheck record099.data.requiredEdges q = true := by decide +kernel
theorem record099_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0126.localPairCheck (embedding (N := 44310) record099) (record099.maps 7) (record099.inverseMaps 7) record099_frame007_indices (Fin.ofNat record099.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record099_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0126.localPairCheck (embedding (N := 44310) record099) (record099.maps 7) (record099.inverseMaps 7) record099_frame007_indices (Fin.ofNat record099.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record099_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0126.localPairCheck (embedding (N := 44310) record099) (record099.maps 7)
      (record099.inverseMaps 7) record099_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record099_frame007_links_0000 record099_frame007_links_0064)
theorem record099_frame007_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) : Supported record099 7 :=
  of_group record099 7 (embedding record099) hcells Papers.RationalityTen.SharedFrameCatalogue.group0126
    Papers.RationalityTen.SharedFrameCatalogue.group0126_facts record099_frame007_indices record099_frame007_graph record099_frame007_links
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (Fin.cases (record099_frame001_supported hcells) (Fin.cases (record099_frame002_supported hcells) (Fin.cases (record099_frame003_supported hcells) (Fin.cases (record099_frame004_supported hcells) (Fin.cases (record099_frame005_supported hcells) (Fin.cases (record099_frame006_supported hcells) (Fin.cases (record099_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00015
