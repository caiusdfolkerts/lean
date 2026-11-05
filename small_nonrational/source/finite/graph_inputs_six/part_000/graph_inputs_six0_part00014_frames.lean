module
prelude
public import GraphInputsSix0Part00014Data
public import RawFrameSupport
public import SharedFrameGroups030Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups032Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014
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
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0491.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0491.count (({ width := 9, code := 0xf8fbbd9eaeef6fb5d6ea74f95c9e470f7dbdd0e7f3d9ccc6531589c2e130782bede6f175b9dc2cd62ae55ea74fa250e85409fcf66d3499cc65d2c8f47639198b44611047f3edeef372b6da6d065b258ec5612f56cb0552953e9b4923d107d3b9c4e06a33184b8592b1489c4a220f4782f0f8743410078341809040080200 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0491.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (embedding (N := 44310) record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (embedding record003) hcells Papers.RationalityTen.SharedFrameCatalogue.group0491
    Papers.RationalityTen.SharedFrameCatalogue.group0491_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0477.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0477.count (({ width := 9, code := 0x984be5d2d964ae55299449e4d259248e45218c45e2d158943e130883c1a0b0481c01fefd7e3e9e6f076ba5cce37037dbcdd6e36daed66ab4da4d164b218ec5612f974b659ac95cab5227d389b4c25d2a9448a3910833f9ecec72371b0ce612d95cac502612c8e45210f87436180ac54210b858280e0682c1408038080200 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0477.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0477.localPairCheck (embedding (N := 44310) record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0477.localPairCheck (embedding (N := 44310) record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0477.localPairCheck (embedding (N := 44310) record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (embedding record003) hcells Papers.RationalityTen.SharedFrameCatalogue.group0477
    Papers.RationalityTen.SharedFrameCatalogue.group0477_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0x3c7dceaf478dc1dd6cf5babd0e733192c5e22ef75b85b2c55faed6aaf51a752a9145a14ee73379b4d66931974b6552993486411f8e46a331187c32170a84c1207017e3e5e6f176ba9d0e56d3418ec4602f972b357aa54aa14ea652c8e441f4f275389b4d46732188c05d2d15ca42d160a84a221007438120883c1c0a048080200 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (embedding record004) hcells Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0478.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0478.count (({ width := 9, code := 0x28b43a04fa7b399acc6592a93c8e411d8cc5a2712884360f0682405fefc7cbd9e8f1773add4e97439dcce57238dc4e170379badc6cb61aed16833d9ccd6632d94c8623097ebd5d2dd6ab255a9d48a350a8138984aa41188942a04fc793a1b4d2663197cb85b2c158a8512712c8c271309444200f87438120883c1c0a048080200 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0478.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0478.localPairCheck (embedding (N := 44310) record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0478.localPairCheck (embedding (N := 44310) record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0478.localPairCheck (embedding (N := 44310) record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (embedding record004) hcells Papers.RationalityTen.SharedFrameCatalogue.group0478
    Papers.RationalityTen.SharedFrameCatalogue.group0478_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0xd65a4f41675cab8f7165fdbed782ef5c3b636b2cdd8eb0d612b4d60ab955ea7549a7943641c768ad0fa1c42f776eddd738970adedb435c69ed257d2f05daba161aa64e6919132054067e0f01d7390710d397d2b654ca694828a4f49b921236444850fe1f43ac6d0ce1883045a0b115c2a8538a41101b03385f0ae1541b83604a08c1001302403c0700a01000c00800 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (embedding record005) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0496.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0496.count (({ width := 9, code := 0xf5fabd3e8f0f83bdddee76bb3d5e9f4b9dcde5f2b91c6e2f1383bedeee7419ecee4b218eb9dcae362afd6ea349a2502673298cb6411c8741202f679bb9c8dc6c3518ab957aad48a04fa71349246a2d0c803e9dce06932988b4572b14ca04d230f87637190c04e260e870341007834180a0400c0200 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0496.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (embedding (N := 44310) record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (embedding (N := 44310) record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0496.localPairCheck (embedding (N := 44310) record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (embedding record005) hcells Papers.RationalityTen.SharedFrameCatalogue.group0496
    Papers.RationalityTen.SharedFrameCatalogue.group0496_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6723373938c7de173039813bceddaecf7665ab955a678739d9c24d8e61d29e93fc9aa3c91cb8db468e3171788a844e625d10e87ac39a1810ab84eb289920c7e62c2f7d6f2af24ee25651868ab4079f9cf8a7b63d39db8eb874a3921aacc8a5be254109471e37716d8acc522282139894c49824511c08c445622310e885841c20710087703aa1c80d986b432c1880ba05b82b014a09e84b822410507f03bc1d20db03601800be05c02b0150068028013809003c01c00d8068030014009804802000f005802400e0040018008002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8be8ba8ac89086986285c85184a81c8157e77e379c79178e78878075c75975374974774574274073e73a73873673072e72b72772572265264e64b64061e6095e15975585135084bb4a849949449047b47346e46142e40f3d43833433042fc2b52a629a29729428827f27926925f25524923f23722b22421e1ed1e71d41bf1b919618917517115814613711f0f60e70e00cc0c40b606a05e05d05a05405203402802702401e01c01b01a01801401301201000f00b009007004003002001000 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0994.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0994.count (({ width := 11, code := 0x160abf57aae95beb6569acd592ac556a9552296529a4f4928fd14a2543e8650aa1141a82502a013fe7f4fb9f53e67c4f79ed21a4147e8ef16623c237b8ee5c7b876acd199c33465cc758c31461abbd6e2b84e493d11a183d4770e71c83866dcd91b035268ccf199328644c5984300580ad14e27c4e8919172144107c8ef1cc378630be1742b8558a20c015c2b05309a12c1882804e0900f01c0360680c0140260480800f0160240380400600800800 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (embedding (N := 44310) record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (embedding (N := 44310) record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (embedding (N := 44310) record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record015_frame003_links_0000 record015_frame003_links_0064)
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group0994
    Papers.RationalityTen.SharedFrameCatalogue.group0994_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x80c8007ce7af77376d76675775274c74173b73272f70b7076ca6ba68a65463d61e61660e6035f75eb5d95c65ba5aa58557256554252c51242741e4153ef3ba3aa39033031e3062ed2d22cf2b72ad2aa2a329628b2642242102011f21df1d61c31ba1a219819217b17516a16515c1481331251151060f50ee0e006105f05a05503803703403202802301401301000e004003002001 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x87687486785384082780e8098027fd7df7cc7c87ad79b79377376d76675775274c74173b73272f70b7076ca6ba68a5eb5ba5aa58751245f4494214184134053f83ef3d83c33ba3aa38e38237735a3443303132fb2ed2e72d22cf2c82b72ad2aa2a129428a2642242101df1c31ba1a219819217b17516a16515a14a1351251151060f50ee0e005a05503f03e03c03803703403202f02d02802301401301000e004003002001 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0495.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0495.count (({ width := 9, code := 0x2391b8d46631178b456291389446210f87436190b85426110783416090381405fcfb7d3cde4f174b6580bf5f2f576b95c2dd6cb55a2c95cad55aa54ea5512813e9d4d2652e95492451e8d45a1d0883409fcfc7b3c9e0ea74389c0da6a33184ba582a9489c33188a450271289046220f8783619078381a0c0200c0401 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0495.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (embedding (N := 44310) record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (embedding (N := 44310) record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0495.localPairCheck (embedding (N := 44310) record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group0495
    Papers.RationalityTen.SharedFrameCatalogue.group0495_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0473.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0473.count (({ width := 8, code := 0xc1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09d958b8a898887868584838281807d7c7a787674716f6e6c6a6967656362605e5c58555452504f4c4b4a4746444341403e3c3a393736352a28232221201f1e1d1b1a18160e0d0c0b04030201 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0473.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0473.localPairCheck (embedding (N := 44310) record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0473.localPairCheck (embedding (N := 44310) record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0473.localPairCheck (embedding (N := 44310) record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group0473
    Papers.RationalityTen.SharedFrameCatalogue.group0473_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x87586d86684c8308178067fa7ca7ab76d75774c74170b7076c966d65463d61e61660e6035f75eb5d95c65ba5aa5865124f74e04cb4b64a44a048a48147046d45f44942841f41640c3ff3f43df3ca3bf3ad38f33031d3052ee2e02d12d02c12b82ac2ab29d29028927726c26424522c22421014b1361251151060f50ee0e008107f05a05502802301b01a01801401301000e004003002001 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (embedding record023) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0497.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0497.count (({ width := 9, code := 0x1c3e0f037bbbdcee36fb4d96c35bacd56a34fa0cc6431986c2e13017fbf5eef579bb5a6a94ba45167d379a4c25b2591472311288c42190b8541e0d05813e1d6e471381b6d56a3459ec863b057ebe5dae56eb0562a94c86409f0ec6e35198c048228d8641f0d8542813088401c0c0200c0401 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (embedding (N := 44310) record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (embedding (N := 44310) record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (embedding (N := 44310) record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (embedding record023) hcells Papers.RationalityTen.SharedFrameCatalogue.group0497
    Papers.RationalityTen.SharedFrameCatalogue.group0497_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0475.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0475.count (({ width := 9, code := 0x158ab556a751a7d3a9b4ba4d228d45a1d0a833c9c4d26731984be592b954a24f269246a11027fbf1f0f5793b9d6e772385c0de6eb71b2d86bb55a8d368b297eba5c2d966b057ab154a652a853e9e4da652e9348a3d187035998c25b2b94c9e3c1d8b8581b0c84c2411078381a0c0200c0401 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0475.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (embedding (N := 44310) record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (embedding (N := 44310) record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (embedding (N := 44310) record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (embedding record023) hcells Papers.RationalityTen.SharedFrameCatalogue.group0475
    Papers.RationalityTen.SharedFrameCatalogue.group0475_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x87587386685283681d8108068047fa7ed7d97a979576f76d76876274e74c73d7376c966c65463d60b5fb5ef5d15be5a85615285144cc4b84a34a148c48246f46e45f4494163ff3ca39d39538f37033d32f31d3052ee2d12d02b82ac2ab29d29028927726c26424522c2242101e61ca1bb1b319719318c17616916614412f12611210a1070f20ef0e40e10c30b70ab0a308107f06e06d06906402902802502301b01a01801401301000e } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
def record026_frame002_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0491.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0491.count (({ width := 9, code := 0x1f2f87bfdbebf4fa3cde4f1783b9d9eaf47a1cde5f1b8bc1dfebf4ba2d06733599cb6572587c05fadd68afd7ab355a652e8d459f4e2612792c8e411f8f45e250e80c01f2f077ba5cee470379b8d86b3519ec460af972af562a1429a4ba2d08813e1d8e66f36194c4572993c9642208f4783a1c87c3c1d0e0542813088401c0c } : Fields).get c.val)
theorem record026_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0491.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (embedding (N := 44310) record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (embedding (N := 44310) record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record026_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (embedding (N := 44310) record026) (record026.maps 2)
      (record026.inverseMaps 2) record026_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record026_frame002_links_0000 record026_frame002_links_0064)
theorem record026_frame002_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 2 :=
  of_group record026 2 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0491
    Papers.RationalityTen.SharedFrameCatalogue.group0491_facts record026_frame002_indices record026_frame002_graph record026_frame002_links
def record026_frame003_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0470.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0470.count (({ width := 9, code := 0x12a9449e4b2390c7e3d1c8d4622d1589c3e1d0c8541e0d04813ddeaf4793b9d6ea7439dcae06db65a6d066b3192c761b097ebe5c2d15eab54a9d4ca451a813c9c4ba59248e46a29128742a1106803f9f8f471379b8d6673318cbe5c2d950a04e251249044219007e3a1b8d0622d160a852281386832180b8542813088401c0c } : Fields).get c.val)
theorem record026_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0470.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0470.localPairCheck (embedding (N := 44310) record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0470.localPairCheck (embedding (N := 44310) record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record026_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0470.localPairCheck (embedding (N := 44310) record026) (record026.maps 3)
      (record026.inverseMaps 3) record026_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record026_frame003_links_0000 record026_frame003_links_0064)
theorem record026_frame003_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 3 :=
  of_group record026 3 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group0470
    Papers.RationalityTen.SharedFrameCatalogue.group0470_facts record026_frame003_indices record026_frame003_graph record026_frame003_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (Fin.cases (record026_frame002_supported hcells) (Fin.cases (record026_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x81080e8048027ec7e77a87a377176f76b76575074e74073a65463d60b5fb5ef5d15be5a859658c58655d5245114ca4a549f48047146c45f4494134073f83da3c33ab39d39538f37033d32f2ed2d22cf2b72ad2aa2a629928c27e27226624c2322262132041e51c91bc1b41aa19619418d18317716816715f15114513c1301271111091080f10f00e30e20c40b80ac0a406e06d06906405b05a05705503e03c037032029028025023 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
def record027_frame002_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0xe7f3b99cbe471f6bb4d4ea34da5cbe5b1f8ebcde2e772b8dbadb6ab459ecd64b1d82ab4ca5d1a813f9dcd64d249147637178ac52270d84411f0ef773a5c6e26fb75b6d76ab4d9ccb64b157ab8592c15aaa5228d409e4da55289147a311286421f0f077381bcd26830978b6582311486421f0f4783b160a8502711084401f } : Fields).get c.val)
theorem record027_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record027_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record027) (record027.maps 2)
      (record027.inverseMaps 2) record027_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record027_frame002_links_0000 record027_frame002_links_0064)
theorem record027_frame002_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 2 :=
  of_group record027 2 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record027_frame002_indices record027_frame002_graph record027_frame002_links
def record027_frame003_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0471.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0471.count (({ width := 9, code := 0xcfe773398c8e431388be5eef378b95c6d368a8d42994aa451689409e4ee75379a4c64d219046e2f1689c421105823fdfaf97abd1e6ef75391b0d36933592c86331184bf5eae96ab358aad449d4d2612a9247a39168943209027e3e1e4ee75391b0d46931988bc5d2b1489c4a1f8f8783b1c0dc6c35150a44c251007c3c1d } : Fields).get c.val)
theorem record027_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (embedding (N := 44310) record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (embedding (N := 44310) record027) (record027.maps 3) (record027.inverseMaps 3) record027_frame003_indices (Fin.ofNat record027.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record027_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (embedding (N := 44310) record027) (record027.maps 3)
      (record027.inverseMaps 3) record027_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record027_frame003_links_0000 record027_frame003_links_0064)
theorem record027_frame003_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 3 :=
  of_group record027 3 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group0471
    Papers.RationalityTen.SharedFrameCatalogue.group0471_facts record027_frame003_indices record027_frame003_graph record027_frame003_links
def record027_frame004_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc036006fa17c9b7ddb7ab63596a16d06e7fd3e199dcc8a57329a65131156c6b40594ab19510a3a4ffa7bd3b899147d22fd0667f63f61ee8f447983b71c44c5e60c2fa9648aa850626592ec95045d1e30e2c5fe2c215c0a184dc26412c094449423b11a08b04221fc0fa07843981bf0d8869c34019a0c7062c30817e0bb05ac2d01620ad854c29a14509f04b024a12208804342040ff07603941bc0d703b01d00de06a03081800ba05b01f00f006e03201480a004a023 } : Fields).get c.val)
theorem record027_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record027) (record027.maps 4) (record027.inverseMaps 4) record027_frame004_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record027) (record027.maps 4) (record027.inverseMaps 4) record027_frame004_indices (Fin.ofNat record027.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record027_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record027) (record027.maps 4)
      (record027.inverseMaps 4) record027_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record027_frame004_links_0000 record027_frame004_links_0064)
theorem record027_frame004_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 4 :=
  of_group record027 4 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record027_frame004_indices record027_frame004_graph record027_frame004_links
def record027_frame005_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0xa454828e51ba2343a7e4f99db3b274ce79bd3726a4d28c916218427841021fbbe47b2f51e73b9726e0db134f69ccf199b3064ac6178ae75bcb1d5baa5534a5547a764a491111a0e4167ecf99f13dc79cf01d83a0718d799b322608b91632a652ca293d25a4a89191b222410818ff1f43d0780ea1cc358680ce17c2f0598b21482744b0910d61a8330610b015c2a0520780ec1b8320520a012823 } : Fields).get c.val)
theorem record027_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (embedding (N := 44310) record027) (record027.maps 5) (record027.inverseMaps 5) record027_frame005_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (embedding (N := 44310) record027) (record027.maps 5) (record027.inverseMaps 5) record027_frame005_indices (Fin.ofNat record027.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record027_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (embedding (N := 44310) record027) (record027.maps 5)
      (record027.inverseMaps 5) record027_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record027_frame005_links_0000 record027_frame005_links_0064)
theorem record027_frame005_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 5 :=
  of_group record027 5 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record027_frame005_indices record027_frame005_graph record027_frame005_links
def record027_frame006_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0491.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0491.count (({ width := 9, code := 0xf479fc9e3eff7bb1d7e97479dcce3f1b85c0d1683399acce5b2b92c7e3b1b86bfdf2db60aed529b4aa351679399bcca5f2b93c9647208fc7a1b027fbe1e2ee753a1cce16fb75b2d76ab4590c3602fd74b7572b552a6512653093482311285411ecea74371b4c8632c150a04c1e8f074391a0cc64311409c48220f8783a1c } : Fields).get c.val)
theorem record027_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0491.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (embedding (N := 44310) record027) (record027.maps 6) (record027.inverseMaps 6) record027_frame006_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (embedding (N := 44310) record027) (record027.maps 6) (record027.inverseMaps 6) record027_frame006_indices (Fin.ofNat record027.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record027_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0491.localPairCheck (embedding (N := 44310) record027) (record027.maps 6)
      (record027.inverseMaps 6) record027_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record027_frame006_links_0000 record027_frame006_links_0064)
theorem record027_frame006_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 6 :=
  of_group record027 6 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group0491
    Papers.RationalityTen.SharedFrameCatalogue.group0491_facts record027_frame006_indices record027_frame006_graph record027_frame006_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (Fin.cases (record027_frame002_supported hcells) (Fin.cases (record027_frame003_supported hcells) (Fin.cases (record027_frame004_supported hcells) (Fin.cases (record027_frame005_supported hcells) (Fin.cases (record027_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x87586d86684c83f8308268178067fa7de7ca7c77ab79a79277376d76075775274c74a74166d65463d5eb5ba5aa5865124cb4b64a44a048a48147046d45f44942441b4143ef3ba3aa38f3302ec2d92ce2ba2b62a929d29028927726c26424522c2242101df1c31ba1a219819217b17516a16514b1361251151060f50ee0e00ca0bb0af0a709f08107f05a05503803703403202802301f01e01d01c01b01a01801401301000e004003002001 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x87586f86d86684e84c8398308208178067fa7d07ca7b17ab76d75c75774c74674165463d60c5a85865124c949e47f46b45f4494143ab38f3302ec2ce2b62a929d29028927726c26424522c2242101ec1d01b91a519117e17416414b1361251151060f50ee0e008107f06906405a05505105004f04e03703202802301f01e01d01c01b01a01801401301000e00a009008007004003002001000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (embedding (N := 44310) record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
def record034_frame002_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0497.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0497.count (({ width := 9, code := 0x387c2e0f037dbdde6ef75b9dc6df6bb4d9ecb61aed6eb357aac86330775b4d52873295c82391887c05f0eb6f3499ac560afd7cbb5cadd60ac552993a9b4d25d269147a310c813e1d8dc6a331809045200f46c32180bc5c2d148983e1b0c8602e160a850261108038180a048200e04018080200 } : Fields).get c.val)
theorem record034_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (embedding (N := 44310) record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (embedding (N := 44310) record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record034_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0497.localPairCheck (embedding (N := 44310) record034) (record034.maps 2)
      (record034.inverseMaps 2) record034_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record034_frame002_links_0000 record034_frame002_links_0064)
theorem record034_frame002_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 2 :=
  of_group record034 2 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0497
    Papers.RationalityTen.SharedFrameCatalogue.group0497_facts record034_frame002_indices record034_frame002_graph record034_frame002_links
def record034_frame003_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0475.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0475.count (({ width := 9, code := 0x2b157ab556a953a9546a14fa7536994ba55269147a351689439a4ce5d238d421f4f074b89c2e06db4194bf5a2b550a350a7d3c9b4ca5d269147a310a83411fcf87a3c1d8e06b33184b6572993c783b1b0d45c2c150a450271188836190b8582a1409848220f07034180a048200e04018080200 } : Fields).get c.val)
theorem record034_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0475.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (embedding (N := 44310) record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (embedding (N := 44310) record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record034_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0475.localPairCheck (embedding (N := 44310) record034) (record034.maps 3)
      (record034.inverseMaps 3) record034_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record034_frame003_links_0000 record034_frame003_links_0064)
theorem record034_frame003_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 3 :=
  of_group record034 3 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0475
    Papers.RationalityTen.SharedFrameCatalogue.group0475_facts record034_frame003_indices record034_frame003_graph record034_frame003_links
def record034_frame004_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x2ab5541a97d4329934b1a2ad1068494109fb4ebe5d12d1930493624b0c885a41de09b036666b1dd746a8b51ba47d1968af44d22310d680d3a69938bf04f925292248ec46a22c91088584021f48f4c6fc3401960bb8550289135892c45a20d100079038a1a60c405a029412a08e840412408d03781a80c005b02b81580aa05401b80c805002300f807803a01c00d8068030014009804001c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record034_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record034) (record034.maps 4) (record034.inverseMaps 4) record034_frame004_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record034) (record034.maps 4) (record034.inverseMaps 4) record034_frame004_indices (Fin.ofNat record034.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record034_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record034) (record034.maps 4)
      (record034.inverseMaps 4) record034_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record034_frame004_links_0000 record034_frame004_links_0064)
theorem record034_frame004_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 4 :=
  of_group record034 4 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record034_frame004_indices record034_frame004_graph record034_frame004_links
def record034_frame005_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x35aeabd4fa8b47689cfd9e33866bcc396713e1fbff7e2e55b4b5d692cc59490f1e6253fd7cee69b935b690cf1983165b6a1d35a173d8758e19b83626a8d299a328638bc1672c25489f9342564888e10f2164087b8ed1c8360678c51842ec4207f0ce18c2d8570a61482885006c0c41402303e0780e81c0360680c0140260400700a0120200380400600800800 } : Fields).get c.val)
theorem record034_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record034) (record034.maps 5) (record034.inverseMaps 5) record034_frame005_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record034) (record034.maps 5) (record034.inverseMaps 5) record034_frame005_indices (Fin.ofNat record034.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record034_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record034) (record034.maps 5)
      (record034.inverseMaps 5) record034_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record034_frame005_links_0000 record034_frame005_links_0064)
theorem record034_frame005_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 5 :=
  of_group record034 5 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record034_frame005_indices record034_frame005_graph record034_frame005_links
def record034_frame006_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0492.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0492.count (({ width := 9, code := 0x3c9e1f077bb7daec753a7d0e6f2b7fbddc6db4f9dcd6572790bcde2e96ab3586a949a24fa77359445e27067bbb1cee16f371b2d66a3499aca6430d74b457aa1449c4d24d1a87419f8ec723719ca04f219087a3b1b8d86a341409c421f0d86832180b8582a13090401c0a048200e04018080200 } : Fields).get c.val)
theorem record034_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record034) (record034.maps 6) (record034.inverseMaps 6) record034_frame006_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record034) (record034.maps 6) (record034.inverseMaps 6) record034_frame006_indices (Fin.ofNat record034.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record034_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0492.localPairCheck (embedding (N := 44310) record034) (record034.maps 6)
      (record034.inverseMaps 6) record034_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record034_frame006_links_0000 record034_frame006_links_0064)
theorem record034_frame006_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 6 :=
  of_group record034 6 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0492
    Papers.RationalityTen.SharedFrameCatalogue.group0492_facts record034_frame006_indices record034_frame006_graph record034_frame006_links
def record034_frame007_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0471.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0471.count (({ width := 9, code := 0x36bb3d96c357aad3e9347a0ce65f1d8dc662af577badbed76aa8d429b409d4ca4b1e8cc562710853e5e6e66bb4196c762b0d82be5e2e568b2582a93e9b4ba451a8742a00f476389b4d0653097088431e0ec6e35198c86230130943e1d0c8602e160a85026110803818090401c0c04018080200 } : Fields).get c.val)
theorem record034_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (embedding (N := 44310) record034) (record034.maps 7) (record034.inverseMaps 7) record034_frame007_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (embedding (N := 44310) record034) (record034.maps 7) (record034.inverseMaps 7) record034_frame007_indices (Fin.ofNat record034.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record034_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0471.localPairCheck (embedding (N := 44310) record034) (record034.maps 7)
      (record034.inverseMaps 7) record034_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record034_frame007_links_0000 record034_frame007_links_0064)
theorem record034_frame007_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 7 :=
  of_group record034 7 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0471
    Papers.RationalityTen.SharedFrameCatalogue.group0471_facts record034_frame007_indices record034_frame007_graph record034_frame007_links
def record034_frame008_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33d59c4cdce65720d8fbc32e17304b81cbf2de66cf366fade56ce8133749b64c325872bb65131156cea3a4ee230d0607e93db9e54edc711319941895038f17e0ad4506261129893048a23811888ac41c1f90f987703821b30d3065c31417b0ba859c2b014a09e84b824211208603f812408d03781a80c005b02b81580aa05401b80c805002300f807803a01c00d8068030014009804001c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record034_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 8) (record034.inverseMaps 8) record034_frame008_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 8) (record034.inverseMaps 8) record034_frame008_indices (Fin.ofNat record034.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record034_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record034) (record034.maps 8)
      (record034.inverseMaps 8) record034_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record034_frame008_links_0000 record034_frame008_links_0064)
theorem record034_frame008_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 8 :=
  of_group record034 8 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record034_frame008_indices record034_frame008_graph record034_frame008_links
def record034_frame009_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x98f98b98998698298097697597297197096b95295093c93992491c91b91190a9077f87dd7756c968a5c656e54c5345255154fa4903cc3872db28b26925124223a23322c21f2192131f91e51df1c81af1a019018017116115b14c13d12e11e10e0ff0ef0e90da09208d06f06a06005b05705605505403703202802301f01e01d01c01b01a01801401301000e00a009008007004003002001000 } : Fields).get c.val)
theorem record034_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record034) (record034.maps 9) (record034.inverseMaps 9) record034_frame009_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record034) (record034.maps 9) (record034.inverseMaps 9) record034_frame009_indices (Fin.ofNat record034.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record034_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (embedding (N := 44310) record034) (record034.maps 9)
      (record034.inverseMaps 9) record034_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record034_frame009_links_0000 record034_frame009_links_0064)
theorem record034_frame009_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 9 :=
  of_group record034 9 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record034_frame009_indices record034_frame009_graph record034_frame009_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (Fin.cases (record034_frame002_supported hcells) (Fin.cases (record034_frame003_supported hcells) (Fin.cases (record034_frame004_supported hcells) (Fin.cases (record034_frame005_supported hcells) (Fin.cases (record034_frame006_supported hcells) (Fin.cases (record034_frame007_supported hcells) (Fin.cases (record034_frame008_supported hcells) (Fin.cases (record034_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
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
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x82ebfb1f70f477613a1dcb6e437043771b8ad756af3571a76d36698b4999bcccf646ac2d604afc4f824b92148ef46ca2e512c87241ba088f067773b71c7ce267093571a74d106803359984c7863231097f8b5a5922bb1594a8453629414409e44d3252925c71c36e1b18ce065831a1718b0857028113786e432e1860bb054827c12e08e83c81ca0d605182840e004201c009004602200a002c0140090040010006002 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (embedding record039) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11ad8bcc56a24d0d585fc095faef807993b2dd28e897263855c14dc66bb357dabad3b69b34c5a4ccea67233816ccafc54829e54c0a4251228452588fb47523510e485341ba088f0e77b3b79d90e3270d3839bc0c226052fe96b8b3c58f2c115ccace53e29d94b49f84de26992b094a49720c8e887043641a20cb86382f11680ae052228113786e432a1860bb055c27812c08d840c1e40e506b02740b805b02d00fc07c03c01c00a40140090040010006002 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x812bff9faef807acbcc9d24e5a709b76da5cd2367533919c0bf05dd2e915f8a61520a89942695e49da4b91f48ef46ca1c906e8223f51f50f7c7873bd9dbcec87073791ac0d206733311964c926343119844c0a5fd2d71678b1e5822b9959ca7c53b296934c94a497234116489443321210646102f11680ae052628113787803861b90c305d81e40e506b02bc15c09d03080f807802900a00280120080028010006002 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (embedding record041) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x98c4c0a4c124d87cc38609f0388013fd1d86eba757380dbf4dee68fb445a14cf867ab3b98deba35832b8556ca7e53628dd3349754a524492008cc45fa2dd16089d44b223d05a8184021f88eda75d3a69b34d7a6a934d1a1ccf064431f98b8c306082fc15e0ad05542a294c8a464ef27513649744ad253125892248a23f91e48e646d21610105742a814489ac49223c116875c38a1a60c405982b214a07883a41c40db058827407002900d00600140090040010006002 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
def record043_frame002_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x811c061efcf7374a3a25c2ae0a6da36b5a72d3469833a99c8ce060a2fe97e0bc15dd2e916ceafb547a9e14c2a26509a7bd2e695049723bd1b2872429a0dd0447ea3ea1ef8f0e77b3b79d90e3a7113841ab4d3868a33f99b4cc463931a188cc226052fe96b8b3c58f2c115ccace53e29d94b49f84de26992b094a49723e11a08b244a20c100860e2f31690ae052228113787f83da1d00dc865430c17608183c81ca0d6055827407002900d00600140090040010006002 } : Fields).get c.val)
theorem record043_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record043_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record043) (record043.maps 2)
      (record043.inverseMaps 2) record043_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record043_frame002_links_0000 record043_frame002_links_0064)
theorem record043_frame002_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 2 :=
  of_group record043 2 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record043_frame002_indices record043_frame002_graph record043_frame002_links
def record043_frame003_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x9d29c99809799028f98b88af89188a8378328307f57f07eb7817767727627607597336e869a68467364f64262d5e05cf5b859358955b54f54754052d52651f4f94f04e74da49e49448f44b43d43242641b4113ec3ea3de3d13ca3c237e37136635c35134431f31c3122f92eb2e62d72d22cb2c02ba2b42ae28e27e1cc1c21b41a819418f18614c14213412811410d1070ca0c30c00bd0a509b03802901a01800a009008004003002 } : Fields).get c.val)
theorem record043_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record043) (record043.maps 3) (record043.inverseMaps 3) record043_frame003_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record043) (record043.maps 3) (record043.inverseMaps 3) record043_frame003_indices (Fin.ofNat record043.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record043_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record043) (record043.maps 3)
      (record043.inverseMaps 3) record043_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record043_frame003_links_0000 record043_frame003_links_0064)
theorem record043_frame003_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 3 :=
  of_group record043 3 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record043_frame003_indices record043_frame003_graph record043_frame003_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (Fin.cases (record043_frame002_supported hcells) (Fin.cases (record043_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11b28cbc57e28910987d439e09aff87f43ea1ea6f4375cbabdd28e8971d38c1c2ae0a5b32981484a24508a4b52168ed46ba1c508683440f9df4ee276c3ad1c74e2270834419accc263c3191884c226052fe9634ae25662a014e4a564f926d934894449420c8e606f036219d0ca462e2b81488a044de24b11a088841c1b90ca86182ec1530a004c023e0fe049815c0ac055024812008c04201c00a404001f00f007401e00e0068028012008002000c004000 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (embedding record045) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x46b634b15a8a94356192ec9734b929bd4d2e69033817e0bd35dd2e916cca62521a8a142a92c48023a91a876f38c9c34e0e6f034819cccc465931a188cc226052fe9678b0456729d94b49f84de26992b094a497234116489443321210647443821b20cb86382e61628ae451e28413908f845821a0f0070c3721860bb04f025811b05782b80c205c02d816807e03e01e00e00520140028010006002 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
def record047_frame002_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x5c0edbf685b32d6ceb4120e8b744ee144efe77438a992cc7162cb11178aa3150627d13be9614a9253128a8603dd1e9cf2c77436e9ae4d3868632e191cc6261d30515a8a8c51e273935c93a47a23510f886a4251fd0fa07b03c21d70e6c5f62d715789e04d022e10587ec39e1c60db062c2f21690a404e826611e08b84041f40f305b82d40c205c02d816807e03e01e00e00520140028010006002 } : Fields).get c.val)
theorem record047_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record047_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record047) (record047.maps 2)
      (record047.inverseMaps 2) record047_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record047_frame002_links_0000 record047_frame002_links_0064)
theorem record047_frame002_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 2 :=
  of_group record047 2 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record047_frame002_indices record047_frame002_graph record047_frame002_links
def record047_frame003_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x9259209089038e08da8057dd7d47ac74173971168367466765a6395ab59c58e58051e51150a50147f45144d44a43e3fd3ea3de3d53bf3b23a439d39834e33d32d3123092ea2dc2d52ba2b52ac28c28327726726025a2101ff1ef1d41c91ac19e19717c17616c14e14213911b10e1090f70f10dc0d50cf09e09d05f05a05905803f03e03c038029014005004003002 } : Fields).get c.val)
theorem record047_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record047_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record047) (record047.maps 3)
      (record047.inverseMaps 3) record047_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record047_frame003_links_0000 record047_frame003_links_0064)
theorem record047_frame003_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 3 :=
  of_group record047 3 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record047_frame003_indices record047_frame003_graph record047_frame003_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (Fin.cases (record047_frame002_supported hcells) (Fin.cases (record047_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11ad8c6456a27310c864c069fdcfdb7babd25e6ceca743b92dc10dd76d334e1a66d2f66fb235846c095f82ee9748a84536a98945ca2850aa7c12588fe4752350e3270d3839bc0d1466d33118e4c686232fe17acace54d29d94b4a064e5269931c94a497234116489443321210647203701b20cd465c31c1730b1457228f14209c84a423e11608683fe1eb0e706e432e1860bb055427812c08d82ac0f405c02d816807e03e01e00e005e02d00a0010006002 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (embedding record056) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
def record059_frame001_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x46a22d715588c43be1910af80c3fb5fb4f737a43cd5da8eca7513a1dcaae4b711b8217dabc45d8ae6d6e2b695b2aa114daa6251728a142a9ef49623f91d48d4439a1490728243fe1f5cf827a938e9c44e1068a3369988c7263431197f4ace54d29d94b49a44ae25112508f045b22610ec85e42020c10007203701b20cd465c31c1730b1457228f14209c84a423e11608683da1d00dc865c30c1760aa84f025811b08103c01c60d406602ac11c08d04601e80b805b02d00e003e01e00e806c03401800a0010006002 } : Fields).get c.val)
theorem record059_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record059_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record059) (record059.maps 1)
      (record059.inverseMaps 1) record059_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record059_frame001_links_0000 record059_frame001_links_0064)
theorem record059_frame001_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) : Supported record059 1 :=
  of_group record059 1 (embedding record059) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record059_frame001_indices record059_frame001_graph record059_frame001_links
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (Fin.cases (record059_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x46a22ed16b8aac48e2310ee85ec2be0470187fdbfa9efcf737ab3d15da0ec27493a1dca2e43709b8217dabb15cdabed4c2a41513284d3de92e48523bd1b287141a207cfb07c23d51e00ee876d3841980c7c62f30f17f4aca54229b14a09a44a224a10bc8404182000e386dc36319c0cb06342f31690ae0526281137892846422010607b43a01b90cb86182ec15209f04b823a0c6047023411805702b015408403301900c4048023011007c03c01d00e006c03401800a0028012008002000c004000 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
def record062_frame002_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x55f6a8352fa865326963478a2ad10663130297dcb924c124d920c89e28512e87bc37e137082826c0d9a12cf4676ae8d56ca9253f29b146e94a49324492008cb45b22bd12e890444a08901a7fd3a699c8c9263931417e0a3a4f4272134c94a490244916488442c2010d6865e31c1758b745942a814489ac49623c116883c3f81ee0f0071434c1880b4056429412c08c842c1fa0d3047023411805702b015408403301900c4048023011007c03c01d00e006c03401800a0028012008002000c004000 } : Fields).get c.val)
theorem record062_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record062) (record062.maps 2) (record062.inverseMaps 2) record062_frame002_indices (Fin.ofNat record062.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record062_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record062) (record062.maps 2)
      (record062.inverseMaps 2) record062_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record062_frame002_links_0000 record062_frame002_links_0064)
theorem record062_frame002_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 2 :=
  of_group record062 2 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record062_frame002_indices record062_frame002_graph record062_frame002_links
def record062_frame003_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xab6a9ba92a88a72a66a4ea3ca2f9d29c99bf9b998097997296791e91a9008f88de8cf8b78ad77075e7576e867365c64f64262d5b85a159358955954653f5275205194f34ea4e548f40f3ef3e63db3c234232231930e2e42d12ca2a029528e27c22620e2051e51e01d61c21b41a819618f18617116615d15414213412811610d1070f10e40df0d40b608c08b08a05705605504203303203102402302201f01e01d01c01b01a01801400a009008004003002000 } : Fields).get c.val)
theorem record062_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record062) (record062.maps 3) (record062.inverseMaps 3) record062_frame003_indices (Fin.ofNat record062.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record062_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record062) (record062.maps 3)
      (record062.inverseMaps 3) record062_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record062_frame003_links_0000 record062_frame003_links_0064)
theorem record062_frame003_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 3 :=
  of_group record062 3 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record062_frame003_indices record062_frame003_graph record062_frame003_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (Fin.cases (record062_frame002_supported hcells) (Fin.cases (record062_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record065_frame001_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd0be7ab3899b9ccae41b1f7865c2e6097039799b5c5abacf366fafc56f2b673ba9d8cdd26d93529a24cae6252c395db32988ab6751aa8413b88be44d20c0ff67e93db9c44c6650126e12a071436617e0b1c56a283129893048a23810707e43e61d00e086cc34c1970c886282f61750ac052827a12e094048422410c04682300f406a034816c0b405702b01540a804201900c404602200f807803a01c00d8068030014008003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record065_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record065_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record065) (record065.maps 1)
      (record065.inverseMaps 1) record065_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record065_frame001_links_0000 record065_frame001_links_0064)
theorem record065_frame001_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) : Supported record065 1 :=
  of_group record065 1 (embedding record065) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record065_frame001_indices record065_frame001_graph record065_frame001_links
def record065_frame002_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xabed56aa8352fa865326963455a20d0928213af98c4c0a5d12d193bc98249b0f786fc3221690ac84dc24e10504d81b33b58eeba3543299946e91a47d232d16c8af44d2034e9a64931417e09e84d3252924091247622c91088584021bf0d006582c71540a244d624b11e08b441a2000e286983101680ac852825411d04682300f406a034816c0b405702b01540a804201900c404602200f807803a01c00d8068030014008003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record065_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record065) (record065.maps 2) (record065.inverseMaps 2) record065_frame002_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record065) (record065.maps 2) (record065.inverseMaps 2) record065_frame002_indices (Fin.ofNat record065.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record065_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record065) (record065.maps 2)
      (record065.inverseMaps 2) record065_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record065_frame002_links_0000 record065_frame002_links_0064)
theorem record065_frame002_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) : Supported record065 2 :=
  of_group record065 2 (embedding record065) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record065_frame002_indices record065_frame002_graph record065_frame002_links
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (Fin.cases (record065_frame001_supported hcells) (Fin.cases (record065_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record068_frame001_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a17cf3671332b934c83627b0cb81ac08dbf6d716aeafc56f2b6741da05cffe7c53c59dd4ca6621304974cb3a586d2b672333586ab67531289d4269ff4f7a7711ce8c0456a26906080c3fd9fa4f6a7a53c99c04c6652e279937c9964bb2540ecc7183791b30bf05b02c715a8a044e225f129893048a23810387e43d81dd0eb87403821b30d3065c32218a0b985b02ca15f0ac054829414409e84a024211307803540c205c02d81680ae05602a80a4048023011007c03c01d00d8068030014007803801a00a004802000a0040018008002000 } : Fields).get c.val)
theorem record068_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record068_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record068) (record068.maps 1) (record068.inverseMaps 1) record068_frame001_indices (Fin.ofNat record068.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record068_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record068) (record068.maps 1)
      (record068.inverseMaps 1) record068_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record068_frame001_links_0000 (interval_append _ 64 128 129 record068_frame001_links_0064 record068_frame001_links_0128))
theorem record068_frame001_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) : Supported record068 1 :=
  of_group record068 1 (embedding record068) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record068_frame001_indices record068_frame001_graph record068_frame001_links
def record068_frame002_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x11a88cac5da2ab142891c38e17b07e83b412e0470187d33df9ee6ec9760bae1d5aea17493929c84e397173889c26bee5da2e796caafb5302891422a004faa7bd25890047523510e284841a207cfb87c63d79db4e106613191884c226052fe9594a8853629413489604a224a117c8a044021790808304001cd0de86c433c1948c5c5e62d215c0a4c50226f11a088841c1fc0f687803a01c30dc86182ec15108083240c205c02d81680ae05602a80a4048023011007c03c01d00d8068030014007803801a00a004802000a0040018008002000 } : Fields).get c.val)
theorem record068_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record068_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record068) (record068.maps 2) (record068.inverseMaps 2) record068_frame002_indices (Fin.ofNat record068.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record068_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record068) (record068.maps 2)
      (record068.inverseMaps 2) record068_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record068_frame002_links_0000 (interval_append _ 64 128 129 record068_frame002_links_0064 record068_frame002_links_0128))
theorem record068_frame002_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) : Supported record068 2 :=
  of_group record068 2 (embedding record068) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record068_frame002_indices record068_frame002_graph record068_frame002_links
def record068_frame003_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1576aacd4eaa114e7a6151f68a341da034c6e5bf2c6928c8423f510b878c3761ad0bc854417608d02d811402dfe4c96640b1e97fcb5c55caa9153aa8d53aa97d2a692c48da429140879434215d07a8364179eb8e0865a32298fcc6862130694d4a2e50a27e12a091447d237916c8ac45122010ac82a3ec1af0cf863e2fd1770b7457a29d13f097049a23c111887042a2050f887803961b70d105a82ae13c07f83480c205c02d81680ae05602a80a4048023011007c03c01d00d8068030014007803801a00a004802000a0040018008002000 } : Fields).get c.val)
theorem record068_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record068) (record068.maps 3) (record068.inverseMaps 3) record068_frame003_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record068) (record068.maps 3) (record068.inverseMaps 3) record068_frame003_indices (Fin.ofNat record068.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record068_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record068) (record068.maps 3) (record068.inverseMaps 3) record068_frame003_indices (Fin.ofNat record068.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record068_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record068) (record068.maps 3)
      (record068.inverseMaps 3) record068_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record068_frame003_links_0000 (interval_append _ 64 128 129 record068_frame003_links_0064 record068_frame003_links_0128))
theorem record068_frame003_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) : Supported record068 3 :=
  of_group record068 3 (embedding record068) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record068_frame003_indices record068_frame003_graph record068_frame003_links
def record068_frame004_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8d98c78bc8af8aa89987d86e86185b8308288258097f37f07b27a77a17a079d79778478177b77376876267265f65b63a6045c05ad5a85a259c5975295105095004d14b84b24a949348f48b4564073af39d39939338a3833183012fd2f62c92b22ad2a729629329028827f2792692242142091ee1e81e01cb1bf1b219719018a17417016c16115814f14613d13711610b0f70cd0ae05f05a05905805505405302902402302201f01e01d01b01a01801400f00e00d00a009008005004003002001000 } : Fields).get c.val)
theorem record068_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record068) (record068.maps 4) (record068.inverseMaps 4) record068_frame004_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record068) (record068.maps 4) (record068.inverseMaps 4) record068_frame004_indices (Fin.ofNat record068.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record068_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record068) (record068.maps 4) (record068.inverseMaps 4) record068_frame004_indices (Fin.ofNat record068.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record068_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record068) (record068.maps 4)
      (record068.inverseMaps 4) record068_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record068_frame004_links_0000 (interval_append _ 64 128 129 record068_frame004_links_0064 record068_frame004_links_0128))
theorem record068_frame004_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) : Supported record068 4 :=
  of_group record068 4 (embedding record068) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record068_frame004_indices record068_frame004_graph record068_frame004_links
def record068_frame005_indices (c : Fin record068.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0994.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0994.count (({ width := 11, code := 0x586b09606be579aef5cab856bad1586aed5caa353ea7535a674c29752da5548a9051da374628aca792f24a39c43804fb5f33e37c0f71ce38c710e01b235369cd1d99b2d652c216c2985049f93ca764e48c5102194267dcf39e03ba71ce11bf36e6c8d81a93085e4b89612b6558a413e2684909011821240c7f8fc1f23d0778ea1cc368698c715e2702c0530a41442704d0980a41202304407c0f01d0360680c01401e0380680a0120200280400600800800 } : Fields).get c.val)
theorem record068_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.graphBitCheck record068.data.requiredEdges q = true := by decide +kernel
theorem record068_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (embedding (N := 44310) record068) (record068.maps 5) (record068.inverseMaps 5) record068_frame005_indices (Fin.ofNat record068.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record068_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (embedding (N := 44310) record068) (record068.maps 5) (record068.inverseMaps 5) record068_frame005_indices (Fin.ofNat record068.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record068_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (embedding (N := 44310) record068) (record068.maps 5) (record068.inverseMaps 5) record068_frame005_indices (Fin.ofNat record068.n i)) 128 129 :=
  interval_of_check _ 128 1 (by decide +kernel)
theorem record068_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0994.localPairCheck (embedding (N := 44310) record068) (record068.maps 5)
      (record068.inverseMaps 5) record068_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 129 record068_frame005_links_0000 (interval_append _ 64 128 129 record068_frame005_links_0064 record068_frame005_links_0128))
theorem record068_frame005_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) : Supported record068 5 :=
  of_group record068 5 (embedding record068) hcells Papers.RationalityTen.SharedFrameCatalogue.group0994
    Papers.RationalityTen.SharedFrameCatalogue.group0994_facts record068_frame005_indices record068_frame005_graph record068_frame005_links
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (Fin.cases (record068_frame001_supported hcells) (Fin.cases (record068_frame002_supported hcells) (Fin.cases (record068_frame003_supported hcells) (Fin.cases (record068_frame004_supported hcells) (Fin.cases (record068_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
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
def record070_frame001_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd0be71332b934c83627b0cb81ac08de66d716aeb3cd9bebf15bcad9cf8a78b3ba994cc426092e99674b0d994b6750827fd3de9dc460226906080c3fd9fa4f6e63326e132c9764a81c60d985f82d81638ad450625312609144701f90ee87403821b30d3065c32218a0ba857c2b01520a5051027a128090844c2180f004682300d4069030816c0b405702b01540a803201880a404602200f807803a01c00d80680300140070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record070_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record070_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record070) (record070.maps 1)
      (record070.inverseMaps 1) record070_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record070_frame001_links_0000 record070_frame001_links_0064)
theorem record070_frame001_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) : Supported record070 1 :=
  of_group record070 1 (embedding record070) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record070_frame001_indices record070_frame001_graph record070_frame001_links
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (Fin.cases (record070_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record088_frame001_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd09e79b379991c9a642b0c785ac11e06aedf760b5859c6ccf5beaba55827d93cf9d9ce8671136e9774b4e58b2a0940c9ce3351828aac4fa23cce666631f986aba05c628894249ef457a26101a7f83f41f20f687a63ca9d28e0266c32c13b89bc4bb1bd8d905b22c415a0a50500272130894c498245118888c42c2070fc87b03aa1ce0e407043761980c485f02da1670af852828812f093844c2160fe07403880de06b02f816c0b005502a00dc066027011808003a01c00d8068030013009003c01c00b005002000e0050018008002000 } : Fields).get c.val)
theorem record088_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record088) (record088.maps 1) (record088.inverseMaps 1) record088_frame001_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record088) (record088.maps 1) (record088.inverseMaps 1) record088_frame001_indices (Fin.ofNat record088.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record088_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record088) (record088.maps 1)
      (record088.inverseMaps 1) record088_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record088_frame001_links_0000 record088_frame001_links_0064)
theorem record088_frame001_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) : Supported record088 1 :=
  of_group record088 1 (embedding record088) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record088_frame001_indices record088_frame001_graph record088_frame001_links
def record088_frame002_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xab4aa8a94a86a7aa74a39a2ca22a19a03a009ce9b59ae98596e95e90d90a8fb8f68f18e68c28bf8ba8ab8a689f87487286e86c86675f7587437316f96f064964063159158354d54553e53152952251c5024e54a649e3e43dc3ca31a30c2d82d02c92bd2b62b02ab2a029528e27125a2472312192041dd1d31ca1c21bc19718517015f15814a13412e11710c0f00e60d80c40c106f06b05f05b05805505403703302702302001d01c01b01a01801301200f00e00b00a008007005003002001000 } : Fields).get c.val)
theorem record088_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record088) (record088.maps 2) (record088.inverseMaps 2) record088_frame002_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record088) (record088.maps 2) (record088.inverseMaps 2) record088_frame002_indices (Fin.ofNat record088.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record088_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record088) (record088.maps 2)
      (record088.inverseMaps 2) record088_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record088_frame002_links_0000 record088_frame002_links_0064)
theorem record088_frame002_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) : Supported record088 2 :=
  of_group record088 2 (embedding record088) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record088_frame002_indices record088_frame002_graph record088_frame002_links
def record088_frame003_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xa1850667df3c79d0cdca63730a9694b0646921c8e5c5f22c9132876c31e04900f7f03f59f82f927ba3d81e9ef3178ebc31daaec5750ba45cdac0e6032f39730b635a9a8ed46aa0e47f23d90a283e4182044ffc7f03f39e88eac71738517e0be65d327793a48d045a22810e485642120d10247e83e01d68e346de34d1968c3c5ec2f01708b3457225b11e88844061fa0f606d83481770b5851827412607c03a40de06b02f816c0b005502a00dc066027011808003a01c00d8068030013009003c01c00b005002000e0050018008002000 } : Fields).get c.val)
theorem record088_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record088) (record088.maps 3) (record088.inverseMaps 3) record088_frame003_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record088) (record088.maps 3) (record088.inverseMaps 3) record088_frame003_indices (Fin.ofNat record088.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record088_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record088) (record088.maps 3)
      (record088.inverseMaps 3) record088_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record088_frame003_links_0000 record088_frame003_links_0064)
theorem record088_frame003_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) : Supported record088 3 :=
  of_group record088 3 (embedding record088) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record088_frame003_indices record088_frame003_graph record088_frame003_links
def record088_frame004_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0xd73ad3546a1d2ba3f3ee77cdf9ab2964fc6788b0d602bdb79ee35c0b7b6f2dc5b0b4567acd591b17626b7d6cacb58aae49792120e3b4568a0fe1fa3ea72ce39b33616b4d35a3341678c9587aed5cea053f27242482cf09db3aa724e09bd3706c4d51a532861cbe9722ce56ca69482864fc9d923236440829021f83b4748d91a6318608bb15c2a8338640b415c2a0510a00d8190270460800e81c0360680c01302403c0700b0140200380500600800800 } : Fields).get c.val)
theorem record088_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record088) (record088.maps 4) (record088.inverseMaps 4) record088_frame004_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record088) (record088.maps 4) (record088.inverseMaps 4) record088_frame004_indices (Fin.ofNat record088.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record088_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (embedding (N := 44310) record088) (record088.maps 4)
      (record088.inverseMaps 4) record088_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record088_frame004_links_0000 record088_frame004_links_0064)
theorem record088_frame004_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) : Supported record088 4 :=
  of_group record088 4 (embedding record088) hcells Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record088_frame004_indices record088_frame004_graph record088_frame004_links
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (Fin.cases (record088_frame001_supported hcells) (Fin.cases (record088_frame002_supported hcells) (Fin.cases (record088_frame003_supported hcells) (Fin.cases (record088_frame004_supported hcells) (fun j => Fin.elim0 j))))))
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
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00014
