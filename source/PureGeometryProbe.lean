module
public import GraphInputsRow29Part00094Data
public meta import GeometricRecordFiles

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace PureGeometryProbe
open Papers.RationalityTen.PackedGraphCertificate
def raw000 : RawData := smallFacetRecord% 0
def raw001 : RawData := smallFacetRecord% 1
def raw002 : RawData := smallFacetRecord% 2
def raw003 : RawData := smallFacetRecord% 3
def raw004 : RawData := smallFacetRecord% 4
def raw005 : RawData := smallFacetRecord% 5
def raw006 : RawData := smallFacetRecord% 6
def raw007 : RawData := smallFacetRecord% 7
def raw008 : RawData := smallFacetRecord% 8
def raw009 : RawData := smallFacetRecord% 9
def raw010 : RawData := smallFacetRecord% 10
def raw011 : RawData := smallFacetRecord% 11
def raw012 : RawData := smallFacetRecord% 12
def raw013 : RawData := smallFacetRecord% 13
def raw014 : RawData := smallFacetRecord% 14
def raw015 : RawData := smallFacetRecord% 15
def raw016 : RawData := smallFacetRecord% 16
def raw017 : RawData := smallFacetRecord% 17
def originals : List RawData := [raw000, raw001, raw002, raw003, raw004, raw005, raw006, raw007, raw008, raw009, raw010, raw011, raw012, raw013, raw014, raw015, raw016, raw017]
def decoded : List RawData := [Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record001, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record002, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record004, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record005, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record006, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record007, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record008, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record009, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record010, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record011, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record012, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record013, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record014, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record015, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record016, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record017]

private theorem consEqual {a b : RawData} {c d : List RawData} (h : a = b) (s : c = d) :
    a :: c = b :: d := by cases h; cases s; rfl
private theorem eq000 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000 = raw000 := by rfl
private theorem eq001 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record001 = raw001 := by rfl
private theorem eq002 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record002 = raw002 := by rfl
private theorem eq003 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003 = raw003 := by rfl
private theorem eq004 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record004 = raw004 := by rfl
private theorem eq005 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record005 = raw005 := by rfl
private theorem eq006 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record006 = raw006 := by rfl
private theorem eq007 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record007 = raw007 := by rfl
private theorem eq008 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record008 = raw008 := by rfl
private theorem eq009 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record009 = raw009 := by rfl
private theorem eq010 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record010 = raw010 := by rfl
private theorem eq011 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record011 = raw011 := by rfl
private theorem eq012 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record012 = raw012 := by rfl
private theorem eq013 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record013 = raw013 := by rfl
private theorem eq014 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record014 = raw014 := by rfl
private theorem eq015 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record015 = raw015 := by rfl
private theorem eq016 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record016 = raw016 := by rfl
private theorem eq017 : Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record017 = raw017 := by rfl
theorem exactRecords : decoded = originals := (consEqual eq000 (consEqual eq001 (consEqual eq002 (consEqual eq003 (consEqual eq004 (consEqual eq005 (consEqual eq006 (consEqual eq007 (consEqual eq008 (consEqual eq009 (consEqual eq010 (consEqual eq011 (consEqual eq012 (consEqual eq013 (consEqual eq014 (consEqual eq015 (consEqual eq016 (consEqual eq017 rfl))))))))))))))))))
theorem rawPayload (p : List RawData → Prop) (h : p originals) : p originals := h
theorem purePayload (p : List RawData → Prop) (h : p decoded) : p decoded := h
end PureGeometryProbe
