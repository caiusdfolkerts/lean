module
prelude
public import Papers.RawWitnesses.TypeD4Data
public import Papers.RawWitnesses.TypeD4Coverage00
public import Papers.RawWitnesses.TypeD4Coverage01
public import Papers.RawWitnesses.TypeD4Coverage02
public import Papers.RawWitnesses.TypeD4Coverage03
public import Papers.RawWitnesses.TypeD4Coverage04
public import Papers.RawWitnesses.TypeD4Coverage05
public import Papers.RawWitnesses.TypeD4Coverage06
public import Papers.RawWitnesses.TypeD4Coverage07
public import Papers.RawWitnesses.TypeD4Coverage08
public import Papers.RawWitnesses.TypeD4Coverage09
public import Papers.RawWitnesses.TypeD4Coverage10
public import Papers.RawWitnesses.TypeD4Coverage11
public import Papers.RawWitnesses.TypeD4Coverage12
public import Papers.RawWitnesses.TypeD4Coverage13
public import Papers.RawWitnesses.TypeD4Coverage14
public import Papers.RawWitnesses.TypeD4Coverage15
public import Papers.RawWitnesses.TypeD4Coverage16
public import Papers.RawWitnesses.TypeD4Coverage17
public import Papers.RawWitnesses.TypeD4Coverage18
public import Papers.RawWitnesses.TypeD4Coverage19
public import Papers.RawWitnesses.TypeD4Coverage20
public import Papers.RawWitnesses.TypeD4Coverage21
public import Papers.RawWitnesses.TypeD4Coverage22
public import Papers.RawWitnesses.TypeD4Coverage23
public import Papers.RawWitnesses.TypeD4Coverage24
public import Papers.RawWitnesses.TypeD4Coverage25
public import Papers.RawWitnesses.TypeD4Coverage26
public import Papers.RawWitnesses.TypeD4Coverage27
public import Papers.RawWitnesses.TypeD4Coverage28
public import Papers.RawWitnesses.TypeD4Coverage29
public import Papers.RawWitnesses.TypeD4Coverage30
public import Papers.RawWitnesses.TypeD4Coverage31

/-! Small ordinary kernel checks for Appendix B type D4. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeD4
open Papers.RationalWitnesses.Raw

theorem coverage_check : Coverage certificate :=
  (forallMask_succ (n := 9) (fun tail => Covered certificate tail)
    (forallMask_succ (n := 8) (fun tail => Covered certificate (Fin.cases false tail))
    (forallMask_succ (n := 7) (fun tail => Covered certificate (Fin.cases false (Fin.cases false tail)))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail)))))
    coverage_chunk_00
    coverage_chunk_01)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail)))))
    coverage_chunk_02
    coverage_chunk_03))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail)))))
    coverage_chunk_04
    coverage_chunk_05)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail)))))
    coverage_chunk_06
    coverage_chunk_07)))
    (forallMask_succ (n := 7) (fun tail => Covered certificate (Fin.cases false (Fin.cases true tail)))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail)))))
    coverage_chunk_08
    coverage_chunk_09)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail)))))
    coverage_chunk_10
    coverage_chunk_11))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases true tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail)))))
    coverage_chunk_12
    coverage_chunk_13)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail)))))
    coverage_chunk_14
    coverage_chunk_15))))
    (forallMask_succ (n := 8) (fun tail => Covered certificate (Fin.cases true tail))
    (forallMask_succ (n := 7) (fun tail => Covered certificate (Fin.cases true (Fin.cases false tail)))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases false tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail)))))
    coverage_chunk_16
    coverage_chunk_17)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail)))))
    coverage_chunk_18
    coverage_chunk_19))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases true tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail)))))
    coverage_chunk_20
    coverage_chunk_21)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail)))))
    coverage_chunk_22
    coverage_chunk_23)))
    (forallMask_succ (n := 7) (fun tail => Covered certificate (Fin.cases true (Fin.cases true tail)))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail)))))
    coverage_chunk_24
    coverage_chunk_25)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail)))))
    coverage_chunk_26
    coverage_chunk_27))
    (forallMask_succ (n := 6) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true tail))))
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail)))))
    coverage_chunk_28
    coverage_chunk_29)
    (forallMask_succ (n := 5) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail)))))
    coverage_chunk_30
    coverage_chunk_31)))))

end Papers.RationalWitnesses.RawWitnesses.TypeD4
