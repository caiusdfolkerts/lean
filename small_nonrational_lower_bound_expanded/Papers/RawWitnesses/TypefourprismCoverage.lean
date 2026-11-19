module
prelude
public import Papers.RawWitnesses.TypefourprismData
public import Papers.RawWitnesses.TypefourprismCoverage00
public import Papers.RawWitnesses.TypefourprismCoverage01
public import Papers.RawWitnesses.TypefourprismCoverage02
public import Papers.RawWitnesses.TypefourprismCoverage03
public import Papers.RawWitnesses.TypefourprismCoverage04
public import Papers.RawWitnesses.TypefourprismCoverage05
public import Papers.RawWitnesses.TypefourprismCoverage06
public import Papers.RawWitnesses.TypefourprismCoverage07
public import Papers.RawWitnesses.TypefourprismCoverage08
public import Papers.RawWitnesses.TypefourprismCoverage09
public import Papers.RawWitnesses.TypefourprismCoverage10
public import Papers.RawWitnesses.TypefourprismCoverage11
public import Papers.RawWitnesses.TypefourprismCoverage12
public import Papers.RawWitnesses.TypefourprismCoverage13
public import Papers.RawWitnesses.TypefourprismCoverage14
public import Papers.RawWitnesses.TypefourprismCoverage15
public import Papers.RawWitnesses.TypefourprismCoverage16
public import Papers.RawWitnesses.TypefourprismCoverage17
public import Papers.RawWitnesses.TypefourprismCoverage18
public import Papers.RawWitnesses.TypefourprismCoverage19
public import Papers.RawWitnesses.TypefourprismCoverage20
public import Papers.RawWitnesses.TypefourprismCoverage21
public import Papers.RawWitnesses.TypefourprismCoverage22
public import Papers.RawWitnesses.TypefourprismCoverage23
public import Papers.RawWitnesses.TypefourprismCoverage24
public import Papers.RawWitnesses.TypefourprismCoverage25
public import Papers.RawWitnesses.TypefourprismCoverage26
public import Papers.RawWitnesses.TypefourprismCoverage27
public import Papers.RawWitnesses.TypefourprismCoverage28
public import Papers.RawWitnesses.TypefourprismCoverage29
public import Papers.RawWitnesses.TypefourprismCoverage30
public import Papers.RawWitnesses.TypefourprismCoverage31

/-! Small ordinary kernel checks for Appendix B type four_prism. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Typefourprism
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

end Papers.RationalWitnesses.RawWitnesses.Typefourprism
