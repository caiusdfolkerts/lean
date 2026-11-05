module
prelude
public import RootedSubsumedForest0724DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_960 : dispositionTest 960 = true := by decide +kernel

theorem disposition_at_961 : dispositionTest 961 = true := by decide +kernel

theorem disposition_at_962 : dispositionTest 962 = true := by decide +kernel


theorem disposition_at_963 : dispositionTest 963 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 963).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1509.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1509) = true
  rw [Nonrational.OldTerminalMatches.M023.r1509_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_964 : dispositionTest 964 = true := by decide +kernel

theorem disposition_at_965 : dispositionTest 965 = true := by decide +kernel

theorem disposition_at_966 : dispositionTest 966 = true := by decide +kernel

theorem disposition_at_967 : dispositionTest 967 = true := by decide +kernel

theorem disposition_at_968 : dispositionTest 968 = true := by decide +kernel

theorem disposition_at_969 : dispositionTest 969 = true := by decide +kernel

theorem disposition_at_970 : dispositionTest 970 = true := by decide +kernel

theorem disposition_at_971 : dispositionTest 971 = true := by decide +kernel

theorem disposition_at_972 : dispositionTest 972 = true := by decide +kernel

theorem disposition_at_973 : dispositionTest 973 = true := by decide +kernel

theorem disposition_at_974 : dispositionTest 974 = true := by decide +kernel

theorem disposition_at_975 : dispositionTest 975 = true := by decide +kernel

theorem disposition_at_976 : dispositionTest 976 = true := by decide +kernel

theorem disposition_at_977 : dispositionTest 977 = true := by decide +kernel

theorem disposition_at_978 : dispositionTest 978 = true := by decide +kernel

theorem disposition_at_979 : dispositionTest 979 = true := by decide +kernel

theorem disposition_at_980 : dispositionTest 980 = true := by decide +kernel

theorem disposition_at_981 : dispositionTest 981 = true := by decide +kernel

theorem disposition_at_982 : dispositionTest 982 = true := by decide +kernel

theorem disposition_at_983 : dispositionTest 983 = true := by decide +kernel

theorem disposition_at_984 : dispositionTest 984 = true := by decide +kernel

theorem disposition_at_985 : dispositionTest 985 = true := by decide +kernel

theorem disposition_at_986 : dispositionTest 986 = true := by decide +kernel

theorem disposition_at_987 : dispositionTest 987 = true := by decide +kernel

theorem disposition_at_988 : dispositionTest 988 = true := by decide +kernel

theorem disposition_at_989 : dispositionTest 989 = true := by decide +kernel


theorem disposition_at_990 : dispositionTest 990 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 990).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1510.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1510) = true
  rw [Nonrational.OldTerminalMatches.M023.r1510_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_991 : dispositionTest 991 = true := by decide +kernel

theorem disposition_interval_960 : Interval dispositionTest 960 961 := by
  intro i hlo hhi
  have h : i = 960 := by omega
  subst i
  exact disposition_at_960


theorem disposition_interval_961 : Interval dispositionTest 961 962 := by
  intro i hlo hhi
  have h : i = 961 := by omega
  subst i
  exact disposition_at_961


theorem disposition_interval_962 : Interval dispositionTest 962 963 := by
  intro i hlo hhi
  have h : i = 962 := by omega
  subst i
  exact disposition_at_962


theorem disposition_interval_963 : Interval dispositionTest 963 964 := by
  intro i hlo hhi
  have h : i = 963 := by omega
  subst i
  exact disposition_at_963


theorem disposition_interval_964 : Interval dispositionTest 964 965 := by
  intro i hlo hhi
  have h : i = 964 := by omega
  subst i
  exact disposition_at_964


theorem disposition_interval_965 : Interval dispositionTest 965 966 := by
  intro i hlo hhi
  have h : i = 965 := by omega
  subst i
  exact disposition_at_965


theorem disposition_interval_966 : Interval dispositionTest 966 967 := by
  intro i hlo hhi
  have h : i = 966 := by omega
  subst i
  exact disposition_at_966


theorem disposition_interval_967 : Interval dispositionTest 967 968 := by
  intro i hlo hhi
  have h : i = 967 := by omega
  subst i
  exact disposition_at_967


theorem disposition_interval_968 : Interval dispositionTest 968 969 := by
  intro i hlo hhi
  have h : i = 968 := by omega
  subst i
  exact disposition_at_968


theorem disposition_interval_969 : Interval dispositionTest 969 970 := by
  intro i hlo hhi
  have h : i = 969 := by omega
  subst i
  exact disposition_at_969


theorem disposition_interval_970 : Interval dispositionTest 970 971 := by
  intro i hlo hhi
  have h : i = 970 := by omega
  subst i
  exact disposition_at_970


theorem disposition_interval_971 : Interval dispositionTest 971 972 := by
  intro i hlo hhi
  have h : i = 971 := by omega
  subst i
  exact disposition_at_971


theorem disposition_interval_972 : Interval dispositionTest 972 973 := by
  intro i hlo hhi
  have h : i = 972 := by omega
  subst i
  exact disposition_at_972


theorem disposition_interval_973 : Interval dispositionTest 973 974 := by
  intro i hlo hhi
  have h : i = 973 := by omega
  subst i
  exact disposition_at_973


theorem disposition_interval_974 : Interval dispositionTest 974 975 := by
  intro i hlo hhi
  have h : i = 974 := by omega
  subst i
  exact disposition_at_974


theorem disposition_interval_975 : Interval dispositionTest 975 976 := by
  intro i hlo hhi
  have h : i = 975 := by omega
  subst i
  exact disposition_at_975


theorem disposition_interval_976 : Interval dispositionTest 976 977 := by
  intro i hlo hhi
  have h : i = 976 := by omega
  subst i
  exact disposition_at_976


theorem disposition_interval_977 : Interval dispositionTest 977 978 := by
  intro i hlo hhi
  have h : i = 977 := by omega
  subst i
  exact disposition_at_977


theorem disposition_interval_978 : Interval dispositionTest 978 979 := by
  intro i hlo hhi
  have h : i = 978 := by omega
  subst i
  exact disposition_at_978


theorem disposition_interval_979 : Interval dispositionTest 979 980 := by
  intro i hlo hhi
  have h : i = 979 := by omega
  subst i
  exact disposition_at_979


theorem disposition_interval_980 : Interval dispositionTest 980 981 := by
  intro i hlo hhi
  have h : i = 980 := by omega
  subst i
  exact disposition_at_980


theorem disposition_interval_981 : Interval dispositionTest 981 982 := by
  intro i hlo hhi
  have h : i = 981 := by omega
  subst i
  exact disposition_at_981


theorem disposition_interval_982 : Interval dispositionTest 982 983 := by
  intro i hlo hhi
  have h : i = 982 := by omega
  subst i
  exact disposition_at_982


theorem disposition_interval_983 : Interval dispositionTest 983 984 := by
  intro i hlo hhi
  have h : i = 983 := by omega
  subst i
  exact disposition_at_983


theorem disposition_interval_984 : Interval dispositionTest 984 985 := by
  intro i hlo hhi
  have h : i = 984 := by omega
  subst i
  exact disposition_at_984


theorem disposition_interval_985 : Interval dispositionTest 985 986 := by
  intro i hlo hhi
  have h : i = 985 := by omega
  subst i
  exact disposition_at_985


theorem disposition_interval_986 : Interval dispositionTest 986 987 := by
  intro i hlo hhi
  have h : i = 986 := by omega
  subst i
  exact disposition_at_986


theorem disposition_interval_987 : Interval dispositionTest 987 988 := by
  intro i hlo hhi
  have h : i = 987 := by omega
  subst i
  exact disposition_at_987


theorem disposition_interval_988 : Interval dispositionTest 988 989 := by
  intro i hlo hhi
  have h : i = 988 := by omega
  subst i
  exact disposition_at_988


theorem disposition_interval_989 : Interval dispositionTest 989 990 := by
  intro i hlo hhi
  have h : i = 989 := by omega
  subst i
  exact disposition_at_989


theorem disposition_interval_990 : Interval dispositionTest 990 991 := by
  intro i hlo hhi
  have h : i = 990 := by omega
  subst i
  exact disposition_at_990


theorem disposition_interval_991 : Interval dispositionTest 991 992 := by
  intro i hlo hhi
  have h : i = 991 := by omega
  subst i
  exact disposition_at_991

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
