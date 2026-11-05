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
theorem disposition_at_1952 : dispositionTest 1952 = true := by decide +kernel

theorem disposition_at_1953 : dispositionTest 1953 = true := by decide +kernel


theorem disposition_at_1954 : dispositionTest 1954 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 1954).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M023.r1535.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M023.r1535) = true
  rw [Nonrational.OldTerminalMatches.M023.r1535_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_1955 : dispositionTest 1955 = true := by decide +kernel

theorem disposition_at_1956 : dispositionTest 1956 = true := by decide +kernel

theorem disposition_at_1957 : dispositionTest 1957 = true := by decide +kernel

theorem disposition_at_1958 : dispositionTest 1958 = true := by decide +kernel

theorem disposition_at_1959 : dispositionTest 1959 = true := by decide +kernel

theorem disposition_at_1960 : dispositionTest 1960 = true := by decide +kernel

theorem disposition_at_1961 : dispositionTest 1961 = true := by decide +kernel

theorem disposition_at_1962 : dispositionTest 1962 = true := by decide +kernel

theorem disposition_at_1963 : dispositionTest 1963 = true := by decide +kernel

theorem disposition_at_1964 : dispositionTest 1964 = true := by decide +kernel

theorem disposition_at_1965 : dispositionTest 1965 = true := by decide +kernel

theorem disposition_at_1966 : dispositionTest 1966 = true := by decide +kernel

theorem disposition_at_1967 : dispositionTest 1967 = true := by decide +kernel

theorem disposition_at_1968 : dispositionTest 1968 = true := by decide +kernel

theorem disposition_at_1969 : dispositionTest 1969 = true := by decide +kernel

theorem disposition_at_1970 : dispositionTest 1970 = true := by decide +kernel

theorem disposition_at_1971 : dispositionTest 1971 = true := by decide +kernel

theorem disposition_at_1972 : dispositionTest 1972 = true := by decide +kernel

theorem disposition_at_1973 : dispositionTest 1973 = true := by decide +kernel

theorem disposition_at_1974 : dispositionTest 1974 = true := by decide +kernel

theorem disposition_at_1975 : dispositionTest 1975 = true := by decide +kernel

theorem disposition_at_1976 : dispositionTest 1976 = true := by decide +kernel

theorem disposition_at_1977 : dispositionTest 1977 = true := by decide +kernel

theorem disposition_at_1978 : dispositionTest 1978 = true := by decide +kernel

theorem disposition_at_1979 : dispositionTest 1979 = true := by decide +kernel

theorem disposition_at_1980 : dispositionTest 1980 = true := by decide +kernel

theorem disposition_at_1981 : dispositionTest 1981 = true := by decide +kernel

theorem disposition_at_1982 : dispositionTest 1982 = true := by decide +kernel

theorem disposition_at_1983 : dispositionTest 1983 = true := by decide +kernel

theorem disposition_interval_1952 : Interval dispositionTest 1952 1953 := by
  intro i hlo hhi
  have h : i = 1952 := by omega
  subst i
  exact disposition_at_1952


theorem disposition_interval_1953 : Interval dispositionTest 1953 1954 := by
  intro i hlo hhi
  have h : i = 1953 := by omega
  subst i
  exact disposition_at_1953


theorem disposition_interval_1954 : Interval dispositionTest 1954 1955 := by
  intro i hlo hhi
  have h : i = 1954 := by omega
  subst i
  exact disposition_at_1954


theorem disposition_interval_1955 : Interval dispositionTest 1955 1956 := by
  intro i hlo hhi
  have h : i = 1955 := by omega
  subst i
  exact disposition_at_1955


theorem disposition_interval_1956 : Interval dispositionTest 1956 1957 := by
  intro i hlo hhi
  have h : i = 1956 := by omega
  subst i
  exact disposition_at_1956


theorem disposition_interval_1957 : Interval dispositionTest 1957 1958 := by
  intro i hlo hhi
  have h : i = 1957 := by omega
  subst i
  exact disposition_at_1957


theorem disposition_interval_1958 : Interval dispositionTest 1958 1959 := by
  intro i hlo hhi
  have h : i = 1958 := by omega
  subst i
  exact disposition_at_1958


theorem disposition_interval_1959 : Interval dispositionTest 1959 1960 := by
  intro i hlo hhi
  have h : i = 1959 := by omega
  subst i
  exact disposition_at_1959


theorem disposition_interval_1960 : Interval dispositionTest 1960 1961 := by
  intro i hlo hhi
  have h : i = 1960 := by omega
  subst i
  exact disposition_at_1960


theorem disposition_interval_1961 : Interval dispositionTest 1961 1962 := by
  intro i hlo hhi
  have h : i = 1961 := by omega
  subst i
  exact disposition_at_1961


theorem disposition_interval_1962 : Interval dispositionTest 1962 1963 := by
  intro i hlo hhi
  have h : i = 1962 := by omega
  subst i
  exact disposition_at_1962


theorem disposition_interval_1963 : Interval dispositionTest 1963 1964 := by
  intro i hlo hhi
  have h : i = 1963 := by omega
  subst i
  exact disposition_at_1963


theorem disposition_interval_1964 : Interval dispositionTest 1964 1965 := by
  intro i hlo hhi
  have h : i = 1964 := by omega
  subst i
  exact disposition_at_1964


theorem disposition_interval_1965 : Interval dispositionTest 1965 1966 := by
  intro i hlo hhi
  have h : i = 1965 := by omega
  subst i
  exact disposition_at_1965


theorem disposition_interval_1966 : Interval dispositionTest 1966 1967 := by
  intro i hlo hhi
  have h : i = 1966 := by omega
  subst i
  exact disposition_at_1966


theorem disposition_interval_1967 : Interval dispositionTest 1967 1968 := by
  intro i hlo hhi
  have h : i = 1967 := by omega
  subst i
  exact disposition_at_1967


theorem disposition_interval_1968 : Interval dispositionTest 1968 1969 := by
  intro i hlo hhi
  have h : i = 1968 := by omega
  subst i
  exact disposition_at_1968


theorem disposition_interval_1969 : Interval dispositionTest 1969 1970 := by
  intro i hlo hhi
  have h : i = 1969 := by omega
  subst i
  exact disposition_at_1969


theorem disposition_interval_1970 : Interval dispositionTest 1970 1971 := by
  intro i hlo hhi
  have h : i = 1970 := by omega
  subst i
  exact disposition_at_1970


theorem disposition_interval_1971 : Interval dispositionTest 1971 1972 := by
  intro i hlo hhi
  have h : i = 1971 := by omega
  subst i
  exact disposition_at_1971


theorem disposition_interval_1972 : Interval dispositionTest 1972 1973 := by
  intro i hlo hhi
  have h : i = 1972 := by omega
  subst i
  exact disposition_at_1972


theorem disposition_interval_1973 : Interval dispositionTest 1973 1974 := by
  intro i hlo hhi
  have h : i = 1973 := by omega
  subst i
  exact disposition_at_1973


theorem disposition_interval_1974 : Interval dispositionTest 1974 1975 := by
  intro i hlo hhi
  have h : i = 1974 := by omega
  subst i
  exact disposition_at_1974


theorem disposition_interval_1975 : Interval dispositionTest 1975 1976 := by
  intro i hlo hhi
  have h : i = 1975 := by omega
  subst i
  exact disposition_at_1975


theorem disposition_interval_1976 : Interval dispositionTest 1976 1977 := by
  intro i hlo hhi
  have h : i = 1976 := by omega
  subst i
  exact disposition_at_1976


theorem disposition_interval_1977 : Interval dispositionTest 1977 1978 := by
  intro i hlo hhi
  have h : i = 1977 := by omega
  subst i
  exact disposition_at_1977


theorem disposition_interval_1978 : Interval dispositionTest 1978 1979 := by
  intro i hlo hhi
  have h : i = 1978 := by omega
  subst i
  exact disposition_at_1978


theorem disposition_interval_1979 : Interval dispositionTest 1979 1980 := by
  intro i hlo hhi
  have h : i = 1979 := by omega
  subst i
  exact disposition_at_1979


theorem disposition_interval_1980 : Interval dispositionTest 1980 1981 := by
  intro i hlo hhi
  have h : i = 1980 := by omega
  subst i
  exact disposition_at_1980


theorem disposition_interval_1981 : Interval dispositionTest 1981 1982 := by
  intro i hlo hhi
  have h : i = 1981 := by omega
  subst i
  exact disposition_at_1981


theorem disposition_interval_1982 : Interval dispositionTest 1982 1983 := by
  intro i hlo hhi
  have h : i = 1982 := by omega
  subst i
  exact disposition_at_1982


theorem disposition_interval_1983 : Interval dispositionTest 1983 1984 := by
  intro i hlo hhi
  have h : i = 1983 := by omega
  subst i
  exact disposition_at_1983

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
