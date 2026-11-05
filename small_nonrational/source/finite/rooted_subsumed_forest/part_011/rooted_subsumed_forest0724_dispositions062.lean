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
theorem disposition_at_1984 : dispositionTest 1984 = true := by decide +kernel

theorem disposition_at_1985 : dispositionTest 1985 = true := by decide +kernel

theorem disposition_at_1986 : dispositionTest 1986 = true := by decide +kernel

theorem disposition_at_1987 : dispositionTest 1987 = true := by decide +kernel

theorem disposition_at_1988 : dispositionTest 1988 = true := by decide +kernel

theorem disposition_at_1989 : dispositionTest 1989 = true := by decide +kernel

theorem disposition_at_1990 : dispositionTest 1990 = true := by decide +kernel

theorem disposition_at_1991 : dispositionTest 1991 = true := by decide +kernel

theorem disposition_at_1992 : dispositionTest 1992 = true := by decide +kernel

theorem disposition_at_1993 : dispositionTest 1993 = true := by decide +kernel

theorem disposition_at_1994 : dispositionTest 1994 = true := by decide +kernel

theorem disposition_at_1995 : dispositionTest 1995 = true := by decide +kernel

theorem disposition_at_1996 : dispositionTest 1996 = true := by decide +kernel

theorem disposition_at_1997 : dispositionTest 1997 = true := by decide +kernel

theorem disposition_at_1998 : dispositionTest 1998 = true := by decide +kernel

theorem disposition_at_1999 : dispositionTest 1999 = true := by decide +kernel

theorem disposition_at_2000 : dispositionTest 2000 = true := by decide +kernel

theorem disposition_at_2001 : dispositionTest 2001 = true := by decide +kernel

theorem disposition_at_2002 : dispositionTest 2002 = true := by decide +kernel

theorem disposition_at_2003 : dispositionTest 2003 = true := by decide +kernel

theorem disposition_at_2004 : dispositionTest 2004 = true := by decide +kernel

theorem disposition_at_2005 : dispositionTest 2005 = true := by decide +kernel

theorem disposition_at_2006 : dispositionTest 2006 = true := by decide +kernel

theorem disposition_at_2007 : dispositionTest 2007 = true := by decide +kernel

theorem disposition_at_2008 : dispositionTest 2008 = true := by decide +kernel

theorem disposition_at_2009 : dispositionTest 2009 = true := by decide +kernel

theorem disposition_at_2010 : dispositionTest 2010 = true := by decide +kernel

theorem disposition_at_2011 : dispositionTest 2011 = true := by decide +kernel

theorem disposition_at_2012 : dispositionTest 2012 = true := by decide +kernel

theorem disposition_at_2013 : dispositionTest 2013 = true := by decide +kernel

theorem disposition_at_2014 : dispositionTest 2014 = true := by decide +kernel

theorem disposition_at_2015 : dispositionTest 2015 = true := by decide +kernel

theorem disposition_interval_1984 : Interval dispositionTest 1984 1985 := by
  intro i hlo hhi
  have h : i = 1984 := by omega
  subst i
  exact disposition_at_1984


theorem disposition_interval_1985 : Interval dispositionTest 1985 1986 := by
  intro i hlo hhi
  have h : i = 1985 := by omega
  subst i
  exact disposition_at_1985


theorem disposition_interval_1986 : Interval dispositionTest 1986 1987 := by
  intro i hlo hhi
  have h : i = 1986 := by omega
  subst i
  exact disposition_at_1986


theorem disposition_interval_1987 : Interval dispositionTest 1987 1988 := by
  intro i hlo hhi
  have h : i = 1987 := by omega
  subst i
  exact disposition_at_1987


theorem disposition_interval_1988 : Interval dispositionTest 1988 1989 := by
  intro i hlo hhi
  have h : i = 1988 := by omega
  subst i
  exact disposition_at_1988


theorem disposition_interval_1989 : Interval dispositionTest 1989 1990 := by
  intro i hlo hhi
  have h : i = 1989 := by omega
  subst i
  exact disposition_at_1989


theorem disposition_interval_1990 : Interval dispositionTest 1990 1991 := by
  intro i hlo hhi
  have h : i = 1990 := by omega
  subst i
  exact disposition_at_1990


theorem disposition_interval_1991 : Interval dispositionTest 1991 1992 := by
  intro i hlo hhi
  have h : i = 1991 := by omega
  subst i
  exact disposition_at_1991


theorem disposition_interval_1992 : Interval dispositionTest 1992 1993 := by
  intro i hlo hhi
  have h : i = 1992 := by omega
  subst i
  exact disposition_at_1992


theorem disposition_interval_1993 : Interval dispositionTest 1993 1994 := by
  intro i hlo hhi
  have h : i = 1993 := by omega
  subst i
  exact disposition_at_1993


theorem disposition_interval_1994 : Interval dispositionTest 1994 1995 := by
  intro i hlo hhi
  have h : i = 1994 := by omega
  subst i
  exact disposition_at_1994


theorem disposition_interval_1995 : Interval dispositionTest 1995 1996 := by
  intro i hlo hhi
  have h : i = 1995 := by omega
  subst i
  exact disposition_at_1995


theorem disposition_interval_1996 : Interval dispositionTest 1996 1997 := by
  intro i hlo hhi
  have h : i = 1996 := by omega
  subst i
  exact disposition_at_1996


theorem disposition_interval_1997 : Interval dispositionTest 1997 1998 := by
  intro i hlo hhi
  have h : i = 1997 := by omega
  subst i
  exact disposition_at_1997


theorem disposition_interval_1998 : Interval dispositionTest 1998 1999 := by
  intro i hlo hhi
  have h : i = 1998 := by omega
  subst i
  exact disposition_at_1998


theorem disposition_interval_1999 : Interval dispositionTest 1999 2000 := by
  intro i hlo hhi
  have h : i = 1999 := by omega
  subst i
  exact disposition_at_1999


theorem disposition_interval_2000 : Interval dispositionTest 2000 2001 := by
  intro i hlo hhi
  have h : i = 2000 := by omega
  subst i
  exact disposition_at_2000


theorem disposition_interval_2001 : Interval dispositionTest 2001 2002 := by
  intro i hlo hhi
  have h : i = 2001 := by omega
  subst i
  exact disposition_at_2001


theorem disposition_interval_2002 : Interval dispositionTest 2002 2003 := by
  intro i hlo hhi
  have h : i = 2002 := by omega
  subst i
  exact disposition_at_2002


theorem disposition_interval_2003 : Interval dispositionTest 2003 2004 := by
  intro i hlo hhi
  have h : i = 2003 := by omega
  subst i
  exact disposition_at_2003


theorem disposition_interval_2004 : Interval dispositionTest 2004 2005 := by
  intro i hlo hhi
  have h : i = 2004 := by omega
  subst i
  exact disposition_at_2004


theorem disposition_interval_2005 : Interval dispositionTest 2005 2006 := by
  intro i hlo hhi
  have h : i = 2005 := by omega
  subst i
  exact disposition_at_2005


theorem disposition_interval_2006 : Interval dispositionTest 2006 2007 := by
  intro i hlo hhi
  have h : i = 2006 := by omega
  subst i
  exact disposition_at_2006


theorem disposition_interval_2007 : Interval dispositionTest 2007 2008 := by
  intro i hlo hhi
  have h : i = 2007 := by omega
  subst i
  exact disposition_at_2007


theorem disposition_interval_2008 : Interval dispositionTest 2008 2009 := by
  intro i hlo hhi
  have h : i = 2008 := by omega
  subst i
  exact disposition_at_2008


theorem disposition_interval_2009 : Interval dispositionTest 2009 2010 := by
  intro i hlo hhi
  have h : i = 2009 := by omega
  subst i
  exact disposition_at_2009


theorem disposition_interval_2010 : Interval dispositionTest 2010 2011 := by
  intro i hlo hhi
  have h : i = 2010 := by omega
  subst i
  exact disposition_at_2010


theorem disposition_interval_2011 : Interval dispositionTest 2011 2012 := by
  intro i hlo hhi
  have h : i = 2011 := by omega
  subst i
  exact disposition_at_2011


theorem disposition_interval_2012 : Interval dispositionTest 2012 2013 := by
  intro i hlo hhi
  have h : i = 2012 := by omega
  subst i
  exact disposition_at_2012


theorem disposition_interval_2013 : Interval dispositionTest 2013 2014 := by
  intro i hlo hhi
  have h : i = 2013 := by omega
  subst i
  exact disposition_at_2013


theorem disposition_interval_2014 : Interval dispositionTest 2014 2015 := by
  intro i hlo hhi
  have h : i = 2014 := by omega
  subst i
  exact disposition_at_2014


theorem disposition_interval_2015 : Interval dispositionTest 2015 2016 := by
  intro i hlo hhi
  have h : i = 2015 := by omega
  subst i
  exact disposition_at_2015

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
