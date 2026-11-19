module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_1536 : FiniteChecks.Interval recordTest 1536 1552 :=
      FiniteChecks.interval_of_check recordTest 1536 16 (by decide +kernel)
    
theorem records_1552 : FiniteChecks.Interval recordTest 1552 1568 :=
      FiniteChecks.interval_of_check recordTest 1552 16 (by decide +kernel)
    
theorem records_1568 : FiniteChecks.Interval recordTest 1568 1584 :=
      FiniteChecks.interval_of_check recordTest 1568 16 (by decide +kernel)
    
theorem records_1584 : FiniteChecks.Interval recordTest 1584 1600 :=
      FiniteChecks.interval_of_check recordTest 1584 16 (by decide +kernel)
    
theorem records_1600 : FiniteChecks.Interval recordTest 1600 1616 :=
      FiniteChecks.interval_of_check recordTest 1600 16 (by decide +kernel)
    
theorem records_1616 : FiniteChecks.Interval recordTest 1616 1632 :=
      FiniteChecks.interval_of_check recordTest 1616 16 (by decide +kernel)
    
theorem records_1632 : FiniteChecks.Interval recordTest 1632 1648 :=
      FiniteChecks.interval_of_check recordTest 1632 16 (by decide +kernel)
    
theorem records_1648 : FiniteChecks.Interval recordTest 1648 1664 :=
      FiniteChecks.interval_of_check recordTest 1648 16 (by decide +kernel)
    
theorem records_1664 : FiniteChecks.Interval recordTest 1664 1680 :=
      FiniteChecks.interval_of_check recordTest 1664 16 (by decide +kernel)
    
theorem records_1680 : FiniteChecks.Interval recordTest 1680 1696 :=
      FiniteChecks.interval_of_check recordTest 1680 16 (by decide +kernel)
    
theorem records_1696 : FiniteChecks.Interval recordTest 1696 1712 :=
      FiniteChecks.interval_of_check recordTest 1696 16 (by decide +kernel)
    
theorem records_1712 : FiniteChecks.Interval recordTest 1712 1728 :=
      FiniteChecks.interval_of_check recordTest 1712 16 (by decide +kernel)
    
theorem records_1728 : FiniteChecks.Interval recordTest 1728 1744 :=
      FiniteChecks.interval_of_check recordTest 1728 16 (by decide +kernel)
    
theorem records_1744 : FiniteChecks.Interval recordTest 1744 1760 :=
      FiniteChecks.interval_of_check recordTest 1744 16 (by decide +kernel)
    
theorem records_1760 : FiniteChecks.Interval recordTest 1760 1776 :=
      FiniteChecks.interval_of_check recordTest 1760 16 (by decide +kernel)
    
theorem records_1776 : FiniteChecks.Interval recordTest 1776 1792 :=
      FiniteChecks.interval_of_check recordTest 1776 16 (by decide +kernel)
    
theorem records_1792 : FiniteChecks.Interval recordTest 1792 1808 :=
      FiniteChecks.interval_of_check recordTest 1792 16 (by decide +kernel)
    
theorem records_1808 : FiniteChecks.Interval recordTest 1808 1824 :=
      FiniteChecks.interval_of_check recordTest 1808 16 (by decide +kernel)
    
theorem records_1824 : FiniteChecks.Interval recordTest 1824 1840 :=
      FiniteChecks.interval_of_check recordTest 1824 16 (by decide +kernel)
    
theorem records_1840 : FiniteChecks.Interval recordTest 1840 1856 :=
      FiniteChecks.interval_of_check recordTest 1840 16 (by decide +kernel)
    
theorem records_1856 : FiniteChecks.Interval recordTest 1856 1872 :=
      FiniteChecks.interval_of_check recordTest 1856 16 (by decide +kernel)
    
theorem records_1872 : FiniteChecks.Interval recordTest 1872 1888 :=
      FiniteChecks.interval_of_check recordTest 1872 16 (by decide +kernel)
    
theorem records_1888 : FiniteChecks.Interval recordTest 1888 1904 :=
      FiniteChecks.interval_of_check recordTest 1888 16 (by decide +kernel)
    
theorem records_1904 : FiniteChecks.Interval recordTest 1904 1920 :=
      FiniteChecks.interval_of_check recordTest 1904 16 (by decide +kernel)
    
theorem records_1920 : FiniteChecks.Interval recordTest 1920 1936 :=
      FiniteChecks.interval_of_check recordTest 1920 16 (by decide +kernel)
    
theorem records_1936 : FiniteChecks.Interval recordTest 1936 1952 :=
      FiniteChecks.interval_of_check recordTest 1936 16 (by decide +kernel)
    
theorem records_1952 : FiniteChecks.Interval recordTest 1952 1968 :=
      FiniteChecks.interval_of_check recordTest 1952 16 (by decide +kernel)
    
theorem records_1968 : FiniteChecks.Interval recordTest 1968 1984 :=
      FiniteChecks.interval_of_check recordTest 1968 16 (by decide +kernel)
    
theorem records_1984 : FiniteChecks.Interval recordTest 1984 2000 :=
      FiniteChecks.interval_of_check recordTest 1984 16 (by decide +kernel)
    
theorem records_2000 : FiniteChecks.Interval recordTest 2000 2016 :=
      FiniteChecks.interval_of_check recordTest 2000 16 (by decide +kernel)
    
theorem records_2016 : FiniteChecks.Interval recordTest 2016 2032 :=
      FiniteChecks.interval_of_check recordTest 2016 16 (by decide +kernel)
    
theorem records_2032 : FiniteChecks.Interval recordTest 2032 2048 :=
      FiniteChecks.interval_of_check recordTest 2032 16 (by decide +kernel)
    
theorem records_join_1536_1568 : FiniteChecks.Interval recordTest 1536 1568 :=
  FiniteChecks.interval_append recordTest 1536 1552 1568 records_1536 records_1552

theorem records_join_1568_1600 : FiniteChecks.Interval recordTest 1568 1600 :=
  FiniteChecks.interval_append recordTest 1568 1584 1600 records_1568 records_1584

theorem records_join_1536_1600 : FiniteChecks.Interval recordTest 1536 1600 :=
  FiniteChecks.interval_append recordTest 1536 1568 1600 records_join_1536_1568 records_join_1568_1600

theorem records_join_1600_1632 : FiniteChecks.Interval recordTest 1600 1632 :=
  FiniteChecks.interval_append recordTest 1600 1616 1632 records_1600 records_1616

theorem records_join_1632_1664 : FiniteChecks.Interval recordTest 1632 1664 :=
  FiniteChecks.interval_append recordTest 1632 1648 1664 records_1632 records_1648

theorem records_join_1600_1664 : FiniteChecks.Interval recordTest 1600 1664 :=
  FiniteChecks.interval_append recordTest 1600 1632 1664 records_join_1600_1632 records_join_1632_1664

theorem records_join_1536_1664 : FiniteChecks.Interval recordTest 1536 1664 :=
  FiniteChecks.interval_append recordTest 1536 1600 1664 records_join_1536_1600 records_join_1600_1664

theorem records_join_1664_1696 : FiniteChecks.Interval recordTest 1664 1696 :=
  FiniteChecks.interval_append recordTest 1664 1680 1696 records_1664 records_1680

theorem records_join_1696_1728 : FiniteChecks.Interval recordTest 1696 1728 :=
  FiniteChecks.interval_append recordTest 1696 1712 1728 records_1696 records_1712

theorem records_join_1664_1728 : FiniteChecks.Interval recordTest 1664 1728 :=
  FiniteChecks.interval_append recordTest 1664 1696 1728 records_join_1664_1696 records_join_1696_1728

theorem records_join_1728_1760 : FiniteChecks.Interval recordTest 1728 1760 :=
  FiniteChecks.interval_append recordTest 1728 1744 1760 records_1728 records_1744

theorem records_join_1760_1792 : FiniteChecks.Interval recordTest 1760 1792 :=
  FiniteChecks.interval_append recordTest 1760 1776 1792 records_1760 records_1776

theorem records_join_1728_1792 : FiniteChecks.Interval recordTest 1728 1792 :=
  FiniteChecks.interval_append recordTest 1728 1760 1792 records_join_1728_1760 records_join_1760_1792

theorem records_join_1664_1792 : FiniteChecks.Interval recordTest 1664 1792 :=
  FiniteChecks.interval_append recordTest 1664 1728 1792 records_join_1664_1728 records_join_1728_1792

theorem records_join_1536_1792 : FiniteChecks.Interval recordTest 1536 1792 :=
  FiniteChecks.interval_append recordTest 1536 1664 1792 records_join_1536_1664 records_join_1664_1792

theorem records_join_1792_1824 : FiniteChecks.Interval recordTest 1792 1824 :=
  FiniteChecks.interval_append recordTest 1792 1808 1824 records_1792 records_1808

theorem records_join_1824_1856 : FiniteChecks.Interval recordTest 1824 1856 :=
  FiniteChecks.interval_append recordTest 1824 1840 1856 records_1824 records_1840

theorem records_join_1792_1856 : FiniteChecks.Interval recordTest 1792 1856 :=
  FiniteChecks.interval_append recordTest 1792 1824 1856 records_join_1792_1824 records_join_1824_1856

theorem records_join_1856_1888 : FiniteChecks.Interval recordTest 1856 1888 :=
  FiniteChecks.interval_append recordTest 1856 1872 1888 records_1856 records_1872

theorem records_join_1888_1920 : FiniteChecks.Interval recordTest 1888 1920 :=
  FiniteChecks.interval_append recordTest 1888 1904 1920 records_1888 records_1904

theorem records_join_1856_1920 : FiniteChecks.Interval recordTest 1856 1920 :=
  FiniteChecks.interval_append recordTest 1856 1888 1920 records_join_1856_1888 records_join_1888_1920

theorem records_join_1792_1920 : FiniteChecks.Interval recordTest 1792 1920 :=
  FiniteChecks.interval_append recordTest 1792 1856 1920 records_join_1792_1856 records_join_1856_1920

theorem records_join_1920_1952 : FiniteChecks.Interval recordTest 1920 1952 :=
  FiniteChecks.interval_append recordTest 1920 1936 1952 records_1920 records_1936

theorem records_join_1952_1984 : FiniteChecks.Interval recordTest 1952 1984 :=
  FiniteChecks.interval_append recordTest 1952 1968 1984 records_1952 records_1968

theorem records_join_1920_1984 : FiniteChecks.Interval recordTest 1920 1984 :=
  FiniteChecks.interval_append recordTest 1920 1952 1984 records_join_1920_1952 records_join_1952_1984

theorem records_join_1984_2016 : FiniteChecks.Interval recordTest 1984 2016 :=
  FiniteChecks.interval_append recordTest 1984 2000 2016 records_1984 records_2000

theorem records_join_2016_2048 : FiniteChecks.Interval recordTest 2016 2048 :=
  FiniteChecks.interval_append recordTest 2016 2032 2048 records_2016 records_2032

theorem records_join_1984_2048 : FiniteChecks.Interval recordTest 1984 2048 :=
  FiniteChecks.interval_append recordTest 1984 2016 2048 records_join_1984_2016 records_join_2016_2048

theorem records_join_1920_2048 : FiniteChecks.Interval recordTest 1920 2048 :=
  FiniteChecks.interval_append recordTest 1920 1984 2048 records_join_1920_1984 records_join_1984_2048

theorem records_join_1792_2048 : FiniteChecks.Interval recordTest 1792 2048 :=
  FiniteChecks.interval_append recordTest 1792 1920 2048 records_join_1792_1920 records_join_1920_2048

theorem records_join_1536_2048 : FiniteChecks.Interval recordTest 1536 2048 :=
  FiniteChecks.interval_append recordTest 1536 1792 2048 records_join_1536_1792 records_join_1792_2048

theorem records_part_003 : FiniteChecks.Interval recordTest 1536 2048 := records_join_1536_2048
    end Papers.RationalityTen.FacetUniverses.FullSmall
    