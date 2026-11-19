module
import GPGeometry.ActualExclusions
import GPGeometry.PrismNine.ActualExclusion
import GPGeometry.SevenSurvivor.ActualExclusion
import GaleType31
import GaleType32
import Papers.A40BoundaryExclusion
import Papers.Witnesses.Type452Realization
import Papers.Witnesses.Type52Realization
import Papers.Witnesses.Type53Realization
import Papers.Witnesses.Type679Realization
import Papers.Witnesses.Type85Realization
import Papers.Witnesses.TypeA14Realization
import Papers.Witnesses.TypeA73Realization
import Papers.Witnesses.TypeD0Realization
import Papers.Witnesses.TypeD4Realization
import Papers.Witnesses.TypefourprismRealization
import Papers.Witnesses.Typetwoprism0Realization
import Papers.Witnesses.Typetwoprism2Realization
public import TerminalRealization

@[expose] public section
noncomputable section
namespace Nonrational.TerminalVerification
open Nonrational.TerminalData
open Papers.RationalityTen.ChirotopeDensity
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem valid_1983 : ValidTarget 1983 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.Type452.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1983)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.Type452.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1984 : ValidTarget 1984 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.Type52.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1984)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.Type52.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1985 : ValidTarget 1985 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.Type53.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1985)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.Type53.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1986 : ValidTarget 1986 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.Type679.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1986)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.Type679.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1987 : ValidTarget 1987 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.Type85.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1987)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.Type85.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1988 : ValidTarget 1988 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.TypeA14.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1988)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.TypeA14.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1989 : ValidTarget 1989 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.TypeA73.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1989)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.TypeA73.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1990 : ValidTarget 1990 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.TypeD0.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1990)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.TypeD0.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1991 : ValidTarget 1991 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.TypeD4.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1991)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.TypeD4.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1992 : ValidTarget 1992 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.Typefourprism.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1992)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.Typefourprism.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1993 : ValidTarget 1993 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.Typetwoprism0.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1993)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.Typetwoprism0.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1994 : ValidTarget 1994 := by
  intro P lab hP hB
  apply Papers.RationalWitnesses.Typetwoprism2.rationallyRealizable P lab hP
  intro T
  rw [facetMask_iff_mem_boundary lab hP hB T]
  have hfacets : (decode (targets 1994)).facets =
      Finset.univ.image (fun k => (Papers.RationalWitnesses.Typetwoprism2.certificate.facets k).vertices) := by decide +kernel
  rw [hfacets]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem valid_1995 : ValidTarget 1995 := by
  intro P lab hP hB
  have heq : decode (targets 1995) = Papers.RationalityTen.GPFiniteGeometry.Literal.C000.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C000.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_1996 : ValidTarget 1996 := by
  intro P lab hP hB
  have heq : decode (targets 1996) = Papers.RationalityTen.GPFiniteGeometry.Literal.C001.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C001.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_1997 : ValidTarget 1997 := by
  intro P lab hP hB
  have heq : decode (targets 1997) = Papers.RationalityTen.GPFiniteGeometry.Literal.C002.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C002.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_1998 : ValidTarget 1998 := by
  intro P lab hP hB
  have heq : decode (targets 1998) = Papers.RationalityTen.GPFiniteGeometry.Literal.C003.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C003.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_1999 : ValidTarget 1999 := by
  intro P lab hP hB
  have heq : decode (targets 1999) = Papers.RationalityTen.GPFiniteGeometry.Literal.C004.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C004.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2000 : ValidTarget 2000 := by
  intro P lab hP hB
  have heq : decode (targets 2000) = Papers.RationalityTen.GPFiniteGeometry.Literal.C005.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C005.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2001 : ValidTarget 2001 := by
  intro P lab hP hB
  have heq : decode (targets 2001) = Papers.RationalityTen.GPFiniteGeometry.Literal.C006.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C006.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2002 : ValidTarget 2002 := by
  intro P lab hP hB
  have heq : decode (targets 2002) = Papers.RationalityTen.GPFiniteGeometry.Literal.C007.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C007.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2003 : ValidTarget 2003 := by
  intro P lab hP hB
  have heq : decode (targets 2003) = Papers.RationalityTen.GPFiniteGeometry.Literal.C008.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C008.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2004 : ValidTarget 2004 := by
  intro P lab hP hB
  have heq : decode (targets 2004) = Papers.RationalityTen.GPFiniteGeometry.Literal.C009.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C009.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2005 : ValidTarget 2005 := by
  intro P lab hP hB
  have heq : decode (targets 2005) = Papers.RationalityTen.GPFiniteGeometry.Literal.C010.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C010.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2006 : ValidTarget 2006 := by
  intro P lab hP hB
  have heq : decode (targets 2006) = Papers.RationalityTen.GPFiniteGeometry.Literal.C011.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C011.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2007 : ValidTarget 2007 := by
  intro P lab hP hB
  have heq : decode (targets 2007) = Papers.RationalityTen.GPFiniteGeometry.Literal.C012.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C012.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2008 : ValidTarget 2008 := by
  intro P lab hP hB
  have heq : decode (targets 2008) = Papers.RationalityTen.GPFiniteGeometry.Literal.C013.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C013.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2009 : ValidTarget 2009 := by
  intro P lab hP hB
  have heq : decode (targets 2009) = Papers.RationalityTen.GPFiniteGeometry.Literal.C014.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C014.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2010 : ValidTarget 2010 := by
  intro P lab hP hB
  have heq : decode (targets 2010) = Papers.RationalityTen.GPFiniteGeometry.Literal.C015.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C015.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2011 : ValidTarget 2011 := by
  intro P lab hP hB
  have heq : decode (targets 2011) = Papers.RationalityTen.GPFiniteGeometry.Literal.C016.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C016.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2012 : ValidTarget 2012 := by
  intro P lab hP hB
  have heq : decode (targets 2012) = Papers.RationalityTen.GPFiniteGeometry.Literal.C017.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C017.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2013 : ValidTarget 2013 := by
  intro P lab hP hB
  have heq : decode (targets 2013) = Papers.RationalityTen.GPFiniteGeometry.Literal.C018.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C018.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2014 : ValidTarget 2014 := by
  intro P lab hP hB
  have heq : decode (targets 2014) = Papers.RationalityTen.GPFiniteGeometry.Literal.C019.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C019.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2015 : ValidTarget 2015 := by
  intro P lab hP hB
  have heq : decode (targets 2015) = Papers.RationalityTen.GPFiniteGeometry.Literal.C020.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C020.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2016 : ValidTarget 2016 := by
  intro P lab hP hB
  have heq : decode (targets 2016) = Papers.RationalityTen.GPFiniteGeometry.Literal.C021.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C021.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2017 : ValidTarget 2017 := by
  intro P lab hP hB
  have heq : decode (targets 2017) = Papers.RationalityTen.GPFiniteGeometry.Literal.C022.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C022.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2018 : ValidTarget 2018 := by
  intro P lab hP hB
  have heq : decode (targets 2018) = Papers.RationalityTen.GPFiniteGeometry.Literal.C023.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C023.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2019 : ValidTarget 2019 := by
  intro P lab hP hB
  have heq : decode (targets 2019) = Papers.RationalityTen.GPFiniteGeometry.Literal.C024.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C024.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2020 : ValidTarget 2020 := by
  intro P lab hP hB
  have heq : decode (targets 2020) = Papers.RationalityTen.GPFiniteGeometry.Literal.C025.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C025.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2021 : ValidTarget 2021 := by
  intro P lab hP hB
  have heq : decode (targets 2021) = Papers.RationalityTen.GPFiniteGeometry.Literal.C026.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C026.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2022 : ValidTarget 2022 := by
  intro P lab hP hB
  have heq : decode (targets 2022) = Papers.RationalityTen.GPFiniteGeometry.Literal.C027.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C027.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2023 : ValidTarget 2023 := by
  intro P lab hP hB
  have heq : decode (targets 2023) = Papers.RationalityTen.GPFiniteGeometry.Literal.C028.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C028.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2024 : ValidTarget 2024 := by
  intro P lab hP hB
  have heq : decode (targets 2024) = Papers.RationalityTen.GPFiniteGeometry.Literal.C029.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C029.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2025 : ValidTarget 2025 := by
  intro P lab hP hB
  have heq : decode (targets 2025) = Papers.RationalityTen.GPFiniteGeometry.Literal.C030.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C030.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2026 : ValidTarget 2026 := by
  intro P lab hP hB
  have heq : decode (targets 2026) = Papers.RationalityTen.GPFiniteGeometry.Literal.C031.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C031.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2027 : ValidTarget 2027 := by
  intro P lab hP hB
  have heq : decode (targets 2027) = Papers.RationalityTen.GPFiniteGeometry.Literal.C032.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C032.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2028 : ValidTarget 2028 := by
  intro P lab hP hB
  have heq : decode (targets 2028) = Papers.RationalityTen.GPFiniteGeometry.Literal.C033.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C033.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2029 : ValidTarget 2029 := by
  intro P lab hP hB
  have heq : decode (targets 2029) = Papers.RationalityTen.GPFiniteGeometry.Literal.C034.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C034.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2030 : ValidTarget 2030 := by
  intro P lab hP hB
  have heq : decode (targets 2030) = Papers.RationalityTen.GPFiniteGeometry.Literal.C035.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C035.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2031 : ValidTarget 2031 := by
  intro P lab hP hB
  have heq : decode (targets 2031) = Papers.RationalityTen.GPFiniteGeometry.Literal.C036.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C036.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2032 : ValidTarget 2032 := by
  intro P lab hP hB
  have heq : decode (targets 2032) = Papers.RationalityTen.GPFiniteGeometry.Literal.C037.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C037.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2033 : ValidTarget 2033 := by
  intro P lab hP hB
  have heq : decode (targets 2033) = Papers.RationalityTen.GPFiniteGeometry.Literal.C038.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C038.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2034 : ValidTarget 2034 := by
  intro P lab hP hB
  have heq : decode (targets 2034) = Papers.RationalityTen.GPFiniteGeometry.Literal.C039.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C039.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2035 : ValidTarget 2035 := by
  intro P lab hP hB
  have heq : decode (targets 2035) = Papers.RationalityTen.GPFiniteGeometry.Literal.C040.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C040.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2036 : ValidTarget 2036 := by
  intro P lab hP hB
  have heq : decode (targets 2036) = Papers.RationalityTen.GPFiniteGeometry.Literal.C041.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C041.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2037 : ValidTarget 2037 := by
  intro P lab hP hB
  have heq : decode (targets 2037) = Papers.RationalityTen.GPFiniteGeometry.Literal.C042.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C042.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2038 : ValidTarget 2038 := by
  intro P lab hP hB
  have heq : decode (targets 2038) = Papers.RationalityTen.GPFiniteGeometry.Literal.C043.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C043.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2039 : ValidTarget 2039 := by
  intro P lab hP hB
  have heq : decode (targets 2039) = Papers.RationalityTen.GPFiniteGeometry.Literal.C044.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.C044.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2040 : ValidTarget 2040 := by
  intro P lab hP hB
  have heq : decode (targets 2040) = Papers.RationalityTen.GPFiniteGeometry.Literal.SevenSurvivor.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.SevenSurvivor.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2041 : ValidTarget 2041 := by
  intro P lab hP hB
  have heq : decode (targets 2041) = Papers.RationalityTen.GPFiniteGeometry.Literal.PrismNine.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.GPFiniteGeometry.Literal.PrismNine.no_actual_boundary P lab hP (by simpa only [heq] using hB)).elim

theorem valid_2042 : ValidTarget 2042 := by
  intro P lab hP hB
  have heq : (decode (targets 2042)).facets = Papers.RationalWitnesses.A40.paperFacetFamily := by decide +kernel
  exact (Papers.RationalWitnesses.A40.no_realizes_A40_boundary P lab _ hB heq).elim

theorem valid_4683 : ValidTarget 4683 := by
  intro P lab hP hB
  have heq : decode (targets 4683) = Papers.RationalityTen.ChirotopeDensity.GaleType31.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.ChirotopeDensity.GaleType31.not_realizable P hP lab (by simpa only [heq] using hB)).elim

theorem valid_4684 : ValidTarget 4684 := by
  intro P lab hP hB
  have heq : decode (targets 4684) = Papers.RationalityTen.ChirotopeDensity.GaleType32.boundary := by
    apply Boundary.ext_faces <;> decide +kernel
  exact (Papers.RationalityTen.ChirotopeDensity.GaleType32.not_realizable P hP lab (by simpa only [heq] using hB)).elim

end Nonrational.TerminalVerification
