module
import Batches.B000
import Mathlib.Tactic.FinCases
public import TerminalGeometry

@[expose] public section
namespace Nonrational.TerminalVerification
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem projection_0000 : Certifies 0 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_000.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0001 : Certifies 1 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_045.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0002 : Certifies 2 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.R_one_six_1831.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0003 : Certifies 3 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_001.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0004 : Certifies 4 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_002.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0005 : Certifies 5 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_003.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0006 : Certifies 6 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_004.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0007 : Certifies 7 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_005.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0008 : Certifies 8 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_006.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0009 : Certifies 9 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_007.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0010 : Certifies 10 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_008.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0011 : Certifies 11 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_009.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0012 : Certifies 12 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_010.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0013 : Certifies 13 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_011.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0014 : Certifies 14 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_012.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0015 : Certifies 15 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_013.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0016 : Certifies 16 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_014.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0017 : Certifies 17 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_015.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0018 : Certifies 18 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_016.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0019 : Certifies 19 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_017.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0020 : Certifies 20 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_018.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0021 : Certifies 21 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_019.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0022 : Certifies 22 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_020.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0023 : Certifies 23 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_022.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0024 : Certifies 24 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_023.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0025 : Certifies 25 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_024.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0026 : Certifies 26 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_025.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0027 : Certifies 27 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_026.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0028 : Certifies 28 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_027.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem projection_0029 : Certifies 29 := by
  apply certified_of_eq Papers.RationalityTen.ChirotopeDensity.FiniteProjection.Certificates.P0_028.certificate
  apply Boundary.ext_faces <;> decide +kernel

theorem certified_B000 (j : Fin 30) :
    Certifies (0 + j.val) := by
  fin_cases j
  · exact projection_0000
  · exact projection_0001
  · exact projection_0002
  · exact projection_0003
  · exact projection_0004
  · exact projection_0005
  · exact projection_0006
  · exact projection_0007
  · exact projection_0008
  · exact projection_0009
  · exact projection_0010
  · exact projection_0011
  · exact projection_0012
  · exact projection_0013
  · exact projection_0014
  · exact projection_0015
  · exact projection_0016
  · exact projection_0017
  · exact projection_0018
  · exact projection_0019
  · exact projection_0020
  · exact projection_0021
  · exact projection_0022
  · exact projection_0023
  · exact projection_0024
  · exact projection_0025
  · exact projection_0026
  · exact projection_0027
  · exact projection_0028
  · exact projection_0029

end Nonrational.TerminalVerification
