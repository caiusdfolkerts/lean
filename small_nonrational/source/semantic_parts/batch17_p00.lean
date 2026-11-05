module
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.BitsetOrigins


section BundlePart0
/- Source: MatroidChecked/SemanticParts/Cases20Part00/Checks03.lean -/



@[expose] public section
noncomputable section


set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C75


noncomputable def certificates_10 : List (Origin 70 724 × List Sat.Literal) :=
  [((.excluded 611),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 45)]),
   ((.excluded 612),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 613),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 614),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 615),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 54),(.pos 58)]),
   ((.excluded 616),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 617),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 54),(.pos 62)]),
   ((.excluded 618),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 54),(.pos 67)]),
   ((.excluded 619),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 54)]),
   ((.excluded 620),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 621),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 58),(.pos 62)]),
   ((.excluded 622),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 58),(.pos 67)]),
   ((.excluded 623),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 58)]),
   ((.excluded 624),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 62),(.pos 67)]),
   ((.excluded 625),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 62)]),
   ((.excluded 626),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 67)]),
   ((.excluded 627),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40)]),
   ((.excluded 628),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 629),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 630),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 631),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 54),(.pos 58)]),
   ((.excluded 632),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 633),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 54),(.pos 62)]),
   ((.excluded 634),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 54),(.pos 67)]),
   ((.excluded 635),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 54)]),
   ((.excluded 636),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 637),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 58),(.pos 62)]),
   ((.excluded 638),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 58),(.pos 67)]),
   ((.excluded 639),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 58)]),
   ((.excluded 640),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 62),(.pos 67)]),
   ((.excluded 641),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 62)]),
   ((.excluded 642),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 67)]),
   ((.excluded 643),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45)]),
   ((.excluded 644),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 645),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 646),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 647),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 54),(.pos 58)]),
   ((.excluded 648),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 649),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 54),(.pos 62)]),
   ((.excluded 650),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 54),(.pos 67)]),
   ((.excluded 651),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 54)]),
   ((.excluded 652),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 653),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 58),(.pos 62)]),
   ((.excluded 654),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 58),(.pos 67)]),
   ((.excluded 655),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 58)]),
   ((.excluded 656),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 62),(.pos 67)]),
   ((.excluded 657),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 62)]),
   ((.excluded 658),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 67)]),
   ((.excluded 659),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38)]),
   ((.excluded 660),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 661),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 662),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 663),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 54),(.pos 58)]),
   ((.excluded 664),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 665),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 54),(.pos 62)]),
   ((.excluded 666),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 54),(.pos 67)]),
   ((.excluded 667),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 54)]),
   ((.excluded 668),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 669),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 58),(.pos 62)]),
   ((.excluded 670),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 58),(.pos 67)]),
   ((.excluded 671),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 58)]),
   ((.excluded 672),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 62),(.pos 67)]),
   ((.excluded 673),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 62)]),
   ((.excluded 674),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 67)]),
   ((.excluded 675),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45)]),
   ((.excluded 676),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 677),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 678),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 679),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 54),(.pos 58)]),
   ((.excluded 680),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 681),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 54),(.pos 62)]),
   ((.excluded 682),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 54),(.pos 67)]),
   ((.excluded 683),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 54)]),
   ((.excluded 684),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 685),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 58),(.pos 62)]),
   ((.excluded 686),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 58),(.pos 67)]),
   ((.excluded 687),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 58)]),
   ((.excluded 688),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 62),(.pos 67)]),
   ((.excluded 689),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 62)]),
   ((.excluded 690),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 67)]),
   ((.excluded 691),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40)]),
   ((.excluded 692),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 693),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 694),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 695),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 54),(.pos 58)]),
   ((.excluded 696),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 697),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 54),(.pos 62)]),
   ((.excluded 698),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 54),(.pos 67)]),
   ((.excluded 699),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 54)]),
   ((.excluded 700),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 701),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 58),(.pos 62)]),
   ((.excluded 702),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 58),(.pos 67)]),
   ((.excluded 703),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 58)]),
   ((.excluded 704),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 62),(.pos 67)]),
   ((.excluded 705),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 62)]),
   ((.excluded 706),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 67)]),
   ((.excluded 707),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45)]),
   ((.excluded 708),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 709),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 710),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 711),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 54),(.pos 58)]),
   ((.excluded 712),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 713),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 54),(.pos 62)]),
   ((.excluded 714),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 54),(.pos 67)]),
   ((.excluded 715),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 54)]),
   ((.excluded 716),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 717),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 58),(.pos 62)]),
   ((.excluded 718),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 58),(.pos 67)]),
   ((.excluded 719),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 58)]),
   ((.excluded 720),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 62),(.pos 67)]),
   ((.excluded 721),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 62)]),
   ((.excluded 722),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 67)]),
   ((.excluded 723),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35)])]

theorem certificates_10_valid : ∀ oc ∈ certificates_10,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.BitsetOrigins.bitsetOrigins_sound
  have hchecks : ∀ i : Fin 113,
    Papers.RationalityTen.MatroidChecked.BitsetOrigins.BitsetOrigin U (7 : Fin 8) old newIndex models
      (certificates_10.get i).1 (certificates_10.get i).2 := by
    refine (Fin.forall_fin_add (m := 56) (n := 57) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 28) (n := 28) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 28) (n := 29) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 14) (n := 15) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro oc hoc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hoc
  exact hchecks i



theorem witness_0 : ∀ j : Fin 128,
    let w : Fin 724 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 724 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 75)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 64) (n := 64) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.bitsetRawWitness_sound 8 _ _ _ _ _ _ hj.2⟩



theorem witness_1 : ∀ j : Fin 128,
    let w : Fin 724 := ⟨128 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 724 := ⟨128 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 75)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 64) (n := 64) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.bitsetRawWitness_sound 8 _ _ _ _ _ _ hj.2⟩



theorem witness_2 : ∀ j : Fin 128,
    let w : Fin 724 := ⟨256 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 724 := ⟨256 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 75)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 64) (n := 64) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.bitsetRawWitness_sound 8 _ _ _ _ _ _ hj.2⟩



theorem witness_3 : ∀ j : Fin 128,
    let w : Fin 724 := ⟨384 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 724 := ⟨384 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 75)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 64) (n := 64) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.bitsetRawWitness_sound 8 _ _ _ _ _ _ hj.2⟩



theorem witness_4 : ∀ j : Fin 128,
    let w : Fin 724 := ⟨512 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 724 := ⟨512 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 75)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 64) (n := 64) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.bitsetRawWitness_sound 8 _ _ _ _ _ _ hj.2⟩



theorem witness_5 : ∀ j : Fin 84,
    let w : Fin 724 := ⟨640 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 84,
      let w : Fin 724 := ⟨640 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 75)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 42) (n := 42) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 21) (n := 21) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 10) (n := 11) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 10) (n := 11) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 21) (n := 21) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 10) (n := 11) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 10) (n := 11) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.bitsetRawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C75

end
end
end BundlePart0

