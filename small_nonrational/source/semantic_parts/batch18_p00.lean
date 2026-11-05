module
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins


section BundlePart0
/- Source: MatroidChecked/SemanticParts/Cases21Part00/Checks05.lean -/



@[expose] public section
noncomputable section


set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C76


noncomputable def certificates_14 : List (Origin 70 1271 × List Sat.Literal) :=
  [((.excluded 1058),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 57)]),
   ((.excluded 1059),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 57),(.pos 69)]),
   ((.excluded 1060),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 57)]),
   ((.excluded 1061),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 57),(.pos 69)]),
   ((.excluded 1062),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 57)]),
   ((.excluded 1063),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 1064),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 60),(.pos 65)]),
   ((.excluded 1065),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 62),(.pos 65)]),
   ((.excluded 1066),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 65)]),
   ((.excluded 1067),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 1068),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 60),(.pos 65)]),
   ((.excluded 1069),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 62),(.pos 65)]),
   ((.excluded 1070),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 65)]),
   ((.excluded 1071),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 49),(.pos 60),(.pos 62)]),
   ((.excluded 1072),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 49),(.pos 62)]),
   ((.excluded 1073),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 60),(.pos 62)]),
   ((.excluded 1074),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 62)]),
   ((.excluded 1075),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 60),(.pos 62)]),
   ((.excluded 1076),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 62)]),
   ((.excluded 1077),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 60),(.pos 62)]),
   ((.excluded 1078),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 62)]),
   ((.excluded 1079),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 49),(.pos 60),(.pos 69)]),
   ((.excluded 1080),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 49),(.pos 60)]),
   ((.excluded 1081),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 49),(.pos 69)]),
   ((.excluded 1082),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 49)]),
   ((.excluded 1083),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 60),(.pos 69)]),
   ((.excluded 1084),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 60)]),
   ((.excluded 1085),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 69)]),
   ((.excluded 1086),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46)]),
   ((.excluded 1087),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 60),(.pos 69)]),
   ((.excluded 1088),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 60)]),
   ((.excluded 1089),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 69)]),
   ((.excluded 1090),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49)]),
   ((.excluded 1091),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 60),(.pos 69)]),
   ((.excluded 1092),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 60)]),
   ((.excluded 1093),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 69)]),
   ((.excluded 1094),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42)]),
   ((.excluded 1095),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 58),(.pos 62)]),
   ((.excluded 1096),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 58),(.pos 62)]),
   ((.excluded 1097),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 60),(.pos 62)]),
   ((.excluded 1098),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 62)]),
   ((.excluded 1099),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 60),(.pos 62)]),
   ((.excluded 1100),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 62)]),
   ((.excluded 1101),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46),(.pos 60),(.pos 69)]),
   ((.excluded 1102),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46),(.pos 60)]),
   ((.excluded 1103),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 60),(.pos 69)]),
   ((.excluded 1104),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 60)]),
   ((.excluded 1105),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 60),(.pos 69)]),
   ((.excluded 1106),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 60)]),
   ((.excluded 1107),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46),(.pos 57),(.pos 58),(.pos 69)]),
   ((.excluded 1108),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46),(.pos 57),(.pos 58)]),
   ((.excluded 1109),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46),(.pos 57),(.pos 69)]),
   ((.excluded 1110),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46),(.pos 57)]),
   ((.excluded 1111),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46),(.pos 58),(.pos 69)]),
   ((.excluded 1112),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46),(.pos 58)]),
   ((.excluded 1113),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46),(.pos 69)]),
   ((.excluded 1114),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46)]),
   ((.excluded 1115),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 57),(.pos 58),(.pos 69)]),
   ((.excluded 1116),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 57),(.pos 58)]),
   ((.excluded 1117),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 57),(.pos 69)]),
   ((.excluded 1118),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 57)]),
   ((.excluded 1119),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 58),(.pos 69)]),
   ((.excluded 1120),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 58)]),
   ((.excluded 1121),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 69)]),
   ((.excluded 1122),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49)]),
   ((.excluded 1123),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 57),(.pos 58),(.pos 69)]),
   ((.excluded 1124),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 57),(.pos 58)]),
   ((.excluded 1125),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 57),(.pos 69)]),
   ((.excluded 1126),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 57)]),
   ((.excluded 1127),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 58),(.pos 69)]),
   ((.excluded 1128),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 58)]),
   ((.excluded 1129),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 69)]),
   ((.excluded 1130),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46)]),
   ((.excluded 1131),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 57),(.pos 65)]),
   ((.excluded 1132),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 57),(.pos 65)]),
   ((.excluded 1133),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 57),(.pos 65)]),
   ((.excluded 1134),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 57),(.pos 65)]),
   ((.excluded 1135),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 57),(.pos 65)]),
   ((.excluded 1136),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 57),(.pos 65)]),
   ((.excluded 1137),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 57),(.pos 58),(.pos 69)]),
   ((.excluded 1138),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 57),(.pos 58)]),
   ((.excluded 1139),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 57),(.pos 69)]),
   ((.excluded 1140),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 57)]),
   ((.excluded 1141),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 57),(.pos 58),(.pos 69)]),
   ((.excluded 1142),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 57),(.pos 58)]),
   ((.excluded 1143),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 57),(.pos 69)]),
   ((.excluded 1144),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 57)]),
   ((.excluded 1145),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 57),(.pos 58),(.pos 69)]),
   ((.excluded 1146),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 57),(.pos 58)]),
   ((.excluded 1147),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 57),(.pos 69)]),
   ((.excluded 1148),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 57)]),
   ((.excluded 1149),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 57),(.pos 58),(.pos 69)]),
   ((.excluded 1150),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 57),(.pos 58)]),
   ((.excluded 1151),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 57),(.pos 69)]),
   ((.excluded 1152),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 57)]),
   ((.excluded 1153),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 57),(.pos 58),(.pos 69)]),
   ((.excluded 1154),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 57),(.pos 58)]),
   ((.excluded 1155),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 57),(.pos 69)]),
   ((.excluded 1156),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 57)]),
   ((.excluded 1157),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 57),(.pos 58),(.pos 69)]),
   ((.excluded 1158),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 57),(.pos 58)]),
   ((.excluded 1159),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 57),(.pos 69)]),
   ((.excluded 1160),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 57)]),
   ((.excluded 1161),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 58),(.pos 69)]),
   ((.excluded 1162),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 58)]),
   ((.excluded 1163),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 58),(.pos 69)]),
   ((.excluded 1164),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 58)]),
   ((.excluded 1165),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 58),(.pos 69)]),
   ((.excluded 1166),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 58)]),
   ((.excluded 1167),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 58),(.pos 69)]),
   ((.excluded 1168),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 58)]),
   ((.excluded 1169),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 60),(.pos 65)]),
   ((.excluded 1170),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 65)]),
   ((.excluded 1171),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 60),(.pos 65)]),
   ((.excluded 1172),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 65)]),
   ((.excluded 1173),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 60),(.pos 65)]),
   ((.excluded 1174),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 65)]),
   ((.excluded 1175),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 60),(.pos 65)]),
   ((.excluded 1176),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 65)]),
   ((.excluded 1177),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 60),(.pos 69)]),
   ((.excluded 1178),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 60)]),
   ((.excluded 1179),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 69)]),
   ((.excluded 1180),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47)]),
   ((.excluded 1181),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 60),(.pos 69)]),
   ((.excluded 1182),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 60)]),
   ((.excluded 1183),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 69)]),
   ((.excluded 1184),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43)]),
   ((.excluded 1185),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 60),(.pos 69)])]

theorem certificates_14_valid : ∀ oc ∈ certificates_14,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.MaskOrigins.maskOrigins_sound (grid := (fun i : Fin 70 => N8R4.gridMasks.get i.val))
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.MaskOrigins.MaskOrigin (fun i : Fin 70 => N8R4.gridMasks.get i.val) (7 : Fin 8) old newIndex models
      (certificates_14.get i).1 (certificates_14.get i).2 := by
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
  intro oc hoc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hoc
  exact hchecks i



noncomputable def certificates_15 : List (Origin 70 1271 × List Sat.Literal) :=
  [((.excluded 1186),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 60)]),
   ((.excluded 1187),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 69)]),
   ((.excluded 1188),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47)]),
   ((.excluded 1189),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 60),(.pos 69)]),
   ((.excluded 1190),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 60)]),
   ((.excluded 1191),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 69)]),
   ((.excluded 1192),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43)]),
   ((.excluded 1193),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 58),(.pos 62)]),
   ((.excluded 1194),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 58),(.pos 62)]),
   ((.excluded 1195),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 58),(.pos 69)]),
   ((.excluded 1196),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 58)]),
   ((.excluded 1197),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 58),(.pos 69)]),
   ((.excluded 1198),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 58)]),
   ((.excluded 1199),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 58),(.pos 62)]),
   ((.excluded 1200),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 58),(.pos 62)]),
   ((.excluded 1201),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 58),(.pos 62)]),
   ((.excluded 1202),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 58),(.pos 62)]),
   ((.excluded 1203),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 58),(.pos 69)]),
   ((.excluded 1204),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 58)]),
   ((.excluded 1205),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 58),(.pos 69)]),
   ((.excluded 1206),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 58)]),
   ((.excluded 1207),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 58),(.pos 69)]),
   ((.excluded 1208),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 58)]),
   ((.excluded 1209),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 58),(.pos 69)]),
   ((.excluded 1210),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 58)]),
   ((.excluded 1211),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 60),(.pos 69)]),
   ((.excluded 1212),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 69)]),
   ((.excluded 1213),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 60),(.pos 69)]),
   ((.excluded 1214),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 69)]),
   ((.excluded 1215),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 60),(.pos 69)]),
   ((.excluded 1216),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 69)]),
   ((.excluded 1217),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 60),(.pos 69)]),
   ((.excluded 1218),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 69)]),
   ((.excluded 1219),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 60),(.pos 69)]),
   ((.excluded 1220),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 69)]),
   ((.excluded 1221),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 60),(.pos 69)]),
   ((.excluded 1222),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 69)]),
   ((.excluded 1223),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 1224),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 60),(.pos 62)]),
   ((.excluded 1225),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 60),(.pos 65)]),
   ((.excluded 1226),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 60)]),
   ((.excluded 1227),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 62),(.pos 65)]),
   ((.excluded 1228),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 62)]),
   ((.excluded 1229),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 65)]),
   ((.excluded 1230),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47)]),
   ((.excluded 1231),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 1232),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 60),(.pos 62)]),
   ((.excluded 1233),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 60),(.pos 65)]),
   ((.excluded 1234),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 60)]),
   ((.excluded 1235),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 62),(.pos 65)]),
   ((.excluded 1236),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 62)]),
   ((.excluded 1237),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47),(.pos 65)]),
   ((.excluded 1238),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 47)]),
   ((.excluded 1239),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 1240),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 60),(.pos 62)]),
   ((.excluded 1241),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 60),(.pos 65)]),
   ((.excluded 1242),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 60)]),
   ((.excluded 1243),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 62),(.pos 65)]),
   ((.excluded 1244),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 62)]),
   ((.excluded 1245),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 65)]),
   ((.excluded 1246),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49)]),
   ((.excluded 1247),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 1248),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 60),(.pos 62)]),
   ((.excluded 1249),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 60),(.pos 65)]),
   ((.excluded 1250),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 60)]),
   ((.excluded 1251),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 62),(.pos 65)]),
   ((.excluded 1252),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 62)]),
   ((.excluded 1253),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 65)]),
   ((.excluded 1254),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40)]),
   ((.excluded 1255),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 1256),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 60),(.pos 62)]),
   ((.excluded 1257),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 60),(.pos 65)]),
   ((.excluded 1258),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 60)]),
   ((.excluded 1259),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 62),(.pos 65)]),
   ((.excluded 1260),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 62)]),
   ((.excluded 1261),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 65)]),
   ((.excluded 1262),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49)]),
   ((.excluded 1263),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 1264),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 60),(.pos 62)]),
   ((.excluded 1265),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 60),(.pos 65)]),
   ((.excluded 1266),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 60)]),
   ((.excluded 1267),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 62),(.pos 65)]),
   ((.excluded 1268),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 62)]),
   ((.excluded 1269),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 65)]),
   ((.excluded 1270),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35)])]

theorem certificates_15_valid : ∀ oc ∈ certificates_15,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.MaskOrigins.maskOrigins_sound (grid := (fun i : Fin 70 => N8R4.gridMasks.get i.val))
  have hchecks : ∀ i : Fin 85,
    Papers.RationalityTen.MatroidChecked.MaskOrigins.MaskOrigin (fun i : Fin 70 => N8R4.gridMasks.get i.val) (7 : Fin 8) old newIndex models
      (certificates_15.get i).1 (certificates_15.get i).2 := by
    refine (Fin.forall_fin_add (m := 42) (n := 43) _).2 ⟨?_, ?_⟩
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
    · refine (Fin.forall_fin_add (m := 21) (n := 22) _).2 ⟨?_, ?_⟩
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
      · refine (Fin.forall_fin_add (m := 11) (n := 11) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro oc hoc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hoc
  exact hchecks i



theorem witness_0 : ∀ j : Fin 128,
    let w : Fin 1271 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 1271 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 76)
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
    let w : Fin 1271 := ⟨128 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 1271 := ⟨128 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 76)
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
    let w : Fin 1271 := ⟨256 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 1271 := ⟨256 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 76)
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
    let w : Fin 1271 := ⟨384 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 1271 := ⟨384 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 76)
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
    let w : Fin 1271 := ⟨512 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 1271 := ⟨512 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 76)
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



theorem witness_5 : ∀ j : Fin 128,
    let w : Fin 1271 := ⟨640 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 1271 := ⟨640 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 76)
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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C76

end
end
end BundlePart0

