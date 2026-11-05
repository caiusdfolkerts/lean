module
public import SemanticParts.Batch12P00
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.Cases00
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.PublicRefutations.N7R3C18
public import MatroidChecked.PublicRefutations.N7R3C19
public import MatroidChecked.PublicRefutations.N7R3C20
public import MatroidChecked.PublicRefutations.N7R3C21
public import MatroidChecked.PublicRefutations.N7R3C22
public import MatroidChecked.PublicRefutations.N7R3C23
public import MatroidChecked.PublicRefutations.N7R3C24
public import MatroidChecked.PublicRefutations.N7R4C0
public import MatroidChecked.PublicRefutations.N7R4C1
public import MatroidChecked.PublicRefutations.N7R4C10
public import MatroidChecked.PublicRefutations.N7R4C11
public import MatroidChecked.PublicRefutations.N7R4C12
public import MatroidChecked.PublicRefutations.N7R4C13
public import MatroidChecked.PublicRefutations.N7R4C14
public import MatroidChecked.PublicRefutations.N7R4C15
public import MatroidChecked.PublicRefutations.N7R4C16
public import MatroidChecked.PublicRefutations.N7R4C17
public import MatroidChecked.PublicRefutations.N7R4C2
public import MatroidChecked.PublicRefutations.N7R4C3
public import MatroidChecked.PublicRefutations.N7R4C4
public import MatroidChecked.PublicRefutations.N7R4C5
public import MatroidChecked.PublicRefutations.N7R4C6
public import MatroidChecked.PublicRefutations.N7R4C7
public import MatroidChecked.PublicRefutations.N7R4C8
public import MatroidChecked.PublicRefutations.N7R4C9
public import MatroidChecked.PublicRefutations.N8R4C0
public import MatroidChecked.PublicRefutations.N8R4C1
public import MatroidChecked.PublicRefutations.N8R4C10
public import MatroidChecked.PublicRefutations.N8R4C11
public import MatroidChecked.PublicRefutations.N8R4C12
public import MatroidChecked.PublicRefutations.N8R4C13
public import MatroidChecked.PublicRefutations.N8R4C14
public import MatroidChecked.PublicRefutations.N8R4C15
public import MatroidChecked.PublicRefutations.N8R4C16
public import MatroidChecked.PublicRefutations.N8R4C17
public import MatroidChecked.PublicRefutations.N8R4C18
public import MatroidChecked.PublicRefutations.N8R4C19
public import MatroidChecked.PublicRefutations.N8R4C2
public import MatroidChecked.PublicRefutations.N8R4C20
public import MatroidChecked.PublicRefutations.N8R4C21
public import MatroidChecked.PublicRefutations.N8R4C22
public import MatroidChecked.PublicRefutations.N8R4C23
public import MatroidChecked.PublicRefutations.N8R4C24
public import MatroidChecked.PublicRefutations.N8R4C25
public import MatroidChecked.PublicRefutations.N8R4C26
public import MatroidChecked.PublicRefutations.N8R4C27
public import MatroidChecked.PublicRefutations.N8R4C28
public import MatroidChecked.PublicRefutations.N8R4C29
public import MatroidChecked.PublicRefutations.N8R4C3
public import MatroidChecked.PublicRefutations.N8R4C30
public import MatroidChecked.PublicRefutations.N8R4C31
public import MatroidChecked.PublicRefutations.N8R4C32
public import MatroidChecked.PublicRefutations.N8R4C33
public import MatroidChecked.PublicRefutations.N8R4C34
public import MatroidChecked.PublicRefutations.N8R4C35
public import MatroidChecked.PublicRefutations.N8R4C36
public import MatroidChecked.PublicRefutations.N8R4C37
public import MatroidChecked.PublicRefutations.N8R4C38
public import MatroidChecked.PublicRefutations.N8R4C39
public import MatroidChecked.PublicRefutations.N8R4C4
public import MatroidChecked.PublicRefutations.N8R4C40
public import MatroidChecked.PublicRefutations.N8R4C41
public import MatroidChecked.PublicRefutations.N8R4C42
public import MatroidChecked.PublicRefutations.N8R4C43
public import MatroidChecked.PublicRefutations.N8R4C44
public import MatroidChecked.PublicRefutations.N8R4C45
public import MatroidChecked.PublicRefutations.N8R4C46
public import MatroidChecked.PublicRefutations.N8R4C47
public import MatroidChecked.PublicRefutations.N8R4C48
public import MatroidChecked.PublicRefutations.N8R4C49
public import MatroidChecked.PublicRefutations.N8R4C5
public import MatroidChecked.PublicRefutations.N8R4C50
public import MatroidChecked.PublicRefutations.N8R4C51
public import MatroidChecked.PublicRefutations.N8R4C52
public import MatroidChecked.PublicRefutations.N8R4C53
public import MatroidChecked.PublicRefutations.N8R4C54
public import MatroidChecked.PublicRefutations.N8R4C55
public import MatroidChecked.PublicRefutations.N8R4C56
public import MatroidChecked.PublicRefutations.N8R4C58
public import MatroidChecked.PublicRefutations.N8R4C59
public import MatroidChecked.PublicRefutations.N8R4C6
public import MatroidChecked.PublicRefutations.N8R4C60
public import MatroidChecked.PublicRefutations.N8R4C63
public import MatroidChecked.PublicRefutations.N8R4C64
public import MatroidChecked.PublicRefutations.N8R4C65
public import MatroidChecked.PublicRefutations.N8R4C66
public import MatroidChecked.PublicRefutations.N8R4C67
public import MatroidChecked.PublicRefutations.N8R4C7
public import MatroidChecked.PublicRefutations.N8R4C71
public import MatroidChecked.PublicRefutations.N8R4C72
public import MatroidChecked.PublicRefutations.N8R4C73
public import MatroidChecked.PublicRefutations.N8R4C74
public import MatroidChecked.PublicRefutations.N8R4C8
public import MatroidChecked.PublicRefutations.N8R4C9


section BundlePart1
/- Source: MatroidChecked/SemanticParts/Cases09Part00/Checks02.lean -/



@[expose] public section
noncomputable section


set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C57


noncomputable def certificates_7 : List (Origin 70 517 × List Sat.Literal) :=
  [((.excluded 308),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 62),(.pos 65)]),
   ((.excluded 309),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 62),(.pos 65)]),
   ((.excluded 310),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 311),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 59),(.pos 65)]),
   ((.excluded 312),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 63),(.pos 65)]),
   ((.excluded 313),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 65)]),
   ((.excluded 314),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 315),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 59),(.pos 65)]),
   ((.excluded 316),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 63),(.pos 65)]),
   ((.excluded 317),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 65)]),
   ((.excluded 318),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 319),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 59),(.pos 65)]),
   ((.excluded 320),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 63),(.pos 65)]),
   ((.excluded 321),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 65)]),
   ((.excluded 322),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 323),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 65)]),
   ((.excluded 324),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 63),(.pos 65)]),
   ((.excluded 325),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 65)]),
   ((.excluded 326),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 63),(.pos 66)]),
   ((.excluded 327),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 328),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 60),(.pos 66)]),
   ((.excluded 329),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 61),(.pos 66)]),
   ((.excluded 330),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 66)]),
   ((.excluded 331),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 332),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 60),(.pos 66)]),
   ((.excluded 333),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 61),(.pos 66)]),
   ((.excluded 334),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 66)]),
   ((.excluded 335),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 58),(.pos 66)]),
   ((.excluded 336),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 337),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 60),(.pos 66)]),
   ((.excluded 338),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 61),(.pos 66)]),
   ((.excluded 339),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 66)]),
   ((.excluded 340),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 60),(.pos 66)]),
   ((.excluded 341),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 342),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 66)]),
   ((.excluded 343),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 61),(.pos 66)]),
   ((.excluded 344),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 61),(.pos 66)]),
   ((.excluded 345),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 58),(.pos 63),(.pos 66)]),
   ((.excluded 346),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 58),(.pos 66)]),
   ((.excluded 347),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 63),(.pos 66)]),
   ((.excluded 348),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 66)]),
   ((.excluded 349),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 58),(.pos 63),(.pos 66)]),
   ((.excluded 350),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 58),(.pos 66)]),
   ((.excluded 351),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 63),(.pos 66)]),
   ((.excluded 352),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 66)]),
   ((.excluded 353),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 58),(.pos 63),(.pos 66)]),
   ((.excluded 354),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 58),(.pos 66)]),
   ((.excluded 355),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 63),(.pos 66)]),
   ((.excluded 356),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 66)]),
   ((.excluded 357),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 63),(.pos 66)]),
   ((.excluded 358),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 66)]),
   ((.excluded 359),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 63),(.pos 66)]),
   ((.excluded 360),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 66)]),
   ((.excluded 361),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 59),(.pos 61)]),
   ((.excluded 362),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 61)]),
   ((.excluded 363),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 59),(.pos 61)]),
   ((.excluded 364),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 61)]),
   ((.excluded 365),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 58),(.pos 62)]),
   ((.excluded 366),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 62)]),
   ((.excluded 367),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 58),(.pos 62)]),
   ((.excluded 368),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 62)]),
   ((.excluded 369),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 58),(.pos 63)]),
   ((.excluded 370),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 58)]),
   ((.excluded 371),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 59),(.pos 63)]),
   ((.excluded 372),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 59)]),
   ((.excluded 373),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51),(.pos 63)]),
   ((.excluded 374),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 51)]),
   ((.excluded 375),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 58),(.pos 63)]),
   ((.excluded 376),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 58)]),
   ((.excluded 377),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 58),(.pos 63)]),
   ((.excluded 378),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 58)]),
   ((.excluded 379),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 59),(.pos 63)]),
   ((.excluded 380),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 59)]),
   ((.excluded 381),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 63)]),
   ((.excluded 382),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52)]),
   ((.excluded 383),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 59),(.pos 63)]),
   ((.excluded 384),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 59)]),
   ((.excluded 385),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 63)]),
   ((.excluded 386),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50)]),
   ((.excluded 387),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 59),(.pos 63)]),
   ((.excluded 388),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 63)]),
   ((.excluded 389),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 59),(.pos 63)]),
   ((.excluded 390),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 63)]),
   ((.excluded 391),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 58),(.pos 63)]),
   ((.excluded 392),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 63)]),
   ((.excluded 393),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 58),(.pos 63)]),
   ((.excluded 394),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 63)]),
   ((.excluded 395),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 58),(.pos 63)]),
   ((.excluded 396),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 59),(.pos 63)]),
   ((.excluded 397),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 63)]),
   ((.excluded 398),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 58),(.pos 63)]),
   ((.excluded 399),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 63)]),
   ((.excluded 400),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 59),(.pos 63)]),
   ((.excluded 401),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 63)]),
   ((.excluded 402),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 63)]),
   ((.excluded 403),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 63)]),
   ((.excluded 404),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 59),(.pos 67)]),
   ((.excluded 405),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 59)]),
   ((.excluded 406),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 60),(.pos 62)]),
   ((.excluded 407),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 60)]),
   ((.excluded 408),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 60),(.pos 62)]),
   ((.excluded 409),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 60)]),
   ((.excluded 410),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 411),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 58),(.pos 62)]),
   ((.excluded 412),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 58),(.pos 67)]),
   ((.excluded 413),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 58)]),
   ((.excluded 414),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 62),(.pos 67)]),
   ((.excluded 415),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 62)]),
   ((.excluded 416),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51),(.pos 67)]),
   ((.excluded 417),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 51)]),
   ((.excluded 418),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 419),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 58),(.pos 62)]),
   ((.excluded 420),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 58),(.pos 67)]),
   ((.excluded 421),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 58)]),
   ((.excluded 422),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 62),(.pos 67)]),
   ((.excluded 423),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 62)]),
   ((.excluded 424),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51),(.pos 67)]),
   ((.excluded 425),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 51)]),
   ((.excluded 426),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 58),(.pos 67)]),
   ((.excluded 427),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 58)]),
   ((.excluded 428),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 58),(.pos 62)]),
   ((.excluded 429),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 58)]),
   ((.excluded 430),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 58),(.pos 62)]),
   ((.excluded 431),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 58)]),
   ((.excluded 432),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 433),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 58),(.pos 62)]),
   ((.excluded 434),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 58),(.pos 67)]),
   ((.excluded 435),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 58)])]

theorem certificates_7_valid : ∀ oc ∈ certificates_7,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.FastSemanticChecks.FastOrigin U (7 : Fin 8) old newIndex models
      (certificates_7.get i).1 (certificates_7.get i).2 := by
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



noncomputable def certificates_8 : List (Origin 70 517 × List Sat.Literal) :=
  [((.excluded 436),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 437),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 62)]),
   ((.excluded 438),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 67)]),
   ((.excluded 439),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58)]),
   ((.excluded 440),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 61),(.pos 67)]),
   ((.excluded 441),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 62),(.pos 67)]),
   ((.excluded 442),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 67)]),
   ((.excluded 443),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 60),(.pos 61)]),
   ((.excluded 444),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 61)]),
   ((.excluded 445),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 60),(.pos 61)]),
   ((.excluded 446),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 61)]),
   ((.excluded 447),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 60),(.pos 62)]),
   ((.excluded 448),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 60)]),
   ((.excluded 449),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 62)]),
   ((.excluded 450),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53)]),
   ((.excluded 451),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 60),(.pos 62)]),
   ((.excluded 452),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 60)]),
   ((.excluded 453),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 62)]),
   ((.excluded 454),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49)]),
   ((.excluded 455),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 62),(.pos 67)]),
   ((.excluded 456),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 62),(.pos 67)]),
   ((.excluded 457),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 60),(.pos 62)]),
   ((.excluded 458),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 62)]),
   ((.excluded 459),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 60),(.pos 62)]),
   ((.excluded 460),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 62)]),
   ((.excluded 461),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 60),(.pos 62)]),
   ((.excluded 462),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 62)]),
   ((.excluded 463),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 62)]),
   ((.excluded 464),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 62)]),
   ((.excluded 465),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 59),(.pos 61)]),
   ((.excluded 466),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 59)]),
   ((.excluded 467),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 59),(.pos 61)]),
   ((.excluded 468),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 59)]),
   ((.excluded 469),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 60),(.pos 61)]),
   ((.excluded 470),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 60)]),
   ((.excluded 471),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53),(.pos 61)]),
   ((.excluded 472),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 53)]),
   ((.excluded 473),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 60),(.pos 61)]),
   ((.excluded 474),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 60)]),
   ((.excluded 475),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 61)]),
   ((.excluded 476),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53)]),
   ((.excluded 477),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 60),(.pos 61)]),
   ((.excluded 478),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 60)]),
   ((.excluded 479),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 60),(.pos 61)]),
   ((.excluded 480),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 60)]),
   ((.excluded 481),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 60),(.pos 61)]),
   ((.excluded 482),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 60)]),
   ((.excluded 483),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 61)]),
   ((.excluded 484),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60)]),
   ((.excluded 485),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 486),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 59),(.pos 61)]),
   ((.excluded 487),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 59),(.pos 67)]),
   ((.excluded 488),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 59)]),
   ((.excluded 489),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 61),(.pos 67)]),
   ((.excluded 490),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 61)]),
   ((.excluded 491),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 67)]),
   ((.excluded 492),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52)]),
   ((.excluded 493),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 494),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 59),(.pos 61)]),
   ((.excluded 495),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 59),(.pos 67)]),
   ((.excluded 496),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 59)]),
   ((.excluded 497),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 61),(.pos 67)]),
   ((.excluded 498),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 61)]),
   ((.excluded 499),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 67)]),
   ((.excluded 500),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48)]),
   ((.excluded 501),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 502),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 59),(.pos 61)]),
   ((.excluded 503),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 59),(.pos 67)]),
   ((.excluded 504),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 59)]),
   ((.excluded 505),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 61),(.pos 67)]),
   ((.excluded 506),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 61)]),
   ((.excluded 507),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 67)]),
   ((.excluded 508),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52)]),
   ((.excluded 509),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 510),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 61)]),
   ((.excluded 511),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 67)]),
   ((.excluded 512),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59)]),
   ((.excluded 513),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 61),(.pos 67)]),
   ((.excluded 514),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 61)]),
   ((.excluded 515),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 67)]),
   ((.excluded 516),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35)])]

theorem certificates_8_valid : ∀ oc ∈ certificates_8,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  have hchecks : ∀ i : Fin 81,
    Papers.RationalityTen.MatroidChecked.FastSemanticChecks.FastOrigin U (7 : Fin 8) old newIndex models
      (certificates_8.get i).1 (certificates_8.get i).2 := by
    refine (Fin.forall_fin_add (m := 40) (n := 41) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 20) (n := 20) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 10) (n := 10) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 10) (n := 10) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 20) (n := 21) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 10) (n := 10) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
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
  intro oc hoc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hoc
  exact hchecks i



theorem witness_0 : ∀ j : Fin 128,
    let w : Fin 517 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 517 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 57)
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
    let w : Fin 517 := ⟨128 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 517 := ⟨128 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 57)
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
    let w : Fin 517 := ⟨256 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 517 := ⟨256 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 57)
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
    let w : Fin 517 := ⟨384 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 517 := ⟨384 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 57)
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



theorem witness_4 : ∀ j : Fin 5,
    let w : Fin 517 := ⟨512 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 5,
      let w : Fin 517 := ⟨512 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 57)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
    · decide +kernel
    · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.bitsetRawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C57

end
end
end BundlePart1

