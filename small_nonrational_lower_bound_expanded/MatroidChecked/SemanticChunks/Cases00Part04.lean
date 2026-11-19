module
public import MatroidCatalogue.Definitions
public import MatroidCases.N6R3C8
import all MatroidCases.N6R3C8
public import MatroidCases.N6R4C0
import all MatroidCases.N6R4C0
public import MatroidCases.N6R4C1
import all MatroidCases.N6R4C1
public import MatroidCases.N6R4C2
import all MatroidCases.N6R4C2
public import MatroidCases.N6R4C3
import all MatroidCases.N6R4C3
public import MatroidCases.N7R1C0
import all MatroidCases.N7R1C0
public import MatroidCases.N7R2C0
import all MatroidCases.N7R2C0

@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N6R3C8Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C8

abbrev U := N6R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R3.family 8
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14)))) (.node 7 (.node 6 (.leaf 15) (.leaf 16)) (.node 8 (.leaf 17) (.node 9 (.leaf 18) (.leaf 19)))))
noncomputable def newIndex (i : Fin 10) : Fin 20 := Fin.ofNat 20 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (948,18,16308432)) (.node 2 (.leaf (874,18,16308418)) (.leaf (990,21,16275665)))) (.node 5 (.node 4 (.leaf (766,21,16272081)) (.leaf (510,21,16271185))) (.node 6 (.leaf (1022,23,16341192)) (.leaf (729,18,16308250))))) (.node 11 (.node 9 (.node 8 (.leaf (455,18,16306458)) (.leaf (927,21,16263401))) (.node 10 (.leaf (863,21,16263373)) (.leaf (991,23,16339491)))) (.node 13 (.node 12 (.leaf (63,18,16288538)) (.leaf (955,21,16263961))) (.node 14 (.leaf (943,21,16263513)) (.leaf (959,23,16325400)))))) (.node 23 (.node 19 (.node 17 (.node 16 (.leaf (1011,21,16274713)) (.leaf (507,21,16270989))) (.node 18 (.leaf (1019,23,16341059)) (.leaf (509,21,16271017)))) (.node 21 (.node 20 (.leaf (511,23,16322915)) (.leaf (1005,21,16275609))) (.node 22 (.leaf (893,21,16272025)) (.leaf (1021,23,16341080))))) (.node 27 (.node 25 (.node 24 (.leaf (751,21,16270541)) (.leaf (1007,23,16339715))) (.node 26 (.leaf (887,21,16270681)) (.leaf (895,23,16325379)))) (.node 29 (.node 28 (.leaf (759,21,16270569)) (.leaf (1015,23,16339736))) (.node 30 (.leaf (767,23,16325155)) (.leaf (1023,24,16434824)))))))

noncomputable def models (i : Fin 31) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 31) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 31) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 20, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 20, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C8

/- Source: MatroidCatalogue/Cases/N6R3C8Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C8


noncomputable def certificates_0 : List (Origin 20 31 × List Sat.Literal) :=
  [((.fixed 0),[(.pos 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.exchange 10 2 1),[(.neg 10),(.neg 2),(.pos 11),(.pos 13)]),
   ((.exchange 10 3 0),[(.neg 10),(.neg 3),(.pos 12),(.pos 14)]),
   ((.exchange 10 5 1),[(.neg 10),(.neg 5),(.pos 11),(.pos 16)]),
   ((.exchange 10 6 0),[(.neg 10),(.neg 6),(.pos 12),(.pos 17)]),
   ((.exchange 10 7 1),[(.neg 10),(.neg 7),(.pos 13),(.pos 16)]),
   ((.exchange 10 8 0),[(.neg 10),(.neg 8),(.pos 14),(.pos 17)]),
   ((.exchange 10 19 1),[(.neg 19),(.neg 10),(.pos 13),(.pos 16)]),
   ((.exchange 11 4 2),[(.neg 11),(.neg 4),(.pos 10),(.pos 16)]),
   ((.exchange 11 6 0),[(.neg 11),(.neg 6),(.pos 12),(.pos 18)]),
   ((.exchange 11 14 0),[(.neg 14),(.neg 11),(.pos 12),(.pos 15)]),
   ((.exchange 11 17 0),[(.neg 17),(.neg 11),(.pos 12),(.pos 18)]),
   ((.exchange 11 19 0),[(.neg 19),(.neg 11),(.pos 15),(.pos 18)]),
   ((.exchange 12 1 2),[(.neg 12),(.neg 1),(.pos 10),(.pos 14)]),
   ((.exchange 12 5 1),[(.neg 12),(.neg 5),(.pos 11),(.pos 18)]),
   ((.exchange 12 8 2),[(.neg 12),(.neg 8),(.pos 14),(.pos 17)]),
   ((.exchange 12 9 1),[(.neg 12),(.neg 9),(.pos 15),(.pos 18)]),
   ((.exchange 12 13 1),[(.neg 13),(.neg 12),(.pos 11),(.pos 15)]),
   ((.exchange 12 13 2),[(.neg 13),(.neg 12),(.pos 10),(.pos 14)]),
   ((.exchange 13 3 0),[(.neg 13),(.neg 3),(.pos 14),(.pos 15)]),
   ((.exchange 13 4 3),[(.neg 13),(.neg 4),(.pos 10),(.pos 16)]),
   ((.exchange 13 8 0),[(.neg 13),(.neg 8),(.pos 14),(.pos 19)]),
   ((.exchange 13 9 0),[(.neg 13),(.neg 9),(.pos 15),(.pos 19)]),
   ((.exchange 13 18 3),[(.neg 18),(.neg 13),(.pos 11),(.pos 16)]),
   ((.exchange 14 0 3),[(.neg 14),(.neg 0),(.pos 10),(.pos 12)]),
   ((.exchange 14 2 1),[(.neg 14),(.neg 2),(.pos 13),(.pos 15)]),
   ((.exchange 14 4 3),[(.neg 14),(.neg 4),(.pos 10),(.pos 17)]),
   ((.exchange 14 7 1),[(.neg 14),(.neg 7),(.pos 13),(.pos 19)]),
   ((.exchange 14 9 1),[(.neg 14),(.neg 9),(.pos 15),(.pos 19)]),
   ((.exchange 14 16 1),[(.neg 16),(.neg 14),(.pos 13),(.pos 19)]),
   ((.exchange 15 5 3),[(.neg 15),(.neg 5),(.pos 11),(.pos 18)]),
   ((.exchange 15 17 2),[(.neg 17),(.neg 15),(.pos 14),(.pos 19)]),
   ((.exchange 15 17 3),[(.neg 17),(.neg 15),(.pos 12),(.pos 18)]),
   ((.exchange 16 0 4),[(.neg 16),(.neg 0),(.pos 10),(.pos 11)]),
   ((.exchange 16 1 4),[(.neg 16),(.neg 1),(.pos 10),(.pos 13)]),
   ((.exchange 16 6 0),[(.neg 16),(.neg 6),(.pos 17),(.pos 18)]),
   ((.exchange 16 8 0),[(.neg 16),(.neg 8),(.pos 17),(.pos 19)]),
   ((.exchange 16 9 0),[(.neg 16),(.neg 9),(.pos 18),(.pos 19)]),
   ((.exchange 17 1 4),[(.neg 17),(.neg 1),(.pos 10),(.pos 14)]),
   ((.exchange 17 5 1),[(.neg 17),(.neg 5),(.pos 16),(.pos 18)]),
   ((.exchange 18 0 4),[(.neg 18),(.neg 0),(.pos 11),(.pos 12)]),
   ((.exchange 18 2 4),[(.neg 18),(.neg 2),(.pos 11),(.pos 15)]),
   ((.exchange 18 4 2),[(.neg 18),(.neg 4),(.pos 16),(.pos 17)]),
   ((.exchange 18 7 2),[(.neg 18),(.neg 7),(.pos 16),(.pos 19)]),
   ((.exchange 18 10 2),[(.neg 18),(.neg 10),(.pos 16),(.pos 17)]),
   ((.exchange 18 10 4),[(.neg 18),(.neg 10),(.pos 11),(.pos 12)]),
   ((.exchange 18 14 2),[(.neg 18),(.neg 14),(.pos 17),(.pos 19)]),
   ((.exchange 19 1 4),[(.neg 19),(.neg 1),(.pos 13),(.pos 14)]),
   ((.exchange 19 2 4),[(.neg 19),(.neg 2),(.pos 13),(.pos 15)]),
   ((.exchange 19 3 4),[(.neg 19),(.neg 3),(.pos 14),(.pos 15)]),
   ((.exchange 19 5 3),[(.neg 19),(.neg 5),(.pos 16),(.pos 18)]),
   ((.exchange 19 6 3),[(.neg 19),(.neg 6),(.pos 17),(.pos 18)]),
   ((.exchange 19 10 4),[(.neg 19),(.neg 10),(.pos 13),(.pos 14)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 0),[(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.neg 14),(.neg 12),(.pos 10),(.pos 11),(.pos 13),(.pos 16)]),
   ((.excluded 1),[(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.neg 13),(.neg 11),(.pos 10),(.pos 12),(.pos 14),(.pos 17)]),
   ((.excluded 2),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 15)]),
   ((.excluded 3),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 18)]),
   ((.excluded 4),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 19)]),
   ((.excluded 5),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10)]),
   ((.excluded 6),[(.neg 19),(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.neg 10),(.pos 11),(.pos 12),(.pos 15),(.pos 18)]),
   ((.excluded 7),[(.neg 18),(.neg 17),(.neg 16),(.neg 12),(.neg 11),(.neg 10),(.pos 13),(.pos 14),(.pos 15),(.pos 19)]),
   ((.excluded 8),[(.neg 19),(.neg 18),(.neg 17),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 15),(.pos 16)]),
   ((.excluded 9),[(.neg 19),(.neg 18),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 15),(.pos 17)]),
   ((.excluded 10),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 15)]),
   ((.excluded 11),[(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 12),[(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.pos 12),(.pos 16)]),
   ((.excluded 13),[(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14),(.pos 16)]),
   ((.excluded 14),[(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 16)]),
   ((.excluded 15),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 11),(.neg 10),(.pos 12),(.pos 13)]),
   ((.excluded 16),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.pos 12),(.pos 19)]),
   ((.excluded 17),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.pos 12)]),
   ((.excluded 18),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 10),(.pos 11),(.pos 19)]),
   ((.excluded 19),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 19)]),
   ((.excluded 20),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 13),(.neg 12),(.neg 10),(.pos 11),(.pos 14)]),
   ((.excluded 21),[(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 10),(.pos 11),(.pos 17)]),
   ((.excluded 22),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 10),(.pos 11)]),
   ((.excluded 23),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14),(.pos 18)]),
   ((.excluded 24),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14)]),
   ((.excluded 25),[(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13),(.pos 17)]),
   ((.excluded 26),[(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 17)]),
   ((.excluded 27),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13),(.pos 18)]),
   ((.excluded 28),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13)]),
   ((.excluded 29),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 18)]),
   ((.excluded 30),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 31,
    let w : Fin 31 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C8

/- Source: MatroidCatalogue/Cases/N6R3C8Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C8

noncomputable def certificates : List (Origin 20 31 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 31,
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 31) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 3)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 3, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N6R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R3C8.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R3C8.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 3 (target w),family_mem 6 3 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C8

/- Source: MatroidCatalogue/Cases/N6R4C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C0

abbrev U := N6R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R4.family 0
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 5) (.leaf 6)) (.node 3 (.leaf 7) (.node 4 (.leaf 8) (.leaf 9)))) (.node 7 (.node 6 (.leaf 10) (.leaf 11)) (.node 8 (.leaf 12) (.node 9 (.leaf 13) (.leaf 14)))))
noncomputable def newIndex (i : Fin 10) : Fin 15 := Fin.ofNat 15 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (512,0,16341192)) (.node 2 (.leaf (384,1,16373896)) (.leaf (896,2,16373896)))) (.node 5 (.node 4 (.leaf (96,1,16373000)) (.leaf (608,2,16373000))) (.node 6 (.leaf (480,4,16406152)) (.leaf (992,5,16406152))))) (.node 11 (.node 9 (.node 8 (.leaf (12,1,16362248)) (.leaf (524,2,16362248))) (.node 10 (.leaf (396,4,16398984)) (.leaf (908,5,16398984)))) (.node 13 (.node 12 (.leaf (108,4,16397640)) (.leaf (620,5,16397640))) (.node 14 (.leaf (492,9,16434824)) (.leaf (1004,10,16434824))))))

noncomputable def models (i : Fin 15) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 15) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 15) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 15, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 15, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C0

/- Source: MatroidCatalogue/Cases/N6R4C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C0


noncomputable def certificates_0 : List (Origin 15 15 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.exchange 3 8 4),[(.neg 8),(.neg 3),(.pos 0),(.pos 7)]),
   ((.exchange 3 11 3),[(.neg 11),(.neg 3),(.pos 1),(.pos 10)]),
   ((.exchange 3 13 2),[(.neg 13),(.neg 3),(.pos 2),(.pos 12)]),
   ((.exchange 4 7 4),[(.neg 7),(.neg 4),(.pos 0),(.pos 8)]),
   ((.exchange 4 10 3),[(.neg 10),(.neg 4),(.pos 1),(.pos 11)]),
   ((.exchange 4 12 2),[(.neg 12),(.neg 4),(.pos 2),(.pos 13)]),
   ((.exchange 5 3 5),[(.neg 5),(.neg 3),(.pos 0),(.pos 1)]),
   ((.exchange 6 3 5),[(.neg 6),(.neg 3),(.pos 0),(.pos 2)]),
   ((.exchange 9 3 5),[(.neg 9),(.neg 3),(.pos 1),(.pos 2)]),
   (.newPoint,[(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 0),[(.neg 14),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11),(.pos 12),(.pos 13)]),
   ((.excluded 1),[(.neg 13),(.neg 12),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11),(.pos 14)]),
   ((.excluded 2),[(.neg 14),(.neg 13),(.neg 12),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11)]),
   ((.excluded 3),[(.neg 11),(.neg 10),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 4),[(.neg 14),(.neg 11),(.neg 10),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 12),(.pos 13)]),
   ((.excluded 5),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 14)]),
   ((.excluded 6),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 7),[(.neg 8),(.neg 7),(.pos 5),(.pos 6),(.pos 9),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 8),[(.neg 14),(.neg 8),(.neg 7),(.pos 5),(.pos 6),(.pos 9),(.pos 10),(.pos 11),(.pos 12),(.pos 13)]),
   ((.excluded 9),[(.neg 13),(.neg 12),(.neg 8),(.neg 7),(.pos 5),(.pos 6),(.pos 9),(.pos 10),(.pos 11),(.pos 14)]),
   ((.excluded 10),[(.neg 14),(.neg 13),(.neg 12),(.neg 8),(.neg 7),(.pos 5),(.pos 6),(.pos 9),(.pos 10),(.pos 11)]),
   ((.excluded 11),[(.neg 11),(.neg 10),(.neg 8),(.neg 7),(.pos 5),(.pos 6),(.pos 9),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 12),[(.neg 14),(.neg 11),(.neg 10),(.neg 8),(.neg 7),(.pos 5),(.pos 6),(.pos 9),(.pos 12),(.pos 13)]),
   ((.excluded 13),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 8),(.neg 7),(.pos 5),(.pos 6),(.pos 9),(.pos 14)]),
   ((.excluded 14),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 8),(.neg 7),(.pos 5),(.pos 6),(.pos 9)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 15,
    let w : Fin 15 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 4 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 4 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C0

/- Source: MatroidCatalogue/Cases/N6R4C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C0

noncomputable def certificates : List (Origin 15 15 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 15,
    target w < MatroidCatalogue.count 6 4 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 15) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 4)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 4, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N6R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R4C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R4C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 4 (target w),family_mem 6 4 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C0

/- Source: MatroidCatalogue/Cases/N6R4C1Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C1

abbrev U := N6R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R4.family 1
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 5) (.leaf 6)) (.node 3 (.leaf 7) (.node 4 (.leaf 8) (.leaf 9)))) (.node 7 (.node 6 (.leaf 10) (.leaf 11)) (.node 8 (.leaf 12) (.node 9 (.leaf 13) (.leaf 14)))))
noncomputable def newIndex (i : Fin 10) : Fin 15 := Fin.ofNat 15 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (768,2,16308432)) (.leaf (640,2,16308418))) (.node 3 (.leaf (384,2,16308250)) (.leaf (896,3,16373896)))) (.node 6 (.node 5 (.leaf (112,4,16306458)) (.leaf (880,6,16406152))) (.node 7 (.leaf (752,6,16406145)) (.node 8 (.leaf (496,6,16406033)) (.leaf (1008,7,16406152)))))) (.node 14 (.node 11 (.node 10 (.leaf (14,4,16288538)) (.leaf (782,6,16398984))) (.node 12 (.leaf (654,6,16398977)) (.node 13 (.leaf (398,6,16398865)) (.leaf (910,7,16398984))))) (.node 16 (.node 15 (.leaf (126,11,16434824)) (.leaf (894,12,16434824))) (.node 17 (.leaf (766,12,16434817)) (.node 18 (.leaf (510,12,16434705)) (.leaf (1022,13,16434824)))))))

noncomputable def models (i : Fin 19) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 19) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 19) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 15, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 15, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C1

/- Source: MatroidCatalogue/Cases/N6R4C1Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C1


noncomputable def certificates_0 : List (Origin 15 19 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.exchange 2 7 4),[(.neg 7),(.neg 2),(.pos 0),(.pos 6)]),
   ((.exchange 2 8 4),[(.neg 8),(.neg 2),(.pos 0),(.pos 6)]),
   ((.exchange 2 10 3),[(.neg 10),(.neg 2),(.pos 1),(.pos 9)]),
   ((.exchange 2 11 3),[(.neg 11),(.neg 2),(.pos 1),(.pos 9)]),
   ((.exchange 3 6 4),[(.neg 6),(.neg 3),(.pos 0),(.pos 7)]),
   ((.exchange 3 8 4),[(.neg 8),(.neg 3),(.pos 0),(.pos 7)]),
   ((.exchange 3 9 3),[(.neg 9),(.neg 3),(.pos 1),(.pos 10)]),
   ((.exchange 3 11 3),[(.neg 11),(.neg 3),(.pos 1),(.pos 10)]),
   ((.exchange 4 6 4),[(.neg 6),(.neg 4),(.pos 0),(.pos 8)]),
   ((.exchange 4 7 4),[(.neg 7),(.neg 4),(.pos 0),(.pos 8)]),
   ((.exchange 4 9 3),[(.neg 9),(.neg 4),(.pos 1),(.pos 11)]),
   ((.exchange 4 10 3),[(.neg 10),(.neg 4),(.pos 1),(.pos 11)]),
   ((.exchange 5 2 5),[(.neg 5),(.neg 2),(.pos 0),(.pos 1)]),
   ((.exchange 12 4 0),[(.neg 12),(.neg 4),(.pos 13),(.pos 14)]),
   ((.exchange 13 3 1),[(.neg 13),(.neg 3),(.pos 12),(.pos 14)]),
   ((.exchange 14 2 2),[(.neg 14),(.neg 2),(.pos 12),(.pos 13)]),
   (.newPoint,[(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 0),[(.neg 14),(.neg 13),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11),(.pos 12)]),
   ((.excluded 1),[(.neg 14),(.neg 12),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11),(.pos 13)]),
   ((.excluded 2),[(.neg 13),(.neg 12),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11),(.pos 14)]),
   ((.excluded 3),[(.neg 14),(.neg 13),(.neg 12),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11)]),
   ((.excluded 4),[(.neg 11),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 5),[(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 12)]),
   ((.excluded 6),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 13)]),
   ((.excluded 7),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 14)]),
   ((.excluded 8),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8)]),
   ((.excluded 9),[(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 9),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 10),[(.neg 14),(.neg 13),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 9),(.pos 10),(.pos 11),(.pos 12)]),
   ((.excluded 11),[(.neg 14),(.neg 12),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 9),(.pos 10),(.pos 11),(.pos 13)]),
   ((.excluded 12),[(.neg 13),(.neg 12),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 9),(.pos 10),(.pos 11),(.pos 14)]),
   ((.excluded 13),[(.neg 14),(.neg 13),(.neg 12),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 9),(.pos 10),(.pos 11)]),
   ((.excluded 14),[(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 15),[(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 12)]),
   ((.excluded 16),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 13)]),
   ((.excluded 17),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 14)]),
   ((.excluded 18),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.pos 5)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 19,
    let w : Fin 19 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 4 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 4 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C1

/- Source: MatroidCatalogue/Cases/N6R4C1Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C1

noncomputable def certificates : List (Origin 15 19 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 19,
    target w < MatroidCatalogue.count 6 4 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 19) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 4)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 4, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N6R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R4C1.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R4C1.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 4 (target w),family_mem 6 4 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C1

/- Source: MatroidCatalogue/Cases/N6R4C2Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C2

abbrev U := N6R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R4.family 2
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 5) (.leaf 6)) (.node 3 (.leaf 7) (.node 4 (.leaf 8) (.leaf 9)))) (.node 7 (.node 6 (.leaf 10) (.leaf 11)) (.node 8 (.leaf 12) (.node 9 (.leaf 13) (.leaf 14)))))
noncomputable def newIndex (i : Fin 10) : Fin 15 := Fin.ofNat 15 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (832,5,16308432)) (.node 2 (.leaf (672,5,16308418)) (.leaf (480,6,16275665)))) (.node 5 (.node 4 (.leaf (992,7,16341192)) (.leaf (400,5,16308250))) (.node 6 (.leaf (112,5,16306458)) (.leaf (496,7,16339491))))) (.node 10 (.node 8 (.leaf (720,6,16275609)) (.node 9 (.leaf (976,7,16341080)) (.leaf (752,7,16339715)))) (.node 12 (.node 11 (.leaf (816,6,16274713)) (.leaf (944,7,16341059))) (.node 13 (.leaf (880,7,16339736)) (.leaf (1008,8,16406152)))))) (.node 21 (.node 17 (.node 15 (.leaf (15,9,16288538)) (.node 16 (.leaf (847,12,16325400)) (.leaf (687,12,16325379)))) (.node 19 (.node 18 (.leaf (495,14,16434824)) (.leaf (1007,15,16434824))) (.node 20 (.leaf (415,12,16325155)) (.leaf (127,12,16322915))))) (.node 25 (.node 23 (.node 22 (.leaf (511,15,16433690)) (.leaf (735,14,16434768))) (.node 24 (.leaf (991,15,16434768)) (.leaf (767,15,16433858)))) (.node 27 (.node 26 (.leaf (831,14,16433872)) (.leaf (959,15,16434754))) (.node 28 (.leaf (895,15,16433872)) (.leaf (1023,16,16434824)))))))

noncomputable def models (i : Fin 29) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 29) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 29) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 15, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 15, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C2

/- Source: MatroidCatalogue/Cases/N6R4C2Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C2


noncomputable def certificates_0 : List (Origin 15 29 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.exchange 1 6 4),[(.neg 6),(.neg 1),(.pos 0),(.pos 5)]),
   ((.exchange 1 7 4),[(.neg 7),(.neg 1),(.pos 0),(.pos 5)]),
   ((.exchange 1 8 4),[(.neg 8),(.neg 1),(.pos 0),(.pos 5)]),
   ((.exchange 2 5 4),[(.neg 5),(.neg 2),(.pos 0),(.pos 6)]),
   ((.exchange 3 5 4),[(.neg 5),(.neg 3),(.pos 0),(.pos 7)]),
   ((.exchange 4 5 4),[(.neg 5),(.neg 4),(.pos 0),(.pos 8)]),
   ((.exchange 9 3 1),[(.neg 9),(.neg 3),(.pos 10),(.pos 12)]),
   ((.exchange 9 4 0),[(.neg 9),(.neg 4),(.pos 11),(.pos 13)]),
   ((.exchange 9 7 1),[(.neg 9),(.neg 7),(.pos 10),(.pos 12)]),
   ((.exchange 9 8 0),[(.neg 9),(.neg 8),(.pos 11),(.pos 13)]),
   ((.exchange 9 14 1),[(.neg 14),(.neg 9),(.pos 10),(.pos 12)]),
   ((.exchange 10 2 2),[(.neg 10),(.neg 2),(.pos 9),(.pos 12)]),
   ((.exchange 10 4 0),[(.neg 10),(.neg 4),(.pos 11),(.pos 14)]),
   ((.exchange 10 6 2),[(.neg 10),(.neg 6),(.pos 9),(.pos 12)]),
   ((.exchange 10 8 0),[(.neg 10),(.neg 8),(.pos 11),(.pos 14)]),
   ((.exchange 10 13 2),[(.neg 13),(.neg 10),(.pos 9),(.pos 12)]),
   ((.exchange 11 2 2),[(.neg 11),(.neg 2),(.pos 9),(.pos 13)]),
   ((.exchange 11 3 1),[(.neg 11),(.neg 3),(.pos 10),(.pos 14)]),
   ((.exchange 11 6 2),[(.neg 11),(.neg 6),(.pos 9),(.pos 13)]),
   ((.exchange 12 1 3),[(.neg 12),(.neg 1),(.pos 9),(.pos 10)]),
   ((.exchange 12 4 0),[(.neg 12),(.neg 4),(.pos 13),(.pos 14)]),
   ((.exchange 12 5 3),[(.neg 12),(.neg 5),(.pos 9),(.pos 10)]),
   ((.exchange 12 8 0),[(.neg 12),(.neg 8),(.pos 13),(.pos 14)]),
   ((.exchange 13 1 3),[(.neg 13),(.neg 1),(.pos 9),(.pos 11)]),
   ((.exchange 13 3 1),[(.neg 13),(.neg 3),(.pos 12),(.pos 14)]),
   ((.exchange 13 10 3),[(.neg 13),(.neg 10),(.pos 9),(.pos 11)]),
   ((.exchange 14 1 3),[(.neg 14),(.neg 1),(.pos 10),(.pos 11)]),
   ((.exchange 14 2 2),[(.neg 14),(.neg 2),(.pos 12),(.pos 13)]),
   ((.exchange 14 5 3),[(.neg 14),(.neg 5),(.pos 10),(.pos 11)]),
   ((.exchange 14 6 2),[(.neg 14),(.neg 6),(.pos 12),(.pos 13)]),
   (.newPoint,[(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 0),[(.neg 14),(.neg 13),(.neg 11),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 12)]),
   ((.excluded 1),[(.neg 14),(.neg 12),(.neg 10),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 11),(.pos 13)]),
   ((.excluded 2),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 14)]),
   ((.excluded 3),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 4),[(.neg 13),(.neg 12),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 10),(.pos 11),(.pos 14)]),
   ((.excluded 5),[(.neg 11),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 6),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 14)]),
   ((.excluded 7),[(.neg 14),(.neg 12),(.neg 11),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 10),(.pos 13)]),
   ((.excluded 8),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 10)]),
   ((.excluded 9),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 13)]),
   ((.excluded 10),[(.neg 14),(.neg 13),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 11),(.pos 12)]),
   ((.excluded 11),[(.neg 14),(.neg 13),(.neg 12),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 11)]),
   ((.excluded 12),[(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 12)]),
   ((.excluded 13),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.pos 5),(.pos 6),(.pos 7),(.pos 8)]),
   ((.excluded 14),[(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 9),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 15),[(.neg 14),(.neg 13),(.neg 11),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 9),(.pos 10),(.pos 12)]),
   ((.excluded 16),[(.neg 14),(.neg 12),(.neg 10),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 9),(.pos 11),(.pos 13)]),
   ((.excluded 17),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 9),(.pos 14)]),
   ((.excluded 18),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 9)]),
   ((.excluded 19),[(.neg 13),(.neg 12),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 10),(.pos 11),(.pos 14)]),
   ((.excluded 20),[(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 21),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 14)]),
   ((.excluded 22),[(.neg 14),(.neg 12),(.neg 11),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 10),(.pos 13)]),
   ((.excluded 23),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 10)]),
   ((.excluded 24),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 13)]),
   ((.excluded 25),[(.neg 14),(.neg 13),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 11),(.pos 12)]),
   ((.excluded 26),[(.neg 14),(.neg 13),(.neg 12),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 11)]),
   ((.excluded 27),[(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 12)]),
   ((.excluded 28),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 29,
    let w : Fin 29 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 4 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 4 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C2

/- Source: MatroidCatalogue/Cases/N6R4C2Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C2

noncomputable def certificates : List (Origin 15 29 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 29,
    target w < MatroidCatalogue.count 6 4 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 29) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 4)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 4, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N6R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R4C2.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R4C2.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 4 (target w),family_mem 6 4 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C2

/- Source: MatroidCatalogue/Cases/N6R4C3Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C3

abbrev U := N6R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R4.family 3
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 5) (.leaf 6)) (.node 3 (.leaf 7) (.node 4 (.leaf 8) (.leaf 9)))) (.node 7 (.node 6 (.leaf 10) (.leaf 11)) (.node 8 (.leaf 12) (.node 9 (.leaf 13) (.leaf 14)))))
noncomputable def newIndex (i : Fin 10) : Fin 15 := Fin.ofNat 15 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (840,10,16308432)) (.node 2 (.leaf (676,10,16308418)) (.leaf (492,12,16275665)))) (.node 4 (.leaf (1004,13,16341192)) (.node 5 (.leaf (402,10,16308250)) (.leaf (730,12,16275609))))) (.node 9 (.node 7 (.leaf (986,13,16341080)) (.node 8 (.leaf (822,12,16275595)) (.leaf (950,13,16341059)))) (.node 10 (.leaf (126,12,16261987)) (.node 11 (.leaf (894,15,16308432)) (.leaf (766,15,16308418)))))) (.node 18 (.node 15 (.node 13 (.leaf (510,15,16308250)) (.node 14 (.leaf (1022,16,16373896)) (.leaf (113,10,16306458)))) (.node 16 (.leaf (15,10,16288538)) (.node 17 (.leaf (127,13,16322915)) (.leaf (825,12,16274713))))) (.node 21 (.node 19 (.leaf (889,13,16339736)) (.node 20 (.leaf (839,12,16263961)) (.leaf (847,13,16325400)))) (.node 23 (.node 22 (.leaf (887,15,16298338)) (.leaf (831,15,16287586))) (.node 24 (.leaf (895,16,16360288)) (.leaf (725,12,16274699))))))) (.node 38 (.node 31 (.node 28 (.node 26 (.leaf (757,13,16339715)) (.node 27 (.leaf (483,12,16274531)) (.leaf (499,13,16339491)))) (.node 29 (.leaf (999,15,16300802)) (.node 30 (.leaf (983,15,16300578)) (.leaf (1015,16,16372804))))) (.node 34 (.node 32 (.leaf (683,12,16263947)) (.node 33 (.leaf (687,13,16325379)) (.leaf (1003,15,16300816)))) (.node 36 (.node 35 (.leaf (495,15,16288538)) (.leaf (1007,16,16362248))) (.node 37 (.leaf (413,12,16263779)) (.leaf (415,13,16325155)))))) (.node 44 (.node 41 (.node 39 (.leaf (509,15,16306458)) (.node 40 (.leaf (511,16,16359980)) (.leaf (989,15,16307984)))) (.node 42 (.leaf (957,15,16307970)) (.node 43 (.leaf (1021,16,16373000)) (.leaf (735,15,16288482))))) (.node 47 (.node 45 (.leaf (991,16,16362080)) (.node 46 (.leaf (955,15,16307746)) (.leaf (959,16,16362052)))) (.node 49 (.node 48 (.leaf (763,15,16306402)) (.leaf (1019,16,16372832))) (.node 50 (.leaf (767,16,16360260)) (.leaf (1023,17,16434824))))))))

noncomputable def models (i : Fin 51) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 51) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 51) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 15, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 15, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C3

/- Source: MatroidCatalogue/Cases/N6R4C3Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C3


noncomputable def certificates_0 : List (Origin 15 51 × List Sat.Literal) :=
  [((.fixed 0),[(.pos 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.exchange 5 2 2),[(.neg 5),(.neg 2),(.pos 6),(.pos 9)]),
   ((.exchange 5 3 1),[(.neg 5),(.neg 3),(.pos 7),(.pos 10)]),
   ((.exchange 5 4 0),[(.neg 5),(.neg 4),(.pos 8),(.pos 11)]),
   ((.exchange 5 12 2),[(.neg 12),(.neg 5),(.pos 6),(.pos 9)]),
   ((.exchange 5 13 0),[(.neg 13),(.neg 5),(.pos 8),(.pos 11)]),
   ((.exchange 5 13 2),[(.neg 13),(.neg 5),(.pos 6),(.pos 9)]),
   ((.exchange 5 14 0),[(.neg 14),(.neg 5),(.pos 8),(.pos 11)]),
   ((.exchange 6 1 3),[(.neg 6),(.neg 1),(.pos 5),(.pos 9)]),
   ((.exchange 6 3 1),[(.neg 6),(.neg 3),(.pos 7),(.pos 12)]),
   ((.exchange 6 4 0),[(.neg 6),(.neg 4),(.pos 8),(.pos 13)]),
   ((.exchange 6 11 0),[(.neg 11),(.neg 6),(.pos 8),(.pos 13)]),
   ((.exchange 6 14 0),[(.neg 14),(.neg 6),(.pos 8),(.pos 13)]),
   ((.exchange 7 1 3),[(.neg 7),(.neg 1),(.pos 5),(.pos 10)]),
   ((.exchange 7 2 2),[(.neg 7),(.neg 2),(.pos 6),(.pos 12)]),
   ((.exchange 7 4 0),[(.neg 7),(.neg 4),(.pos 8),(.pos 14)]),
   ((.exchange 8 1 3),[(.neg 8),(.neg 1),(.pos 5),(.pos 11)]),
   ((.exchange 8 2 2),[(.neg 8),(.neg 2),(.pos 6),(.pos 13)]),
   ((.exchange 8 3 1),[(.neg 8),(.neg 3),(.pos 7),(.pos 14)]),
   ((.exchange 8 9 2),[(.neg 9),(.neg 8),(.pos 6),(.pos 13)]),
   ((.exchange 9 0 4),[(.neg 9),(.neg 0),(.pos 5),(.pos 6)]),
   ((.exchange 9 3 1),[(.neg 9),(.neg 3),(.pos 10),(.pos 12)]),
   ((.exchange 9 4 0),[(.neg 9),(.neg 4),(.pos 11),(.pos 13)]),
   ((.exchange 9 14 0),[(.neg 14),(.neg 9),(.pos 11),(.pos 13)]),
   ((.exchange 10 0 4),[(.neg 10),(.neg 0),(.pos 5),(.pos 7)]),
   ((.exchange 10 2 2),[(.neg 10),(.neg 2),(.pos 9),(.pos 12)]),
   ((.exchange 10 4 0),[(.neg 10),(.neg 4),(.pos 11),(.pos 14)]),
   ((.exchange 10 13 0),[(.neg 13),(.neg 10),(.pos 11),(.pos 14)]),
   ((.exchange 11 2 2),[(.neg 11),(.neg 2),(.pos 9),(.pos 13)]),
   ((.exchange 11 3 1),[(.neg 11),(.neg 3),(.pos 10),(.pos 14)]),
   ((.exchange 11 7 4),[(.neg 11),(.neg 7),(.pos 5),(.pos 8)]),
   ((.exchange 11 12 1),[(.neg 12),(.neg 11),(.pos 10),(.pos 14)]),
   ((.exchange 12 0 4),[(.neg 12),(.neg 0),(.pos 6),(.pos 7)]),
   ((.exchange 12 1 3),[(.neg 12),(.neg 1),(.pos 9),(.pos 10)]),
   ((.exchange 12 4 0),[(.neg 12),(.neg 4),(.pos 13),(.pos 14)]),
   ((.exchange 12 8 4),[(.neg 12),(.neg 8),(.pos 6),(.pos 7)]),
   ((.exchange 13 0 4),[(.neg 13),(.neg 0),(.pos 6),(.pos 8)]),
   ((.exchange 13 1 3),[(.neg 13),(.neg 1),(.pos 9),(.pos 11)]),
   ((.exchange 13 3 1),[(.neg 13),(.neg 3),(.pos 12),(.pos 14)]),
   ((.exchange 13 5 3),[(.neg 13),(.neg 5),(.pos 9),(.pos 11)]),
   ((.exchange 13 5 4),[(.neg 13),(.neg 5),(.pos 6),(.pos 8)]),
   ((.exchange 14 0 4),[(.neg 14),(.neg 0),(.pos 7),(.pos 8)]),
   ((.exchange 14 1 3),[(.neg 14),(.neg 1),(.pos 10),(.pos 11)]),
   ((.exchange 14 2 2),[(.neg 14),(.neg 2),(.pos 12),(.pos 13)]),
   ((.exchange 14 5 3),[(.neg 14),(.neg 5),(.pos 10),(.pos 11)]),
   ((.exchange 14 5 4),[(.neg 14),(.neg 5),(.pos 7),(.pos 8)]),
   ((.exchange 14 6 2),[(.neg 14),(.neg 6),(.pos 12),(.pos 13)]),
   (.newPoint,[(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 0),[(.neg 14),(.neg 13),(.neg 11),(.neg 8),(.pos 5),(.pos 6),(.pos 7),(.pos 9),(.pos 10),(.pos 12)]),
   ((.excluded 1),[(.neg 14),(.neg 12),(.neg 10),(.neg 7),(.pos 5),(.pos 6),(.pos 8),(.pos 9),(.pos 11),(.pos 13)]),
   ((.excluded 2),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 8),(.neg 7),(.pos 5),(.pos 6),(.pos 9),(.pos 14)]),
   ((.excluded 3),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 8),(.neg 7),(.pos 5),(.pos 6),(.pos 9)]),
   ((.excluded 4),[(.neg 13),(.neg 12),(.neg 9),(.neg 6),(.pos 5),(.pos 7),(.pos 8),(.pos 10),(.pos 11),(.pos 14)]),
   ((.excluded 5),[(.neg 14),(.neg 12),(.neg 11),(.neg 9),(.neg 8),(.neg 6),(.pos 5),(.pos 7),(.pos 10),(.pos 13)]),
   ((.excluded 6),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 9),(.neg 8),(.neg 6),(.pos 5),(.pos 7),(.pos 10)]),
   ((.excluded 7),[(.neg 14),(.neg 13),(.neg 10),(.neg 9),(.neg 7),(.neg 6),(.pos 5),(.pos 8),(.pos 11),(.pos 12)]),
   ((.excluded 8),[(.neg 14),(.neg 13),(.neg 12),(.neg 10),(.neg 9),(.neg 7),(.neg 6),(.pos 5),(.pos 8),(.pos 11)]),
   ((.excluded 9),[(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 10),[(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 12)]),
   ((.excluded 11),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 13)]),
   ((.excluded 12),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.pos 5),(.pos 14)]),
   ((.excluded 13),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.pos 5)]),
   ((.excluded 14),[(.neg 11),(.neg 10),(.neg 9),(.neg 5),(.pos 6),(.pos 7),(.pos 8),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 15),[(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 9),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 16),[(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 17),[(.neg 14),(.neg 13),(.neg 10),(.neg 9),(.neg 8),(.neg 5),(.pos 6),(.pos 7),(.pos 11),(.pos 12)]),
   ((.excluded 18),[(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 5),(.pos 6),(.pos 7),(.pos 12)]),
   ((.excluded 19),[(.neg 14),(.neg 13),(.neg 11),(.neg 7),(.neg 6),(.neg 5),(.pos 8),(.pos 9),(.pos 10),(.pos 12)]),
   ((.excluded 20),[(.neg 14),(.neg 13),(.neg 11),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 9),(.pos 10),(.pos 12)]),
   ((.excluded 21),[(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.neg 9),(.neg 7),(.neg 6),(.neg 5),(.pos 8),(.pos 12)]),
   ((.excluded 22),[(.neg 14),(.neg 13),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 11),(.pos 12)]),
   ((.excluded 23),[(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 12)]),
   ((.excluded 24),[(.neg 14),(.neg 12),(.neg 11),(.neg 9),(.neg 7),(.neg 5),(.pos 6),(.pos 8),(.pos 10),(.pos 13)]),
   ((.excluded 25),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 7),(.neg 5),(.pos 6),(.pos 8),(.pos 13)]),
   ((.excluded 26),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 6),(.neg 5),(.pos 7),(.pos 8),(.pos 9),(.pos 14)]),
   ((.excluded 27),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 6),(.neg 5),(.pos 7),(.pos 8),(.pos 14)]),
   ((.excluded 28),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 7),(.neg 6),(.neg 5),(.pos 8),(.pos 9)]),
   ((.excluded 29),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 9),(.neg 7),(.neg 6),(.neg 5),(.pos 8),(.pos 10)]),
   ((.excluded 30),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 7),(.neg 6),(.neg 5),(.pos 8)]),
   ((.excluded 31),[(.neg 14),(.neg 12),(.neg 10),(.neg 8),(.neg 6),(.neg 5),(.pos 7),(.pos 9),(.pos 11),(.pos 13)]),
   ((.excluded 32),[(.neg 14),(.neg 12),(.neg 10),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 9),(.pos 11),(.pos 13)]),
   ((.excluded 33),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 8),(.neg 6),(.neg 5),(.pos 7),(.pos 9)]),
   ((.excluded 34),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 9),(.pos 14)]),
   ((.excluded 35),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 9)]),
   ((.excluded 36),[(.neg 13),(.neg 12),(.neg 9),(.neg 8),(.neg 7),(.neg 5),(.pos 6),(.pos 10),(.pos 11),(.pos 14)]),
   ((.excluded 37),[(.neg 13),(.neg 12),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 10),(.pos 11),(.pos 14)]),
   ((.excluded 38),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 5),(.pos 6),(.pos 14)]),
   ((.excluded 39),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 14)]),
   ((.excluded 40),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 9),(.neg 8),(.neg 7),(.neg 5),(.pos 6),(.pos 10)]),
   ((.excluded 41),[(.neg 14),(.neg 13),(.neg 12),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 5),(.pos 6),(.pos 11)]),
   ((.excluded 42),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 5),(.pos 6)]),
   ((.excluded 43),[(.neg 14),(.neg 12),(.neg 11),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 10),(.pos 13)]),
   ((.excluded 44),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 10)]),
   ((.excluded 45),[(.neg 14),(.neg 13),(.neg 12),(.neg 10),(.neg 9),(.neg 8),(.neg 6),(.neg 5),(.pos 7),(.pos 11)]),
   ((.excluded 46),[(.neg 14),(.neg 13),(.neg 12),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 11)]),
   ((.excluded 47),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 6),(.neg 5),(.pos 7),(.pos 13)]),
   ((.excluded 48),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 6),(.neg 5),(.pos 7)]),
   ((.excluded 49),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 13)]),
   ((.excluded 50),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 51,
    let w : Fin 51 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 4 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 4 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C3

/- Source: MatroidCatalogue/Cases/N6R4C3Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C3

noncomputable def certificates : List (Origin 15 51 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 51,
    target w < MatroidCatalogue.count 6 4 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 51) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 4)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 4, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N6R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R4C3.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R4C3.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 4 (target w),family_mem 6 4 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R4C3

/- Source: MatroidCatalogue/Cases/N7R1C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R1C0

abbrev U := N7R1.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R1.family 0
noncomputable def newIndexTree : Table ℕ := (.leaf 6)
noncomputable def newIndex (i : Fin 1) : Fin 7 := Fin.ofNat 7 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.leaf (1,0,16434824))

noncomputable def models (i : Fin 1) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 1) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 1) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 7, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 7, (6 : Fin 8) ∈ U i → ∃ j : Fin 1, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R1C0

/- Source: MatroidCatalogue/Cases/N7R1C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R1C0


noncomputable def certificates_0 : List (Origin 7 1 × List Sat.Literal) :=
  [(.newPoint,[(.pos 6)]),
   ((.excluded 0),[(.neg 6)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 1,
    let w : Fin 1 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 1 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 1 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R1C0

/- Source: MatroidCatalogue/Cases/N7R1C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R1C0

noncomputable def certificates : List (Origin 7 1 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 1,
    target w < MatroidCatalogue.count 7 1 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 1 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 1) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 1)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 1, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=1) (by decide)
    catalogue old U newIndex models certificates
    N7R1.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R1C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R1C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 1 (target w),family_mem 7 1 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R1C0

/- Source: MatroidCatalogue/Cases/N7R2C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C0

abbrev U := N7R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R2.family 0
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 16) (.leaf 17))) (.node 4 (.leaf 18) (.node 5 (.leaf 19) (.leaf 20))))
noncomputable def newIndex (i : Fin 6) : Fin 21 := Fin.ofNat 21 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 1 (.leaf (32,0,16205448)) (.node 2 (.leaf (31,1,16434824)) (.leaf (63,2,16434824))))

noncomputable def models (i : Fin 3) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 3) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 3) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 21, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 21, (6 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C0

/- Source: MatroidCatalogue/Cases/N7R2C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C0


noncomputable def certificates_0 : List (Origin 21 3 × List Sat.Literal) :=
  [((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.exchange 10 19 5),[(.neg 19),(.neg 10),(.pos 6),(.pos 15)]),
   ((.exchange 11 19 5),[(.neg 19),(.neg 11),(.pos 7),(.pos 16)]),
   ((.exchange 12 19 5),[(.neg 19),(.neg 12),(.pos 8),(.pos 17)]),
   ((.exchange 13 19 5),[(.neg 19),(.neg 13),(.pos 9),(.pos 18)]),
   ((.exchange 14 15 5),[(.neg 15),(.neg 14),(.pos 6),(.pos 19)]),
   ((.exchange 14 16 5),[(.neg 16),(.neg 14),(.pos 7),(.pos 19)]),
   ((.exchange 14 17 5),[(.neg 17),(.neg 14),(.pos 8),(.pos 19)]),
   ((.exchange 14 18 5),[(.neg 18),(.neg 14),(.pos 9),(.pos 19)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 0),[(.neg 20),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 1),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20)]),
   ((.excluded 2),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 3,
    let w : Fin 3 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C0

/- Source: MatroidCatalogue/Cases/N7R2C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C0

noncomputable def certificates : List (Origin 21 3 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 3,
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 3) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 2)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 2, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N7R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R2C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R2C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 2 (target w),family_mem 7 2 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C0

