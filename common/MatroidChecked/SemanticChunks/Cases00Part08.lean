module
public import MatroidCatalogue.Definitions
public import MatroidCases.N7R3C12
import all MatroidCases.N7R3C12
public import MatroidCases.N7R3C13
import all MatroidCases.N7R3C13
public import MatroidCases.N7R3C14
import all MatroidCases.N7R3C14
public import MatroidCases.N7R3C15
import all MatroidCases.N7R3C15

@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N7R3C12Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C12

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 12
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (11968,20,15161370)) (.node 2 (.leaf (29440,17,15423688)) (.leaf (24000,21,15684872)))) (.node 5 (.node 4 (.leaf (32704,25,15947400)) (.leaf (11326,34,15641864))) (.node 6 (.leaf (766,34,15555848)) (.leaf (12030,41,16137352))))) (.node 10 (.node 8 (.leaf (24382,38,16205448)) (.node 9 (.leaf (32574,39,16201864)) (.leaf (24574,42,16148104)))) (.node 12 (.node 11 (.leaf (29182,38,16148104)) (.leaf (29694,39,16115848))) (.node 13 (.leaf (32254,42,16205448)) (.leaf (32766,43,16434824))))))

noncomputable def models (i : Fin 14) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 14) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 14) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C12

/- Source: MatroidCatalogue/Cases/N7R3C12Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C12


noncomputable def certificates_0 : List (Origin 35 14 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 5 22 4),[(.neg 22),(.neg 5),(.pos 0),(.pos 21)]),
   ((.exchange 5 23 4),[(.neg 23),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 5 24 4),[(.neg 24),(.neg 5),(.pos 0),(.pos 2),(.pos 21)]),
   ((.exchange 5 25 4),[(.neg 25),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 5 27 2),[(.neg 27),(.neg 5),(.pos 4),(.pos 26)]),
   ((.exchange 5 32 0),[(.neg 32),(.neg 5),(.pos 18),(.pos 28)]),
   ((.exchange 5 34 0),[(.neg 34),(.neg 5),(.pos 18),(.pos 28)]),
   ((.exchange 6 21 4),[(.neg 21),(.neg 6),(.pos 0),(.pos 22)]),
   ((.exchange 6 23 4),[(.neg 23),(.neg 6),(.pos 0),(.pos 3),(.pos 22)]),
   ((.exchange 6 24 4),[(.neg 24),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 6 25 4),[(.neg 25),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 6 26 2),[(.neg 26),(.neg 6),(.pos 4),(.pos 27)]),
   ((.exchange 7 21 4),[(.neg 21),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 7 22 4),[(.neg 22),(.neg 7),(.pos 1),(.pos 2),(.pos 23)]),
   ((.exchange 7 24 4),[(.neg 24),(.neg 7),(.pos 1),(.pos 23)]),
   ((.exchange 7 25 4),[(.neg 25),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 8 21 4),[(.neg 21),(.neg 8),(.pos 1),(.pos 3),(.pos 24)]),
   ((.exchange 8 22 4),[(.neg 22),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 8 23 4),[(.neg 23),(.neg 8),(.pos 1),(.pos 24)]),
   ((.exchange 8 25 4),[(.neg 25),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 9 21 4),[(.neg 21),(.neg 9),(.pos 2),(.pos 25)]),
   ((.exchange 9 22 4),[(.neg 22),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 9 23 4),[(.neg 23),(.neg 9),(.pos 2),(.pos 25)]),
   ((.exchange 9 24 4),[(.neg 24),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 11 28 0),[(.neg 28),(.neg 11),(.pos 18),(.pos 32)]),
   ((.exchange 11 31 2),[(.neg 31),(.neg 11),(.pos 10),(.pos 30)]),
   ((.exchange 11 34 0),[(.neg 34),(.neg 11),(.pos 18),(.pos 32)]),
   ((.exchange 12 30 2),[(.neg 30),(.neg 12),(.pos 10),(.pos 31)]),
   ((.exchange 16 32 0),[(.neg 32),(.neg 16),(.pos 18),(.pos 34)]),
   ((.exchange 20 5 6),[(.neg 20),(.neg 5),(.pos 0),(.pos 4)]),
   ((.exchange 21 16 2),[(.neg 21),(.neg 16),(.pos 26),(.pos 30)]),
   ((.exchange 22 16 2),[(.neg 22),(.neg 16),(.pos 20),(.pos 27),(.pos 31)]),
   ((.exchange 23 19 0),[(.neg 23),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 23 34 0),[(.neg 34),(.neg 23),(.pos 29),(.pos 33)]),
   ((.exchange 26 11 4),[(.neg 26),(.neg 11),(.pos 21),(.pos 30)]),
   ((.exchange 27 11 4),[(.neg 27),(.neg 11),(.pos 20),(.pos 22),(.pos 31)]),
   ((.exchange 27 19 1),[(.neg 27),(.neg 19),(.pos 29),(.pos 34)]),
   ((.exchange 28 8 2),[(.neg 28),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 29 11 4),[(.neg 29),(.neg 11),(.pos 23),(.pos 25),(.pos 33)]),
   ((.exchange 29 13 4),[(.neg 29),(.neg 13),(.pos 23),(.pos 33)]),
   ((.exchange 29 15 4),[(.neg 29),(.neg 15),(.pos 25),(.pos 33)]),
   ((.exchange 29 22 3),[(.neg 29),(.neg 22),(.pos 27),(.pos 28)]),
   ((.exchange 30 5 5),[(.neg 30),(.neg 5),(.pos 21),(.pos 26)]),
   ((.exchange 30 7 5),[(.neg 30),(.neg 7),(.pos 23),(.pos 26)]),
   ((.exchange 30 19 0),[(.neg 30),(.neg 19),(.pos 33),(.pos 34)]),
   ((.exchange 30 28 5),[(.neg 30),(.neg 28),(.pos 21),(.pos 26)]),
   ((.exchange 31 5 5),[(.neg 31),(.neg 5),(.pos 20),(.pos 22),(.pos 27)]),
   ((.exchange 31 7 5),[(.neg 31),(.neg 7),(.pos 20),(.pos 24),(.pos 27)]),
   ((.exchange 31 15 1),[(.neg 31),(.neg 15),(.pos 32),(.pos 33)]),
   ((.exchange 32 14 2),[(.neg 32),(.neg 14),(.pos 31),(.pos 33)]),
   ((.exchange 33 5 5),[(.neg 33),(.neg 5),(.pos 23),(.pos 25),(.pos 29)]),
   ((.exchange 33 6 5),[(.neg 33),(.neg 6),(.pos 24),(.pos 25),(.pos 29)]),
   ((.exchange 33 7 5),[(.neg 33),(.neg 7),(.pos 23),(.pos 29)]),
   ((.exchange 33 11 3),[(.neg 33),(.neg 11),(.pos 30),(.pos 32)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 28),(.pos 32),(.pos 34)]),
   ((.excluded 1),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 30),(.pos 31)]),
   ((.excluded 2),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 29),(.pos 33)]),
   ((.excluded 3),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25)]),
   ((.excluded 4),[(.neg 33),(.neg 31),(.neg 30),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 32),(.pos 34)]),
   ((.excluded 5),[(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 28),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 6),[(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 28),(.pos 32),(.pos 34)]),
   ((.excluded 7),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27),(.pos 33)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27)]),
   ((.excluded 9),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 33)]),
   ((.excluded 10),[(.neg 34),(.neg 33),(.neg 32),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 29),(.pos 30),(.pos 31)]),
   ((.excluded 11),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 30),(.pos 31)]),
   ((.excluded 12),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 29)]),
   ((.excluded 13),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 14,
    let w : Fin 14 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C12

/- Source: MatroidCatalogue/Cases/N7R3C12Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C12

noncomputable def certificates : List (Origin 35 14 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 14,
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 14) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 3)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 3, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N7R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C12.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C12.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C12

/- Source: MatroidCatalogue/Cases/N7R3C13Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C13

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 13
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (29440,18,15423688)) (.leaf (28352,22,15685768))) (.node 3 (.leaf (24000,22,15684872)) (.node 4 (.leaf (16320,25,15423688)) (.leaf (32704,26,15947400))))) (.node 7 (.node 6 (.leaf (15422,35,15674120)) (.leaf (1022,35,15559432))) (.node 8 (.leaf (16382,44,16434824)) (.node 9 (.leaf (28478,39,15685768)) (.leaf (24382,39,15684872)))))) (.node 15 (.node 12 (.node 11 (.leaf (32574,40,16205448)) (.leaf (28158,42,15947400))) (.node 13 (.leaf (28670,43,16148104)) (.node 14 (.leaf (24318,42,15918728)) (.leaf (24574,43,16147656))))) (.node 18 (.node 16 (.leaf (29438,39,15657096)) (.node 17 (.leaf (29182,39,15656200)) (.leaf (29694,40,16148104)))) (.node 19 (.leaf (32510,43,16205448)) (.node 20 (.leaf (32254,43,16205000)) (.leaf (32766,45,16434824)))))))

noncomputable def models (i : Fin 21) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 21) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 21) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C13

/- Source: MatroidCatalogue/Cases/N7R3C13Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C13


noncomputable def certificates_0 : List (Origin 35 21 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 5 22 4),[(.neg 22),(.neg 5),(.pos 0),(.pos 21)]),
   ((.exchange 5 23 4),[(.neg 23),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 5 24 4),[(.neg 24),(.neg 5),(.pos 0),(.pos 2),(.pos 21)]),
   ((.exchange 5 25 4),[(.neg 25),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 5 27 2),[(.neg 27),(.neg 5),(.pos 4),(.pos 26)]),
   ((.exchange 6 21 4),[(.neg 21),(.neg 6),(.pos 0),(.pos 22)]),
   ((.exchange 6 23 4),[(.neg 23),(.neg 6),(.pos 0),(.pos 3),(.pos 22)]),
   ((.exchange 6 24 4),[(.neg 24),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 6 25 4),[(.neg 25),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 6 26 2),[(.neg 26),(.neg 6),(.pos 4),(.pos 27)]),
   ((.exchange 7 21 4),[(.neg 21),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 7 22 4),[(.neg 22),(.neg 7),(.pos 1),(.pos 2),(.pos 23)]),
   ((.exchange 7 24 4),[(.neg 24),(.neg 7),(.pos 1),(.pos 23)]),
   ((.exchange 7 25 4),[(.neg 25),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 8 21 4),[(.neg 21),(.neg 8),(.pos 1),(.pos 3),(.pos 24)]),
   ((.exchange 8 22 4),[(.neg 22),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 8 23 4),[(.neg 23),(.neg 8),(.pos 1),(.pos 24)]),
   ((.exchange 8 25 4),[(.neg 25),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 9 21 4),[(.neg 21),(.neg 9),(.pos 2),(.pos 25)]),
   ((.exchange 9 22 4),[(.neg 22),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 9 24 4),[(.neg 24),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 11 31 2),[(.neg 31),(.neg 11),(.pos 10),(.pos 30)]),
   ((.exchange 12 30 2),[(.neg 30),(.neg 12),(.pos 10),(.pos 31)]),
   ((.exchange 20 5 6),[(.neg 20),(.neg 5),(.pos 0),(.pos 4)]),
   ((.exchange 21 16 2),[(.neg 21),(.neg 16),(.pos 26),(.pos 30)]),
   ((.exchange 21 18 0),[(.neg 21),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 21 34 0),[(.neg 34),(.neg 21),(.pos 28),(.pos 32)]),
   ((.exchange 22 16 2),[(.neg 22),(.neg 16),(.pos 20),(.pos 27),(.pos 31)]),
   ((.exchange 23 19 0),[(.neg 23),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 24 34 1),[(.neg 34),(.neg 24),(.pos 29),(.pos 33)]),
   ((.exchange 26 11 4),[(.neg 26),(.neg 11),(.pos 21),(.pos 30)]),
   ((.exchange 26 13 4),[(.neg 26),(.neg 13),(.pos 23),(.pos 30)]),
   ((.exchange 26 18 0),[(.neg 26),(.neg 18),(.pos 28),(.pos 34)]),
   ((.exchange 27 11 4),[(.neg 27),(.neg 11),(.pos 20),(.pos 22),(.pos 31)]),
   ((.exchange 27 13 4),[(.neg 27),(.neg 13),(.pos 20),(.pos 24),(.pos 31)]),
   ((.exchange 27 32 1),[(.neg 32),(.neg 27),(.pos 28),(.pos 34)]),
   ((.exchange 28 8 2),[(.neg 28),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 28 11 4),[(.neg 28),(.neg 11),(.pos 21),(.pos 32)]),
   ((.exchange 28 16 2),[(.neg 28),(.neg 16),(.pos 26),(.pos 34)]),
   ((.exchange 28 17 2),[(.neg 28),(.neg 17),(.pos 27),(.pos 34)]),
   ((.exchange 28 19 2),[(.neg 28),(.neg 19),(.pos 29),(.pos 34)]),
   ((.exchange 29 11 4),[(.neg 29),(.neg 11),(.pos 23),(.pos 25),(.pos 33)]),
   ((.exchange 29 31 4),[(.neg 31),(.neg 29),(.pos 24),(.pos 33)]),
   ((.exchange 29 32 3),[(.neg 32),(.neg 29),(.pos 28),(.pos 34)]),
   ((.exchange 30 5 5),[(.neg 30),(.neg 5),(.pos 21),(.pos 26)]),
   ((.exchange 30 8 5),[(.neg 30),(.neg 8),(.pos 20),(.pos 23),(.pos 26)]),
   ((.exchange 30 18 0),[(.neg 30),(.neg 18),(.pos 32),(.pos 34)]),
   ((.exchange 30 19 0),[(.neg 30),(.neg 19),(.pos 33),(.pos 34)]),
   ((.exchange 31 5 5),[(.neg 31),(.neg 5),(.pos 20),(.pos 22),(.pos 27)]),
   ((.exchange 31 9 5),[(.neg 31),(.neg 9),(.pos 22),(.pos 24),(.pos 27)]),
   ((.exchange 31 15 1),[(.neg 31),(.neg 15),(.pos 32),(.pos 33)]),
   ((.exchange 32 5 5),[(.neg 32),(.neg 5),(.pos 21),(.pos 28)]),
   ((.exchange 32 6 5),[(.neg 32),(.neg 6),(.pos 22),(.pos 28)]),
   ((.exchange 32 9 5),[(.neg 32),(.neg 9),(.pos 25),(.pos 28)]),
   ((.exchange 32 14 2),[(.neg 32),(.neg 14),(.pos 31),(.pos 33)]),
   ((.exchange 32 17 2),[(.neg 32),(.neg 17),(.pos 31),(.pos 34)]),
   ((.exchange 33 5 5),[(.neg 33),(.neg 5),(.pos 23),(.pos 25),(.pos 29)]),
   ((.exchange 33 7 5),[(.neg 33),(.neg 7),(.pos 23),(.pos 29)]),
   ((.exchange 33 8 5),[(.neg 33),(.neg 8),(.pos 24),(.pos 29)]),
   ((.exchange 33 12 3),[(.neg 33),(.neg 12),(.pos 31),(.pos 32)]),
   ((.exchange 34 5 5),[(.neg 34),(.neg 5),(.pos 26),(.pos 28)]),
   ((.exchange 34 6 5),[(.neg 34),(.neg 6),(.pos 27),(.pos 28)]),
   ((.exchange 34 9 5),[(.neg 34),(.neg 9),(.pos 28),(.pos 29)]),
   ((.exchange 34 15 4),[(.neg 34),(.neg 15),(.pos 32),(.pos 33)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 30),(.pos 31)]),
   ((.excluded 1),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 28),(.pos 32)]),
   ((.excluded 2),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 29),(.pos 33)]),
   ((.excluded 3),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 34)]),
   ((.excluded 4),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25)]),
   ((.excluded 5),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 34)]),
   ((.excluded 6),[(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 7),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 34)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27),(.pos 32)]),
   ((.excluded 9),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27),(.pos 33)]),
   ((.excluded 10),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27)]),
   ((.excluded 11),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 29),(.pos 32)]),
   ((.excluded 12),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 32)]),
   ((.excluded 13),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 28),(.pos 33)]),
   ((.excluded 14),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 33)]),
   ((.excluded 15),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 28),(.pos 30),(.pos 31)]),
   ((.excluded 16),[(.neg 34),(.neg 33),(.neg 32),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 29),(.pos 30),(.pos 31)]),
   ((.excluded 17),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 30),(.pos 31)]),
   ((.excluded 18),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 28)]),
   ((.excluded 19),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 29)]),
   ((.excluded 20),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 21,
    let w : Fin 21 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C13

/- Source: MatroidCatalogue/Cases/N7R3C13Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C13

noncomputable def certificates : List (Origin 35 21 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 21,
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 21) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 3)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 3, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N7R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C13.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C13.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C13

/- Source: MatroidCatalogue/Cases/N7R3C14Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C14

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 14
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 5 (.node 2 (.node 1 (.leaf (3288,23,15086645)) (.leaf (3270,23,15085749))) (.node 3 (.leaf (3102,23,15074997)) (.node 4 (.leaf (222,23,14960309)) (.leaf (3294,27,15835701))))) (.node 8 (.node 6 (.leaf (29472,30,15423688)) (.node 7 (.leaf (32760,41,16434824)) (.leaf (32742,41,16434376)))) (.node 9 (.leaf (32574,41,16427208)) (.node 10 (.leaf (29694,41,16341192)) (.leaf (32766,46,16434824))))))

noncomputable def models (i : Fin 11) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 11) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 11) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C14

/- Source: MatroidCatalogue/Cases/N7R3C14Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C14


noncomputable def certificates_0 : List (Origin 35 11 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.exchange 2 22 3),[(.neg 22),(.neg 2),(.pos 0),(.pos 21)]),
   ((.exchange 2 24 2),[(.neg 24),(.neg 2),(.pos 1),(.pos 23)]),
   ((.exchange 2 32 0),[(.neg 32),(.neg 2),(.pos 15),(.pos 25)]),
   ((.exchange 2 33 0),[(.neg 33),(.neg 2),(.pos 15),(.pos 25)]),
   ((.exchange 3 21 3),[(.neg 21),(.neg 3),(.pos 0),(.pos 22)]),
   ((.exchange 3 23 2),[(.neg 23),(.neg 3),(.pos 1),(.pos 24)]),
   ((.exchange 5 27 2),[(.neg 27),(.neg 5),(.pos 4),(.pos 26)]),
   ((.exchange 5 32 0),[(.neg 32),(.neg 5),(.pos 18),(.pos 28)]),
   ((.exchange 5 33 0),[(.neg 33),(.neg 5),(.pos 9),(.pos 18),(.pos 28)]),
   ((.exchange 6 26 2),[(.neg 26),(.neg 6),(.pos 4),(.pos 27)]),
   ((.exchange 7 32 0),[(.neg 32),(.neg 7),(.pos 9),(.pos 19),(.pos 29)]),
   ((.exchange 7 33 0),[(.neg 33),(.neg 7),(.pos 19),(.pos 29)]),
   ((.exchange 11 25 0),[(.neg 25),(.neg 11),(.pos 15),(.pos 32)]),
   ((.exchange 11 28 0),[(.neg 28),(.neg 11),(.pos 18),(.pos 32)]),
   ((.exchange 11 29 0),[(.neg 29),(.neg 11),(.pos 15),(.pos 18),(.pos 32)]),
   ((.exchange 11 31 2),[(.neg 31),(.neg 11),(.pos 10),(.pos 30)]),
   ((.exchange 11 33 0),[(.neg 33),(.neg 11),(.pos 15),(.pos 32)]),
   ((.exchange 11 34 0),[(.neg 34),(.neg 11),(.pos 18),(.pos 32)]),
   ((.exchange 12 30 2),[(.neg 30),(.neg 12),(.pos 10),(.pos 31)]),
   ((.exchange 13 25 0),[(.neg 25),(.neg 13),(.pos 15),(.pos 33)]),
   ((.exchange 13 28 0),[(.neg 28),(.neg 13),(.pos 15),(.pos 19),(.pos 33)]),
   ((.exchange 13 29 0),[(.neg 29),(.neg 13),(.pos 19),(.pos 33)]),
   ((.exchange 13 32 0),[(.neg 32),(.neg 13),(.pos 15),(.pos 33)]),
   ((.exchange 13 34 0),[(.neg 34),(.neg 13),(.pos 19),(.pos 33)]),
   ((.exchange 16 32 0),[(.neg 32),(.neg 16),(.pos 18),(.pos 34)]),
   ((.exchange 16 33 0),[(.neg 33),(.neg 16),(.pos 19),(.pos 34)]),
   ((.exchange 20 2 6),[(.neg 20),(.neg 2),(.pos 0),(.pos 1)]),
   ((.exchange 21 8 2),[(.neg 21),(.neg 8),(.pos 20),(.pos 23),(.pos 26)]),
   ((.exchange 21 13 2),[(.neg 21),(.neg 13),(.pos 23),(.pos 30)]),
   ((.exchange 21 16 2),[(.neg 21),(.neg 16),(.pos 26),(.pos 30)]),
   ((.exchange 22 13 2),[(.neg 22),(.neg 13),(.pos 20),(.pos 24),(.pos 31)]),
   ((.exchange 22 16 2),[(.neg 22),(.neg 16),(.pos 20),(.pos 27),(.pos 31)]),
   ((.exchange 23 11 3),[(.neg 23),(.neg 11),(.pos 21),(.pos 30)]),
   ((.exchange 23 16 3),[(.neg 23),(.neg 16),(.pos 26),(.pos 30)]),
   ((.exchange 24 11 3),[(.neg 24),(.neg 11),(.pos 20),(.pos 22),(.pos 31)]),
   ((.exchange 24 16 3),[(.neg 24),(.neg 16),(.pos 20),(.pos 27),(.pos 31)]),
   ((.exchange 26 2 4),[(.neg 26),(.neg 2),(.pos 21),(.pos 23)]),
   ((.exchange 26 11 4),[(.neg 26),(.neg 11),(.pos 21),(.pos 30)]),
   ((.exchange 26 33 4),[(.neg 33),(.neg 26),(.pos 23),(.pos 30)]),
   ((.exchange 27 2 4),[(.neg 27),(.neg 2),(.pos 20),(.pos 22),(.pos 24)]),
   ((.exchange 27 32 4),[(.neg 32),(.neg 27),(.pos 22),(.pos 31)]),
   ((.exchange 27 33 4),[(.neg 33),(.neg 27),(.pos 24),(.pos 31)]),
   ((.exchange 30 3 5),[(.neg 30),(.neg 3),(.pos 20),(.pos 21),(.pos 23)]),
   ((.exchange 30 6 5),[(.neg 30),(.neg 6),(.pos 20),(.pos 21),(.pos 26)]),
   ((.exchange 30 28 5),[(.neg 30),(.neg 28),(.pos 21),(.pos 26)]),
   ((.exchange 30 29 5),[(.neg 30),(.neg 29),(.pos 23),(.pos 26)]),
   ((.exchange 31 3 5),[(.neg 31),(.neg 3),(.pos 22),(.pos 24)]),
   ((.exchange 31 6 5),[(.neg 31),(.neg 6),(.pos 22),(.pos 27)]),
   ((.exchange 31 7 5),[(.neg 31),(.neg 7),(.pos 20),(.pos 24),(.pos 27)]),
   ((.exchange 31 28 5),[(.neg 31),(.neg 28),(.pos 22),(.pos 27)]),
   ((.exchange 31 29 5),[(.neg 31),(.neg 29),(.pos 24),(.pos 27)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 25),(.pos 28),(.pos 29),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 1),[(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.neg 22),(.neg 21),(.pos 20),(.pos 23),(.pos 24),(.pos 25),(.pos 28),(.pos 29),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 2),[(.neg 31),(.neg 30),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 3),[(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 4),[(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 28),(.pos 29),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 5),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 25),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 26),(.pos 27),(.pos 30),(.pos 31)]),
   ((.excluded 6),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22)]),
   ((.excluded 7),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 22),(.neg 21),(.pos 20),(.pos 23),(.pos 24)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27)]),
   ((.excluded 9),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 30),(.pos 31)]),
   ((.excluded 10),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 11,
    let w : Fin 11 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C14

/- Source: MatroidCatalogue/Cases/N7R3C14Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C14

noncomputable def certificates : List (Origin 35 11 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 11,
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 11) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 3)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 3, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N7R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C14.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C14.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C14

/- Source: MatroidCatalogue/Cases/N7R3C15Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C15

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 15
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (15232,24,15161552)) (.leaf (30528,25,15161538))) (.node 3 (.leaf (28352,25,15161370)) (.node 4 (.leaf (24000,25,15159578)) (.leaf (32704,28,15947400))))) (.node 7 (.node 6 (.leaf (14399,41,15141658)) (.leaf (959,41,14969626))) (.node 8 (.leaf (15295,47,16137352)) (.node 9 (.leaf (28543,48,16148104)) (.leaf (24447,48,16147656)))))) (.node 15 (.node 12 (.node 11 (.leaf (32639,49,16205448)) (.leaf (28159,48,16204888))) (.node 13 (.leaf (28671,49,16148048)) (.node 14 (.leaf (30207,48,16205000)) (.leaf (32255,49,16204496))))) (.node 18 (.node 16 (.leaf (30463,48,16205448)) (.node 17 (.leaf (30719,49,16148104)) (.leaf (24319,48,16147544)))) (.node 19 (.leaf (32511,49,16205392)) (.node 20 (.leaf (24575,49,16147152)) (.leaf (32767,50,16434824)))))))

noncomputable def models (i : Fin 21) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 21) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 21) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C15

/- Source: MatroidCatalogue/Cases/N7R3C15Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C15


noncomputable def certificates_0 : List (Origin 35 21 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 4 21 4),[(.neg 21),(.neg 4),(.pos 0),(.pos 20)]),
   ((.exchange 4 22 4),[(.neg 22),(.neg 4),(.pos 0),(.pos 20)]),
   ((.exchange 4 30 1),[(.neg 30),(.neg 4),(.pos 16),(.pos 26)]),
   ((.exchange 5 20 4),[(.neg 20),(.neg 5),(.pos 0),(.pos 21)]),
   ((.exchange 5 22 4),[(.neg 22),(.neg 5),(.pos 0),(.pos 21)]),
   ((.exchange 5 23 4),[(.neg 23),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 5 24 4),[(.neg 24),(.neg 5),(.pos 0),(.pos 2),(.pos 21)]),
   ((.exchange 5 25 4),[(.neg 25),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 6 20 4),[(.neg 20),(.neg 6),(.pos 0),(.pos 22)]),
   ((.exchange 6 21 4),[(.neg 21),(.neg 6),(.pos 0),(.pos 22)]),
   ((.exchange 6 23 4),[(.neg 23),(.neg 6),(.pos 0),(.pos 3),(.pos 22)]),
   ((.exchange 6 24 4),[(.neg 24),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 6 25 4),[(.neg 25),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 7 21 4),[(.neg 21),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 7 22 4),[(.neg 22),(.neg 7),(.pos 1),(.pos 2),(.pos 23)]),
   ((.exchange 8 21 4),[(.neg 21),(.neg 8),(.pos 1),(.pos 3),(.pos 24)]),
   ((.exchange 8 22 4),[(.neg 22),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 9 21 4),[(.neg 21),(.neg 9),(.pos 2),(.pos 25)]),
   ((.exchange 9 22 4),[(.neg 22),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 10 26 1),[(.neg 26),(.neg 10),(.pos 16),(.pos 30)]),
   ((.exchange 10 34 1),[(.neg 34),(.neg 10),(.pos 16),(.pos 30)]),
   ((.exchange 17 30 1),[(.neg 30),(.neg 17),(.pos 16),(.pos 34)]),
   ((.exchange 20 17 0),[(.neg 20),(.neg 17),(.pos 27),(.pos 31)]),
   ((.exchange 21 18 0),[(.neg 21),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 22 34 1),[(.neg 34),(.neg 22),(.pos 28),(.pos 32)]),
   ((.exchange 22 34 2),[(.neg 34),(.neg 22),(.pos 27),(.pos 31)]),
   ((.exchange 23 19 0),[(.neg 23),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 26 8 0),[(.neg 26),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 26 9 0),[(.neg 26),(.neg 9),(.pos 28),(.pos 29)]),
   ((.exchange 27 10 4),[(.neg 27),(.neg 10),(.pos 20),(.pos 31)]),
   ((.exchange 27 12 4),[(.neg 27),(.neg 12),(.pos 22),(.pos 31)]),
   ((.exchange 27 18 1),[(.neg 27),(.neg 18),(.pos 28),(.pos 34)]),
   ((.exchange 28 4 2),[(.neg 28),(.neg 4),(.pos 26),(.pos 27)]),
   ((.exchange 28 7 2),[(.neg 28),(.neg 7),(.pos 26),(.pos 29)]),
   ((.exchange 28 10 4),[(.neg 28),(.neg 10),(.pos 21),(.pos 22),(.pos 32)]),
   ((.exchange 28 12 4),[(.neg 28),(.neg 12),(.pos 22),(.pos 32)]),
   ((.exchange 29 10 4),[(.neg 29),(.neg 10),(.pos 23),(.pos 24),(.pos 33)]),
   ((.exchange 29 18 3),[(.neg 29),(.neg 18),(.pos 28),(.pos 34)]),
   ((.exchange 30 15 0),[(.neg 30),(.neg 15),(.pos 32),(.pos 33)]),
   ((.exchange 31 6 5),[(.neg 31),(.neg 6),(.pos 22),(.pos 27)]),
   ((.exchange 31 18 1),[(.neg 31),(.neg 18),(.pos 32),(.pos 34)]),
   ((.exchange 31 19 1),[(.neg 31),(.neg 19),(.pos 33),(.pos 34)]),
   ((.exchange 32 4 2),[(.neg 32),(.neg 4),(.pos 30),(.pos 31),(.pos 34)]),
   ((.exchange 32 6 5),[(.neg 32),(.neg 6),(.pos 22),(.pos 28)]),
   ((.exchange 32 14 2),[(.neg 32),(.neg 14),(.pos 31),(.pos 33)]),
   ((.exchange 33 4 5),[(.neg 33),(.neg 4),(.pos 23),(.pos 24),(.pos 29)]),
   ((.exchange 33 6 3),[(.neg 33),(.neg 6),(.pos 31),(.pos 32),(.pos 34)]),
   ((.exchange 33 7 5),[(.neg 33),(.neg 7),(.pos 23),(.pos 29)]),
   ((.exchange 34 12 4),[(.neg 34),(.neg 12),(.pos 31),(.pos 32)]),
   ((.exchange 34 22 5),[(.neg 34),(.neg 22),(.pos 27),(.pos 28)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 30),(.pos 34)]),
   ((.excluded 1),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 27),(.pos 31)]),
   ((.excluded 2),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 28),(.pos 32)]),
   ((.excluded 3),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 29),(.pos 33)]),
   ((.excluded 4),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25)]),
   ((.excluded 5),[(.neg 33),(.neg 32),(.neg 31),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 6),[(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 26),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 7),[(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 26),(.pos 30),(.pos 34)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 27),(.pos 32)]),
   ((.excluded 9),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 27),(.pos 33)]),
   ((.excluded 10),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 27)]),
   ((.excluded 11),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 29),(.pos 32)]),
   ((.excluded 12),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 32)]),
   ((.excluded 13),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 29),(.pos 31)]),
   ((.excluded 14),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 29)]),
   ((.excluded 15),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 28),(.pos 31)]),
   ((.excluded 16),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 31)]),
   ((.excluded 17),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 28),(.pos 33)]),
   ((.excluded 18),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 28)]),
   ((.excluded 19),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 33)]),
   ((.excluded 20),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 21,
    let w : Fin 21 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C15

/- Source: MatroidCatalogue/Cases/N7R3C15Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C15

noncomputable def certificates : List (Origin 35 21 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 21,
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 21) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 3)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 3, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N7R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C15.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C15.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C15

