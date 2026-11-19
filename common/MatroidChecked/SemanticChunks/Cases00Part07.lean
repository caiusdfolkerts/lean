module
public import MatroidCatalogue.Definitions
public import MatroidCases.N7R3C6
import all MatroidCases.N7R3C6
public import MatroidCases.N7R3C7
import all MatroidCases.N7R3C7
public import MatroidCases.N7R3C8
import all MatroidCases.N7R3C8
public import MatroidCases.N7R3C9
import all MatroidCases.N7R3C9
public import MatroidCases.N7R3C10
import all MatroidCases.N7R3C10
public import MatroidCases.N7R3C11
import all MatroidCases.N7R3C11

@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N7R3C6Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C6

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 6
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 4 (.node 2 (.node 1 (.leaf (7616,14,15947400)) (.leaf (7224,14,15940232))) (.node 3 (.leaf (504,14,15854216)) (.leaf (7672,30,16434824)))) (.node 6 (.node 5 (.leaf (25088,10,15685768)) (.leaf (32704,17,15947400))) (.node 7 (.leaf (32312,17,15940232)) (.node 8 (.leaf (25592,17,15854216)) (.leaf (32760,31,16434824))))))

noncomputable def models (i : Fin 9) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 9) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 9) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C6

/- Source: MatroidCatalogue/Cases/N7R3C6Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C6


noncomputable def certificates_0 : List (Origin 35 9 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 19),[(.neg 19)]),
   ((.exchange 7 24 4),[(.neg 24),(.neg 7),(.pos 1),(.pos 23)]),
   ((.exchange 7 25 4),[(.neg 25),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 7 28 3),[(.neg 28),(.neg 7),(.pos 5),(.pos 26)]),
   ((.exchange 7 33 0),[(.neg 33),(.neg 7),(.pos 19),(.pos 29)]),
   ((.exchange 8 23 4),[(.neg 23),(.neg 8),(.pos 1),(.pos 24)]),
   ((.exchange 8 25 4),[(.neg 25),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 8 28 3),[(.neg 28),(.neg 8),(.pos 6),(.pos 27)]),
   ((.exchange 9 23 4),[(.neg 23),(.neg 9),(.pos 2),(.pos 25)]),
   ((.exchange 9 24 4),[(.neg 24),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 9 26 3),[(.neg 26),(.neg 9),(.pos 5),(.pos 28)]),
   ((.exchange 9 27 3),[(.neg 27),(.neg 9),(.pos 6),(.pos 28)]),
   ((.exchange 13 29 0),[(.neg 29),(.neg 13),(.pos 19),(.pos 33)]),
   ((.exchange 13 31 3),[(.neg 31),(.neg 13),(.pos 10),(.pos 30)]),
   ((.exchange 13 34 0),[(.neg 34),(.neg 13),(.pos 19),(.pos 33)]),
   ((.exchange 14 30 3),[(.neg 30),(.neg 14),(.pos 10),(.pos 31)]),
   ((.exchange 14 32 3),[(.neg 32),(.neg 14),(.pos 12),(.pos 31)]),
   ((.exchange 15 31 3),[(.neg 31),(.neg 15),(.pos 12),(.pos 32)]),
   ((.exchange 16 33 0),[(.neg 33),(.neg 16),(.pos 19),(.pos 34)]),
   ((.exchange 20 7 6),[(.neg 20),(.neg 7),(.pos 1),(.pos 4)]),
   ((.exchange 21 7 6),[(.neg 21),(.neg 7),(.pos 2),(.pos 5)]),
   ((.exchange 22 7 6),[(.neg 22),(.neg 7),(.pos 0),(.pos 3),(.pos 6)]),
   ((.exchange 23 16 3),[(.neg 23),(.neg 16),(.pos 26),(.pos 30)]),
   ((.exchange 24 16 3),[(.neg 24),(.neg 16),(.pos 20),(.pos 27),(.pos 31)]),
   ((.exchange 25 16 3),[(.neg 25),(.neg 16),(.pos 21),(.pos 28),(.pos 32)]),
   ((.exchange 26 13 4),[(.neg 26),(.neg 13),(.pos 23),(.pos 30)]),
   ((.exchange 27 13 4),[(.neg 27),(.neg 13),(.pos 20),(.pos 24),(.pos 31)]),
   ((.exchange 28 13 4),[(.neg 28),(.neg 13),(.pos 21),(.pos 25),(.pos 32)]),
   ((.exchange 30 7 5),[(.neg 30),(.neg 7),(.pos 23),(.pos 26)]),
   ((.exchange 30 29 5),[(.neg 30),(.neg 29),(.pos 23),(.pos 26)]),
   ((.exchange 31 7 5),[(.neg 31),(.neg 7),(.pos 20),(.pos 24),(.pos 27)]),
   ((.exchange 31 29 5),[(.neg 31),(.neg 29),(.pos 24),(.pos 27)]),
   ((.exchange 32 7 5),[(.neg 32),(.neg 7),(.pos 21),(.pos 25),(.pos 28)]),
   ((.exchange 32 29 5),[(.neg 32),(.neg 29),(.pos 25),(.pos 28)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 29),(.pos 33),(.pos 34)]),
   ((.excluded 1),[(.neg 32),(.neg 31),(.neg 30),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 33),(.pos 34)]),
   ((.excluded 2),[(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 3),[(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 29),(.pos 33),(.pos 34)]),
   ((.excluded 4),[(.neg 34),(.neg 33),(.neg 29),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 30),(.pos 31),(.pos 32)]),
   ((.excluded 5),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25)]),
   ((.excluded 6),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 26),(.pos 27),(.pos 28)]),
   ((.excluded 7),[(.neg 34),(.neg 33),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 30),(.pos 31),(.pos 32)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 9,
    let w : Fin 9 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C6

/- Source: MatroidCatalogue/Cases/N7R3C6Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C6

noncomputable def certificates : List (Origin 35 9 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 9,
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 9) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 3)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 3, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N7R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C6.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C6.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C6

/- Source: MatroidCatalogue/Cases/N7R3C7Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C7

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 7
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (24000,15,15947400)) (.node 2 (.leaf (15416,15,15940232)) (.leaf (25080,17,15624840)))) (.node 5 (.node 4 (.leaf (32248,31,16205448)) (.leaf (25088,11,15685768))) (.node 6 (.leaf (1016,15,15854216)) (.leaf (25592,18,15854216))))) (.node 10 (.node 8 (.leaf (16320,17,15685768)) (.node 9 (.leaf (32704,18,15947400)) (.leaf (24120,17,15682184)))) (.node 12 (.node 11 (.leaf (32312,18,15940232)) (.leaf (24568,31,16148104))) (.node 13 (.leaf (16376,31,16137352)) (.leaf (32760,32,16434824))))))

noncomputable def models (i : Fin 14) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 14) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 14) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C7

/- Source: MatroidCatalogue/Cases/N7R3C7Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C7


noncomputable def certificates_0 : List (Origin 35 14 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 7 24 4),[(.neg 24),(.neg 7),(.pos 1),(.pos 23)]),
   ((.exchange 7 25 4),[(.neg 25),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 7 27 3),[(.neg 27),(.neg 7),(.pos 4),(.pos 26)]),
   ((.exchange 7 28 3),[(.neg 28),(.neg 7),(.pos 5),(.pos 26)]),
   ((.exchange 8 23 4),[(.neg 23),(.neg 8),(.pos 1),(.pos 24)]),
   ((.exchange 8 25 4),[(.neg 25),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 8 26 3),[(.neg 26),(.neg 8),(.pos 4),(.pos 27)]),
   ((.exchange 8 28 3),[(.neg 28),(.neg 8),(.pos 6),(.pos 27)]),
   ((.exchange 9 23 4),[(.neg 23),(.neg 9),(.pos 2),(.pos 25)]),
   ((.exchange 9 24 4),[(.neg 24),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 9 26 3),[(.neg 26),(.neg 9),(.pos 5),(.pos 28)]),
   ((.exchange 9 27 3),[(.neg 27),(.neg 9),(.pos 6),(.pos 28)]),
   ((.exchange 13 31 3),[(.neg 31),(.neg 13),(.pos 10),(.pos 30)]),
   ((.exchange 13 32 3),[(.neg 32),(.neg 13),(.pos 11),(.pos 30)]),
   ((.exchange 14 30 3),[(.neg 30),(.neg 14),(.pos 10),(.pos 31)]),
   ((.exchange 15 30 3),[(.neg 30),(.neg 15),(.pos 11),(.pos 32)]),
   ((.exchange 20 7 6),[(.neg 20),(.neg 7),(.pos 1),(.pos 4)]),
   ((.exchange 21 7 6),[(.neg 21),(.neg 7),(.pos 2),(.pos 5)]),
   ((.exchange 22 7 6),[(.neg 22),(.neg 7),(.pos 0),(.pos 3),(.pos 6)]),
   ((.exchange 23 16 3),[(.neg 23),(.neg 16),(.pos 26),(.pos 30)]),
   ((.exchange 23 34 0),[(.neg 34),(.neg 23),(.pos 29),(.pos 33)]),
   ((.exchange 24 16 3),[(.neg 24),(.neg 16),(.pos 20),(.pos 27),(.pos 31)]),
   ((.exchange 25 16 3),[(.neg 25),(.neg 16),(.pos 21),(.pos 28),(.pos 32)]),
   ((.exchange 25 19 2),[(.neg 25),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 26 13 4),[(.neg 26),(.neg 13),(.pos 23),(.pos 30)]),
   ((.exchange 26 19 0),[(.neg 26),(.neg 19),(.pos 29),(.pos 34)]),
   ((.exchange 27 13 4),[(.neg 27),(.neg 13),(.pos 20),(.pos 24),(.pos 31)]),
   ((.exchange 28 13 4),[(.neg 28),(.neg 13),(.pos 21),(.pos 25),(.pos 32)]),
   ((.exchange 29 13 4),[(.neg 29),(.neg 13),(.pos 23),(.pos 33)]),
   ((.exchange 29 15 4),[(.neg 29),(.neg 15),(.pos 25),(.pos 33)]),
   ((.exchange 29 16 3),[(.neg 29),(.neg 16),(.pos 26),(.pos 34)]),
   ((.exchange 30 7 5),[(.neg 30),(.neg 7),(.pos 23),(.pos 26)]),
   ((.exchange 30 9 5),[(.neg 30),(.neg 9),(.pos 21),(.pos 23),(.pos 26)]),
   ((.exchange 30 19 0),[(.neg 30),(.neg 19),(.pos 33),(.pos 34)]),
   ((.exchange 31 7 5),[(.neg 31),(.neg 7),(.pos 20),(.pos 24),(.pos 27)]),
   ((.exchange 31 9 5),[(.neg 31),(.neg 9),(.pos 22),(.pos 24),(.pos 27)]),
   ((.exchange 32 7 5),[(.neg 32),(.neg 7),(.pos 21),(.pos 25),(.pos 28)]),
   ((.exchange 32 9 5),[(.neg 32),(.neg 9),(.pos 25),(.pos 28)]),
   ((.exchange 33 7 5),[(.neg 33),(.neg 7),(.pos 23),(.pos 29)]),
   ((.exchange 33 16 3),[(.neg 33),(.neg 16),(.pos 30),(.pos 34)]),
   ((.exchange 33 26 5),[(.neg 33),(.neg 26),(.pos 23),(.pos 29)]),
   ((.exchange 34 13 4),[(.neg 34),(.neg 13),(.pos 30),(.pos 33)]),
   ((.exchange 34 25 5),[(.neg 34),(.neg 25),(.pos 28),(.pos 29)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 29),(.pos 33)]),
   ((.excluded 1),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 34)]),
   ((.excluded 2),[(.neg 34),(.neg 33),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 29),(.pos 30),(.pos 31),(.pos 32)]),
   ((.excluded 3),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 29)]),
   ((.excluded 4),[(.neg 34),(.neg 33),(.neg 29),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 30),(.pos 31),(.pos 32)]),
   ((.excluded 5),[(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 6),[(.neg 34),(.neg 33),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 30),(.pos 31),(.pos 32)]),
   ((.excluded 7),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 34)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25)]),
   ((.excluded 9),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 26),(.pos 27),(.pos 28),(.pos 33)]),
   ((.excluded 10),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 26),(.pos 27),(.pos 28)]),
   ((.excluded 11),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 33)]),
   ((.excluded 12),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 34)]),
   ((.excluded 13),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 14,
    let w : Fin 14 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C7

/- Source: MatroidCatalogue/Cases/N7R3C7Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C7

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C7.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C7.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C7

/- Source: MatroidCatalogue/Cases/N7R3C8Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C8

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 8
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 3 (.node 1 (.leaf (13056,12,15387848)) (.node 2 (.leaf (3264,12,15385139)) (.leaf (16320,19,16434824)))) (.node 5 (.node 4 (.leaf (30,12,15239987)) (.leaf (13086,19,16362248))) (.node 6 (.leaf (3294,19,16359980)) (.leaf (16350,33,16434824)))))

noncomputable def models (i : Fin 7) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 7) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 7) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C8

/- Source: MatroidCatalogue/Cases/N7R3C8Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C8


noncomputable def certificates_0 : List (Origin 35 7 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
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
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.exchange 5 22 4),[(.neg 22),(.neg 5),(.pos 0),(.pos 21)]),
   ((.exchange 5 23 4),[(.neg 23),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 5 24 4),[(.neg 24),(.neg 5),(.pos 0),(.pos 2),(.pos 21)]),
   ((.exchange 5 31 2),[(.neg 31),(.neg 5),(.pos 4),(.pos 16),(.pos 26)]),
   ((.exchange 5 32 0),[(.neg 32),(.neg 5),(.pos 18),(.pos 28)]),
   ((.exchange 5 33 0),[(.neg 33),(.neg 5),(.pos 9),(.pos 18),(.pos 28)]),
   ((.exchange 6 21 4),[(.neg 21),(.neg 6),(.pos 0),(.pos 22)]),
   ((.exchange 6 23 4),[(.neg 23),(.neg 6),(.pos 0),(.pos 3),(.pos 22)]),
   ((.exchange 6 24 4),[(.neg 24),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 6 31 2),[(.neg 31),(.neg 6),(.pos 17),(.pos 27)]),
   ((.exchange 7 21 4),[(.neg 21),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 7 22 4),[(.neg 22),(.neg 7),(.pos 1),(.pos 2),(.pos 23)]),
   ((.exchange 7 24 4),[(.neg 24),(.neg 7),(.pos 1),(.pos 23)]),
   ((.exchange 7 32 0),[(.neg 32),(.neg 7),(.pos 9),(.pos 19),(.pos 29)]),
   ((.exchange 7 33 0),[(.neg 33),(.neg 7),(.pos 19),(.pos 29)]),
   ((.exchange 8 21 4),[(.neg 21),(.neg 8),(.pos 1),(.pos 3),(.pos 24)]),
   ((.exchange 8 22 4),[(.neg 22),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 8 23 4),[(.neg 23),(.neg 8),(.pos 1),(.pos 24)]),
   ((.exchange 11 28 0),[(.neg 28),(.neg 11),(.pos 18),(.pos 32)]),
   ((.exchange 11 29 0),[(.neg 29),(.neg 11),(.pos 15),(.pos 18),(.pos 32)]),
   ((.exchange 11 31 2),[(.neg 31),(.neg 11),(.pos 10),(.pos 30)]),
   ((.exchange 11 33 0),[(.neg 33),(.neg 11),(.pos 15),(.pos 32)]),
   ((.exchange 12 26 2),[(.neg 26),(.neg 12),(.pos 10),(.pos 17),(.pos 31)]),
   ((.exchange 12 27 2),[(.neg 27),(.neg 12),(.pos 17),(.pos 31)]),
   ((.exchange 12 30 2),[(.neg 30),(.neg 12),(.pos 10),(.pos 31)]),
   ((.exchange 13 28 0),[(.neg 28),(.neg 13),(.pos 15),(.pos 19),(.pos 33)]),
   ((.exchange 13 29 0),[(.neg 29),(.neg 13),(.pos 19),(.pos 33)]),
   ((.exchange 13 32 0),[(.neg 32),(.neg 13),(.pos 15),(.pos 33)]),
   ((.exchange 20 5 6),[(.neg 20),(.neg 5),(.pos 0),(.pos 4)]),
   ((.exchange 25 5 6),[(.neg 25),(.neg 5),(.pos 2),(.pos 9)]),
   ((.exchange 34 5 6),[(.neg 34),(.neg 5),(.pos 16),(.pos 18)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 30),(.pos 31),(.pos 34)]),
   ((.excluded 1),[(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 28),(.pos 29),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 2),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 34)]),
   ((.excluded 3),[(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 4),[(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 26),(.pos 27),(.pos 30),(.pos 31),(.pos 34)]),
   ((.excluded 5),[(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 28),(.pos 29),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 6),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 34)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 7,
    let w : Fin 7 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C8

/- Source: MatroidCatalogue/Cases/N7R3C8Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C8

noncomputable def certificates : List (Origin 35 7 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 7,
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 7) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 3)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 3, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N7R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C8.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C8.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C8

/- Source: MatroidCatalogue/Cases/N7R3C9Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C9

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 9
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 4 (.node 2 (.node 1 (.leaf (13056,13,15423688)) (.leaf (19648,14,15421987))) (.node 3 (.leaf (32704,20,15947400)) (.leaf (12318,19,15674120)))) (.node 6 (.node 5 (.leaf (798,19,15559432)) (.leaf (13086,23,15838536))) (.node 7 (.leaf (31966,34,16205448)) (.node 8 (.leaf (20446,34,16148104)) (.leaf (32734,35,16434824))))))

noncomputable def models (i : Fin 9) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 9) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 9) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C9

/- Source: MatroidCatalogue/Cases/N7R3C9Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C9


noncomputable def certificates_0 : List (Origin 35 9 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
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
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 5 22 4),[(.neg 22),(.neg 5),(.pos 0),(.pos 21)]),
   ((.exchange 5 29 0),[(.neg 29),(.neg 5),(.pos 9),(.pos 28)]),
   ((.exchange 5 31 2),[(.neg 31),(.neg 5),(.pos 4),(.pos 16),(.pos 26)]),
   ((.exchange 6 21 4),[(.neg 21),(.neg 6),(.pos 0),(.pos 22)]),
   ((.exchange 6 23 4),[(.neg 23),(.neg 6),(.pos 0),(.pos 3),(.pos 22)]),
   ((.exchange 6 24 4),[(.neg 24),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 6 31 2),[(.neg 31),(.neg 6),(.pos 17),(.pos 27)]),
   ((.exchange 7 22 4),[(.neg 22),(.neg 7),(.pos 1),(.pos 2),(.pos 23)]),
   ((.exchange 7 28 0),[(.neg 28),(.neg 7),(.pos 9),(.pos 29)]),
   ((.exchange 8 22 4),[(.neg 22),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 11 31 2),[(.neg 31),(.neg 11),(.pos 10),(.pos 30)]),
   ((.exchange 11 33 0),[(.neg 33),(.neg 11),(.pos 15),(.pos 32)]),
   ((.exchange 12 26 2),[(.neg 26),(.neg 12),(.pos 10),(.pos 17),(.pos 31)]),
   ((.exchange 12 27 2),[(.neg 27),(.neg 12),(.pos 17),(.pos 31)]),
   ((.exchange 12 30 2),[(.neg 30),(.neg 12),(.pos 10),(.pos 31)]),
   ((.exchange 12 34 2),[(.neg 34),(.neg 12),(.pos 17),(.pos 31)]),
   ((.exchange 13 32 0),[(.neg 32),(.neg 13),(.pos 15),(.pos 33)]),
   ((.exchange 18 31 2),[(.neg 31),(.neg 18),(.pos 17),(.pos 34)]),
   ((.exchange 20 5 6),[(.neg 20),(.neg 5),(.pos 0),(.pos 4)]),
   ((.exchange 21 18 0),[(.neg 21),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 22 18 1),[(.neg 22),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 23 18 0),[(.neg 23),(.neg 18),(.pos 25),(.pos 29),(.pos 33)]),
   ((.exchange 23 19 0),[(.neg 23),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 24 19 1),[(.neg 24),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 25 5 6),[(.neg 25),(.neg 5),(.pos 2),(.pos 9)]),
   ((.exchange 28 11 4),[(.neg 28),(.neg 11),(.pos 21),(.pos 32)]),
   ((.exchange 28 12 4),[(.neg 28),(.neg 12),(.pos 22),(.pos 32)]),
   ((.exchange 29 11 4),[(.neg 29),(.neg 11),(.pos 23),(.pos 25),(.pos 33)]),
   ((.exchange 29 12 4),[(.neg 29),(.neg 12),(.pos 24),(.pos 25),(.pos 33)]),
   ((.exchange 32 6 5),[(.neg 32),(.neg 6),(.pos 22),(.pos 28)]),
   ((.exchange 33 5 5),[(.neg 33),(.neg 5),(.pos 23),(.pos 25),(.pos 29)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 30),(.pos 31),(.pos 34)]),
   ((.excluded 1),[(.neg 34),(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 28),(.pos 29),(.pos 32),(.pos 33)]),
   ((.excluded 2),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25)]),
   ((.excluded 3),[(.neg 33),(.neg 32),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 34)]),
   ((.excluded 4),[(.neg 29),(.neg 28),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 26),(.pos 27),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 5),[(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 26),(.pos 27),(.pos 30),(.pos 31),(.pos 34)]),
   ((.excluded 6),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 28),(.pos 29)]),
   ((.excluded 7),[(.neg 34),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 32),(.pos 33)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 9,
    let w : Fin 9 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C9

/- Source: MatroidCatalogue/Cases/N7R3C9Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C9

noncomputable def certificates : List (Origin 35 9 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 9,
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 9) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 3)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 3, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N7R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C9.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C9.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C9

/- Source: MatroidCatalogue/Cases/N7R3C10Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C10

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 10
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (16320,21,15947400)) (.node 2 (.leaf (29440,15,15423688)) (.leaf (19648,15,15421987)))) (.node 5 (.node 4 (.leaf (32704,22,15947400)) (.leaf (15390,33,16205448))) (.node 6 (.leaf (990,33,16148104)) (.leaf (16350,36,16434824))))) (.node 10 (.node 8 (.leaf (20254,34,15918728)) (.node 9 (.leaf (32542,35,16205448)) (.leaf (20446,35,16146970)))) (.node 12 (.node 11 (.leaf (28894,34,15947400)) (.leaf (31966,35,16204314))) (.node 13 (.leaf (29662,35,16148104)) (.leaf (32734,37,16434824))))))

noncomputable def models (i : Fin 14) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 14) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 14) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C10

/- Source: MatroidCatalogue/Cases/N7R3C10Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C10


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
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 5 22 4),[(.neg 22),(.neg 5),(.pos 0),(.pos 21)]),
   ((.exchange 5 23 4),[(.neg 23),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 5 24 4),[(.neg 24),(.neg 5),(.pos 0),(.pos 2),(.pos 21)]),
   ((.exchange 5 27 2),[(.neg 27),(.neg 5),(.pos 4),(.pos 26)]),
   ((.exchange 5 29 0),[(.neg 29),(.neg 5),(.pos 9),(.pos 28)]),
   ((.exchange 6 21 4),[(.neg 21),(.neg 6),(.pos 0),(.pos 22)]),
   ((.exchange 6 23 4),[(.neg 23),(.neg 6),(.pos 0),(.pos 3),(.pos 22)]),
   ((.exchange 6 24 4),[(.neg 24),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 6 26 2),[(.neg 26),(.neg 6),(.pos 4),(.pos 27)]),
   ((.exchange 7 21 4),[(.neg 21),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 7 22 4),[(.neg 22),(.neg 7),(.pos 1),(.pos 2),(.pos 23)]),
   ((.exchange 7 24 4),[(.neg 24),(.neg 7),(.pos 1),(.pos 23)]),
   ((.exchange 7 28 0),[(.neg 28),(.neg 7),(.pos 9),(.pos 29)]),
   ((.exchange 8 21 4),[(.neg 21),(.neg 8),(.pos 1),(.pos 3),(.pos 24)]),
   ((.exchange 8 22 4),[(.neg 22),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 8 23 4),[(.neg 23),(.neg 8),(.pos 1),(.pos 24)]),
   ((.exchange 11 31 2),[(.neg 31),(.neg 11),(.pos 10),(.pos 30)]),
   ((.exchange 11 33 0),[(.neg 33),(.neg 11),(.pos 15),(.pos 32)]),
   ((.exchange 12 30 2),[(.neg 30),(.neg 12),(.pos 10),(.pos 31)]),
   ((.exchange 13 32 0),[(.neg 32),(.neg 13),(.pos 15),(.pos 33)]),
   ((.exchange 20 5 6),[(.neg 20),(.neg 5),(.pos 0),(.pos 4)]),
   ((.exchange 21 16 2),[(.neg 21),(.neg 16),(.pos 26),(.pos 30)]),
   ((.exchange 21 18 0),[(.neg 21),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 22 16 2),[(.neg 22),(.neg 16),(.pos 20),(.pos 27),(.pos 31)]),
   ((.exchange 22 18 1),[(.neg 22),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 23 18 0),[(.neg 23),(.neg 18),(.pos 25),(.pos 29),(.pos 33)]),
   ((.exchange 23 19 0),[(.neg 23),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 24 19 1),[(.neg 24),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 25 5 6),[(.neg 25),(.neg 5),(.pos 2),(.pos 9)]),
   ((.exchange 26 11 4),[(.neg 26),(.neg 11),(.pos 21),(.pos 30)]),
   ((.exchange 26 18 0),[(.neg 26),(.neg 18),(.pos 28),(.pos 34)]),
   ((.exchange 26 19 0),[(.neg 26),(.neg 19),(.pos 29),(.pos 34)]),
   ((.exchange 27 11 4),[(.neg 27),(.neg 11),(.pos 20),(.pos 22),(.pos 31)]),
   ((.exchange 28 11 4),[(.neg 28),(.neg 11),(.pos 21),(.pos 32)]),
   ((.exchange 28 12 4),[(.neg 28),(.neg 12),(.pos 22),(.pos 32)]),
   ((.exchange 28 16 2),[(.neg 28),(.neg 16),(.pos 26),(.pos 34)]),
   ((.exchange 29 11 4),[(.neg 29),(.neg 11),(.pos 23),(.pos 25),(.pos 33)]),
   ((.exchange 29 12 4),[(.neg 29),(.neg 12),(.pos 24),(.pos 25),(.pos 33)]),
   ((.exchange 29 13 4),[(.neg 29),(.neg 13),(.pos 23),(.pos 33)]),
   ((.exchange 29 16 3),[(.neg 29),(.neg 16),(.pos 26),(.pos 34)]),
   ((.exchange 30 6 5),[(.neg 30),(.neg 6),(.pos 20),(.pos 21),(.pos 26)]),
   ((.exchange 30 8 5),[(.neg 30),(.neg 8),(.pos 20),(.pos 23),(.pos 26)]),
   ((.exchange 30 19 0),[(.neg 30),(.neg 19),(.pos 33),(.pos 34)]),
   ((.exchange 31 6 5),[(.neg 31),(.neg 6),(.pos 22),(.pos 27)]),
   ((.exchange 31 8 5),[(.neg 31),(.neg 8),(.pos 24),(.pos 27)]),
   ((.exchange 32 5 5),[(.neg 32),(.neg 5),(.pos 21),(.pos 28)]),
   ((.exchange 32 7 5),[(.neg 32),(.neg 7),(.pos 21),(.pos 25),(.pos 28)]),
   ((.exchange 32 8 5),[(.neg 32),(.neg 8),(.pos 22),(.pos 25),(.pos 28)]),
   ((.exchange 32 17 2),[(.neg 32),(.neg 17),(.pos 31),(.pos 34)]),
   ((.exchange 33 5 5),[(.neg 33),(.neg 5),(.pos 23),(.pos 25),(.pos 29)]),
   ((.exchange 33 7 5),[(.neg 33),(.neg 7),(.pos 23),(.pos 29)]),
   ((.exchange 33 8 5),[(.neg 33),(.neg 8),(.pos 24),(.pos 29)]),
   ((.exchange 34 5 5),[(.neg 34),(.neg 5),(.pos 26),(.pos 28)]),
   ((.exchange 34 6 5),[(.neg 34),(.neg 6),(.pos 27),(.pos 28)]),
   ((.exchange 34 7 5),[(.neg 34),(.neg 7),(.pos 26),(.pos 29)]),
   ((.exchange 34 8 5),[(.neg 34),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 34 11 4),[(.neg 34),(.neg 11),(.pos 30),(.pos 32)]),
   ((.exchange 34 22 5),[(.neg 34),(.neg 22),(.pos 27),(.pos 28)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 34)]),
   ((.excluded 1),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 30),(.pos 31)]),
   ((.excluded 2),[(.neg 34),(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 28),(.pos 29),(.pos 32),(.pos 33)]),
   ((.excluded 3),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25)]),
   ((.excluded 4),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 34)]),
   ((.excluded 5),[(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 6),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 34)]),
   ((.excluded 7),[(.neg 34),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 26),(.pos 27),(.pos 32),(.pos 33)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 26),(.pos 27)]),
   ((.excluded 9),[(.neg 34),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 32),(.pos 33)]),
   ((.excluded 10),[(.neg 34),(.neg 33),(.neg 32),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 28),(.pos 29),(.pos 30),(.pos 31)]),
   ((.excluded 11),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 28),(.pos 29)]),
   ((.excluded 12),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 30),(.pos 31)]),
   ((.excluded 13),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 14,
    let w : Fin 14 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C10

/- Source: MatroidCatalogue/Cases/N7R3C10Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C10

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C10.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C10.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C10

/- Source: MatroidCatalogue/Cases/N7R3C11Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C11

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 11
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (13056,16,15387848)) (.node 2 (.leaf (28352,20,15685768)) (.leaf (24000,20,15684872)))) (.node 5 (.node 4 (.leaf (32704,24,15947400)) (.leaf (12350,20,15609160))) (.node 6 (.leaf (830,20,15551816)) (.leaf (13118,24,15838536))))) (.node 10 (.node 8 (.leaf (24318,38,16434824)) (.node 9 (.leaf (32510,39,16431240)) (.leaf (24574,39,16373000)))) (.node 12 (.node 11 (.leaf (28158,38,16406152)) (.leaf (32254,39,16430344))) (.node 13 (.leaf (28670,39,16373896)) (.leaf (32766,40,16434824))))))

noncomputable def models (i : Fin 14) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 14) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 14) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C11

/- Source: MatroidCatalogue/Cases/N7R3C11Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C11


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
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 5 22 4),[(.neg 22),(.neg 5),(.pos 0),(.pos 21)]),
   ((.exchange 5 23 4),[(.neg 23),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 5 24 4),[(.neg 24),(.neg 5),(.pos 0),(.pos 2),(.pos 21)]),
   ((.exchange 5 25 4),[(.neg 25),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 5 30 2),[(.neg 30),(.neg 5),(.pos 16),(.pos 26)]),
   ((.exchange 6 21 4),[(.neg 21),(.neg 6),(.pos 0),(.pos 22)]),
   ((.exchange 6 25 4),[(.neg 25),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 6 30 2),[(.neg 30),(.neg 6),(.pos 4),(.pos 17),(.pos 27)]),
   ((.exchange 7 21 4),[(.neg 21),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 7 25 4),[(.neg 25),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 8 21 4),[(.neg 21),(.neg 8),(.pos 1),(.pos 3),(.pos 24)]),
   ((.exchange 8 25 4),[(.neg 25),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 9 21 4),[(.neg 21),(.neg 9),(.pos 2),(.pos 25)]),
   ((.exchange 9 22 4),[(.neg 22),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 9 23 4),[(.neg 23),(.neg 9),(.pos 2),(.pos 25)]),
   ((.exchange 9 24 4),[(.neg 24),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 11 26 2),[(.neg 26),(.neg 11),(.pos 16),(.pos 30)]),
   ((.exchange 11 27 2),[(.neg 27),(.neg 11),(.pos 10),(.pos 16),(.pos 30)]),
   ((.exchange 11 31 2),[(.neg 31),(.neg 11),(.pos 10),(.pos 30)]),
   ((.exchange 11 34 2),[(.neg 34),(.neg 11),(.pos 16),(.pos 30)]),
   ((.exchange 12 30 2),[(.neg 30),(.neg 12),(.pos 10),(.pos 31)]),
   ((.exchange 18 30 2),[(.neg 30),(.neg 18),(.pos 16),(.pos 34)]),
   ((.exchange 20 5 6),[(.neg 20),(.neg 5),(.pos 0),(.pos 4)]),
   ((.exchange 21 18 0),[(.neg 21),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 21 34 0),[(.neg 34),(.neg 21),(.pos 28),(.pos 32)]),
   ((.exchange 23 19 0),[(.neg 23),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 25 19 2),[(.neg 25),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 26 9 0),[(.neg 26),(.neg 9),(.pos 28),(.pos 29)]),
   ((.exchange 28 7 2),[(.neg 28),(.neg 7),(.pos 26),(.pos 29)]),
   ((.exchange 28 11 4),[(.neg 28),(.neg 11),(.pos 21),(.pos 32)]),
   ((.exchange 29 11 4),[(.neg 29),(.neg 11),(.pos 23),(.pos 25),(.pos 33)]),
   ((.exchange 29 15 4),[(.neg 29),(.neg 15),(.pos 25),(.pos 33)]),
   ((.exchange 29 18 3),[(.neg 29),(.neg 18),(.pos 28),(.pos 34)]),
   ((.exchange 32 5 5),[(.neg 32),(.neg 5),(.pos 21),(.pos 28)]),
   ((.exchange 32 7 2),[(.neg 32),(.neg 7),(.pos 30),(.pos 33),(.pos 34)]),
   ((.exchange 32 9 5),[(.neg 32),(.neg 9),(.pos 25),(.pos 28)]),
   ((.exchange 33 6 5),[(.neg 33),(.neg 6),(.pos 24),(.pos 25),(.pos 29)]),
   ((.exchange 33 7 5),[(.neg 33),(.neg 7),(.pos 23),(.pos 29)]),
   ((.exchange 33 18 3),[(.neg 33),(.neg 18),(.pos 32),(.pos 34)]),
   ((.exchange 34 15 4),[(.neg 34),(.neg 15),(.pos 32),(.pos 33)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 30),(.pos 31),(.pos 34)]),
   ((.excluded 1),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 28),(.pos 32)]),
   ((.excluded 2),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 29),(.pos 33)]),
   ((.excluded 3),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25)]),
   ((.excluded 4),[(.neg 33),(.neg 32),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 34)]),
   ((.excluded 5),[(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 6),[(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27),(.pos 30),(.pos 31),(.pos 34)]),
   ((.excluded 7),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 28),(.pos 33)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 28)]),
   ((.excluded 9),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 33)]),
   ((.excluded 10),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 29),(.pos 32)]),
   ((.excluded 11),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 29)]),
   ((.excluded 12),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 32)]),
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C11

/- Source: MatroidCatalogue/Cases/N7R3C11Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C11

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C11.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C11.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C11

