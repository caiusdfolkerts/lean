module
public import MatroidCatalogue.Definitions
public import MatroidCases.N7R2C9
import all MatroidCases.N7R2C9
public import MatroidCases.N7R3C0
import all MatroidCases.N7R3C0
public import MatroidCases.N7R3C1
import all MatroidCases.N7R3C1
public import MatroidCases.N7R3C2
import all MatroidCases.N7R3C2
public import MatroidCases.N7R3C3
import all MatroidCases.N7R3C3
public import MatroidCases.N7R3C4
import all MatroidCases.N7R3C4
public import MatroidCases.N7R3C5
import all MatroidCases.N7R3C5

@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N7R2C9Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C9

abbrev U := N7R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R2.family 9
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 16) (.leaf 17))) (.node 4 (.leaf 18) (.node 5 (.leaf 19) (.leaf 20))))
noncomputable def newIndex (i : Fin 6) : Fin 21 := Fin.ofNat 21 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 3 (.node 1 (.leaf (62,12,15161552)) (.node 2 (.leaf (61,12,15161538)) (.leaf (59,12,15161370)))) (.node 5 (.node 4 (.leaf (55,12,15159578)) (.leaf (47,12,15141658))) (.node 6 (.leaf (31,12,14969626)) (.leaf (63,13,16434824)))))

noncomputable def models (i : Fin 7) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 7) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 7) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 21, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 21, (6 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C9

/- Source: MatroidCatalogue/Cases/N7R2C9Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C9


noncomputable def certificates_0 : List (Origin 21 7 × List Sat.Literal) :=
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
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.exchange 15 2 0),[(.neg 15),(.neg 2),(.pos 16),(.pos 17)]),
   ((.exchange 15 4 0),[(.neg 15),(.neg 4),(.pos 16),(.pos 18)]),
   ((.exchange 15 7 0),[(.neg 15),(.neg 7),(.pos 16),(.pos 19)]),
   ((.exchange 15 11 0),[(.neg 15),(.neg 11),(.pos 16),(.pos 20)]),
   ((.exchange 15 12 0),[(.neg 15),(.neg 12),(.pos 17),(.pos 20)]),
   ((.exchange 15 13 0),[(.neg 15),(.neg 13),(.pos 18),(.pos 20)]),
   ((.exchange 15 14 0),[(.neg 15),(.neg 14),(.pos 19),(.pos 20)]),
   ((.exchange 16 1 1),[(.neg 16),(.neg 1),(.pos 15),(.pos 17)]),
   ((.exchange 16 3 1),[(.neg 16),(.neg 3),(.pos 15),(.pos 18)]),
   ((.exchange 16 6 1),[(.neg 16),(.neg 6),(.pos 15),(.pos 19)]),
   ((.exchange 16 8 1),[(.neg 16),(.neg 8),(.pos 17),(.pos 19)]),
   ((.exchange 16 9 1),[(.neg 16),(.neg 9),(.pos 18),(.pos 19)]),
   ((.exchange 16 10 1),[(.neg 16),(.neg 10),(.pos 15),(.pos 20)]),
   ((.exchange 17 0 2),[(.neg 17),(.neg 0),(.pos 15),(.pos 16)]),
   ((.exchange 18 2 3),[(.neg 18),(.neg 2),(.pos 16),(.pos 17)]),
   ((.exchange 19 2 4),[(.neg 19),(.neg 2),(.pos 16),(.pos 17)]),
   ((.exchange 19 5 4),[(.neg 19),(.neg 5),(.pos 17),(.pos 18)]),
   ((.exchange 20 2 5),[(.neg 20),(.neg 2),(.pos 16),(.pos 17)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 0),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15)]),
   ((.excluded 1),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16)]),
   ((.excluded 2),[(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17)]),
   ((.excluded 3),[(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18)]),
   ((.excluded 4),[(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19)]),
   ((.excluded 5),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20)]),
   ((.excluded 6),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 7,
    let w : Fin 7 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C9

/- Source: MatroidCatalogue/Cases/N7R2C9Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C9

noncomputable def certificates : List (Origin 21 7 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 7,
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 7) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 2)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 2, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N7R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R2C9.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R2C9.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 2 (target w),family_mem 7 2 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C9

/- Source: MatroidCatalogue/Cases/N7R3C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C0

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 0
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 3 (.node 1 (.leaf (15360,1,16205448)) (.node 2 (.leaf (960,1,16148104)) (.leaf (16320,10,16434824)))) (.node 5 (.node 4 (.leaf (16384,0,15947400)) (.leaf (31744,2,16205448))) (.node 6 (.leaf (17344,2,16148104)) (.leaf (32704,11,16434824)))))

noncomputable def models (i : Fin 7) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 7) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 7) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C0

/- Source: MatroidCatalogue/Cases/N7R3C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C0


noncomputable def certificates_0 : List (Origin 35 7 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 16 27 5),[(.neg 27),(.neg 16),(.pos 4),(.pos 26)]),
   ((.exchange 16 28 5),[(.neg 28),(.neg 16),(.pos 5),(.pos 26)]),
   ((.exchange 16 31 4),[(.neg 31),(.neg 16),(.pos 10),(.pos 30)]),
   ((.exchange 17 26 5),[(.neg 26),(.neg 17),(.pos 4),(.pos 27)]),
   ((.exchange 17 28 5),[(.neg 28),(.neg 17),(.pos 6),(.pos 27)]),
   ((.exchange 17 29 5),[(.neg 29),(.neg 17),(.pos 8),(.pos 27)]),
   ((.exchange 17 30 4),[(.neg 30),(.neg 17),(.pos 10),(.pos 31)]),
   ((.exchange 17 32 4),[(.neg 32),(.neg 17),(.pos 12),(.pos 31)]),
   ((.exchange 17 33 4),[(.neg 33),(.neg 17),(.pos 14),(.pos 31)]),
   ((.exchange 18 26 5),[(.neg 26),(.neg 18),(.pos 5),(.pos 28)]),
   ((.exchange 18 27 5),[(.neg 27),(.neg 18),(.pos 6),(.pos 28)]),
   ((.exchange 18 29 5),[(.neg 29),(.neg 18),(.pos 9),(.pos 28)]),
   ((.exchange 18 31 4),[(.neg 31),(.neg 18),(.pos 12),(.pos 32)]),
   ((.exchange 19 27 5),[(.neg 27),(.neg 19),(.pos 8),(.pos 29)]),
   ((.exchange 19 28 5),[(.neg 28),(.neg 19),(.pos 9),(.pos 29)]),
   ((.exchange 19 31 4),[(.neg 31),(.neg 19),(.pos 14),(.pos 33)]),
   ((.exchange 20 16 6),[(.neg 20),(.neg 16),(.pos 4),(.pos 10)]),
   ((.exchange 21 16 6),[(.neg 21),(.neg 16),(.pos 5),(.pos 11)]),
   ((.exchange 22 16 6),[(.neg 22),(.neg 16),(.pos 0),(.pos 6),(.pos 12)]),
   ((.exchange 23 16 6),[(.neg 23),(.neg 16),(.pos 7),(.pos 13)]),
   ((.exchange 24 16 6),[(.neg 24),(.neg 16),(.pos 1),(.pos 8),(.pos 14)]),
   ((.exchange 25 16 6),[(.neg 25),(.neg 16),(.pos 2),(.pos 9),(.pos 15)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 34)]),
   ((.excluded 1),[(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 2),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 34)]),
   ((.excluded 3),[(.neg 34),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33)]),
   ((.excluded 4),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29)]),
   ((.excluded 5),[(.neg 34),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 30),(.pos 31),(.pos 32),(.pos 33)]),
   ((.excluded 6),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 7,
    let w : Fin 7 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C0

/- Source: MatroidCatalogue/Cases/N7R3C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C0

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C0

/- Source: MatroidCatalogue/Cases/N7R3C1Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C1

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 1
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 3 (.node 1 (.leaf (24576,1,15685768)) (.node 2 (.leaf (7168,3,16205448)) (.leaf (31744,4,16205448)))) (.node 5 (.node 4 (.leaf (504,12,16148104)) (.leaf (25080,13,16434824))) (.node 6 (.leaf (7672,14,16434824)) (.leaf (32248,15,16434824)))))

noncomputable def models (i : Fin 7) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 7) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 7) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C1

/- Source: MatroidCatalogue/Cases/N7R3C1Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C1


noncomputable def certificates_0 : List (Origin 35 7 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.exchange 13 24 5),[(.neg 24),(.neg 13),(.pos 1),(.pos 23)]),
   ((.exchange 13 25 5),[(.neg 25),(.neg 13),(.pos 2),(.pos 23)]),
   ((.exchange 13 26 5),[(.neg 26),(.neg 13),(.pos 7),(.pos 23)]),
   ((.exchange 13 27 5),[(.neg 27),(.neg 13),(.pos 1),(.pos 7),(.pos 23)]),
   ((.exchange 13 28 5),[(.neg 28),(.neg 13),(.pos 2),(.pos 7),(.pos 23)]),
   ((.exchange 13 31 3),[(.neg 31),(.neg 13),(.pos 10),(.pos 30)]),
   ((.exchange 13 34 0),[(.neg 34),(.neg 13),(.pos 19),(.pos 33)]),
   ((.exchange 14 23 5),[(.neg 23),(.neg 14),(.pos 1),(.pos 24)]),
   ((.exchange 14 25 5),[(.neg 25),(.neg 14),(.pos 3),(.pos 24)]),
   ((.exchange 14 28 5),[(.neg 28),(.neg 14),(.pos 3),(.pos 8),(.pos 24)]),
   ((.exchange 14 30 3),[(.neg 30),(.neg 14),(.pos 10),(.pos 31)]),
   ((.exchange 14 32 3),[(.neg 32),(.neg 14),(.pos 12),(.pos 31)]),
   ((.exchange 15 23 5),[(.neg 23),(.neg 15),(.pos 2),(.pos 25)]),
   ((.exchange 15 24 5),[(.neg 24),(.neg 15),(.pos 3),(.pos 25)]),
   ((.exchange 15 26 5),[(.neg 26),(.neg 15),(.pos 2),(.pos 9),(.pos 25)]),
   ((.exchange 15 27 5),[(.neg 27),(.neg 15),(.pos 3),(.pos 9),(.pos 25)]),
   ((.exchange 15 28 5),[(.neg 28),(.neg 15),(.pos 9),(.pos 25)]),
   ((.exchange 15 31 3),[(.neg 31),(.neg 15),(.pos 12),(.pos 32)]),
   ((.exchange 16 23 5),[(.neg 23),(.neg 16),(.pos 7),(.pos 26)]),
   ((.exchange 16 25 5),[(.neg 25),(.neg 16),(.pos 5),(.pos 7),(.pos 26)]),
   ((.exchange 16 28 5),[(.neg 28),(.neg 16),(.pos 5),(.pos 26)]),
   ((.exchange 16 33 0),[(.neg 33),(.neg 16),(.pos 19),(.pos 34)]),
   ((.exchange 17 23 5),[(.neg 23),(.neg 17),(.pos 4),(.pos 8),(.pos 27)]),
   ((.exchange 17 25 5),[(.neg 25),(.neg 17),(.pos 6),(.pos 8),(.pos 27)]),
   ((.exchange 17 28 5),[(.neg 28),(.neg 17),(.pos 6),(.pos 27)]),
   ((.exchange 18 23 5),[(.neg 23),(.neg 18),(.pos 5),(.pos 9),(.pos 28)]),
   ((.exchange 18 24 5),[(.neg 24),(.neg 18),(.pos 6),(.pos 9),(.pos 28)]),
   ((.exchange 18 25 5),[(.neg 25),(.neg 18),(.pos 9),(.pos 28)]),
   ((.exchange 18 26 5),[(.neg 26),(.neg 18),(.pos 5),(.pos 28)]),
   ((.exchange 18 27 5),[(.neg 27),(.neg 18),(.pos 6),(.pos 28)]),
   ((.exchange 20 13 6),[(.neg 20),(.neg 13),(.pos 1),(.pos 10)]),
   ((.exchange 21 13 6),[(.neg 21),(.neg 13),(.pos 2),(.pos 11)]),
   ((.exchange 22 13 6),[(.neg 22),(.neg 13),(.pos 0),(.pos 3),(.pos 12)]),
   ((.exchange 29 13 6),[(.neg 29),(.neg 13),(.pos 7),(.pos 19)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 33),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32)]),
   ((.excluded 1),[(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 33),(.pos 34)]),
   ((.excluded 2),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29)]),
   ((.excluded 3),[(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 4),[(.neg 34),(.neg 33),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 29),(.pos 30),(.pos 31),(.pos 32)]),
   ((.excluded 5),[(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 29),(.pos 33),(.pos 34)]),
   ((.excluded 6),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 29)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 7,
    let w : Fin 7 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C1

/- Source: MatroidCatalogue/Cases/N7R3C1Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C1

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C1.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C1.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C1

/- Source: MatroidCatalogue/Cases/N7R3C2Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C2

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 2
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 4 (.node 2 (.node 1 (.leaf (24576,2,15685768)) (.leaf (23552,4,15947400))) (.node 3 (.leaf (15360,4,15940232)) (.leaf (31744,5,16205448)))) (.node 6 (.node 5 (.leaf (1016,13,15854216)) (.leaf (25592,16,16148104))) (.node 7 (.leaf (24568,17,16434824)) (.node 8 (.leaf (16376,17,16431240)) (.leaf (32760,18,16434824))))))

noncomputable def models (i : Fin 9) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 9) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 9) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C2

/- Source: MatroidCatalogue/Cases/N7R3C2Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C2


noncomputable def certificates_0 : List (Origin 35 9 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 13 25 5),[(.neg 25),(.neg 13),(.pos 2),(.pos 23)]),
   ((.exchange 13 28 5),[(.neg 28),(.neg 13),(.pos 2),(.pos 7),(.pos 23)]),
   ((.exchange 13 31 3),[(.neg 31),(.neg 13),(.pos 10),(.pos 30)]),
   ((.exchange 14 25 5),[(.neg 25),(.neg 14),(.pos 3),(.pos 24)]),
   ((.exchange 14 28 5),[(.neg 28),(.neg 14),(.pos 3),(.pos 8),(.pos 24)]),
   ((.exchange 14 30 3),[(.neg 30),(.neg 14),(.pos 10),(.pos 31)]),
   ((.exchange 14 32 3),[(.neg 32),(.neg 14),(.pos 12),(.pos 31)]),
   ((.exchange 15 23 5),[(.neg 23),(.neg 15),(.pos 2),(.pos 25)]),
   ((.exchange 15 24 5),[(.neg 24),(.neg 15),(.pos 3),(.pos 25)]),
   ((.exchange 15 26 5),[(.neg 26),(.neg 15),(.pos 2),(.pos 9),(.pos 25)]),
   ((.exchange 15 27 5),[(.neg 27),(.neg 15),(.pos 3),(.pos 9),(.pos 25)]),
   ((.exchange 15 28 5),[(.neg 28),(.neg 15),(.pos 9),(.pos 25)]),
   ((.exchange 15 29 5),[(.neg 29),(.neg 15),(.pos 9),(.pos 25)]),
   ((.exchange 15 31 3),[(.neg 31),(.neg 15),(.pos 12),(.pos 32)]),
   ((.exchange 16 25 5),[(.neg 25),(.neg 16),(.pos 5),(.pos 7),(.pos 26)]),
   ((.exchange 16 28 5),[(.neg 28),(.neg 16),(.pos 5),(.pos 26)]),
   ((.exchange 17 25 5),[(.neg 25),(.neg 17),(.pos 6),(.pos 8),(.pos 27)]),
   ((.exchange 17 28 5),[(.neg 28),(.neg 17),(.pos 6),(.pos 27)]),
   ((.exchange 18 23 5),[(.neg 23),(.neg 18),(.pos 5),(.pos 9),(.pos 28)]),
   ((.exchange 18 24 5),[(.neg 24),(.neg 18),(.pos 6),(.pos 9),(.pos 28)]),
   ((.exchange 18 25 5),[(.neg 25),(.neg 18),(.pos 9),(.pos 28)]),
   ((.exchange 18 26 5),[(.neg 26),(.neg 18),(.pos 5),(.pos 28)]),
   ((.exchange 18 27 5),[(.neg 27),(.neg 18),(.pos 6),(.pos 28)]),
   ((.exchange 18 29 5),[(.neg 29),(.neg 18),(.pos 9),(.pos 28)]),
   ((.exchange 19 25 5),[(.neg 25),(.neg 19),(.pos 9),(.pos 29)]),
   ((.exchange 19 28 5),[(.neg 28),(.neg 19),(.pos 9),(.pos 29)]),
   ((.exchange 20 13 6),[(.neg 20),(.neg 13),(.pos 1),(.pos 10)]),
   ((.exchange 21 13 6),[(.neg 21),(.neg 13),(.pos 2),(.pos 11)]),
   ((.exchange 22 13 6),[(.neg 22),(.neg 13),(.pos 0),(.pos 3),(.pos 12)]),
   ((.exchange 30 19 0),[(.neg 30),(.neg 19),(.pos 33),(.pos 34)]),
   ((.exchange 33 16 3),[(.neg 33),(.neg 16),(.pos 30),(.pos 34)]),
   ((.exchange 34 14 4),[(.neg 34),(.neg 14),(.pos 31),(.pos 33)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 33),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32)]),
   ((.excluded 1),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 33)]),
   ((.excluded 2),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 34)]),
   ((.excluded 3),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29)]),
   ((.excluded 4),[(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 5),[(.neg 34),(.neg 33),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 30),(.pos 31),(.pos 32)]),
   ((.excluded 6),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 33)]),
   ((.excluded 7),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 34)]),
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C2

/- Source: MatroidCatalogue/Cases/N7R3C2Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C2

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C2.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C2.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C2

/- Source: MatroidCatalogue/Cases/N7R3C3Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C3

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 3
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 4 (.node 2 (.node 1 (.leaf (28672,4,15423688)) (.leaf (19456,4,15421987))) (.node 3 (.leaf (15360,6,16205448)) (.leaf (31744,7,16205448)))) (.node 6 (.node 5 (.leaf (990,19,16148104)) (.leaf (29662,20,16434824))) (.node 7 (.leaf (20446,20,16433690)) (.node 8 (.leaf (16350,21,16434824)) (.leaf (32734,22,16434824))))))

noncomputable def models (i : Fin 9) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 9) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 9) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C3

/- Source: MatroidCatalogue/Cases/N7R3C3Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C3


noncomputable def certificates_0 : List (Origin 35 9 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 11 22 5),[(.neg 22),(.neg 11),(.pos 0),(.pos 21)]),
   ((.exchange 11 28 5),[(.neg 28),(.neg 11),(.pos 5),(.pos 21)]),
   ((.exchange 11 31 2),[(.neg 31),(.neg 11),(.pos 10),(.pos 30)]),
   ((.exchange 11 33 0),[(.neg 33),(.neg 11),(.pos 15),(.pos 32)]),
   ((.exchange 12 21 5),[(.neg 21),(.neg 12),(.pos 0),(.pos 22)]),
   ((.exchange 12 23 5),[(.neg 23),(.neg 12),(.pos 0),(.pos 3),(.pos 22)]),
   ((.exchange 12 24 5),[(.neg 24),(.neg 12),(.pos 3),(.pos 22)]),
   ((.exchange 12 26 5),[(.neg 26),(.neg 12),(.pos 0),(.pos 6),(.pos 22)]),
   ((.exchange 12 27 5),[(.neg 27),(.neg 12),(.pos 6),(.pos 22)]),
   ((.exchange 12 28 5),[(.neg 28),(.neg 12),(.pos 6),(.pos 22)]),
   ((.exchange 12 29 5),[(.neg 29),(.neg 12),(.pos 3),(.pos 6),(.pos 22)]),
   ((.exchange 12 30 2),[(.neg 30),(.neg 12),(.pos 10),(.pos 31)]),
   ((.exchange 13 22 5),[(.neg 22),(.neg 13),(.pos 1),(.pos 2),(.pos 23)]),
   ((.exchange 13 28 5),[(.neg 28),(.neg 13),(.pos 2),(.pos 7),(.pos 23)]),
   ((.exchange 13 32 0),[(.neg 32),(.neg 13),(.pos 15),(.pos 33)]),
   ((.exchange 14 22 5),[(.neg 22),(.neg 14),(.pos 3),(.pos 24)]),
   ((.exchange 14 28 5),[(.neg 28),(.neg 14),(.pos 3),(.pos 8),(.pos 24)]),
   ((.exchange 16 22 5),[(.neg 22),(.neg 16),(.pos 4),(.pos 5),(.pos 26)]),
   ((.exchange 16 28 5),[(.neg 28),(.neg 16),(.pos 5),(.pos 26)]),
   ((.exchange 17 22 5),[(.neg 22),(.neg 17),(.pos 6),(.pos 27)]),
   ((.exchange 17 28 5),[(.neg 28),(.neg 17),(.pos 6),(.pos 27)]),
   ((.exchange 18 21 5),[(.neg 21),(.neg 18),(.pos 5),(.pos 28)]),
   ((.exchange 18 22 5),[(.neg 22),(.neg 18),(.pos 6),(.pos 28)]),
   ((.exchange 18 23 5),[(.neg 23),(.neg 18),(.pos 5),(.pos 9),(.pos 28)]),
   ((.exchange 18 24 5),[(.neg 24),(.neg 18),(.pos 6),(.pos 9),(.pos 28)]),
   ((.exchange 18 26 5),[(.neg 26),(.neg 18),(.pos 5),(.pos 28)]),
   ((.exchange 18 27 5),[(.neg 27),(.neg 18),(.pos 6),(.pos 28)]),
   ((.exchange 18 29 5),[(.neg 29),(.neg 18),(.pos 9),(.pos 28)]),
   ((.exchange 19 22 5),[(.neg 22),(.neg 19),(.pos 8),(.pos 9),(.pos 29)]),
   ((.exchange 19 28 5),[(.neg 28),(.neg 19),(.pos 9),(.pos 29)]),
   ((.exchange 20 11 6),[(.neg 20),(.neg 11),(.pos 0),(.pos 10)]),
   ((.exchange 25 11 6),[(.neg 25),(.neg 11),(.pos 2),(.pos 15)]),
   ((.exchange 30 18 0),[(.neg 30),(.neg 18),(.pos 32),(.pos 34)]),
   ((.exchange 33 17 3),[(.neg 33),(.neg 17),(.pos 31),(.pos 34)]),
   ((.exchange 34 14 4),[(.neg 34),(.neg 14),(.pos 31),(.pos 33)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 33),(.neg 32),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31)]),
   ((.excluded 1),[(.neg 34),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 32),(.pos 33)]),
   ((.excluded 2),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 34)]),
   ((.excluded 3),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29)]),
   ((.excluded 4),[(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 5),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 30),(.pos 31)]),
   ((.excluded 6),[(.neg 34),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 32),(.pos 33)]),
   ((.excluded 7),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 34)]),
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C3

/- Source: MatroidCatalogue/Cases/N7R3C3Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C3

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C3.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C3.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C3

/- Source: MatroidCatalogue/Cases/N7R3C4Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C4

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 4
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 5 (.node 2 (.node 1 (.leaf (28672,5,15423688)) (.leaf (27648,7,15685768))) (.node 3 (.leaf (23552,7,15684872)) (.node 4 (.leaf (15360,7,15674120)) (.leaf (31744,8,16205448))))) (.node 8 (.node 6 (.leaf (1022,23,16434824)) (.node 7 (.leaf (29694,24,16434824)) (.leaf (28670,25,16434824)))) (.node 9 (.leaf (24574,25,16434376)) (.node 10 (.leaf (16382,25,16427208)) (.leaf (32766,26,16434824))))))

noncomputable def models (i : Fin 11) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 11) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 11) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C4

/- Source: MatroidCatalogue/Cases/N7R3C4Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C4


noncomputable def certificates_0 : List (Origin 35 11 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
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
   ((.exchange 11 22 5),[(.neg 22),(.neg 11),(.pos 0),(.pos 21)]),
   ((.exchange 11 23 5),[(.neg 23),(.neg 11),(.pos 2),(.pos 21)]),
   ((.exchange 11 24 5),[(.neg 24),(.neg 11),(.pos 0),(.pos 2),(.pos 21)]),
   ((.exchange 11 25 5),[(.neg 25),(.neg 11),(.pos 2),(.pos 21)]),
   ((.exchange 11 26 5),[(.neg 26),(.neg 11),(.pos 5),(.pos 21)]),
   ((.exchange 11 27 5),[(.neg 27),(.neg 11),(.pos 0),(.pos 5),(.pos 21)]),
   ((.exchange 11 28 5),[(.neg 28),(.neg 11),(.pos 5),(.pos 21)]),
   ((.exchange 11 29 5),[(.neg 29),(.neg 11),(.pos 2),(.pos 5),(.pos 21)]),
   ((.exchange 11 31 2),[(.neg 31),(.neg 11),(.pos 10),(.pos 30)]),
   ((.exchange 12 21 5),[(.neg 21),(.neg 12),(.pos 0),(.pos 22)]),
   ((.exchange 12 23 5),[(.neg 23),(.neg 12),(.pos 0),(.pos 3),(.pos 22)]),
   ((.exchange 12 24 5),[(.neg 24),(.neg 12),(.pos 3),(.pos 22)]),
   ((.exchange 12 25 5),[(.neg 25),(.neg 12),(.pos 3),(.pos 22)]),
   ((.exchange 12 26 5),[(.neg 26),(.neg 12),(.pos 0),(.pos 6),(.pos 22)]),
   ((.exchange 12 27 5),[(.neg 27),(.neg 12),(.pos 6),(.pos 22)]),
   ((.exchange 12 28 5),[(.neg 28),(.neg 12),(.pos 6),(.pos 22)]),
   ((.exchange 12 29 5),[(.neg 29),(.neg 12),(.pos 3),(.pos 6),(.pos 22)]),
   ((.exchange 12 30 2),[(.neg 30),(.neg 12),(.pos 10),(.pos 31)]),
   ((.exchange 13 21 5),[(.neg 21),(.neg 13),(.pos 2),(.pos 23)]),
   ((.exchange 13 22 5),[(.neg 22),(.neg 13),(.pos 1),(.pos 2),(.pos 23)]),
   ((.exchange 13 25 5),[(.neg 25),(.neg 13),(.pos 2),(.pos 23)]),
   ((.exchange 14 21 5),[(.neg 21),(.neg 14),(.pos 1),(.pos 3),(.pos 24)]),
   ((.exchange 14 22 5),[(.neg 22),(.neg 14),(.pos 3),(.pos 24)]),
   ((.exchange 14 25 5),[(.neg 25),(.neg 14),(.pos 3),(.pos 24)]),
   ((.exchange 15 21 5),[(.neg 21),(.neg 15),(.pos 2),(.pos 25)]),
   ((.exchange 15 22 5),[(.neg 22),(.neg 15),(.pos 3),(.pos 25)]),
   ((.exchange 15 23 5),[(.neg 23),(.neg 15),(.pos 2),(.pos 25)]),
   ((.exchange 15 24 5),[(.neg 24),(.neg 15),(.pos 3),(.pos 25)]),
   ((.exchange 15 26 5),[(.neg 26),(.neg 15),(.pos 2),(.pos 9),(.pos 25)]),
   ((.exchange 15 27 5),[(.neg 27),(.neg 15),(.pos 3),(.pos 9),(.pos 25)]),
   ((.exchange 15 28 5),[(.neg 28),(.neg 15),(.pos 9),(.pos 25)]),
   ((.exchange 15 29 5),[(.neg 29),(.neg 15),(.pos 9),(.pos 25)]),
   ((.exchange 16 21 5),[(.neg 21),(.neg 16),(.pos 5),(.pos 26)]),
   ((.exchange 16 22 5),[(.neg 22),(.neg 16),(.pos 4),(.pos 5),(.pos 26)]),
   ((.exchange 16 25 5),[(.neg 25),(.neg 16),(.pos 5),(.pos 7),(.pos 26)]),
   ((.exchange 17 21 5),[(.neg 21),(.neg 17),(.pos 4),(.pos 6),(.pos 27)]),
   ((.exchange 17 22 5),[(.neg 22),(.neg 17),(.pos 6),(.pos 27)]),
   ((.exchange 17 25 5),[(.neg 25),(.neg 17),(.pos 6),(.pos 8),(.pos 27)]),
   ((.exchange 18 21 5),[(.neg 21),(.neg 18),(.pos 5),(.pos 28)]),
   ((.exchange 18 22 5),[(.neg 22),(.neg 18),(.pos 6),(.pos 28)]),
   ((.exchange 18 25 5),[(.neg 25),(.neg 18),(.pos 9),(.pos 28)]),
   ((.exchange 19 21 5),[(.neg 21),(.neg 19),(.pos 7),(.pos 9),(.pos 29)]),
   ((.exchange 19 22 5),[(.neg 22),(.neg 19),(.pos 8),(.pos 9),(.pos 29)]),
   ((.exchange 19 25 5),[(.neg 25),(.neg 19),(.pos 9),(.pos 29)]),
   ((.exchange 20 11 6),[(.neg 20),(.neg 11),(.pos 0),(.pos 10)]),
   ((.exchange 30 15 0),[(.neg 30),(.neg 15),(.pos 32),(.pos 33)]),
   ((.exchange 30 18 0),[(.neg 30),(.neg 18),(.pos 32),(.pos 34)]),
   ((.exchange 30 19 0),[(.neg 30),(.neg 19),(.pos 33),(.pos 34)]),
   ((.exchange 32 14 2),[(.neg 32),(.neg 14),(.pos 31),(.pos 33)]),
   ((.exchange 33 12 3),[(.neg 33),(.neg 12),(.pos 31),(.pos 32)]),
   ((.exchange 33 17 3),[(.neg 33),(.neg 17),(.pos 31),(.pos 34)]),
   ((.exchange 34 13 4),[(.neg 34),(.neg 13),(.pos 30),(.pos 33)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 33),(.neg 32),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31)]),
   ((.excluded 1),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 32)]),
   ((.excluded 2),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 33)]),
   ((.excluded 3),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 34)]),
   ((.excluded 4),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29)]),
   ((.excluded 5),[(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 6),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 30),(.pos 31)]),
   ((.excluded 7),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 32)]),
   ((.excluded 8),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 33)]),
   ((.excluded 9),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 34)]),
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C4

/- Source: MatroidCatalogue/Cases/N7R3C4Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C4

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C4.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C4.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C4

/- Source: MatroidCatalogue/Cases/N7R3C5Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C5

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 5
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 6 (.node 3 (.node 1 (.leaf (30720,8,15161552)) (.node 2 (.leaf (29696,8,15161538)) (.leaf (27648,8,15161370)))) (.node 4 (.leaf (23552,8,15159578)) (.node 5 (.leaf (15360,8,15141658)) (.leaf (31744,9,16205448))))) (.node 9 (.node 7 (.leaf (1023,27,16434824)) (.node 8 (.leaf (31743,28,16434824)) (.leaf (30719,28,16434817)))) (.node 11 (.node 10 (.leaf (28671,28,16434705)) (.leaf (24575,28,16433361))) (.node 12 (.leaf (16383,28,16419025)) (.leaf (32767,29,16434824))))))

noncomputable def models (i : Fin 13) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 13) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 13) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C5

/- Source: MatroidCatalogue/Cases/N7R3C5Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C5


noncomputable def certificates_0 : List (Origin 35 13 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 10 21 5),[(.neg 21),(.neg 10),(.pos 0),(.pos 20)]),
   ((.exchange 10 22 5),[(.neg 22),(.neg 10),(.pos 0),(.pos 20)]),
   ((.exchange 10 23 5),[(.neg 23),(.neg 10),(.pos 1),(.pos 20)]),
   ((.exchange 10 24 5),[(.neg 24),(.neg 10),(.pos 1),(.pos 20)]),
   ((.exchange 10 25 5),[(.neg 25),(.neg 10),(.pos 0),(.pos 1),(.pos 20)]),
   ((.exchange 10 26 5),[(.neg 26),(.neg 10),(.pos 4),(.pos 20)]),
   ((.exchange 10 27 5),[(.neg 27),(.neg 10),(.pos 4),(.pos 20)]),
   ((.exchange 10 28 5),[(.neg 28),(.neg 10),(.pos 0),(.pos 4),(.pos 20)]),
   ((.exchange 10 29 5),[(.neg 29),(.neg 10),(.pos 1),(.pos 4),(.pos 20)]),
   ((.exchange 11 20 5),[(.neg 20),(.neg 11),(.pos 0),(.pos 21)]),
   ((.exchange 11 22 5),[(.neg 22),(.neg 11),(.pos 0),(.pos 21)]),
   ((.exchange 11 23 5),[(.neg 23),(.neg 11),(.pos 2),(.pos 21)]),
   ((.exchange 11 24 5),[(.neg 24),(.neg 11),(.pos 0),(.pos 2),(.pos 21)]),
   ((.exchange 11 25 5),[(.neg 25),(.neg 11),(.pos 2),(.pos 21)]),
   ((.exchange 11 26 5),[(.neg 26),(.neg 11),(.pos 5),(.pos 21)]),
   ((.exchange 11 27 5),[(.neg 27),(.neg 11),(.pos 0),(.pos 5),(.pos 21)]),
   ((.exchange 11 28 5),[(.neg 28),(.neg 11),(.pos 5),(.pos 21)]),
   ((.exchange 11 29 5),[(.neg 29),(.neg 11),(.pos 2),(.pos 5),(.pos 21)]),
   ((.exchange 12 20 5),[(.neg 20),(.neg 12),(.pos 0),(.pos 22)]),
   ((.exchange 12 21 5),[(.neg 21),(.neg 12),(.pos 0),(.pos 22)]),
   ((.exchange 12 25 5),[(.neg 25),(.neg 12),(.pos 3),(.pos 22)]),
   ((.exchange 13 20 5),[(.neg 20),(.neg 13),(.pos 1),(.pos 23)]),
   ((.exchange 13 21 5),[(.neg 21),(.neg 13),(.pos 2),(.pos 23)]),
   ((.exchange 13 25 5),[(.neg 25),(.neg 13),(.pos 2),(.pos 23)]),
   ((.exchange 14 20 5),[(.neg 20),(.neg 14),(.pos 1),(.pos 24)]),
   ((.exchange 14 21 5),[(.neg 21),(.neg 14),(.pos 1),(.pos 3),(.pos 24)]),
   ((.exchange 14 25 5),[(.neg 25),(.neg 14),(.pos 3),(.pos 24)]),
   ((.exchange 15 20 5),[(.neg 20),(.neg 15),(.pos 2),(.pos 3),(.pos 25)]),
   ((.exchange 15 21 5),[(.neg 21),(.neg 15),(.pos 2),(.pos 25)]),
   ((.exchange 15 22 5),[(.neg 22),(.neg 15),(.pos 3),(.pos 25)]),
   ((.exchange 15 23 5),[(.neg 23),(.neg 15),(.pos 2),(.pos 25)]),
   ((.exchange 15 24 5),[(.neg 24),(.neg 15),(.pos 3),(.pos 25)]),
   ((.exchange 15 26 5),[(.neg 26),(.neg 15),(.pos 2),(.pos 9),(.pos 25)]),
   ((.exchange 15 27 5),[(.neg 27),(.neg 15),(.pos 3),(.pos 9),(.pos 25)]),
   ((.exchange 15 28 5),[(.neg 28),(.neg 15),(.pos 9),(.pos 25)]),
   ((.exchange 15 29 5),[(.neg 29),(.neg 15),(.pos 9),(.pos 25)]),
   ((.exchange 16 20 5),[(.neg 20),(.neg 16),(.pos 4),(.pos 26)]),
   ((.exchange 16 21 5),[(.neg 21),(.neg 16),(.pos 5),(.pos 26)]),
   ((.exchange 16 25 5),[(.neg 25),(.neg 16),(.pos 5),(.pos 7),(.pos 26)]),
   ((.exchange 17 20 5),[(.neg 20),(.neg 17),(.pos 4),(.pos 27)]),
   ((.exchange 17 21 5),[(.neg 21),(.neg 17),(.pos 4),(.pos 6),(.pos 27)]),
   ((.exchange 17 25 5),[(.neg 25),(.neg 17),(.pos 6),(.pos 8),(.pos 27)]),
   ((.exchange 18 20 5),[(.neg 20),(.neg 18),(.pos 5),(.pos 6),(.pos 28)]),
   ((.exchange 18 21 5),[(.neg 21),(.neg 18),(.pos 5),(.pos 28)]),
   ((.exchange 18 25 5),[(.neg 25),(.neg 18),(.pos 9),(.pos 28)]),
   ((.exchange 19 20 5),[(.neg 20),(.neg 19),(.pos 7),(.pos 8),(.pos 29)]),
   ((.exchange 19 21 5),[(.neg 21),(.neg 19),(.pos 7),(.pos 9),(.pos 29)]),
   ((.exchange 19 25 5),[(.neg 25),(.neg 19),(.pos 9),(.pos 29)]),
   ((.exchange 30 14 0),[(.neg 30),(.neg 14),(.pos 31),(.pos 33)]),
   ((.exchange 30 15 0),[(.neg 30),(.neg 15),(.pos 32),(.pos 33)]),
   ((.exchange 30 18 0),[(.neg 30),(.neg 18),(.pos 32),(.pos 34)]),
   ((.exchange 31 11 1),[(.neg 31),(.neg 11),(.pos 30),(.pos 32)]),
   ((.exchange 31 13 1),[(.neg 31),(.neg 13),(.pos 30),(.pos 33)]),
   ((.exchange 31 16 1),[(.neg 31),(.neg 16),(.pos 30),(.pos 34)]),
   ((.exchange 31 19 1),[(.neg 31),(.neg 19),(.pos 33),(.pos 34)]),
   ((.exchange 32 14 2),[(.neg 32),(.neg 14),(.pos 31),(.pos 33)]),
   ((.exchange 33 10 3),[(.neg 33),(.neg 10),(.pos 30),(.pos 31)]),
   ((.exchange 33 12 3),[(.neg 33),(.neg 12),(.pos 31),(.pos 32)]),
   ((.exchange 33 17 3),[(.neg 33),(.neg 17),(.pos 31),(.pos 34)]),
   ((.exchange 34 14 4),[(.neg 34),(.neg 14),(.pos 31),(.pos 33)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30)]),
   ((.excluded 1),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 31)]),
   ((.excluded 2),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 32)]),
   ((.excluded 3),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 33)]),
   ((.excluded 4),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 34)]),
   ((.excluded 5),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29)]),
   ((.excluded 6),[(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 7),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 30)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 31)]),
   ((.excluded 9),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 32)]),
   ((.excluded 10),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 33)]),
   ((.excluded 11),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 34)]),
   ((.excluded 12),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 13,
    let w : Fin 13 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C5

/- Source: MatroidCatalogue/Cases/N7R3C5Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C5

noncomputable def certificates : List (Origin 35 13 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 13,
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 13) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 3)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 3, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N7R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C5.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C5.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C5

