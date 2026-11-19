module
public import MatroidCatalogue.Definitions
public import MatroidCases.N7R3C16
import all MatroidCases.N7R3C16
public import MatroidCases.N7R3C17
import all MatroidCases.N7R3C17

@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N7R3C16Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C16

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 16
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (31616,26,15161552)) (.node 2 (.leaf (30528,26,15161538)) (.leaf (28352,26,15161370)))) (.node 5 (.node 4 (.leaf (24000,26,15159578)) (.leaf (16320,28,14899409))) (.node 6 (.leaf (32704,29,15947400)) (.leaf (15423,46,15141658))))) (.node 11 (.node 9 (.node 8 (.leaf (1023,46,14969626)) (.leaf (16383,51,16434824))) (.node 10 (.leaf (30655,49,15918728)) (.leaf (28607,49,15918672)))) (.node 13 (.node 12 (.leaf (24511,49,15917776)) (.leaf (32703,50,16205448))) (.node 14 (.leaf (30463,49,15947330)) (.leaf (30207,49,15946434)))))) (.node 22 (.node 18 (.node 16 (.leaf (30719,50,16148097)) (.node 17 (.leaf (31487,49,15947344)) (.leaf (24319,49,15917594)))) (.node 20 (.node 19 (.leaf (32511,50,16205329)) (.leaf (24447,49,15917762))) (.node 21 (.leaf (24575,50,16146641)) (.leaf (31615,49,15947400))))) (.node 26 (.node 24 (.node 23 (.leaf (28543,49,15918658)) (.leaf (32639,50,16205441))) (.node 25 (.leaf (31231,49,15946448)) (.leaf (31743,50,16148104)))) (.node 28 (.node 27 (.leaf (28159,49,15946266)) (.leaf (32255,50,16203985))) (.node 29 (.leaf (28671,50,16147985)) (.leaf (32767,52,16434824)))))))

noncomputable def models (i : Fin 30) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 30) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 30) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C16

/- Source: MatroidCatalogue/Cases/N7R3C16Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C16


noncomputable def certificates_0 : List (Origin 35 30 × List Sat.Literal) :=
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
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 4 21 4),[(.neg 21),(.neg 4),(.pos 0),(.pos 20)]),
   ((.exchange 4 23 4),[(.neg 23),(.neg 4),(.pos 1),(.pos 20)]),
   ((.exchange 4 25 4),[(.neg 25),(.neg 4),(.pos 0),(.pos 1),(.pos 20)]),
   ((.exchange 5 20 4),[(.neg 20),(.neg 5),(.pos 0),(.pos 21)]),
   ((.exchange 5 22 4),[(.neg 22),(.neg 5),(.pos 0),(.pos 21)]),
   ((.exchange 5 23 4),[(.neg 23),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 5 24 4),[(.neg 24),(.neg 5),(.pos 0),(.pos 2),(.pos 21)]),
   ((.exchange 5 25 4),[(.neg 25),(.neg 5),(.pos 2),(.pos 21)]),
   ((.exchange 6 21 4),[(.neg 21),(.neg 6),(.pos 0),(.pos 22)]),
   ((.exchange 6 25 4),[(.neg 25),(.neg 6),(.pos 3),(.pos 22)]),
   ((.exchange 7 21 4),[(.neg 21),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 7 22 4),[(.neg 22),(.neg 7),(.pos 1),(.pos 2),(.pos 23)]),
   ((.exchange 7 24 4),[(.neg 24),(.neg 7),(.pos 1),(.pos 23)]),
   ((.exchange 7 25 4),[(.neg 25),(.neg 7),(.pos 2),(.pos 23)]),
   ((.exchange 8 21 4),[(.neg 21),(.neg 8),(.pos 1),(.pos 3),(.pos 24)]),
   ((.exchange 8 25 4),[(.neg 25),(.neg 8),(.pos 3),(.pos 24)]),
   ((.exchange 9 20 4),[(.neg 20),(.neg 9),(.pos 2),(.pos 3),(.pos 25)]),
   ((.exchange 9 21 4),[(.neg 21),(.neg 9),(.pos 2),(.pos 25)]),
   ((.exchange 9 22 4),[(.neg 22),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 9 23 4),[(.neg 23),(.neg 9),(.pos 2),(.pos 25)]),
   ((.exchange 9 24 4),[(.neg 24),(.neg 9),(.pos 3),(.pos 25)]),
   ((.exchange 20 17 0),[(.neg 20),(.neg 17),(.pos 27),(.pos 31)]),
   ((.exchange 21 16 2),[(.neg 21),(.neg 16),(.pos 26),(.pos 30)]),
   ((.exchange 21 18 0),[(.neg 21),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 22 17 2),[(.neg 22),(.neg 17),(.pos 27),(.pos 31)]),
   ((.exchange 22 18 1),[(.neg 22),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 23 19 0),[(.neg 23),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 24 17 3),[(.neg 24),(.neg 17),(.pos 27),(.pos 31)]),
   ((.exchange 25 18 3),[(.neg 25),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 25 19 2),[(.neg 25),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 26 8 0),[(.neg 26),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 26 11 4),[(.neg 26),(.neg 11),(.pos 21),(.pos 30)]),
   ((.exchange 26 17 0),[(.neg 26),(.neg 17),(.pos 27),(.pos 34)]),
   ((.exchange 27 10 4),[(.neg 27),(.neg 10),(.pos 20),(.pos 31)]),
   ((.exchange 27 16 1),[(.neg 27),(.neg 16),(.pos 26),(.pos 34)]),
   ((.exchange 27 32 1),[(.neg 32),(.neg 27),(.pos 28),(.pos 34)]),
   ((.exchange 27 32 4),[(.neg 32),(.neg 27),(.pos 22),(.pos 31)]),
   ((.exchange 27 33 1),[(.neg 33),(.neg 27),(.pos 29),(.pos 34)]),
   ((.exchange 27 33 4),[(.neg 33),(.neg 27),(.pos 24),(.pos 31)]),
   ((.exchange 28 4 2),[(.neg 28),(.neg 4),(.pos 26),(.pos 27)]),
   ((.exchange 28 7 2),[(.neg 28),(.neg 7),(.pos 26),(.pos 29)]),
   ((.exchange 28 8 2),[(.neg 28),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 28 10 4),[(.neg 28),(.neg 10),(.pos 21),(.pos 22),(.pos 32)]),
   ((.exchange 28 11 4),[(.neg 28),(.neg 11),(.pos 21),(.pos 32)]),
   ((.exchange 28 17 2),[(.neg 28),(.neg 17),(.pos 27),(.pos 34)]),
   ((.exchange 28 23 2),[(.neg 28),(.neg 23),(.pos 26),(.pos 29)]),
   ((.exchange 28 31 4),[(.neg 31),(.neg 28),(.pos 22),(.pos 32)]),
   ((.exchange 28 33 4),[(.neg 33),(.neg 28),(.pos 25),(.pos 32)]),
   ((.exchange 29 10 4),[(.neg 29),(.neg 10),(.pos 23),(.pos 24),(.pos 33)]),
   ((.exchange 29 15 4),[(.neg 29),(.neg 15),(.pos 25),(.pos 33)]),
   ((.exchange 29 17 3),[(.neg 29),(.neg 17),(.pos 27),(.pos 34)]),
   ((.exchange 30 4 5),[(.neg 30),(.neg 4),(.pos 20),(.pos 26)]),
   ((.exchange 30 12 0),[(.neg 30),(.neg 12),(.pos 31),(.pos 32)]),
   ((.exchange 30 15 0),[(.neg 30),(.neg 15),(.pos 32),(.pos 33)]),
   ((.exchange 30 17 0),[(.neg 30),(.neg 17),(.pos 31),(.pos 34)]),
   ((.exchange 30 18 0),[(.neg 30),(.neg 18),(.pos 32),(.pos 34)]),
   ((.exchange 30 19 0),[(.neg 30),(.neg 19),(.pos 33),(.pos 34)]),
   ((.exchange 31 4 5),[(.neg 31),(.neg 4),(.pos 20),(.pos 27)]),
   ((.exchange 31 6 5),[(.neg 31),(.neg 6),(.pos 22),(.pos 27)]),
   ((.exchange 31 8 5),[(.neg 31),(.neg 8),(.pos 24),(.pos 27)]),
   ((.exchange 31 11 1),[(.neg 31),(.neg 11),(.pos 30),(.pos 32)]),
   ((.exchange 31 13 1),[(.neg 31),(.neg 13),(.pos 30),(.pos 33)]),
   ((.exchange 31 16 1),[(.neg 31),(.neg 16),(.pos 30),(.pos 34)]),
   ((.exchange 31 28 5),[(.neg 31),(.neg 28),(.pos 22),(.pos 27)]),
   ((.exchange 32 5 5),[(.neg 32),(.neg 5),(.pos 21),(.pos 28)]),
   ((.exchange 32 6 5),[(.neg 32),(.neg 6),(.pos 22),(.pos 28)]),
   ((.exchange 32 9 5),[(.neg 32),(.neg 9),(.pos 25),(.pos 28)]),
   ((.exchange 32 10 2),[(.neg 32),(.neg 10),(.pos 30),(.pos 31)]),
   ((.exchange 32 14 2),[(.neg 32),(.neg 14),(.pos 31),(.pos 33)]),
   ((.exchange 33 7 5),[(.neg 33),(.neg 7),(.pos 23),(.pos 29)]),
   ((.exchange 33 9 5),[(.neg 33),(.neg 9),(.pos 25),(.pos 29)]),
   ((.exchange 33 10 3),[(.neg 33),(.neg 10),(.pos 30),(.pos 31)]),
   ((.exchange 34 4 5),[(.neg 34),(.neg 4),(.pos 26),(.pos 27)]),
   ((.exchange 34 5 5),[(.neg 34),(.neg 5),(.pos 26),(.pos 28)]),
   ((.exchange 34 6 5),[(.neg 34),(.neg 6),(.pos 27),(.pos 28)]),
   ((.exchange 34 8 5),[(.neg 34),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 34 9 5),[(.neg 34),(.neg 9),(.pos 28),(.pos 29)]),
   ((.exchange 34 12 4),[(.neg 34),(.neg 12),(.pos 31),(.pos 32)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 30)]),
   ((.excluded 1),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 27),(.pos 31)]),
   ((.excluded 2),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 28),(.pos 32)]),
   ((.excluded 3),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 29),(.pos 33)]),
   ((.excluded 4),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 34)]),
   ((.excluded 5),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25)]),
   ((.excluded 6),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 34)]),
   ((.excluded 7),[(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 8),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 34)]),
   ((.excluded 9),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 26),(.pos 31)]),
   ((.excluded 10),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 26),(.pos 32)]),
   ((.excluded 11),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 26),(.pos 33)]),
   ((.excluded 12),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 26)]),
   ((.excluded 13),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 28),(.pos 31)]),
   ((.excluded 14),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 29),(.pos 31)]),
   ((.excluded 15),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 31)]),
   ((.excluded 16),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 28),(.pos 30)]),
   ((.excluded 17),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 28),(.pos 33)]),
   ((.excluded 18),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 28)]),
   ((.excluded 19),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 27),(.pos 33)]),
   ((.excluded 20),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 33)]),
   ((.excluded 21),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 27),(.pos 30)]),
   ((.excluded 22),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 27),(.pos 32)]),
   ((.excluded 23),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 27)]),
   ((.excluded 24),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 29),(.pos 30)]),
   ((.excluded 25),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 30)]),
   ((.excluded 26),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 29),(.pos 32)]),
   ((.excluded 27),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 29)]),
   ((.excluded 28),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 32)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



noncomputable def certificates_1 : List (Origin 35 30 × List Sat.Literal) :=
  [((.excluded 29),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 30,
    let w : Fin 30 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C16

/- Source: MatroidCatalogue/Cases/N7R3C16Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C16

noncomputable def certificates : List (Origin 35 30 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

theorem models_valid : ∀ w : Fin 30,
    target w < MatroidCatalogue.count 7 3 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 30) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 3)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 3, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N7R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C16.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C16.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C16

/- Source: MatroidCatalogue/Cases/N7R3C17Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C17

abbrev U := N7R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R3.family 17
noncomputable def newIndexTree : Table ℕ := (.node 7 (.node 3 (.node 1 (.leaf 20) (.node 2 (.leaf 21) (.leaf 22))) (.node 5 (.node 4 (.leaf 23) (.leaf 24)) (.node 6 (.leaf 25) (.leaf 26)))) (.node 11 (.node 9 (.node 8 (.leaf 27) (.leaf 28)) (.node 10 (.leaf 29) (.leaf 30))) (.node 13 (.node 12 (.leaf 31) (.leaf 32)) (.node 14 (.leaf 33) (.leaf 34)))))
noncomputable def newIndex (i : Fin 15) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (27864,35,15161370)) (.leaf (23750,35,15159578))) (.node 3 (.leaf (15390,35,15141658)) (.node 4 (.leaf (28894,41,15423688)) (.leaf (31966,46,16205448))))) (.node 7 (.node 6 (.leaf (29472,31,15423688)) (.leaf (1022,36,15559432))) (.node 8 (.leaf (29694,44,15559432)) (.node 9 (.leaf (24568,42,15657096)) (.leaf (16376,42,15649928)))))) (.node 15 (.node 12 (.node 11 (.leaf (32760,43,15685768)) (.leaf (24382,42,15640968))) (.node 13 (.leaf (24574,53,16147656)) (.node 14 (.leaf (28478,42,15641864)) (.leaf (32574,43,15674120))))) (.node 18 (.node 16 (.leaf (28646,42,15656200)) (.node 17 (.leaf (16358,42,15648136)) (.leaf (32742,43,15684872)))) (.node 19 (.leaf (28670,53,16148104)) (.node 20 (.leaf (16382,53,16133320)) (.leaf (32766,54,16434824)))))))

noncomputable def models (i : Fin 21) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 21) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 21) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 15, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C17

/- Source: MatroidCatalogue/Cases/N7R3C17Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C17


noncomputable def certificates_0 : List (Origin 35 21 × List Sat.Literal) :=
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
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.exchange 2 22 3),[(.neg 22),(.neg 2),(.pos 0),(.pos 21)]),
   ((.exchange 2 24 2),[(.neg 24),(.neg 2),(.pos 1),(.pos 23)]),
   ((.exchange 2 28 0),[(.neg 28),(.neg 2),(.pos 9),(.pos 25)]),
   ((.exchange 2 29 0),[(.neg 29),(.neg 2),(.pos 9),(.pos 25)]),
   ((.exchange 3 21 3),[(.neg 21),(.neg 3),(.pos 0),(.pos 22)]),
   ((.exchange 3 23 2),[(.neg 23),(.neg 3),(.pos 1),(.pos 24)]),
   ((.exchange 5 25 0),[(.neg 25),(.neg 5),(.pos 9),(.pos 28)]),
   ((.exchange 5 27 2),[(.neg 27),(.neg 5),(.pos 4),(.pos 26)]),
   ((.exchange 5 29 0),[(.neg 29),(.neg 5),(.pos 9),(.pos 28)]),
   ((.exchange 6 26 2),[(.neg 26),(.neg 6),(.pos 4),(.pos 27)]),
   ((.exchange 7 25 0),[(.neg 25),(.neg 7),(.pos 9),(.pos 29)]),
   ((.exchange 7 28 0),[(.neg 28),(.neg 7),(.pos 9),(.pos 29)]),
   ((.exchange 11 31 2),[(.neg 31),(.neg 11),(.pos 10),(.pos 30)]),
   ((.exchange 12 30 2),[(.neg 30),(.neg 12),(.pos 10),(.pos 31)]),
   ((.exchange 20 2 6),[(.neg 20),(.neg 2),(.pos 0),(.pos 1)]),
   ((.exchange 21 13 2),[(.neg 21),(.neg 13),(.pos 23),(.pos 30)]),
   ((.exchange 21 15 0),[(.neg 21),(.neg 15),(.pos 25),(.pos 32)]),
   ((.exchange 21 16 2),[(.neg 21),(.neg 16),(.pos 26),(.pos 30)]),
   ((.exchange 21 18 0),[(.neg 21),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 21 33 2),[(.neg 33),(.neg 21),(.pos 23),(.pos 30)]),
   ((.exchange 22 13 2),[(.neg 22),(.neg 13),(.pos 20),(.pos 24),(.pos 31)]),
   ((.exchange 22 16 2),[(.neg 22),(.neg 16),(.pos 20),(.pos 27),(.pos 31)]),
   ((.exchange 22 18 1),[(.neg 22),(.neg 18),(.pos 28),(.pos 32)]),
   ((.exchange 22 33 2),[(.neg 33),(.neg 22),(.pos 24),(.pos 31)]),
   ((.exchange 23 6 3),[(.neg 23),(.neg 6),(.pos 20),(.pos 21),(.pos 26)]),
   ((.exchange 23 11 3),[(.neg 23),(.neg 11),(.pos 21),(.pos 30)]),
   ((.exchange 23 15 0),[(.neg 23),(.neg 15),(.pos 25),(.pos 33)]),
   ((.exchange 23 19 0),[(.neg 23),(.neg 19),(.pos 29),(.pos 33)]),
   ((.exchange 24 6 3),[(.neg 24),(.neg 6),(.pos 22),(.pos 27)]),
   ((.exchange 24 11 3),[(.neg 24),(.neg 11),(.pos 20),(.pos 22),(.pos 31)]),
   ((.exchange 24 15 1),[(.neg 24),(.neg 15),(.pos 25),(.pos 33)]),
   ((.exchange 25 11 3),[(.neg 25),(.neg 11),(.pos 21),(.pos 32)]),
   ((.exchange 25 13 2),[(.neg 25),(.neg 13),(.pos 23),(.pos 33)]),
   ((.exchange 25 14 2),[(.neg 25),(.neg 14),(.pos 24),(.pos 33)]),
   ((.exchange 26 2 4),[(.neg 26),(.neg 2),(.pos 21),(.pos 23)]),
   ((.exchange 26 15 0),[(.neg 26),(.neg 15),(.pos 28),(.pos 29),(.pos 34)]),
   ((.exchange 26 25 4),[(.neg 26),(.neg 25),(.pos 21),(.pos 23)]),
   ((.exchange 27 2 4),[(.neg 27),(.neg 2),(.pos 20),(.pos 22),(.pos 24)]),
   ((.exchange 27 15 1),[(.neg 27),(.neg 15),(.pos 28),(.pos 29),(.pos 34)]),
   ((.exchange 27 25 4),[(.neg 27),(.neg 25),(.pos 22),(.pos 24)]),
   ((.exchange 28 2 4),[(.neg 28),(.neg 2),(.pos 21),(.pos 25)]),
   ((.exchange 28 30 2),[(.neg 30),(.neg 28),(.pos 26),(.pos 34)]),
   ((.exchange 28 30 4),[(.neg 30),(.neg 28),(.pos 21),(.pos 32)]),
   ((.exchange 28 31 2),[(.neg 31),(.neg 28),(.pos 27),(.pos 34)]),
   ((.exchange 29 2 4),[(.neg 29),(.neg 2),(.pos 23),(.pos 25)]),
   ((.exchange 30 18 0),[(.neg 30),(.neg 18),(.pos 32),(.pos 34)]),
   ((.exchange 30 19 0),[(.neg 30),(.neg 19),(.pos 33),(.pos 34)]),
   ((.exchange 30 28 5),[(.neg 30),(.neg 28),(.pos 21),(.pos 26)]),
   ((.exchange 30 29 5),[(.neg 30),(.neg 29),(.pos 23),(.pos 26)]),
   ((.exchange 31 2 5),[(.neg 31),(.neg 2),(.pos 20),(.pos 22),(.pos 24)]),
   ((.exchange 31 7 5),[(.neg 31),(.neg 7),(.pos 20),(.pos 24),(.pos 27)]),
   ((.exchange 31 15 1),[(.neg 31),(.neg 15),(.pos 32),(.pos 33)]),
   ((.exchange 31 28 5),[(.neg 31),(.neg 28),(.pos 22),(.pos 27)]),
   ((.exchange 31 29 5),[(.neg 31),(.neg 29),(.pos 24),(.pos 27)]),
   ((.exchange 32 5 5),[(.neg 32),(.neg 5),(.pos 21),(.pos 28)]),
   ((.exchange 32 6 5),[(.neg 32),(.neg 6),(.pos 22),(.pos 28)]),
   ((.exchange 32 14 2),[(.neg 32),(.neg 14),(.pos 31),(.pos 33)]),
   ((.exchange 32 17 2),[(.neg 32),(.neg 17),(.pos 31),(.pos 34)]),
   ((.exchange 33 3 5),[(.neg 33),(.neg 3),(.pos 24),(.pos 25)]),
   ((.exchange 33 5 5),[(.neg 33),(.neg 5),(.pos 23),(.pos 25),(.pos 29)]),
   ((.exchange 33 6 5),[(.neg 33),(.neg 6),(.pos 24),(.pos 25),(.pos 29)]),
   ((.exchange 33 8 5),[(.neg 33),(.neg 8),(.pos 24),(.pos 29)]),
   ((.exchange 33 12 3),[(.neg 33),(.neg 12),(.pos 31),(.pos 32)]),
   ((.exchange 34 5 5),[(.neg 34),(.neg 5),(.pos 26),(.pos 28)]),
   ((.exchange 34 6 5),[(.neg 34),(.neg 6),(.pos 27),(.pos 28)]),
   ((.exchange 34 15 4),[(.neg 34),(.neg 15),(.pos 32),(.pos 33)]),
   (.newPoint,[(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 25),(.pos 28),(.pos 29),(.pos 32)]),
   ((.excluded 1),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.neg 22),(.neg 21),(.pos 20),(.pos 23),(.pos 24),(.pos 25),(.pos 28),(.pos 29),(.pos 33)]),
   ((.excluded 2),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 34)]),
   ((.excluded 3),[(.neg 34),(.neg 33),(.neg 32),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 28),(.pos 29),(.pos 30),(.pos 31)]),
   ((.excluded 4),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 25),(.pos 28),(.pos 29)]),
   ((.excluded 5),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 25),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 26),(.pos 27),(.pos 30),(.pos 31)]),
   ((.excluded 6),[(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 7),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 30),(.pos 31)]),
   ((.excluded 8),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 33)]),
   ((.excluded 9),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22),(.pos 34)]),
   ((.excluded 10),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.pos 20),(.pos 21),(.pos 22)]),
   ((.excluded 11),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27),(.pos 33)]),
   ((.excluded 12),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 33)]),
   ((.excluded 13),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27),(.pos 32)]),
   ((.excluded 14),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 26),(.pos 27)]),
   ((.excluded 15),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 22),(.neg 21),(.pos 20),(.pos 23),(.pos 24),(.pos 32)]),
   ((.excluded 16),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 22),(.neg 21),(.pos 20),(.pos 23),(.pos 24),(.pos 34)]),
   ((.excluded 17),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 22),(.neg 21),(.pos 20),(.pos 23),(.pos 24)]),
   ((.excluded 18),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 32)]),
   ((.excluded 19),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.pos 20),(.pos 34)]),
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C17

/- Source: MatroidCatalogue/Cases/N7R3C17Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C17

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R3C17.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R3C17.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 3 (target w),family_mem 7 3 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R3C17
