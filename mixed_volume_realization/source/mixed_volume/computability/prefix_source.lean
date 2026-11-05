/- Exact one-sided boundary form of the recovered universal correspondence source. -/
module

public import matrix_mortality.undecidability.universal_mortality35

set_option autoImplicit false

@[expose] public section

namespace MixedVolume.Computability

open MatrixMortality MatrixMortality.Undecidability

theorem spell_reverse {α β : Type*} (side : α → List β) (word : List α) :
    spell (fun a => (side a).reverse) word.reverse = (spell side word).reverse := by
  induction word with
  | nil => simp [spell]
  | cons a word ih =>
    simp only [List.reverse_cons, spell_append, ih]
    simp [spell, List.reverse_append]

/-- Reverse each tile and each boundary, and interchange the boundary sides.
The witness word is reversed as well. -/
def reverseProblem (p : BinaryGPCP4) : BinaryGPCP4 where
  upper := fun a => (p.upper a).reverse
  lower := fun a => (p.lower a).reverse
  upperLeft := p.upperRight.reverse
  upperRight := p.upperLeft.reverse
  lowerLeft := p.lowerRight.reverse
  lowerRight := p.lowerLeft.reverse

theorem reverseProblem_involutive : Function.Involutive reverseProblem := by
  intro p
  cases p
  simp [reverseProblem]

theorem reverseProblem_solvable_iff (p : BinaryGPCP4) :
    (reverseProblem p).Solvable ↔ p.Solvable := by
  have forward (q : BinaryGPCP4) : q.Solvable → (reverseProblem q).Solvable := by
    rintro ⟨word, hword⟩
    refine ⟨word.reverse, ?_⟩
    have h := congrArg List.reverse hword
    simpa only [reverseProblem, spell_reverse, List.reverse_append, List.append_assoc] using h
  constructor
  · intro h
    simpa only [reverseProblem_involutive p] using forward (reverseProblem p) h
  · exact forward p

/-- The source already has empty left boundaries. Reversal therefore leaves
only the explicit marker prefix, with no suffix to encode in a final vector. -/
def prefixSource (beta : ℕ) (body : List TagLetter) : BinaryGPCP4 :=
  reverseProblem (nearyGPCP4 beta body)

@[simp] theorem prefixSource_upperLeft (beta : ℕ) (body : List TagLetter) :
    (prefixSource beta body).upperLeft = (nearyMarker beta).reverse := rfl

@[simp] theorem prefixSource_upperRight (beta : ℕ) (body : List TagLetter) :
    (prefixSource beta body).upperRight = [] := rfl

@[simp] theorem prefixSource_lowerLeft (beta : ℕ) (body : List TagLetter) :
    (prefixSource beta body).lowerLeft = [] := rfl

@[simp] theorem prefixSource_lowerRight (beta : ℕ) (body : List TagLetter) :
    (prefixSource beta body).lowerRight = [] := rfl

theorem prefixSource_primrec (beta : ℕ) : Primrec (prefixSource beta) := by
  refine BinaryGPCP4.primrec_mk
    (fun _ : List TagLetter => fun a => (nearyUpper beta (nearyTileOfFin a)).reverse)
    (fun body : List TagLetter => fun a => (nearyLower beta body (nearyTileOfFin a)).reverse)
    (fun _ => (nearyMarker beta).reverse) (fun _ => []) (fun _ => []) (fun _ => [])
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact Primrec.const _
  · apply MatrixMortality.Primrec.fin_function
    intro a
    exact Primrec.list_reverse.comp (nearyLower_primrec beta (nearyTileOfFin a))
  · exact Primrec.const _
  · exact Primrec.const _
  · exact Primrec.const _
  · exact Primrec.const _

theorem prefixSource_solvable_iff (beta : ℕ) (body : List TagLetter) :
    (prefixSource beta body).Solvable ↔ (nearyGPCP4 beta body).Solvable :=
  reverseProblem_solvable_iff _

/-- A primitive-recursive halting reduction with four tiles, a single left
marker and completely empty right boundaries, including the empty-word case. -/
noncomputable def prefixReduction : PrimrecReduction CodeHalts BinaryGPCP4.Solvable where
  emit index := prefixSource UniversalNeary.source.width (UniversalNeary.source.body index)
  emit_primrec := (prefixSource_primrec UniversalNeary.source.width).comp
    UniversalNeary.source.body_primrec
  target_iff_source index := by
    rw [prefixSource_solvable_iff]
    exact UniversalNeary.gpcp4Reduction.target_iff_source index

theorem prefixReduction_suffixes (index : Nat.Partrec.Code) :
    (prefixReduction.emit index).upperRight = [] ∧
      (prefixReduction.emit index).lowerRight = [] ∧
      (prefixReduction.emit index).lowerLeft = [] := by
  exact ⟨rfl, rfl, rfl⟩

end MixedVolume.Computability
