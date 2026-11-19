module
public import Papers.MatrixSupportCounts
public import Papers.RelationMatrixDensity

@[expose] public section

/-!
# Exact algebra interfaces for the small relation-matrix arguments

These propositions state the matrix conclusions supplied by the finite
rank-four classification and its omitted-incidence charts. No existence or
density assertion is assumed as an axiom. The separate classification proof
establishes these propositions before the geometric assembly uses them.

-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity
open Set Matrix
open scoped Classical

def OmitsEveryNineFourSupportFamily {c : ℕ}
    (C : Matrix (Fin c) (Fin 9) ℝ) : Prop :=
  ∀ L : Finset (Finset (Fin c)), L.card = 9 →
    (∀ S ∈ L, S.card = 4) → ∃ S ∈ L, ∀ j, columnSupport C j ≠ S

/-- The row positions where one column vanishes. These are the subsets whose
ranks must be preserved in the coordinate-functional reconstruction. -/
def columnZeroSet {c n : ℕ} (C : Matrix (Fin c) (Fin n) ℝ) (j : Fin n) :
    Finset (Fin c) :=
  Finset.univ.filter fun i => C i j = 0

theorem columnZeroSet_eq_compl_columnSupport {c n : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (j : Fin n) :
    columnZeroSet C j = (columnSupport C j)ᶜ := by
  ext i
  simp [columnZeroSet, columnSupport]

/-- On eight row positions, complementation preserves four-element sets.
The geometric support-counting conclusion therefore excludes a required
flat in every nine-member family of four-element zero-row flats as well. -/
theorem OmitsEveryNineFourSupportFamily.zeroSets {c : ℕ}
    {C : Matrix (Fin c) (Fin 9) ℝ} (h : OmitsEveryNineFourSupportFamily C)
    (hc : c = 8) (L : Finset (Finset (Fin c)))
    (hL : L.card = 9) (hfour : ∀ S ∈ L, S.card = 4) :
    ∃ S ∈ L, ∀ j, columnZeroSet C j ≠ S := by
  let M := L.image (fun S => Sᶜ)
  have hM : M.card = 9 := by
    rw [Finset.card_image_of_injective _ compl_injective]
    exact hL
  have hMfour : ∀ S ∈ M, S.card = 4 := by
    rintro S hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    rw [Finset.card_compl, Fintype.card_fin, hfour T hT]
    omega
  obtain ⟨S, hS, homit⟩ := h M hM hMfour
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
  refine ⟨T, hT, ?_⟩
  intro j hj
  apply homit j
  have hh := congrArg (fun S : Finset (Fin c) => Sᶜ) hj
  simpa only [columnZeroSet_eq_compl_columnSupport, compl_compl] using hh

/-- The precise matrix-density input left after the actual nine-vertex
geometric analysis. Its proof belongs to the finite rank-four chart chain. -/
def NineColumnExceptionalMatrixDensity : Prop :=
  ∀ (c : ℕ) (C : Matrix (Fin c) (Fin 9) ℝ), c = 8 →
    ((∃ v : Fin c → ℝ, v ≠ 0 ∧ C.transpose.mulVec v = 0 ∧
        (vectorSupport v).card ≤ 3) ∨ OmitsEveryNineFourSupportFamily C) →
    C ∈ closure {D : Matrix (Fin c) (Fin 9) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D}

/-- The only classification information used in the eight-row geometric
argument. It is weaker than the full identification of the golden matroid. -/
def EightRowMatrixDensityOrFourSupport : Prop :=
  ∀ (c n : ℕ) (C : Matrix (Fin c) (Fin n) ℝ), c ≤ 8 →
    C ∈ closure {D : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D} ∨
      ∀ j ∈ activeColumns C, 4 ≤ (columnSupport C j).card

end Papers.RationalityTen.ChirotopeDensity
