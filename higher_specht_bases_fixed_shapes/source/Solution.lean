module

public import higher_specht.verified.remaining03_coefficients

@[expose] public section
noncomputable section

open TauCeti

namespace HigherSpecht

theorem springer_fixedSpan_specht
    {K : Type*} [Field K] (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) (hS : CatDominates S lam)
    (hchar : ringChar K = 0 ∨ lam.card < ringChar K) :
    ∃ W : Subrepresentation (springerRepresentation K lam),
      W.toSubmodule = springerFixedCopySpanOver K lam part S ∧
      W.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K part)
        W.toRepresentation) :=
  ⟨springerFixedCopyOver K lam part S, springerFixedCopyOver_toSubmodule K lam part S,
    corollary_8_1_springer_copy_irreducible lam part S hS hchar⟩

theorem griffin_fixedSpan_specht
    {K : Type*} [Field K] {n : ℕ} (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (part : n.Partition)
    (i : PartitionGriffinCopies n lam hk s part)
    (hchar : ringChar K = 0 ∨ n < ringChar K) (hheight : lam.colLen 0 ≤ s) :
    ∃ W : Subrepresentation (griffinRepresentation K n lam s),
      W.toSubmodule = griffinFixedCopySpanOver K lam hk s part i ∧
      W.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K part)
        W.toRepresentation) :=
  ⟨griffinFixedCopyOver K lam hk s part i, griffinFixedCopyOver_toSubmodule K lam hk s part i,
    corollary_8_1_griffin_copy_irreducible lam hk s part i hchar hheight⟩

end HigherSpecht
