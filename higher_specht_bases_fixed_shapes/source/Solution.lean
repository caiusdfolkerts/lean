module

public import higher_specht.verified.remaining03_coefficients

@[expose] public section
noncomputable section

universe palomarRepU

open TauCeti

namespace HigherSpecht
open TauCeti.YoungTableau Finset Module
open scoped BigOperators Classical

abbrev canonicalTabloidRepresentationOver (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Representation R (Equiv.Perm (Fin mu.card)) (TabloidSpaceOver R mu) where
  toFun g :=
    { toFun f := fun q => f (g⁻¹ • q)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by ext f q; simp
  map_mul' g h := by ext f q; simp [mul_smul]

abbrev canonicalPolytabloidOver (R : Type*) [CommRing R] {mu : YoungDiagram}
    (T : YoungTableau mu) : TabloidSpaceOver R mu :=
  ∑ g : colSubgroup T, ((Equiv.Perm.sign g.val : ℤ) : R) •
    Pi.single (g.val • tabloid T) 1

theorem canonicalPolytabloidSpan_stable (R : Type*) [CommRing R] (mu : YoungDiagram)
    (g : Equiv.Perm (Fin mu.card)) (v : TabloidSpaceOver R mu)
    (hv : v ∈ Submodule.span R (Set.range (canonicalPolytabloidOver R (mu := mu)))) :
    canonicalTabloidRepresentationOver R mu g v ∈
      Submodule.span R (Set.range (canonicalPolytabloidOver R (mu := mu))) := by
  exact polytabloidSpan_stable R mu g v hv

abbrev canonicalSpechtSubrepresentationOver (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Subrepresentation (canonicalTabloidRepresentationOver R mu) where
  toSubmodule := Submodule.span R (Set.range (canonicalPolytabloidOver R (mu := mu)))
  apply_mem_toSubmodule := canonicalPolytabloidSpan_stable R mu

abbrev canonicalPartitionSpechtRepresentation (R : Type palomarRepU) [CommRing R] {n : ℕ}
    (part : n.Partition) :=
  (canonicalSpechtSubrepresentationOver R (YoungDiagram.ofPartition part)).toRepresentation.comp
    (finCongr (YoungDiagram.card_ofPartition part).symm).permCongrHom.toMonoidHom



theorem springer_fixedSpan_specht
    {K : Type*} [Field K] (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) (hS : CatDominates S lam)
    (hchar : ringChar K = 0 ∨ lam.card < ringChar K) :
    ∃ W : Subrepresentation (springerRepresentation K lam),
      W.toSubmodule = springerFixedCopySpanOver K lam part S ∧
      W.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (canonicalPartitionSpechtRepresentation K part)
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
      Nonempty (Representation.Equiv (canonicalPartitionSpechtRepresentation K part)
        W.toRepresentation) :=
  ⟨griffinFixedCopyOver K lam hk s part i, griffinFixedCopyOver_toSubmodule K lam hk s part i,
    corollary_8_1_griffin_copy_irreducible lam hk s part i hchar hheight⟩

end HigherSpecht
