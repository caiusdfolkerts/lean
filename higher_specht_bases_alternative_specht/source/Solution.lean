module

public import higher_specht.verified.remaining03_complete

@[expose] public section
noncomputable section

universe palomarRepU
open TauCeti MvPolynomial

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


end HigherSpecht

namespace HigherSpecht.GriffinIdealExpression
variable {n s : ℕ}

theorem alternative_specht_spans
    (e : GriffinIdealExpression n s) (hs : 0 < s) (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ j : {j : FiniteHarmonicIndex n s // j ∈ e.eligible},
      IsDominanceTriangularMultiplier n j.val.multiplier (f j.val.multiplier))
    (i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible}) :
    ∃ W : Subrepresentation (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)),
      W.toSubmodule =
        Submodule.span ℂ (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part) =>
          e.alternativeFamily f ⟨i, T⟩) ∧
      W.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (canonicalPartitionSpechtRepresentation ℂ i.val.part)
        W.toRepresentation) :=
  ⟨e.alternativeCopyOnEligible f hf i, e.corollary_5_3_alternative_copy_onEligible f hf hs i⟩

end HigherSpecht.GriffinIdealExpression

namespace HigherSpecht

theorem griffin_alternative_specht_spans
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ z : GriffinIndex n lam hk s,
      IsDominanceTriangularMultiplier n z.multiplier (f z.multiplier))
    (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part) :
    ∃ W : Subrepresentation (griffinRepresentation ℂ n lam s),
      W.toSubmodule =
        Submodule.span ℂ (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
          Ideal.Quotient.mk (griffinIdeal ℂ n lam s)
            (rename (finCongr (YoungDiagram.card_ofPartition part))
              (higherSpechtPolynomial i.left T) * f i.multiplier)) ∧
      W.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (canonicalPartitionSpechtRepresentation ℂ part) W.toRepresentation) := by
  exact corollary_4_3_copy_on_admissible_multipliers n lam hk s hs hheight f hf part i

end HigherSpecht
