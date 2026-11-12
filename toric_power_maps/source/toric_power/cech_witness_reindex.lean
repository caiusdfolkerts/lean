module

public import ToricPower.CechNegativeSupportGeneric

/-!
# Changing only the witnesses of the relative incidence complex

The relative scalar condition depends on a witness type only through the
actual forbidden-tuple predicate. An equivalence of witness types induces
an isomorphism of the complete relative cochain complexes, with every
scalar and every chart tuple unchanged. In particular, a finite ray type
may be enumerated in `Fin` without changing the cochain complex or imposing
a universe restriction on the ambient fan.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace ToricPower.NegativeSupportCech

variable (𝕜 : Type) [Field 𝕜]
variable {Ray Ray' : Type*} {Chart : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
variable (incidence' : Ray' → Chart → Prop) (negative' : Ray' → Prop)
variable (same : ∀ degree tuple,
  tupleForbidden incidence negative degree tuple ↔
    tupleForbidden incidence' negative' degree tuple)

def relativeScalarEquivOfForbiddenIff (degree : ℕ)
    (tuple : Fin (degree + 1) → Chart) :
    relativeScalarCoefficient 𝕜 incidence negative degree tuple ≃+
      relativeScalarCoefficient 𝕜 incidence' negative' degree tuple where
  toFun scalar := ⟨scalar.val, fun forbidden => scalar.property ((same degree tuple).mpr forbidden)⟩
  invFun scalar := ⟨scalar.val, fun forbidden => scalar.property ((same degree tuple).mp forbidden)⟩
  left_inv scalar := Subtype.ext rfl
  right_inv scalar := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

def relativeDegreeIsoOfForbiddenIff (degree : ℕ) :
    relativeDegree 𝕜 incidence negative degree ≅
      relativeDegree 𝕜 incidence' negative' degree :=
  Limits.Pi.mapIso (fun tuple =>
    (relativeScalarEquivOfForbiddenIff 𝕜 incidence negative incidence' negative' same
      degree tuple).toAddCommGrpIso)

theorem relativeDegreeIsoOfForbiddenIff_selection {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1)) :
    (relativeDegreeIsoOfForbiddenIff 𝕜 incidence negative incidence' negative' same degree).hom ≫
      relativeTupleMap 𝕜 incidence' negative' selection =
        relativeTupleMap 𝕜 incidence negative selection ≫
          (relativeDegreeIsoOfForbiddenIff 𝕜 incidence negative incidence' negative' same next).hom := by
  apply Limits.Pi.hom_ext
  intro tuple
  simp only [Category.assoc, relativeTupleMap, relativeDegreeIsoOfForbiddenIff,
    Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc,
    Limits.Pi.mapIso_hom_π, Limits.Pi.mapIso_hom_π_assoc]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro cochain
  apply Subtype.ext
  rfl

/-- The actual cochain isomorphism, including all differentials. -/
def relativeComplexIsoOfForbiddenIff :
    relativeComplex 𝕜 incidence negative ≅ relativeComplex 𝕜 incidence' negative' :=
  HomologicalComplex.Hom.isoOfComponents
    (relativeDegreeIsoOfForbiddenIff 𝕜 incidence negative incidence' negative' same)
    (fun degree next related => by
      change degree + 1 = next at related
      subst next
      rw [relativeComplex_d, relativeComplex_d]
      simp only [comp_sum, sum_comp, comp_zsmul, zsmul_comp]
      apply Finset.sum_congr rfl
      intro deleted _
      exact congrArg (fun mapping => (-1 : ℤ) ^ deleted.val • mapping)
        (relativeDegreeIsoOfForbiddenIff_selection 𝕜 incidence negative incidence' negative'
          same deleted.succAbove))

/-- Reindexing witnesses by an actual equivalence preserves the literal
existential forbidden-tuple condition. -/
theorem tupleForbidden_reindex_iff (equivalence : Ray' ≃ Ray)
    (degree : ℕ) (tuple : Fin (degree + 1) → Chart) :
    tupleForbidden incidence negative degree tuple ↔
      tupleForbidden (fun ray chart => incidence (equivalence ray) chart)
        (fun ray => negative (equivalence ray)) degree tuple := by
  constructor
  · rintro ⟨ray, bad, contains⟩
    refine ⟨equivalence.symm ray, ?_, ?_⟩
    · simpa only [equivalence.apply_symm_apply] using bad
    · intro column
      simpa only [equivalence.apply_symm_apply] using contains column
  · rintro ⟨ray, bad, contains⟩
    exact ⟨equivalence ray, bad, contains⟩

def relativeWitnessReindexIso (equivalence : Ray' ≃ Ray) :
    relativeComplex 𝕜 incidence negative ≅
      relativeComplex 𝕜 (fun ray chart => incidence (equivalence ray) chart)
        (fun ray => negative (equivalence ray)) :=
  relativeComplexIsoOfForbiddenIff 𝕜 incidence negative _ _
    (tupleForbidden_reindex_iff incidence negative equivalence)

end ToricPower.NegativeSupportCech
