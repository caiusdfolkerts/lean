module

public import PaperVerification.ToricLaurentPicard
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# Units of the actual Laurent character ring

Maximum and minimum exponents of a product cannot cancel in a linearly
ordered character group. If the product is one, the two support widths
must both be zero. The finite-rank lattice receives its lexicographic
order only for this proof; the resulting classification is intrinsic.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra

section Ordered

variable {k A : Type*} [Field k] [AddCommGroup A] [LinearOrder A]
    [IsOrderedAddMonoid A]

private theorem uniqueAdd_max (s t : Finset A) (hs : s.Nonempty) (ht : t.Nonempty) :
    UniqueAdd s t (s.max' hs) (t.max' ht) := by
  intro a b ha hb hab
  have ha' := Finset.le_max' s a ha
  have hb' := Finset.le_max' t b hb
  rcases lt_or_eq_of_le ha' with hlt | heq
  · exact ((ne_of_lt (add_lt_add_of_lt_of_le hlt hb')) hab).elim
  · exact ⟨heq, add_left_cancel ((congrArg (fun z => z+b) heq.symm).trans hab)⟩

private theorem uniqueAdd_min (s t : Finset A) (hs : s.Nonempty) (ht : t.Nonempty) :
    UniqueAdd s t (s.min' hs) (t.min' ht) := by
  intro a b ha hb hab
  have ha' := Finset.min'_le s a ha
  have hb' := Finset.min'_le t b hb
  rcases lt_or_eq_of_le ha' with hlt | heq
  · exact ((ne_of_lt (add_lt_add_of_lt_of_le hlt hb')) hab.symm).elim
  · exact ⟨heq.symm, add_left_cancel ((congrArg (fun z => z+b) heq).trans hab)⟩

/-- A unit of a group algebra of a linearly ordered abelian group is a
single character with a nonzero scalar coefficient. -/
theorem orderedCharacter_unit_single (u : (AddMonoidAlgebra k A)ˣ) :
    ∃ (c : kˣ) (m : A), (u : AddMonoidAlgebra k A) = single m (c : k) := by
  classical
  let f : AddMonoidAlgebra k A := u
  let g : AddMonoidAlgebra k A := ↑(u⁻¹)
  have hf : f ≠ 0 := Units.ne_zero u
  have hg : g ≠ 0 := Units.ne_zero (u⁻¹)
  have hs : f.coeff.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    intro h
    exact hf (AddMonoidAlgebra.coeff_eq_zero.mp h)
  have ht : g.coeff.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    intro h
    exact hg (AddMonoidAlgebra.coeff_eq_zero.mp h)
  have hprod : f * g = 1 := u.val_inv
  let amax := f.coeff.support.max' hs
  let amin := f.coeff.support.min' hs
  let bmax := g.coeff.support.max' ht
  let bmin := g.coeff.support.min' ht
  have hmax : amax + bmax = 0 := by
    have hcoeff : (f*g).coeff (amax+bmax) ≠ 0 := by
      rw [coeff_mul_add_of_uniqueAdd (uniqueAdd_max _ _ hs ht)]
      exact mul_ne_zero
        (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hs))
        (Finsupp.mem_support_iff.mp (Finset.max'_mem _ ht))
    by_contra hne
    rw [hprod] at hcoeff
    simpa [AddMonoidAlgebra.one_def, hne] using hcoeff
  have hmin : amin + bmin = 0 := by
    have hcoeff : (f*g).coeff (amin+bmin) ≠ 0 := by
      rw [coeff_mul_add_of_uniqueAdd (uniqueAdd_min _ _ hs ht)]
      exact mul_ne_zero
        (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hs))
        (Finsupp.mem_support_iff.mp (Finset.min'_mem _ ht))
    by_contra hne
    rw [hprod] at hcoeff
    simpa [AddMonoidAlgebra.one_def, hne] using hcoeff
  have hb : bmin ≤ bmax := Finset.min'_le _ _ (Finset.max'_mem _ ht)
  have hwidth : amax ≤ amin := (add_le_add_iff_right bmax).mp <| calc
    amax+bmax = amin+bmin := hmax.trans hmin.symm
    _ ≤ amin+bmax := add_le_add_right hb amin
  have hsupport : ∀ a ∈ f.coeff.support, a = amin := by
    intro a ha
    exact le_antisymm ((Finset.le_max' _ _ ha).trans hwidth) (Finset.min'_le _ _ ha)
  have hc : f.coeff amin ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hs)
  refine ⟨Units.mk0 (f.coeff amin) hc, amin, ?_⟩
  change f = single amin (f.coeff amin)
  apply AddMonoidAlgebra.ext
  ext a
  by_cases ha : a = amin
  · subst a
    simp
  · have hnot : a ∉ f.coeff.support := fun h => ha (hsupport a h)
    simp [Finsupp.notMem_support_iff.mp hnot, ha, Ne.symm ha]

end Ordered

variable (k : Type*) [Field k] (n : ℕ)

/-- The actual units of k[Z^n] are exactly nonzero constants times
individual lattice characters, in every rank including zero. -/
theorem laurent_unit_single (u : (AddMonoidAlgebra k (Fin n → ℤ))ˣ) :
    ∃ (c : kˣ) (m : Fin n → ℤ),
      (u : AddMonoidAlgebra k (Fin n → ℤ)) = single m (c : k) := by
  let e : (Fin n → ℤ) ≃+ Lex (Fin n → ℤ) :=
    { toFun := toLex, invFun := ofLex, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  let E := AddMonoidAlgebra.domCongr k k e
  obtain ⟨c,m,hm⟩ := orderedCharacter_unit_single (Units.map E.toMonoidHom u)
  refine ⟨c,ofLex m,?_⟩
  apply E.injective
  change E (u : AddMonoidAlgebra k (Fin n → ℤ)) =
    E (single (ofLex m) (c:k))
  change E (u : AddMonoidAlgebra k (Fin n → ℤ)) = single m (c:k) at hm
  have he : e (ofLex m) = m := by
    change toLex (ofLex m) = m
    exact toLex_ofLex m
  simpa only [E,AddMonoidAlgebra.domCongr_single,he] using hm

/-- Conversely every displayed scalar-character monomial is a unit. -/
theorem isUnit_single_character (c : kˣ) (m : Fin n → ℤ) :
    IsUnit (single m (c : k) : AddMonoidAlgebra k (Fin n → ℤ)) := by
  refine ⟨⟨single m (c:k), single (-m) ((c⁻¹:kˣ):k), ?_, ?_⟩, rfl⟩ <;>
    simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]

theorem laurent_isUnit_iff (f : AddMonoidAlgebra k (Fin n → ℤ)) :
    IsUnit f ↔ ∃ (c : kˣ) (m : Fin n → ℤ), f = single m (c:k) := by
  constructor
  · rintro ⟨u,rfl⟩
    exact laurent_unit_single k n u
  · rintro ⟨c,m,rfl⟩
    exact isUnit_single_character k n c m

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.laurent_unit_single
