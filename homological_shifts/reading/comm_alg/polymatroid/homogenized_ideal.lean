import CommAlg.Polymatroid.HomogenizedBases

/-! # The actual homogenized polynomial ideal

This is the algebraic identity in Theorem 5.1. Extension of an ideal to the
polynomial ring with one extra variable is `Ideal.map` under the actual
variable-renaming homomorphism. Multiplication by the specified power of the
new variable is multiplication by its principal ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset
open scoped Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V]

section Semiring

variable (k : Type*) [CommSemiring k]

theorem monomialIdeal_union (B C : Family V) :
    monomialIdeal k (B ∪ C) = monomialIdeal k B + monomialIdeal k C := by
  simp only [monomialIdeal, Finset.coe_union, Set.image_union, Ideal.span_union,
    Ideal.add_eq_sup]

theorem monomialIdeal_biUnion {J : Type*} [DecidableEq J]
    (s : Finset J) (B : J → Family V) :
    monomialIdeal k (s.biUnion B) = ∑ j ∈ s, monomialIdeal k (B j) := by
  induction s using Finset.induction_on with
  | empty => simp [monomialIdeal]
  | @insert j s hj ih =>
    rw [Finset.biUnion_insert, monomialIdeal_union, Finset.sum_insert hj, ih]

theorem monomial_optionElim (a : Exponent V) (z : ℕ) :
    MvPolynomial.X (R := k) none ^ z *
        MvPolynomial.rename some (MvPolynomial.monomial a 1) =
      MvPolynomial.monomial (a.optionElim z) 1 := by
  have he : Finsupp.single none z + a.mapDomain some = a.optionElim z := by
    change Finsupp.single none z + a.mapDomain (Function.Embedding.some : V ↪ Option V) = _
    rw [← Finsupp.embDomain_eq_mapDomain]
    ext x
    cases x <;> simp
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.rename_monomial,
    MvPolynomial.monomial_mul, one_mul, he]

theorem monomialIdeal_optionElim (B : Family V) (z : ℕ) :
    Ideal.span {MvPolynomial.X (R := k) none ^ z} *
      Ideal.map (MvPolynomial.rename some).toRingHom (monomialIdeal k B) =
        monomialIdeal k (B.image (fun a => a.optionElim z)) := by
  unfold monomialIdeal
  rw [Ideal.map_span, Ideal.span_mul_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · intro hf
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hf
    obtain rfl := Set.mem_singleton_iff.mp hx
    obtain ⟨q, hq, rfl⟩ := hy
    obtain ⟨a, ha, rfl⟩ := hq
    refine ⟨a.optionElim z, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    exact (monomial_optionElim k a z).symm
  · rintro ⟨e, he, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact Set.mem_mul.mpr ⟨_, Set.mem_singleton _, _,
      ⟨MvPolynomial.monomial a 1, ⟨a, ha, rfl⟩, rfl⟩, monomial_optionElim k a z⟩

/-- The displayed sum in Theorem 5.1, at this stage with the explicit rank
formula in place of the separately defined genuine homological-shift ideal. -/
def homogenizedShiftIdeal (g : RankFunction V) : Ideal (MvPolynomial (Option V) k) :=
  ∑ i ∈ Finset.range (shiftLength g + 1),
    Ideal.span {MvPolynomial.X (R := k) none ^ (shiftLength g - i)} *
      Ideal.map (MvPolynomial.rename some).toRingHom (rankShiftIdeal k g i)

/-- Every generator in every shift layer occurs, and there are no additional
minimal generators. This is an equality of actual polynomial ideals. -/
theorem homogenizedShiftIdeal_eq_rankIdeal (g : RankFunction V) :
    homogenizedShiftIdeal k g = rankIdeal k (homogenizedShiftRank g) := by
  rw [rankIdeal, rankBases_homogenizedShift, monomialIdeal_biUnion]
  unfold homogenizedShiftIdeal
  apply Finset.sum_congr rfl
  intro i hi
  rw [rankShiftIdeal_eq_monomialIdeal, monomialIdeal_optionElim]

end Semiring

/-- The canonical upper rank of the precise union of homogenized shift bases. -/
theorem homogenizedShiftFamily_upperRank (g : RankFunction V)
    (A : Finset (Option V)) :
    upperRank ((Finset.range (shiftLength g + 1)).biUnion (fun i =>
      (rankShiftFamily g i).image (fun a => a.optionElim (shiftLength g - i)))) A =
        homogenizedShiftRank g A := by
  rw [← rankBases_homogenizedShift, upperRank_rankBases]

/-- The full union of homogenized shift bases satisfies the ordinary discrete
polymatroid exchange axiom. -/
theorem homogenizedShiftFamily_polymatroidal (g : RankFunction V) :
    IsPolymatroidal ((Finset.range (shiftLength g + 1)).biUnion (fun i =>
      (rankShiftFamily g i).image (fun a => a.optionElim (shiftLength g - i)))) := by
  rw [← rankBases_homogenizedShift]
  exact rankBases_polymatroidal _

end CommAlg.Polymatroid
