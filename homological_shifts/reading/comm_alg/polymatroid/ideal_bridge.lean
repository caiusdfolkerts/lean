import CommAlg.Polymatroid.HomologicalMain
import CommAlg.Polymatroid.MultiRank

/-! # Polymatroidal ideals as actual polynomial ideals

The defining exchange family is unique: every equigenerated family is an
antichain, and monomial membership recovers an antichain of generators.
Consequently the homological shift below is independent of a presentation;
it is computed from the genuine derived-Tor components of the actual ideal.
This bridge includes both the zero and the unit ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

def IsPolymatroidalIdeal (I : Ideal (MvPolynomial V k)) : Prop :=
  ∃ B : Family V, IsPolymatroidal B ∧ I = monomialIdeal k B

theorem monomialIdeal_family_unique {B C : Family V}
    (hB : IsPolymatroidal B) (hC : IsPolymatroidal C)
    (he : monomialIdeal k B = monomialIdeal k C) : B = C := by
  obtain ⟨d, hd⟩ := hB.1
  obtain ⟨e, heq⟩ := hC.1
  apply family_eq_of_contains_iff hd.antichain heq.antichain
  intro a
  rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k), he]

def idealGenerators (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) : Family V :=
  hI.choose

theorem idealGenerators_polymatroidal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) : IsPolymatroidal (idealGenerators I hI) :=
  hI.choose_spec.1

theorem monomialIdeal_idealGenerators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) : monomialIdeal k (idealGenerators I hI) = I :=
  hI.choose_spec.2.symm

theorem idealGenerators_eq_of_presentation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (B : Family V) (hB : IsPolymatroidal B)
    (he : I = monomialIdeal k B) : idealGenerators I hI = B :=
  monomialIdeal_family_unique (idealGenerators_polymatroidal I hI) hB
    ((monomialIdeal_idealGenerators I hI).trans he)

theorem isPolymatroidalIdeal_monomialIdeal (B : Family V) (hB : IsPolymatroidal B) :
    IsPolymatroidalIdeal (monomialIdeal k B) := ⟨B, hB, rfl⟩

theorem isPolymatroidalIdeal_rankIdeal (g : RankFunction V) :
    IsPolymatroidalIdeal (rankIdeal k g) :=
  ⟨rankBases g, rankBases_polymatroidal g, rfl⟩

theorem isPolymatroidalIdeal_bot : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)) := by
  refine ⟨∅, ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩, ?_⟩
  simp [monomialIdeal]

theorem isPolymatroidalIdeal_top : IsPolymatroidalIdeal (⊤ : Ideal (MvPolynomial V k)) := by
  simpa only [rankIdeal_zeroRank] using
    (isPolymatroidalIdeal_rankIdeal (k := k) (zeroRank (V := V)))

theorem IsPolymatroidalIdeal.eq_bot_or_rank {I : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) : I = ⊥ ∨ ∃ g : RankFunction V, I = rankIdeal k g := by
  obtain ⟨B, hB, rfl⟩ := hI
  by_cases hne : B.Nonempty
  · obtain ⟨d, hd⟩ := hB.1
    refine Or.inr ⟨canonicalRank B hne d hd hB, ?_⟩
    rw [rankIdeal, rankBases_canonical B hne d hd hB]
  · have he := not_nonempty_iff_eq_empty.mp hne
    exact Or.inl (by simp [he, monomialIdeal])

theorem IsPolymatroidalIdeal.exists_rank {I : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (hne : I ≠ ⊥) : ∃ g : RankFunction V, I = rankIdeal k g :=
  hI.eq_bot_or_rank.resolve_left hne

theorem IsPolymatroidalIdeal.mul {I J : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J) :
    IsPolymatroidalIdeal (I * J) := by
  rcases hI.eq_bot_or_rank with rfl | ⟨g, rfl⟩
  · simpa using (isPolymatroidalIdeal_bot (V := V) (k := k))
  rcases hJ.eq_bot_or_rank with rfl | ⟨h, rfl⟩
  · simpa using (isPolymatroidalIdeal_bot (V := V) (k := k))
  rw [← rankIdeal_add]
  exact isPolymatroidalIdeal_rankIdeal _

theorem IsPolymatroidalIdeal.pow {I : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (s : ℕ) : IsPolymatroidalIdeal (I ^ s) := by
  induction s with
  | zero => simpa using (isPolymatroidalIdeal_top (V := V) (k := k))
  | succ s ih => simpa only [pow_succ] using ih.mul hI

theorem IsPolymatroidalIdeal.prod {J : Type*} (F : Finset J)
    (I : J → Ideal (MvPolynomial V k)) (hI : ∀ j ∈ F, IsPolymatroidalIdeal (I j)) :
    IsPolymatroidalIdeal (∏ j ∈ F, I j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (isPolymatroidalIdeal_top (V := V) (k := k))
  | @insert j F hj ih =>
    rw [Finset.prod_insert hj]
    exact (hI j (mem_insert_self _ _)).mul (ih (fun x hx => hI x (mem_insert_of_mem hx)))

/-- The homological shift of an actual polymatroidal ideal. The uniquely
determined generator family only supplies the finite presentation used to
construct its standard multigrading on genuine derived Tor. -/
def homologicalShiftIdeal (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) : Ideal (MvPolynomial V k) :=
  Koszul.homologicalShift (k := k) (idealGenerators I hI) i

theorem homologicalShiftIdeal_of_presentation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (B : Family V) (hB : IsPolymatroidal B)
    (he : I = monomialIdeal k B) (i : ℕ) :
    homologicalShiftIdeal I hI i = Koszul.homologicalShift (k := k) B i := by
  unfold homologicalShiftIdeal
  rw [idealGenerators_eq_of_presentation I hI B hB he]

theorem homologicalShiftIdeal_eq_rankShiftIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) (i : ℕ) :
    homologicalShiftIdeal I hI i = rankShiftIdeal k g i := by
  rw [homologicalShiftIdeal_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he,
    homologicalShift_rankBases]

@[simp] theorem homologicalShiftIdeal_bot (hI : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)))
    (i : ℕ) : homologicalShiftIdeal ⊥ hI i = ⊥ := by
  rw [homologicalShiftIdeal_of_presentation _ hI ∅
    ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩ (by simp [monomialIdeal]),
    homologicalShift_empty]

theorem homologicalShiftIdeal_congr {I J : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J) (he : I = J) (i : ℕ) :
    homologicalShiftIdeal I hI i = homologicalShiftIdeal J hJ i := by
  subst J
  rfl

theorem homologicalShiftIdeal_polymatroidal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : IsPolymatroidalIdeal (homologicalShiftIdeal I hI i) := by
  obtain ⟨B, hB, he⟩ := homologicalShift_polymatroidal (k := k) (idealGenerators I hI)
    (idealGenerators_polymatroidal I hI) i
  exact ⟨B, hB, he⟩

end CommAlg.Polymatroid
