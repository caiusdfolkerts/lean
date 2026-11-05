module
public import PaperVerification.ToricStatements
public import Mathlib.GroupTheory.QuotientGroup.Defs
@[expose] public section
/-!
# Prescribed parity as the actual quotient M / 2M

The principal Lean target quantifies over lattice representatives. This file
proves its equivalence to the paper's quantification over quotient classes.
The subgroup is exactly the image of doubling, with no finite restriction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange

/-- The actual subgroup 2M of the coordinate lattice. -/
def twiceLattice (n : ℕ) : AddSubgroup (Lattice n) where
  carrier := {z | ∃ w, z = w + w}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u + v, by abel⟩
  neg_mem' := by
    rintro a ⟨u, rfl⟩
    exact ⟨-u, by abel⟩

/-- The quotient group used in the original prescribed-parity statement. -/
abbrev ParityClass (n : ℕ) := Lattice n ⧸ twiceLattice n

/-- Send a lattice vector to its actual class modulo the doubled lattice. -/
def parityClass (n : ℕ) : Lattice n →+ ParityClass n :=
  QuotientAddGroup.mk' (twiceLattice n)

theorem parityClass_surjective (n : ℕ) : Function.Surjective (parityClass n) :=
  QuotientAddGroup.mk'_surjective (twiceLattice n)

/-- The witness-based parity relation is precisely equality in M/2M. -/
theorem sameParity_iff_parityClass_eq {n : ℕ} (a b : Lattice n) :
    SameParity a b ↔ parityClass n a = parityClass n b := by
  change SameParity a b ↔ (a : Lattice n ⧸ twiceLattice n) = b
  rw [QuotientAddGroup.eq_iff_sub_mem]
  rfl

/-- Prescribing every representative is equivalent to prescribing every
quotient class, for arbitrary summand sets and an arbitrary fixed total. -/
theorem prescribedParity_representatives_iff_classes {n : ℕ}
    (S T : Set (Lattice n)) (m : Lattice n) :
    (∀ c : Lattice n, ∃ a b : Lattice n,
      a ∈ S ∧ b ∈ T ∧ a + b = m ∧ SameParity a c) ↔
    (∀ α : ParityClass n, ∃ a b : Lattice n,
      a ∈ S ∧ b ∈ T ∧ a + b = m ∧ parityClass n a = α) := by
  constructor
  · intro h α
    obtain ⟨c, rfl⟩ := parityClass_surjective n α
    obtain ⟨a, b, ha, hb, hab, hpar⟩ := h c
    exact ⟨a, b, ha, hb, hab, (sameParity_iff_parityClass_eq a c).mp hpar⟩
  · intro h c
    obtain ⟨a, b, ha, hb, hab, hpar⟩ := h (parityClass n c)
    exact ⟨a, b, ha, hb, hab, (sameParity_iff_parityClass_eq a c).mpr hpar⟩

/-- The principal parity target is exactly equivalent to the quotient-class
formulation used in the paper, with every other quantifier unchanged. -/
theorem theorem1_2_iff_quotient_classes :
    Theorem1_2PolytopeStatement ↔
      ∀ n : ℕ, ∀ P Q : LatticePolytope n,
        P.Smooth → Q.Smooth → P.SameNormalFan Q →
        P.EdgesAtLeast n → Q.EdgesAtLeast n →
        ∀ m : Lattice n, embed n m ∈ interior (P.minkowskiSum Q) →
          ∀ α : ParityClass n, ∃ a b : Lattice n,
            embed n a ∈ P.carrier ∧ embed n b ∈ Q.carrier ∧
            a + b = m ∧ parityClass n a = α := by
  constructor
  · intro h n P Q hP hQ hfan hlP hlQ m hm
    exact (prescribedParity_representatives_iff_classes
      ((embed n) ⁻¹' P.carrier) ((embed n) ⁻¹' Q.carrier) m).mp
        (h n P Q hP hQ hfan hlP hlQ m hm)
  · intro h n P Q hP hQ hfan hlP hlQ m hm
    exact (prescribedParity_representatives_iff_classes
      ((embed n) ⁻¹' P.carrier) ((embed n) ⁻¹' Q.carrier) m).mpr
        (h n P Q hP hQ hfan hlP hlQ m hm)

end PaperVerification.ToricGeometry

