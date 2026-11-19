module

public import PaperVerification.AlternatingFormsOrbitSlotBasis
public import PaperVerification.AlternatingFormsOrbitCanonical
public import PaperVerification.AlternatingFormsEvenOrbitPolynomial

/-!
# The odd and even block slots are complete exterior coordinate systems

The block lists in the two orbit calculations orient each unequal pair of
coordinate positions exactly once.  The resulting bases are genuine bases
of the second exterior power.  This file also reconstructs a matrix from its
slot coefficients when its diagonal is zero and it is skew-symmetric.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators Classical

theorem oddOrbitPairSlots (t : ℕ) :
    OrbitPairSlots (oddOrbitSlotRow t) (oddOrbitSlotCol t) where
  injective := by
    intro i j h
    rcases i with p | (p | p) <;> rcases j with q | (q | q) <;>
      simpa only [oddOrbitSlotRow, oddOrbitSlotCol, Prod.mk.injEq,
        Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
        Subtype.ext_iff, Prod.ext_iff, false_and, and_false] using h
  no_reverse := by
    intro i j h
    rcases i with p | (p | p) <;> rcases j with q | (q | q) <;>
      simp only [oddOrbitSlotRow, oddOrbitSlotCol, Sum.inl.injEq,
        Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false] at h
    all_goals
      have hp := p.property
      rw [h.1, h.2] at hp
      exact (not_lt_of_ge q.property.le) hp
  covers := by
    intro u v huv
    rcases u with i | i <;> rcases v with j | j
    · rcases lt_trichotomy i j with hij | hij | hji
      · exact ⟨Sum.inl ⟨(i, j), hij⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact (huv (congrArg Sum.inl hij)).elim
      · exact ⟨Sum.inl ⟨(j, i), hji⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨Sum.inr (Sum.inr (i, j)), Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨Sum.inr (Sum.inr (j, i)), Or.inr ⟨rfl, rfl⟩⟩
    · rcases lt_trichotomy i j with hij | hij | hji
      · exact ⟨Sum.inr (Sum.inl ⟨(i, j), hij⟩), Or.inl ⟨rfl, rfl⟩⟩
      · exact (huv (congrArg Sum.inr hij)).elim
      · exact ⟨Sum.inr (Sum.inl ⟨(j, i), hji⟩), Or.inr ⟨rfl, rfl⟩⟩

theorem evenOrbitPairSlots (k : ℕ) :
    OrbitPairSlots (evenOrbitSlotRow k) (evenOrbitSlotCol k) where
  injective := by
    intro i j h
    have hr := congrArg Prod.fst h
    have hc := congrArg Prod.snd h
    rcases i with i | ⟨p, a, b⟩ <;> rcases j with j | ⟨q, c, d⟩
    · exact congrArg Sum.inl (congrArg Prod.snd hr)
    · have h₁ : i = q.val.1 := congrArg Prod.snd hr
      have h₂ : i = q.val.2 := congrArg Prod.snd hc
      exact (q.property.ne (h₁.symm.trans h₂)).elim
    · have h₁ : p.val.1 = j := congrArg Prod.snd hr
      have h₂ : p.val.2 = j := congrArg Prod.snd hc
      exact (p.property.ne (h₁.trans h₂.symm)).elim
    · have hpf : p.val.1 = q.val.1 := congrArg (fun z : EvenOrbitMode k => z.2) hr
      have hps : p.val.2 = q.val.2 := congrArg (fun z : EvenOrbitMode k => z.2) hc
      have hp : p = q := Subtype.ext (Prod.ext hpf hps)
      have ha : a = c := congrArg (fun z : EvenOrbitMode k => z.1) hr
      have hb : b = d := congrArg (fun z : EvenOrbitMode k => z.1) hc
      exact congrArg Sum.inr (Prod.ext hp (Prod.ext ha hb))
  no_reverse := by
    intro i j h
    rcases i with i | ⟨p, a, b⟩ <;> rcases j with j | ⟨q, c, d⟩
    · exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst h.1)
    · have h₁ : i = q.val.2 := congrArg Prod.snd h.1
      have h₂ : i = q.val.1 := congrArg Prod.snd h.2
      exact q.property.ne (h₂.symm.trans h₁)
    · have h₁ : p.val.1 = j := congrArg Prod.snd h.1
      have h₂ : p.val.2 = j := congrArg Prod.snd h.2
      exact p.property.ne (h₁.trans h₂.symm)
    · have h₁ : p.val.1 = q.val.2 := congrArg Prod.snd h.1
      have h₂ : p.val.2 = q.val.1 := congrArg Prod.snd h.2
      have hp := p.property
      rw [h₁, h₂] at hp
      exact (not_lt_of_ge q.property.le) hp
  covers := by
    rintro ⟨a, i⟩ ⟨b, j⟩ huv
    rcases lt_trichotomy i j with hij | hij | hji
    · exact ⟨Sum.inr (⟨(i, j), hij⟩, (a, b)), Or.inl ⟨rfl, rfl⟩⟩
    · subst j
      fin_cases a <;> fin_cases b
      · exact (huv rfl).elim
      · exact ⟨Sum.inl i, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨Sum.inl i, Or.inr ⟨rfl, rfl⟩⟩
      · exact (huv rfl).elim
    · exact ⟨Sum.inr (⟨(j, i), hji⟩, (b, a)), Or.inr ⟨rfl, rfl⟩⟩

section Reconstruction

variable {K ν ι : Type*} [CommRing K]
  [Fintype ν] [DecidableEq ν] [Fintype ι] [DecidableEq ι]

/-- Selected entries reconstruct exactly the given alternating matrix. -/
theorem orbitTwoFormOfSlots_matrix_of_alternating {row col : ι → ν}
    (h : OrbitPairSlots row col) (A : Matrix ν ν K)
    (hdiag : ∀ u, A u u = 0) (hskew : ∀ u v, A v u = -A u v) :
    orbitExteriorCoefficientMatrix
      (orbitTwoFormOfSlots row col (fun i => A (row i) (col i))) = A := by
  ext u v
  by_cases huv : u = v
  · subst v
    rw [orbitExteriorCoefficientMatrix_diagonal, hdiag]
  · obtain ⟨i, hi | hi⟩ := h.covers u v huv
    · rw [← hi.1, ← hi.2, orbitTwoFormOfSlots_coefficient h]
    · rw [← hi.2, ← hi.1, orbitExteriorCoefficientMatrix_skew,
        orbitTwoFormOfSlots_coefficient h, hskew, neg_neg]

end Reconstruction

section Bases

variable {K : Type*} [CommRing K]

def oddOrbitExteriorBasis (t : ℕ) :
    Module.Basis (OddOrbitSlot t) K (⋀[K]^2 (OddOrbitMode t → K)) :=
  orbitSlotBasis (oddOrbitPairSlots t)

def evenOrbitExteriorBasis (k : ℕ) :
    Module.Basis (EvenOrbitSlot k) K (⋀[K]^2 (EvenOrbitMode k → K)) :=
  orbitSlotBasis (evenOrbitPairSlots k)

theorem oddOrbitExteriorBasis_repr (t : ℕ) (f : ⋀[K]^2 (OddOrbitMode t → K))
    (i : OddOrbitSlot t) :
    (oddOrbitExteriorBasis t).repr f i =
      orbitExteriorCoefficientMatrix f (oddOrbitSlotRow t i) (oddOrbitSlotCol t i) :=
  orbitSlotBasis_repr (oddOrbitPairSlots t) f i

theorem evenOrbitExteriorBasis_repr (k : ℕ) (f : ⋀[K]^2 (EvenOrbitMode k → K))
    (i : EvenOrbitSlot k) :
    (evenOrbitExteriorBasis k).repr f i =
      orbitExteriorCoefficientMatrix f (evenOrbitSlotRow k i) (evenOrbitSlotCol k i) :=
  orbitSlotBasis_repr (evenOrbitPairSlots k) f i

end Bases

end PaperVerification.AlternatingForms
