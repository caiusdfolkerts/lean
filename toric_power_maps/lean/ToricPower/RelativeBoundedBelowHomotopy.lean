module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Bounded-below relative Hom acyclicity

The usual bounded-below injective homotopy construction needs only one
lifting property: a map annihilating the preceding source differential
must factor through the following differential. This is exactly row
exactness of `Hom(K, Y)`. It need not come from injectivity of `Y`.

The proof below constructs an actual null homotopy, degree by degree,
using Mathlib's cochain induction and its verified limiting construction.
This is the bounded-below acyclic-assembly argument needed for Čech
coefficients of injective quasicoherent complexes.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CochainComplex HomComplex

namespace ToricPower

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every closed map from one term of `K` into `Y` is a horizontal boundary. -/
def RightHomExact (K : CochainComplex C ℤ) (Y : C) : Prop :=
  ∀ (n : ℤ) (f : K.X (n+1) ⟶ Y), K.d n (n+1) ≫ f = 0 →
    ∃ (g : K.X (n+2) ⟶ Y), K.d (n+1) (n+2) ≫ g = f

/-- One step of the relative null-homotopy construction. -/
theorem relativeHomotopyStep {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (α : Cochain K L (-1)) (n m : ℤ) (hnm : n+1=m)
    (hrow : RightHomExact K (L.X m))
    (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) :
    ∃ (h : K.X (n+2) ⟶ L.X (n+1)),
      (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f) m := by
  subst hnm
  let u := f.f (n+1) - α.v (n+1) n (by lia) ≫ L.d n (n+1) -
    K.d (n+1) (n+2) ≫ α.v (n+2) (n+1) (by lia)
  have hu : K.d n (n+1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n-1) (n+1)
      (by lia) (by lia), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  obtain ⟨β, hβ⟩ := hrow n u hu
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by lia
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by lia) (by lia), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p-1) (p+1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia),
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n+1) (n+1) (by lia) n (n+2)
      (by lia) (by lia), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp [hβ, u]

open Cochain.InductionUp in
/-- If every coefficient row is exact, every map into a bounded-below
complex is actually null homotopic. No injectivity assumption is hidden
in the statement. -/
theorem nonempty_homotopy_zero_of_rightHomExact
    (K L : CochainComplex C ℤ) (d : ℤ) [L.IsStrictlyGE d]
    (hrow : ∀ n, RightHomExact K (L.X n)) (f : K ⟶ L) :
    Nonempty (Homotopy f 0) := by
  let X (n : ℕ) : Set (Cochain K L (-1)) :=
    Set.ofPred (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n+d-1))
  let x₀ : X 0 := ⟨0, fun p q hpq hp =>
    IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by lia)) _ _⟩
  let φ (n : ℕ) (α : X n) : X (n+1) :=
    ⟨_, (relativeHomotopyStep f α.1 (n+d-1) ((n+1 : ℕ)+d-1)
      (by lia) (hrow _) α.2).choose_spec⟩
  have hφ (k : ℕ) (x : X k) : (φ k x).1.EqUpTo x.1 (d+k) := fun p q hpq hp => by
    dsimp [φ]
    rw [add_eq_left, Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  ext n
  let k₀ := (n-d+1).toNat
  rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by lia),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n-1) (n+1) rfl (by lia),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n-1) (n+1) rfl (by lia),
    limitSequence_eqUpTo φ hφ x₀ k₀ n (n-1) (by lia) (by lia),
    limitSequence_eqUpTo φ hφ x₀ k₀ (n+1) n (by lia) (by lia)]

end ToricPower
