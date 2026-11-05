module

public import PaperVerification.PowerDegreeQuotient
public import PaperVerification.PowerGroupedParameters
public import PaperVerification.QuotientLinearAction
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The actual permutation action on the differential tail

Every permutation fixing the coefficient tuple acts by renaming polynomial
variables. The proof includes the characteristic-remainder correction, so
both maps of the deformation complex are equivariant with their Koszul
generator indices fixed. The quotient action is induced on the literal
operator-image quotient, and preserves every actual homogeneous piece.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

def polynomialPermutationAction (R : Type*) [CommRing R]
    (G : Subgroup (Equiv.Perm (Fin n))) :
    Representation R G (MvPolynomial (Fin n) R) where
  toFun g := (MvPolynomial.rename (g : Equiv.Perm (Fin n))).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro p
    exact MvPolynomial.rename_id_apply p
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    change MvPolynomial.rename (↑(g*h) : Equiv.Perm (Fin n)) p =
      MvPolynomial.rename (g : Equiv.Perm (Fin n))
        (MvPolynomial.rename (h : Equiv.Perm (Fin n)) p)
    rw [MvPolynomial.rename_rename]
    simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul]

@[simp] theorem polynomialPermutationAction_apply
    (G : Subgroup (Equiv.Perm (Fin n))) (g : G) (p : MvPolynomial (Fin n) R) :
    polynomialPermutationAction R G g p = MvPolynomial.rename (g : Equiv.Perm (Fin n)) p := rfl

theorem rename_euler (e : Equiv.Perm (Fin n)) (i : Fin n)
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.rename e (euler i p) = euler (e i) (MvPolynomial.rename e p) := by
  simp only [euler_apply, map_mul, MvPolynomial.rename_X,
    MvPolynomial.pderiv_rename e.injective]

theorem rename_component (e : Equiv.Perm (Fin n)) (c lam : R) (i : Fin n) (k : ℕ)
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.rename e (component c lam i k p) =
      component c lam (e i) k (MvPolynomial.rename e p) := by
  simp only [component_apply, map_mul, map_pow, map_add, map_smul,
    MvPolynomial.rename_X, rename_euler]

theorem rename_reversed (e : Equiv.Perm (Fin n)) (c : Fin n → R) (lam : R)
    (hfix : ∀ i, c (e i) = c i) (k : ℕ) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.rename e (reversed c lam k p) =
      reversed c lam k (MvPolynomial.rename e p) := by
  simp only [reversed_apply, map_sum, rename_component]
  calc
    _ = ∑ i, component (c (e i)) lam (e i) k (MvPolynomial.rename e p) := by
      simp only [hfix]
    _ = _ := Equiv.sum_comp e
      (fun i : Fin n => component (c i) lam i k (MvPolynomial.rename e p))

theorem rename_tailCoefficient (e : Equiv.Perm (Fin n)) (k : ℕ) (j : Fin n) :
    MvPolynomial.rename e (tailCoefficient (K := R) k j) = tailCoefficient (K := R) k j := by
  have hchar :
      (Fermion.parameterPolynomial (fun i : Fin n => (X i : MvPolynomial (Fin n) R))).map
          (MvPolynomial.rename e).toRingHom =
        Fermion.parameterPolynomial (fun i : Fin n => (X i : MvPolynomial (Fin n) R)) := by
    simp only [Fermion.parameterPolynomial, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    change (∏ i : Fin n, (Polynomial.X - Polynomial.C
      (MvPolynomial.rename e (X i : MvPolynomial (Fin n) R)))) = _
    simp only [MvPolynomial.rename_X]
    exact Equiv.prod_comp e (fun i : Fin n =>
      (Polynomial.X-Polynomial.C (X i : MvPolynomial (Fin n) R)))
  unfold tailCoefficient
  change (MvPolynomial.rename e).toRingHom
    ((Polynomial.X ^ k %ₘ Fermion.parameterPolynomial
      (fun i : Fin n => (X i : MvPolynomial (Fin n) R))).coeff j.val) = _
  rw [← Polynomial.coeff_map (MvPolynomial.rename e).toRingHom,
    Polynomial.map_modByMonic (MvPolynomial.rename e).toRingHom
      (Fermion.parameterPolynomial_monic
        (fun i : Fin n => (X i : MvPolynomial (Fin n) R))),
    Polynomial.map_pow, Polynomial.map_X, hchar]

theorem rename_homogeneousTailCoefficient (e : Equiv.Perm (Fin n)) (k : ℕ) (j : Fin n) :
    MvPolynomial.rename e (homogeneousTailCoefficient (R := R) k j) =
      homogeneousTailCoefficient (R := R) k j := by
  unfold homogeneousTailCoefficient
  split_ifs
  · rw [MvPolynomial.rename_homogeneousComponent, rename_tailCoefficient]
  · exact map_zero _

theorem rename_recurrenceVector (e : Equiv.Perm (Fin n)) (m : ℕ) (i j l : Fin n)
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.rename e (recurrenceVector m i j p l) =
      recurrenceVector m i j (MvPolynomial.rename e p) l := by
  simp only [recurrenceVector_apply, map_mul, rename_homogeneousTailCoefficient]

theorem rename_elementarySyzygy (e : Equiv.Perm (Fin n)) (c : Fin n → R) (lam : R)
    (hfix : ∀ i, c (e i) = c i) (m : ℕ) (i j l : Fin n)
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.rename e (elementarySyzygy c lam m i j p l) =
      elementarySyzygy c lam m i j (MvPolynomial.rename e p) l := by
  classical
  simp only [elementarySyzygy_apply, Pi.sub_apply, Pi.smul_apply, map_sub,
    map_smul, rename_recurrenceVector, Pi.single_apply]
  split_ifs <;> simp only [rename_reversed e c lam hfix, map_zero]

theorem rename_tailMap (e : Equiv.Perm (Fin n)) (c : Fin n → R) (lam : R)
    (hfix : ∀ i, c (e i) = c i) (m : ℕ) (v : Fin n → MvPolynomial (Fin n) R) :
    MvPolynomial.rename e (tailMap c lam m v) =
      tailMap c lam m (fun i => MvPolynomial.rename e (v i)) := by
  simp only [tailMap_apply, map_sum, rename_reversed e c lam hfix]

theorem rename_syzygyMap (e : Equiv.Perm (Fin n)) (c : Fin n → R) (lam : R)
    (hfix : ∀ i, c (e i) = c i) (m : ℕ)
    (A : Fin n → Fin n → MvPolynomial (Fin n) R) (l : Fin n) :
    MvPolynomial.rename e (syzygyMap c lam m A l) =
      syzygyMap c lam m (fun i j => MvPolynomial.rename e (A i j)) l := by
  simp only [syzygyMap_apply, Finset.sum_apply, map_sum,
    rename_elementarySyzygy e c lam hfix]

theorem rename_mem_tailHit (e : Equiv.Perm (Fin n)) (c : Fin n → R) (lam : R)
    (hfix : ∀ i, c (e i) = c i) (m : ℕ)
    {p : MvPolynomial (Fin n) R} (hp : p ∈ tailHit c lam m) :
    MvPolynomial.rename e p ∈ tailHit c lam m := by
  rw [← range_tailMap] at hp ⊢
  obtain ⟨v, rfl⟩ := hp
  exact ⟨fun i => MvPolynomial.rename e (v i), (rename_tailMap e c lam hfix m v).symm⟩

theorem rename_mem_homogeneousSubmodule (e : Equiv.Perm (Fin n)) (d : ℕ)
    {p : MvPolynomial (Fin n) R} (hp : p ∈ homogeneousSubmodule (Fin n) R d) :
    MvPolynomial.rename e p ∈ homogeneousSubmodule (Fin n) R d := by
  have he : homogeneousComponent d (MvPolynomial.rename e p) = MvPolynomial.rename e p := by
    rw [← MvPolynomial.rename_homogeneousComponent, homogeneousComponent_eq_self hp]
  rw [← he]
  exact homogeneousComponent_mem _ _

end Ring

section Field

variable {K : Type*} [Field K] {n : ℕ}
variable (G : Subgroup (Equiv.Perm (Fin n))) (c : Fin n → K) (lam : K) (m : ℕ)
variable (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)

/-- The actual induced representation on the complete joint-image quotient. -/
def tailQuotientAction : Representation K G (MvPolynomial (Fin n) K ⧸ tailHit c lam m) :=
  QuotientLinearAction.action (polynomialPermutationAction K G) (tailHit c lam m)
    (fun g _ hp => rename_mem_tailHit (g : Equiv.Perm (Fin n)) c lam (hfix g) m hp)

@[simp] theorem tailQuotientAction_mkQ (g : G) (p : MvPolynomial (Fin n) K) :
    tailQuotientAction G c lam m hfix g ((tailHit c lam m).mkQ p) =
      (tailHit c lam m).mkQ (MvPolynomial.rename (g : Equiv.Perm (Fin n)) p) := rfl

theorem tailQuotientAction_preserves_degree (g : G) (d : ℕ)
    {z : MvPolynomial (Fin n) K ⧸ tailHit c lam m}
    (hz : z ∈ tailQuotientDegree c lam m d) :
    tailQuotientAction G c lam m hfix g z ∈ tailQuotientDegree c lam m d := by
  obtain ⟨p, hp, rfl⟩ := hz
  rw [tailQuotientAction_mkQ]
  exact ⟨_, rename_mem_homogeneousSubmodule (g : Equiv.Perm (Fin n)) d hp, rfl⟩

/-- The genuine degreewise representation used in the comparison theorem. -/
def tailQuotientDegreeRepresentation (d : ℕ) :
    Representation K G (tailQuotientDegree c lam m d) :=
  Representation.subrepresentation (tailQuotientAction G c lam m hfix)
    (tailQuotientDegree c lam m d)
    (fun g _ hz => tailQuotientAction_preserves_degree G c lam m hfix g d hz)

end Field

end PaperVerification.PowerOperators
