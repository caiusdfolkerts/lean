import cubical.generic_rank
import cubical.bipartite_system
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The local polynomial system at a white vertex

The rows are (i) the common normal equation at the central white vertex,
(ii) a difference equation for each incident square, and (iii) coordinate
pins at the black vertices of a facet.  The columns are actual black-vertex
velocities.  In particular, the definition does not include a rank property.
-/

noncomputable section

namespace Cubical.Local

open Matrix

variable {B W L T : Type*} [Fintype B] [Fintype L] [Fintype T]

abbrev Row (B L T : Type*) (d : ℕ) := B ⊕ (L ⊕ (T × Fin d))

/-- The polynomial matrix for the local pinned equations. -/
def polynomialMatrix (d : ℕ) (center : W) (opposite : L → W)
    (left right : L → B) (pin : T → B) :
    Matrix (Row B L T d) (B × Fin d) (MvPolynomial (W × Fin d) ℝ) := by
  classical
  exact fun r c ↦ match r with
  | .inl b => if c.1 = b then MvPolynomial.X (center, c.2) else 0
  | .inr (.inl e) =>
      (if c.1 = left e then MvPolynomial.X (opposite e, c.2) else 0) -
      (if c.1 = right e then MvPolynomial.X (opposite e, c.2) else 0)
  | .inr (.inr ti) => if c.1 = pin ti.1 ∧ c.2 = ti.2 then 1 else 0

theorem normal_row (d : ℕ) (center : W) (opposite : L → W)
    (left right : L → B) (pin : T → B) (p : W × Fin d → ℝ)
    (u : B × Fin d → ℝ) (b : B) :
    (evalMatrix (polynomialMatrix d center opposite left right pin) p *ᵥ u)
      (.inl b) = ∑ i, p (center, i) * u (b, i) := by
  classical
  simp [evalMatrix, polynomialMatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, apply_ite, ite_mul]

theorem square_row (d : ℕ) (center : W) (opposite : L → W)
    (left right : L → B) (pin : T → B) (p : W × Fin d → ℝ)
    (u : B × Fin d → ℝ) (e : L) :
    (evalMatrix (polynomialMatrix d center opposite left right pin) p *ᵥ u)
      (.inr (.inl e)) =
      ∑ i, p (opposite e, i) * (u (left e, i) - u (right e, i)) := by
  classical
  simp only [evalMatrix, polynomialMatrix, Matrix.mulVec, dotProduct,
    Matrix.map_apply, Fintype.sum_prod_type, map_sub]
  simp only [apply_ite (MvPolynomial.eval p), MvPolynomial.eval_X, map_zero, sub_mul, ite_mul,
    zero_mul, Finset.sum_sub_distrib, mul_sub]
  simp

theorem pin_row (d : ℕ) (center : W) (opposite : L → W)
    (left right : L → B) (pin : T → B) (p : W × Fin d → ℝ)
    (u : B × Fin d → ℝ) (t : T) (i : Fin d) :
    (evalMatrix (polynomialMatrix d center opposite left right pin) p *ᵥ u)
      (.inr (.inr (t, i))) = u (pin t, i) := by
  classical
  simp [evalMatrix, polynomialMatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, apply_ite, ite_mul, ite_and]

/-- The matrix kernel is exactly the displayed local system in Lemma 2. -/
theorem kernel_iff (d : ℕ) (center : W) (opposite : L → W)
    (left right : L → B) (pin : T → B) (p : W × Fin d → ℝ)
    (u : B × Fin d → ℝ) :
    evalMatrix (polynomialMatrix d center opposite left right pin) p *ᵥ u = 0 ↔
    (∀ b, ∑ i, p (center, i) * u (b, i) = 0) ∧
    (∀ e, ∑ i, p (opposite e, i) * (u (left e, i) - u (right e, i)) = 0) ∧
    (∀ t i, u (pin t, i) = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro b
      simpa only [normal_row, Pi.zero_apply] using congrFun h (.inl b)
    · intro e
      simpa only [square_row, Pi.zero_apply] using congrFun h (.inr (.inl e))
    · intro t i
      simpa only [pin_row, Pi.zero_apply] using congrFun h (.inr (.inr (t, i)))
  · rintro ⟨hn, he, hp⟩
    funext r
    rcases r with b | e | ⟨t, i⟩
    · simpa only [normal_row, Pi.zero_apply] using hn b
    · simpa only [square_row, Pi.zero_apply] using he e
    · simpa only [pin_row, Pi.zero_apply] using hp t i

/-- Coordinate form of infinitesimal rigidity after the selected vertices are
pinned. This is an explicit auxiliary hypothesis, to be discharged using
Euclidean rigidity and affine independence. -/
def PinnedRigid (k : ℕ) (left right : L → B) (pin : T → B)
    (q : B → Fin k → ℝ) : Prop :=
  ∀ v : B → Fin k → ℝ,
    (∀ e, ∑ i, (q (left e) i - q (right e) i) *
      (v (left e) i - v (right e) i) = 0) →
    (∀ t, v (pin t) = 0) → v = 0

private def specialization (k : ℕ) (center : W) (opposite : L → W)
    (left right : L → B) (q : B → Fin k → ℝ) : W × Fin (k + 1) → ℝ := by
  classical
  exact fun wi ↦
    if wi.1 = center then
      Fin.snoc (α := fun _ : Fin (k + 1) ↦ ℝ) (fun _ ↦ 0) 1 wi.2
    else Function.extend opposite
      (fun e ↦ Fin.snoc (α := fun _ : Fin (k + 1) ↦ ℝ)
        (fun i ↦ q (left e) i - q (right e) i) 0)
      (fun _ (_ : Fin (k + 1)) ↦ (0 : ℝ)) wi.1 wi.2

private theorem specialization_center (k : ℕ) (center : W) (opposite : L → W)
    (left right : L → B) (q : B → Fin k → ℝ) (i : Fin (k + 1)) :
    specialization k center opposite left right q (center, i) =
      Fin.snoc (α := fun _ : Fin (k + 1) ↦ ℝ) (fun _ ↦ 0) 1 i := by
  simp [specialization]

private theorem specialization_opposite (k : ℕ) (center : W) (opposite : L → W)
    (left right : L → B) (q : B → Fin k → ℝ)
    (hinj : Function.Injective opposite) (hne : ∀ e, opposite e ≠ center)
    (e : L) (i : Fin (k + 1)) :
    specialization k center opposite left right q (opposite e, i) =
      Fin.snoc (α := fun _ : Fin (k + 1) ↦ ℝ)
        (fun j ↦ q (left e) j - q (right e) j) 0 i := by
  simp [specialization, hne e, hinj.extend_apply]

/-- The specialization in the paper is consistent and has zero pinned kernel.
Its only substantive mathematical input is pinned rigidity of the link. -/
theorem exists_injective_specialization (k : ℕ) (center : W) (opposite : L → W)
    (left right : L → B) (pin : T → B)
    (hinj : Function.Injective opposite) (hne : ∀ e, opposite e ≠ center)
    (q : B → Fin k → ℝ) (hq : PinnedRigid k left right pin q) :
    ∃ p : W × Fin (k + 1) → ℝ,
      Function.Injective
        (evalMatrix (polynomialMatrix (k + 1) center opposite left right pin) p).mulVec := by
  classical
  let p := specialization k center opposite left right q
  refine ⟨p, ?_⟩
  change Function.Injective
    (evalMatrix (polynomialMatrix (k + 1) center opposite left right pin) p).mulVecLin
  rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro u hu
  obtain ⟨hn, he, hp⟩ := (kernel_iff (k + 1) center opposite left right pin p u).mp hu
  have hlast : ∀ b, u (b, Fin.last k) = 0 := by
    intro b
    have h := hn b
    simp only [p, specialization_center] at h
    simpa [Fin.sum_univ_castSucc] using h
  let v : B → Fin k → ℝ := fun b i ↦ u (b, i.castSucc)
  have hv : v = 0 := by
    apply hq
    · intro e
      have h := he e
      simp only [p, specialization_opposite k center opposite left right q hinj hne] at h
      simpa [Fin.sum_univ_castSucc, v] using h
    · intro t
      funext i
      exact hp t i.castSucc
  funext bi
  obtain ⟨b, i⟩ := bi
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · exact hlast b
  · exact congrFun (congrFun hv b) j

end Cubical.Local
