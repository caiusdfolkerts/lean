module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Tactic.Abel

/-!
# A linear homotopy argument for bounded Koszul comparisons

This module proves the lifting argument needed at the top of a Koszul comparison
without introducing a derived-category hypothesis. A chain map from degreewise
projective modules into a complex exact in positive degrees is null-homotopic
when its degree-zero map lands in boundaries. If the target has no term above
the top degree, the top map factors through the source differential.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

variable {R : Type*} [CommRing R]

/-- Projectivity lifts a linear map whose image is contained in the image of
another map. The hypothesis concerns the actual images, not chosen presentations. -/
theorem exists_linear_lift_of_range_le
    {P X Y : Type*} [AddCommGroup P] [AddCommGroup X] [AddCommGroup Y]
    [Module R P] [Module R X] [Module R Y] [Module.Projective R P]
    (d : X →ₗ[R] Y) (f : P →ₗ[R] Y) (hf : LinearMap.range f ≤ LinearMap.range d) :
    ∃ h : P →ₗ[R] X, d ∘ₗ h = f := by
  let f' : P →ₗ[R] LinearMap.range d :=
    f.codRestrict (LinearMap.range d) fun p ↦ hf ⟨p, rfl⟩
  obtain ⟨h, hh⟩ := Module.projective_lifting_property d.rangeRestrict f'
    d.surjective_rangeRestrict
  refine ⟨h, LinearMap.ext fun p ↦ ?_⟩
  exact congrArg Subtype.val (LinearMap.congr_fun hh p)

section Complex

variable {C D : ℕ → Type*}
    [∀ n, AddCommGroup (C n)] [∀ n, AddCommGroup (D n)]
    [∀ n, Module R (C n)] [∀ n, Module R (D n)]
    [∀ n, Module.Projective R (C n)]

/-- A degree-zero comparison compatible with the two presentations extends to
a chain map when the target complex is exact in positive degrees. -/
theorem exists_linear_chain_comparison
    (dC : ∀ n, C (n + 1) →ₗ[R] C n)
    (dD : ∀ n, D (n + 1) →ₗ[R] D n)
    (hC : ∀ n, dC n ∘ₗ dC (n + 1) = 0)
    (hD : ∀ n, Function.Exact (dD (n + 1)) (dD n))
    (fzero : C 0 →ₗ[R] D 0)
    (hzero : LinearMap.range (fzero ∘ₗ dC 0) ≤ LinearMap.range (dD 0)) :
    ∃ f : ∀ n, C n →ₗ[R] D n,
      f 0 = fzero ∧ ∀ n, dD n ∘ₗ f (n + 1) = f n ∘ₗ dC n := by
  obtain ⟨fone, hone⟩ := exists_linear_lift_of_range_le (dD 0) (fzero ∘ₗ dC 0) hzero
  let State (n : ℕ) :=
    {p : (C n →ₗ[R] D n) × (C (n + 1) →ₗ[R] D (n + 1)) //
      dD n ∘ₗ p.2 = p.1 ∘ₗ dC n}
  have step (n : ℕ) (s : State n) :
      ∃ h : C (n + 2) →ₗ[R] D (n + 2), dD (n + 1) ∘ₗ h = s.val.2 ∘ₗ dC (n + 1) := by
    apply exists_linear_lift_of_range_le
    rintro y ⟨x, rfl⟩
    apply (hD n _).mp
    have hz : dD n ∘ₗ (s.val.2 ∘ₗ dC (n + 1)) = 0 := by
      rw [← LinearMap.comp_assoc, s.property, LinearMap.comp_assoc, hC,
        LinearMap.comp_zero]
    exact LinearMap.congr_fun hz x
  let next (n : ℕ) (s : State n) : State (n + 1) :=
    ⟨(s.val.2, (step n s).choose), (step n s).choose_spec⟩
  let states : (n : ℕ) → State n := Nat.rec ⟨(fzero, fone), hone⟩ next
  refine ⟨fun n ↦ (states n).val.1, rfl, ?_⟩
  intro n
  exact (states n).property

/-- The successive homotopy equations for a chain map lifting zero. All
projectivity, exactness, and degree-zero hypotheses are explicit. -/
theorem exists_linear_chain_homotopy_step
    (dC : ∀ n, C (n + 1) →ₗ[R] C n)
    (dD : ∀ n, D (n + 1) →ₗ[R] D n)
    (f : ∀ n, C n →ₗ[R] D n)
    (hC : ∀ n, dC n ∘ₗ dC (n + 1) = 0)
    (hD : ∀ n, Function.Exact (dD (n + 1)) (dD n))
    (hf : ∀ n, dD n ∘ₗ f (n + 1) = f n ∘ₗ dC n)
    (hzero : LinearMap.range (f 0) ≤ LinearMap.range (dD 0)) (n : ℕ) :
    ∃ (h : C n →ₗ[R] D (n + 1)) (h' : C (n + 1) →ₗ[R] D (n + 2)),
      f (n + 1) = dD (n + 1) ∘ₗ h' + h ∘ₗ dC n := by
  have lift_step (k : ℕ) (h : C k →ₗ[R] D (k + 1))
      (hcycle : dD k ∘ₗ (f (k + 1) - h ∘ₗ dC k) = 0) :
      ∃ h' : C (k + 1) →ₗ[R] D (k + 2),
        f (k + 1) = dD (k + 1) ∘ₗ h' + h ∘ₗ dC k := by
    obtain ⟨h', hh'⟩ := exists_linear_lift_of_range_le (dD (k + 1))
      (f (k + 1) - h ∘ₗ dC k) (by
        rintro y ⟨x, rfl⟩
        exact (hD k _).mp (LinearMap.congr_fun hcycle x))
    exact ⟨h', by rw [hh']; abel⟩
  induction n with
  | zero =>
      obtain ⟨h, hh⟩ := exists_linear_lift_of_range_le (dD 0) (f 0) hzero
      obtain ⟨h', hh'⟩ := lift_step 0 h (by
        rw [LinearMap.comp_sub, hf, ← LinearMap.comp_assoc, hh, sub_self])
      exact ⟨h, h', hh'⟩
  | succ n ih =>
      obtain ⟨h, h', hh⟩ := ih
      obtain ⟨h'', hh'⟩ := lift_step (n + 1) h' (by
        rw [LinearMap.comp_sub, hf, hh, LinearMap.add_comp]
        simp only [LinearMap.comp_assoc, hC, LinearMap.comp_zero, add_zero, sub_self])
      exact ⟨h', h'', hh'⟩

/-- At a bounded top degree, the null-homotopy equation says the comparison map
factors through the source differential. This is the injectivity step used in
the determinant-colon argument. -/
theorem linear_chain_map_top_factors
    (dC : ∀ n, C (n + 1) →ₗ[R] C n)
    (dD : ∀ n, D (n + 1) →ₗ[R] D n)
    (f : ∀ n, C n →ₗ[R] D n)
    (hC : ∀ n, dC n ∘ₗ dC (n + 1) = 0)
    (hD : ∀ n, Function.Exact (dD (n + 1)) (dD n))
    (hf : ∀ n, dD n ∘ₗ f (n + 1) = f n ∘ₗ dC n)
    (hzero : LinearMap.range (f 0) ≤ LinearMap.range (dD 0))
    (n : ℕ) [Subsingleton (D (n + 2))] :
    ∃ h : C n →ₗ[R] D (n + 1), f (n + 1) = h ∘ₗ dC n := by
  obtain ⟨h, h', hh⟩ := exists_linear_chain_homotopy_step dC dD f hC hD hf hzero n
  refine ⟨h, ?_⟩
  have hh' : h' = 0 := Subsingleton.elim _ _
  simpa only [hh', LinearMap.comp_zero, zero_add] using hh

end Complex

end PaperVerification.Fermion
