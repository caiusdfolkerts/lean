module
public import Papers.PlaneChirotopeDensity
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Matrix Set Filter Topology

namespace Papers.RationalityTen

namespace ChirotopeDensity

open PlaneRationalization

def RationalCoordinates {n r : ℕ} (p : Fin n → Fin r → ℝ) : Prop :=
  ∀ i j, RatScalar (p i j)

def minor {n r : ℕ} (p : Fin n → Fin r → ℝ) (b : Fin r → Fin n) : ℝ :=
  (Matrix.of (fun i j => p (b i) j)).det

/-- Equality of all labelled maximal-minor signs. For a spanning vector
configuration this is precisely equality of its represented oriented matroid,
with a fixed global orientation convention. -/
def SameChirotope {n r : ℕ} (p q : Fin n → Fin r → ℝ) : Prop :=
  ∀ b, SignType.sign (minor q b) = SignType.sign (minor p b)

def PreservesZeroMinors {n r : ℕ} (p q : Fin n → Fin r → ℝ) : Prop :=
  ∀ b, minor p b = 0 → minor q b = 0

def RationalRealizations {n r : ℕ} (p : Fin n → Fin r → ℝ) :
    Set (Fin n → Fin r → ℝ) :=
  {q | RationalCoordinates q ∧ SameChirotope p q}

theorem rationalCoordinates_dense (n r : ℕ) :
    Dense {p : Fin n → Fin r → ℝ | RationalCoordinates p} := by
  have h : DenseRange
      (fun p : Fin n → Fin r → ℚ => fun i j => (p i j : ℝ)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => Rat.denseRange_cast
  apply h.mono
  rintro _ ⟨p,rfl⟩ i j
  exact ⟨p i j,rfl⟩

theorem scalarCoordinates_dense (n : ℕ) :
    Dense {c : Fin n → ℝ | ∀ i, RatScalar (c i)} := by
  have h : DenseRange (fun c : Fin n → ℚ => fun i => (c i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  apply h.mono
  rintro _ ⟨c,rfl⟩ i
  exact ⟨c i,rfl⟩

theorem continuous_minor {n r : ℕ} (b : Fin r → Fin n) :
    Continuous (fun p : Fin n → Fin r → ℝ => minor p b) := by
  unfold minor
  have h : Continuous (fun p : Fin n → Fin r → ℝ =>
      Matrix.of (fun i j : Fin r => p (b i) j)) :=
    continuous_matrix fun i j =>
      (continuous_apply j).comp (continuous_apply (b i))
  exact h.matrix_det

theorem eventually_nonzero_minor_signs {n r : ℕ} (p : Fin n → Fin r → ℝ) :
    ∀ᶠ q in 𝓝 p, ∀ b, minor p b ≠ 0 →
      SignType.sign (minor q b) = SignType.sign (minor p b) := by
  apply eventually_all.mpr
  intro b
  by_cases hb : minor p b = 0
  · exact Eventually.of_forall fun _ h => (h hb).elim
  · exact (eventually_sign_eq_of_nonzero (continuous_minor b).continuousAt hb).mono
      fun _ h _ => h

/-- Open inequalities supply exactly the nonzero chirotope signs after the
algebraic construction has preserved every zero minor. -/
theorem density_of_zero_minor_density {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (h : p ∈ closure {q | RationalCoordinates q ∧ PreservesZeroMinors p q}) :
    p ∈ closure (RationalRealizations p) := by
  have hcl := mem_closure_inter_of_eventually h (eventually_nonzero_minor_signs p)
  apply closure_mono (s := {q | RationalCoordinates q ∧ PreservesZeroMinors p q} ∩
    {q | ∀ b, minor p b ≠ 0 →
      SignType.sign (minor q b) = SignType.sign (minor p b)}) ?_ hcl
  intro q hq
  refine ⟨hq.1.1,?_⟩
  intro b
  by_cases hb : minor p b = 0
  · rw [hq.1.2 b hb,hb]
  · exact hq.2 b hb

/-- The complete rank-three result with the literal at-most-eight bound. -/
theorem rank_three_density {n : ℕ} (hn : n ≤ 8) (p : Fin n → Fin 3 → ℝ) :
    p ∈ closure (RationalRealizations p) := by
  classical
  let e : Fin n → Fin 8 := Fin.castLE hn
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin 8 => k.val) hij
  let padded : Fin 8 → V := Function.extend e p (fun _ => 0)
  have hpad : ∀ i, padded (e i) = p i :=
    fun i => he.extend_apply p (fun _ => 0) i
  let restrict : (Fin 8 → V) → (Fin n → Fin 3 → ℝ) :=
    fun q i => q (e i)
  have hr : Continuous restrict := continuous_pi fun i => continuous_apply (e i)
  have hrp : restrict padded = p := funext hpad
  have hcl : p ∈ closure
      (restrict '' {q | RatConfiguration q ∧ SameTripleSigns padded q}) := by
    simpa only [hrp] using
      mem_closure_image hr.continuousAt (rational_triple_signs_dense padded)
  apply closure_mono (s := restrict '' _) ?_ hcl
  rintro _ ⟨q,hq,rfl⟩
  refine ⟨fun i j => hq.1 (e i) j,?_⟩
  intro b
  have h := hq.2 (e (b 0)) (e (b 1)) (e (b 2))
  simpa [minor,restrict,Matrix.det_fin_three,hpad] using h

end ChirotopeDensity

end Papers.RationalityTen
