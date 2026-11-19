module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option autoImplicit false

/-!
# Rational quadratic separation from certified finite rational nets

This file verifies the abstract separation step used in Section 8 of
`Volume polynomials and the Heine–Shephard problem`.

It does **not** assume or assert that a particular set is a volume-polynomial
locus. Its interface records every geometric input needed to apply the result:
a closed target, finite rational approximations to that target, and certified
vanishing errors in both directions. The centers need not lie exactly in the
target. Proving these inputs for convex bodies is a separate obligation.
-/

open scoped BigOperators Topology
open Filter Metric

namespace VolumePolynomials.QuadraticSeparation

variable {ι : Type*} [Fintype ι]

abbrev Space (ι : Type*) := PiLp 2 (fun _ : ι => ℝ)

/-- A vector with rational coordinates, regarded as a Euclidean vector. -/
def ofRat (a : ι → ℚ) : Space ι := WithLp.toLp 2 (fun i => (a i : ℝ))

theorem real_norm_sq_eq (x : Space ι) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  first
  | simpa only [Real.norm_eq_abs, sq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ) x)

@[simp] theorem ofRat_apply (a : ι → ℚ) (i : ι) : ofRat a i = (a i : ℝ) := rfl

theorem denseRange_ofRat : DenseRange (ofRat (ι := ι)) := by
  first
  | have h : DenseRange (fun a : ι → ℚ => fun i => (a i : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    exact (PiLp.homeomorph 2 (fun _ : ι => ℝ)).symm.surjective.denseRange.comp h
      (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))

/-- Squared distances between rational vectors can be tested using only rationals. -/
theorem dist_ofRat_sq (a b : ι → ℚ) :
    dist (ofRat a) (ofRat b) ^ 2 = ((∑ i, (a i - b i) ^ 2 : ℚ) : ℝ) := by
  first
  | rw [dist_eq_norm, real_norm_sq_eq]
    simp [ofRat, Rat.cast_sum]

/-- The precise interface supplied by the finite-net construction in Section 8.1. -/
structure Model (ι : Type*) [Fintype ι] where
  target : Set (Space ι)
  closed : IsClosed target
  net : ℕ → Finset (ι → ℚ)
  error : ℕ → ℚ
  error_nonneg : ∀ m, 0 ≤ error m
  error_tendsto : Tendsto (fun m => (error m : ℝ)) atTop (𝓝 0)
  net_near : ∀ m q, q ∈ net m →
    ∃ y ∈ target, dist (ofRat q) y ≤ (error m : ℝ)
  covers : ∀ m x, x ∈ target → ∃ q ∈ net m, dist x (ofRat q) ≤ (error m : ℝ)

namespace Model

variable (M : Model ι)

/-- The finite rational admission test (8.4), with the net's certified radius. -/
def Admitted (a : ι → ℚ) (r : ℚ) (m : ℕ) : Prop :=
  0 < r ∧ ∀ q ∈ M.net m, (r + M.error m) ^ 2 < ∑ i, (a i - q i) ^ 2

instance admittedDecidable (a : ι → ℚ) (r : ℚ) (m : ℕ) :
    Decidable (M.Admitted a r m) := by
  first
  | unfold Admitted
    infer_instance

/-- An admitted rational ball is disjoint from the target, with strict separation. -/
theorem admitted_separates {a : ι → ℚ} {r : ℚ} {m : ℕ}
    (ha : M.Admitted a r m) {x : Space ι} (hx : x ∈ M.target) :
    (r : ℝ) < dist x (ofRat a) := by
  first
  | obtain ⟨q, hq, hdist⟩ := M.covers m x hx
    have hr : 0 < (r : ℝ) := by exact_mod_cast ha.1
    have he : 0 ≤ (M.error m : ℝ) := by exact_mod_cast M.error_nonneg m
    have hsq : ((r : ℝ) + (M.error m : ℝ)) ^ 2 < dist (ofRat a) (ofRat q) ^ 2 := by
      first
      | rw [dist_ofRat_sq]
        exact_mod_cast ha.2 q hq
    have hlt : (r : ℝ) + (M.error m : ℝ) < dist (ofRat a) (ofRat q) :=
      (sq_lt_sq₀ (by positivity) dist_nonneg).mp hsq
    have htri := dist_triangle (ofRat a) x (ofRat q)
    rw [dist_comm (ofRat a) x] at htri
    linarith

/-- Every point outside the closed target belongs to an admitted rational ball. -/
theorem exists_admitted_of_not_mem {x : Space ι} (hx : x ∉ M.target) :
    ∃ a : ι → ℚ, ∃ r : ℚ, ∃ m : ℕ,
      M.Admitted a r m ∧ dist x (ofRat a) < (r : ℝ) := by
  first
  | obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp M.closed.isOpen_compl x hx
    obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp denseRange_ofRat x (δ / 8) (by positivity)
    obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show δ / 4 < δ / 2 by linarith)
    have hevent : ∀ᶠ m in atTop, (M.error m : ℝ) < δ / 8 :=
      M.error_tendsto.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm⟩ := hevent.exists
    have hr : 0 < (r : ℝ) := by linarith
    refine ⟨a, r, m, ⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hr
    · intro q hq
      obtain ⟨y, hy, hqy⟩ := M.net_near m q hq
      have hδy : δ ≤ dist x y := by
        first
        | by_contra! h
          exact hball (by simpa [Metric.mem_ball, dist_comm] using h) hy
      have hxy := dist_triangle x (ofRat q) y
      have htri := dist_triangle x (ofRat a) (ofRat q)
      have hlt : (r : ℝ) + (M.error m : ℝ) < dist (ofRat a) (ofRat q) := by
        first
        | linarith
      have he : 0 ≤ (M.error m : ℝ) := by exact_mod_cast M.error_nonneg m
      have hsq := (sq_lt_sq₀ (by positivity : 0 ≤ (r : ℝ) + (M.error m : ℝ))
        dist_nonneg).mpr hlt
      rw [dist_ofRat_sq] at hsq
      exact_mod_cast hsq
    · linarith

/-- The exact rational-ball characterization before homogenizing (8.5). -/
theorem mem_iff_admitted_balls (x : Space ι) :
    x ∈ M.target ↔
      ∀ (a : ι → ℚ) (r : ℚ) (m : ℕ), M.Admitted a r m →
        (r : ℝ) ^ 2 ≤ dist x (ofRat a) ^ 2 := by
  first
  | constructor
    · intro hx a r m ha
      have hr : 0 ≤ (r : ℝ) := by exact_mod_cast ha.1.le
      exact (sq_le_sq₀ hr dist_nonneg).mpr (M.admitted_separates ha hx).le
    · intro h
      by_contra hx
      obtain ⟨a, r, m, hadm, hdist⟩ := M.exists_admitted_of_not_mem hx
      have hr : 0 ≤ (r : ℝ) := by exact_mod_cast hadm.1.le
      have hlt := (sq_lt_sq₀ dist_nonneg hr).mpr hdist
      exact (not_lt_of_ge (h a r m hadm)) hlt

/-- The finite tests at every scale characterize membership in the closed target. -/
theorem mem_iff_all_finite_tests (x : Space ι) :
    x ∈ M.target ↔ ∀ m, ∃ q ∈ M.net m, dist x (ofRat q) ≤ (M.error m : ℝ) := by
  first
  | refine ⟨fun hx m => M.covers m x hx, ?_⟩
    intro h
    by_contra hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp M.closed.isOpen_compl x hx
    obtain ⟨m, hm⟩ :=
      (M.error_tendsto.eventually (gt_mem_nhds (by positivity : 0 < δ / 2))).exists
    obtain ⟨q, hq, hdist⟩ := h m
    obtain ⟨y, hy, hqy⟩ := M.net_near m q hq
    have hxy : dist x y < δ := by
      first
      | have htri := dist_triangle x (ofRat q) y
        linarith
    exact hball (by simpa [Metric.mem_ball, dist_comm] using hxy) hy

end Model

/-- The paper's exact rational nets are a special case of the certified
approximate-net interface. This constructor makes the equivalence explicit. -/
def Model.ofExact (target : Set (Space ι)) (closed : IsClosed target)
    (net : ℕ → Finset (ι → ℚ)) (error : ℕ → ℚ)
    (error_nonneg : ∀ m, 0 ≤ error m)
    (error_tendsto : Tendsto (fun m => (error m : ℝ)) atTop (𝓝 0))
    (net_mem : ∀ m q, q ∈ net m → ofRat q ∈ target)
    (covers : ∀ m x, x ∈ target → ∃ q ∈ net m, dist x (ofRat q) ≤ (error m : ℝ)) :
    Model ι where
  target := target
  closed := closed
  net := net
  error := error
  error_nonneg := error_nonneg
  error_tendsto := error_tendsto
  net_near := by
    first
    | intro m q hq
      refine ⟨ofRat q, net_mem m q hq, ?_⟩
      have hm : 0 ≤ (error m : ℝ) := by exact_mod_cast error_nonneg m
      simpa only [dist_self] using hm
  covers := covers

/-- Sum of the ordinary coefficients. -/
def total (c : Space ι) : ℝ := ∑ i, c i

/-- Division by the coefficient sum, used only with a proved nonzero sum. -/
noncomputable def normalize (c : Space ι) : Space ι := (total c)⁻¹ • c

/-- The real quadratic form in (8.5), written intrinsically in Euclidean space. -/
noncomputable def quadratic (a : ι → ℚ) (r : ℚ) (c : Space ι) : ℝ :=
  ‖c - total c • ofRat a‖ ^ 2 - (r : ℝ) ^ 2 * total c ^ 2

theorem quadratic_eq_sum (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    quadratic a r c = ∑ i, (c i - total c * (a i : ℝ)) ^ 2 -
      (r : ℝ) ^ 2 * total c ^ 2 := by
  first
  | rw [quadratic, real_norm_sq_eq]
    rfl

@[simp] theorem total_zero : total (0 : Space ι) = 0 := by simp [total]

@[simp] theorem total_smul (t : ℝ) (c : Space ι) : total (t • c) = t * total c := by
  first
  | simp [total, Finset.mul_sum]

@[simp] theorem quadratic_zero (a : ι → ℚ) (r : ℚ) :
    quadratic a r (0 : Space ι) = 0 := by simp [quadratic]

/-- Exact homogeneity: each admitted inequality is a homogeneous quadratic. -/
theorem quadratic_smul (a : ι → ℚ) (r : ℚ) (t : ℝ) (c : Space ι) :
    quadratic a r (t • c) = t ^ 2 * quadratic a r c := by
  first
  | simp only [quadratic, total_smul, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring

theorem quadratic_eq_normalized (a : ι → ℚ) (r : ℚ) (c : Space ι)
    (hc : total c ≠ 0) :
    quadratic a r c = total c ^ 2 *
      (dist (normalize c) (ofRat a) ^ 2 - (r : ℝ) ^ 2) := by
  first
  | have heq : c - total c • ofRat a = total c • (normalize c - ofRat a) := by
      first
      | simp [normalize, smul_sub, smul_smul, hc]
    rw [quadratic, heq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, dist_eq_norm]
    ring

/-- Rational polynomial representing exactly the real quadratic form. -/
noncomputable def rationalForm (a : ι → ℚ) (r : ℚ) : MvPolynomial ι ℚ :=
  ∑ i, (MvPolynomial.X i - (∑ j, MvPolynomial.X j) * MvPolynomial.C (a i)) ^ 2 -
    MvPolynomial.C (r ^ 2) * (∑ j, MvPolynomial.X j) ^ 2

theorem eval_rationalForm (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (rationalForm a r) =
      quadratic a r c := by
  first
  | rw [quadratic_eq_sum]
    simp [rationalForm, total, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_pow, MvPolynomial.eval₂_mul]

/-- The polynomial form, not merely its evaluation, is homogeneous of degree two. -/
theorem rationalForm_isHomogeneous (a : ι → ℚ) (r : ℚ) :
    (rationalForm a r).IsHomogeneous 2 := by
  first
  | have hsum : (∑ i : ι, (MvPolynomial.X i : MvPolynomial ι ℚ)).IsHomogeneous 1 :=
      MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_X _ i)
    unfold rationalForm
    apply MvPolynomial.IsHomogeneous.sub
    · apply MvPolynomial.IsHomogeneous.sum
      intro i _
      have hlin : (MvPolynomial.X i - (∑ j, MvPolynomial.X j) *
          MvPolynomial.C (a i) : MvPolynomial ι ℚ).IsHomogeneous 1 := by
        first
        | apply (MvPolynomial.isHomogeneous_X _ i).sub
          simpa [mul_comm] using hsum.C_mul (a i)
      simpa using hlin.pow 2
    · exact (hsum.pow 2).C_mul (r ^ 2)

/-- A computable index type for the rational centers, radii, and net scales. -/
abbrev CertificateIndex (ι : Type*) := (ι → ℚ) × ℚ × ℕ

/-- Computable enumeration of the admitted descriptors, relative to the rational net data. -/
def enumeratedCertificate [Encodable ι] (M : Model ι) (k : ℕ) : Option (CertificateIndex ι) :=
  match Encodable.decode (α := CertificateIndex ι) k with
  | none => none
  | some (a, r, m) => if M.Admitted a r m then some (a, r, m) else none

/-- Every admitted descriptor is returned at its explicit natural-number code. -/
theorem enumeratedCertificate_encode [Encodable ι] (M : Model ι)
    (a : ι → ℚ) (r : ℚ) (m : ℕ) (h : M.Admitted a r m) :
    enumeratedCertificate M (Encodable.encode (a, r, m)) = some (a, r, m) := by
  first
  | simp [enumeratedCertificate, h]

/-- An explicitly computable rational matrix of coefficients for (8.5). -/
def rationalMatrix [DecidableEq ι] (a : ι → ℚ) (r : ℚ) (i j : ι) : ℚ :=
  (if i = j then 1 else 0) - a i - a j + (∑ k, a k ^ 2) - r ^ 2

theorem quadratic_expansion (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    quadratic a r c = (∑ i, c i ^ 2) -
      2 * total c * (∑ i, (a i : ℝ) * c i) +
      total c ^ 2 * ((∑ i, (a i : ℝ) ^ 2) - (r : ℝ) ^ 2) := by
  first
  | rw [quadratic_eq_sum]
    have h : (∑ i, (c i - total c * (a i : ℝ)) ^ 2) =
        (∑ i, c i ^ 2) - 2 * total c * (∑ i, (a i : ℝ) * c i) +
          total c ^ 2 * (∑ i, (a i : ℝ) ^ 2) := by
      first
      | calc
          _ = ∑ i, (c i ^ 2 - 2 * total c * ((a i : ℝ) * c i) +
              total c ^ 2 * (a i : ℝ) ^ 2) := by
            first
            | apply Finset.sum_congr rfl
              intro i _
              ring
          _ = _ := by
            first
            | simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [h]
    ring

/-- The computable rational matrix evaluates to exactly (8.5), with every coefficient checked. -/
theorem quadratic_eq_matrix [DecidableEq ι] (a : ι → ℚ) (r : ℚ) (c : Space ι) :
    quadratic a r c = ∑ i, ∑ j, (rationalMatrix a r i j : ℝ) * c i * c j := by
  first
  | rw [quadratic_expansion]
    have hdiag : (∑ i, ∑ j, ((if i = j then 1 else 0 : ℝ) * c i * c j)) =
        ∑ i, c i ^ 2 := by
      first
      | simp [sq, ite_mul]
    have hleft : (∑ i, ∑ j, (a i : ℝ) * c i * c j) =
        (∑ i, (a i : ℝ) * c i) * total c := by
      first
      | calc
          _ = ∑ i, ((a i : ℝ) * c i) * total c := by
            first
            | apply Finset.sum_congr rfl
              intro i _
              rw [total, Finset.mul_sum]
          _ = _ := (Finset.sum_mul _ _ _).symm
    have hright : (∑ i, ∑ j, (a j : ℝ) * c i * c j) =
        total c * (∑ i, (a i : ℝ) * c i) := by
      first
      | calc
          _ = ∑ i, c i * (∑ j, (a j : ℝ) * c j) := by
            first
            | apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
          _ = _ := (Finset.sum_mul _ _ _).symm
    have hconst (t : ℝ) : (∑ i, ∑ j, t * c i * c j) = t * total c ^ 2 := by
      first
      | simp only [total, sq, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    have hexpand : (∑ i, ∑ j, (rationalMatrix a r i j : ℝ) * c i * c j) =
        (∑ i, ∑ j, ((if i = j then 1 else 0 : ℝ) * c i * c j)) -
        (∑ i, ∑ j, (a i : ℝ) * c i * c j) -
        (∑ i, ∑ j, (a j : ℝ) * c i * c j) +
        (∑ i, ∑ j, ((∑ k, (a k : ℝ) ^ 2) - (r : ℝ) ^ 2) * c i * c j) := by
      first
      | simp only [rationalMatrix, Rat.cast_sub, Rat.cast_add, Rat.cast_sum, Rat.cast_pow,
          apply_ite, Rat.cast_one, Rat.cast_zero]
        simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        ring
    rw [hexpand, hdiag, hleft, hright, hconst]
    ring

/--
An explicit countable sequence of rational forms. Nonadmitted indices and unused
natural-number codes produce the zero form. Its rational descriptors are computed
by `enumeratedCertificate`; the `MvPolynomial` representation uses Mathlib's
noncomputable polynomial implementation.
-/
noncomputable def enumeratedForm [Encodable ι] (M : Model ι) (k : ℕ) : MvPolynomial ι ℚ :=
  match Encodable.decode (α := CertificateIndex ι) k with
  | none => 0
  | some (a, r, m) => if M.Admitted a r m then rationalForm a r else 0

theorem enumeratedForm_isHomogeneous [Encodable ι] (M : Model ι) (k : ℕ) :
    (enumeratedForm M k).IsHomogeneous 2 := by
  first
  | unfold enumeratedForm
    split
    · exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℚ) 2
    · split
      · exact rationalForm_isHomogeneous _ _
      · exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℚ) 2

/-- Enumerating all natural-number codes loses no admitted inequality. -/
theorem forall_enumerated_iff [Encodable ι] (M : Model ι) (c : Space ι) :
    (∀ k, 0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k)) ↔
      ∀ (a : ι → ℚ) (r : ℚ) (m : ℕ), M.Admitted a r m → 0 ≤ quadratic a r c := by
  first
  | constructor
    · intro h a r m ha
      have hk := h (Encodable.encode (a, r, m))
      simpa [enumeratedForm, Encodable.encodek, ha, eval_rationalForm] using hk
    · intro h k
      unfold enumeratedForm
      split
      · simp
      · split
        · rw [eval_rationalForm]
          exact h _ _ _ ‹_›
        · simp

/-- A nonzero nonnegative coefficient vector has a strictly positive total. -/
theorem total_pos {c : Space ι} (hn : ∀ i, 0 ≤ c i) (hc : c ≠ 0) : 0 < total c := by
  first
  | have hnonneg : 0 ≤ total c := Finset.sum_nonneg (fun i _ => hn i)
    refine lt_of_le_of_ne hnonneg ?_
    intro heq
    apply hc
    ext i
    have hzero : ∀ i, c i = 0 := by
      first
      | simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp heq.symm
    exact hzero i

/--
The full abstract homogenized characterization.

The four hypotheses explicitly connect the target set to the intended coefficient
locus; none is silently treated as an axiom about convex geometry.
-/
theorem coefficient_characterization (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) :
    c ∈ V ↔ (∀ i, 0 ≤ c i) ∧
      ∀ (a : ι → ℚ) (r : ℚ) (m : ℕ), M.Admitted a r m → 0 ≤ quadratic a r c := by
  first
  | constructor
    · intro hc
      refine ⟨hnonneg c hc, ?_⟩
      intro a r m ha
      by_cases hz : c = 0
      · simp [hz]
      have hs := total_pos (hnonneg c hc) hz
      rw [quadratic_eq_normalized _ _ _ hs.ne']
      apply mul_nonneg (sq_nonneg _)
      exact sub_nonneg.mpr ((M.mem_iff_admitted_balls _).mp (hnormalize c hc hz) a r m ha)
    · rintro ⟨hn, hq⟩
      by_cases hz : c = 0
      · simpa [hz] using hzero
      have hs := total_pos hn hz
      apply hrealize c hs
      apply (M.mem_iff_admitted_balls _).mpr
      intro a r m ha
      have hquad := hq a r m ha
      rw [quadratic_eq_normalized _ _ _ hs.ne'] at hquad
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (sq_pos_of_pos hs)).mp hquad)

/-- Countably indexed rational homogeneous quadratic forms give the same exact criterion. -/
theorem countable_coefficient_characterization [Encodable ι]
    (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) :
    c ∈ V ↔ (∀ i, 0 ≤ c i) ∧
      ∀ k, 0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k) := by
  first
  | rw [forall_enumerated_iff]
    exact coefficient_characterization M V hzero hnonneg hnormalize hrealize c

/-- Every vector outside the intended locus has one strictly violated finite certificate. -/
theorem exists_strict_certificate [Encodable ι]
    (M : Model ι) (V : Set (Space ι))
    (hzero : (0 : Space ι) ∈ V)
    (hnonneg : ∀ c ∈ V, ∀ i, 0 ≤ c i)
    (hnormalize : ∀ c ∈ V, c ≠ 0 → normalize c ∈ M.target)
    (hrealize : ∀ c, 0 < total c → normalize c ∈ M.target → c ∈ V)
    (c : Space ι) (hc : c ∉ V) :
    (∃ i, c i < 0) ∨ ∃ k,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun i => c i) (enumeratedForm M k) < 0 := by
  first
  | have h := (countable_coefficient_characterization M V hzero hnonneg hnormalize hrealize c).not.mp hc
    push_neg at h
    by_cases hn : ∀ i, 0 ≤ c i
    · exact Or.inr (h hn)
    · exact Or.inl (by simpa only [not_forall, not_le] using hn)

end VolumePolynomials.QuadraticSeparation
