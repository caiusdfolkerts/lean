module
public import Papers.MatrixGaugeNormalization
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Rat

set_option Elab.async false

section BundlePart0
/- Source: Papers/MatrixBasisNormalization.lean -/



@[expose] public section
noncomputable section
open Matrix Set Filter Topology
open scoped BigOperators

namespace Papers.MatrixGaugeNormalization

variable {ι : Type*} [DecidableEq ι]

/-- The purely combinatorial part of a rooted-forest normalisation certificate. -/
def checkSchedule (S : Finset ι) : List (ι × ι) → Bool
  | [] => true
  | (u,v)::t => decide (u∈S ∧ v∉S) && checkSchedule (insert v S) t

theorem validSteps_of_check (w : ι→ι→ℝ) {S : Finset ι} {t : List (ι×ι)}
    (hc : checkSchedule S t=true) (hw : ∀e∈t,w e.1 e.2≠0) :
    ValidSteps w S t := by
  induction t generalizing S with
  | nil => exact ValidSteps.nil S
  | cons e t ih =>
    obtain ⟨u,v⟩ := e
    simp only [checkSchedule,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact ValidSteps.cons hc.1.1 hc.1.2 (hw (u,v) (by simp))
      (ih hc.2 (fun e he => hw e (by simp [he])))

def basisMatrix {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (b : Fin r → Fin n) : Matrix (Fin r) (Fin r) ℝ := p.submatrix b id

def normalizeBasis {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (b : Fin r → Fin n) : Matrix (Fin n) (Fin r) ℝ :=
  p * (basisMatrix p b)⁻¹

theorem submatrix_mul_right {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → Fin n) :
    (p*A).submatrix b id = p.submatrix b id * A := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.mul_apply,id_eq]

theorem normalizeBasis_basis {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (b : Fin r → Fin n) (hb : (basisMatrix p b).det≠0) :
    (normalizeBasis p b).submatrix b id = 1 := by
  rw [normalizeBasis,submatrix_mul_right]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hb)

theorem normalizeBasis_reconstruct {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (b : Fin r → Fin n) (hb : (basisMatrix p b).det≠0) :
    normalizeBasis p b * basisMatrix p b = p := by
  exact Matrix.nonsing_inv_mul_cancel_right _ _ (isUnit_iff_ne_zero.mpr hb)

theorem scale_normalizeBasis_basis {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (b : Fin r → Fin n) (hb : (basisMatrix p b).det≠0)
    (a : Fin n → ℝ) (c : Fin r → ℝ) (hscale : ∀i,a (b i)*c i=1) :
    (scaleRowsColumns (normalizeBasis p b) a c).submatrix b id=1 := by
  ext i j
  have h := congrFun (congrFun (normalizeBasis_basis p b hb) i) j
  change normalizeBasis p b (b i) j=(1 : Matrix (Fin r) (Fin r) ℝ) i j at h
  change a (b i)*normalizeBasis p b (b i) j*c j=(1 : Matrix (Fin r) (Fin r) ℝ) i j
  rw [h]
  by_cases hij : i=j
  · subst j
    simpa only [Matrix.one_apply_eq,mul_one] using hscale i
  · simp [Matrix.one_apply,hij]

theorem right_mul_minor {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (b : Fin r → Fin n) :
    ((p*A).submatrix b id).det = (p.submatrix b id).det*A.det := by
  rw [submatrix_mul_right,Matrix.det_mul]

theorem normalizeBasis_zero_minor_iff {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (b : Fin r → Fin n)
    (hb : (basisMatrix p b).det≠0) (s : Fin r → Fin n) :
    ((normalizeBasis p b).submatrix s id).det=0 ↔ (p.submatrix s id).det=0 := by
  rw [normalizeBasis,right_mul_minor,Matrix.det_nonsing_inv]
  simp [hb]

theorem det_updateRow_one {r : ℕ} (i : Fin r) (x : Fin r → ℝ) :
    ((1 : Matrix (Fin r) (Fin r) ℝ).updateRow i x).det=x i := by
  have hs : (∑k,x k • (1 : Matrix (Fin r) (Fin r) ℝ) k)=x := by
    ext j
    simp [Matrix.one_apply,Pi.smul_apply,Finset.sum_apply]
  simpa only [hs,Matrix.det_one,smul_eq_mul,mul_one] using
    Matrix.det_updateRow_sum (1 : Matrix (Fin r) (Fin r) ℝ) i x

/-- Each nonbasis coordinate is precisely the minor obtained by replacing
the corresponding basis row. Thus the forest's nonzero weights are justified
by the represented matroid, rather than extra genericity hypotheses. -/
theorem coordinate_eq_exchange_minor {n r : ℕ}
    (q : Matrix (Fin n) (Fin r) ℝ) (b : Fin r → Fin n)
    (hb : q.submatrix b id=1) (v : Fin n) (i : Fin r) :
    (q.submatrix (Function.update b i v) id).det=q v i := by
  have hM : q.submatrix (Function.update b i v) id=
      (q.submatrix b id).updateRow i (q v) := by
    ext j k
    by_cases hji : j=i <;>
      simp [Matrix.submatrix,Matrix.updateRow_apply,Function.update_apply,hji]
  rw [hM,hb,det_updateRow_one]

theorem mul_rational {n r s : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (A : Matrix (Fin r) (Fin s) ℝ)
    (hp : Papers.RationalKernelCharts.RationalCoordinates p)
    (hA : Papers.RationalKernelCharts.RationalCoordinates A) :
    Papers.RationalKernelCharts.RationalCoordinates (p*A) := by
  exact Papers.RationalKernelCharts.rationalCoordinates_mul hp hA

/-- Reconstruction permits arbitrary nearby basis matrices; all zero minors
remain exact, even before imposing an open invertibility condition. -/
theorem right_mul_preserves_zero_minors {n r : ℕ}
    (p q : Matrix (Fin n) (Fin r) ℝ) (A B : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.det≠0)
    (hz : ∀s : Fin r → Fin n,(p.submatrix s id).det=0 → (q.submatrix s id).det=0) :
    ∀s : Fin r → Fin n,((p*A).submatrix s id).det=0 →
      ((q*B).submatrix s id).det=0 := by
  intro s hs
  rw [right_mul_minor] at hs ⊢
  have hp : (p.submatrix s id).det=0 := (mul_eq_zero.mp hs).resolve_right hA
  rw [hz s hp,zero_mul]

end Papers.MatrixGaugeNormalization

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/MatrixNormalizationDensity.lean -/





@[expose] public section
noncomputable section
open Matrix Set Filter Topology
open scoped BigOperators

namespace Papers.MatrixGaugeNormalization

open Papers.RationalKernelCharts

def ZeroRationalRealizations {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ) :
    Set (Matrix (Fin n) (Fin r) ℝ) :=
  {q | RationalCoordinates q ∧ ∀s : Fin r → Fin n,
    (p.submatrix s id).det=0 → (q.submatrix s id).det=0}

theorem rational_matrices_dense (n r : ℕ) :
    Dense {p : Matrix (Fin n) (Fin r) ℝ | RationalCoordinates p} := by
  have h : DenseRange (fun p : Fin n → Fin r → ℚ =>
      Matrix.of (fun i j => (p i j : ℝ))) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => Rat.denseRange_cast))
  apply h.mono
  rintro _ ⟨p,rfl⟩ i j
  exact ⟨p i j,rfl⟩

theorem rational_scalars_dense (n : ℕ) :
    Dense {a : Fin n → ℝ | ∀i,RatScalar (a i)} := by
  have h : DenseRange (fun a : Fin n → ℚ => fun i => (a i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  apply h.mono
  rintro _ ⟨a,rfl⟩ i
  exact ⟨a i,rfl⟩

theorem right_mul_zero_density {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.det≠0)
    (hp : p∈closure (ZeroRationalRealizations p)) :
    p*A∈closure (ZeroRationalRealizations (p*A)) := by
  have hprod : (p,A)∈closure (ZeroRationalRealizations p ×ˢ
      {B : Matrix (Fin r) (Fin r) ℝ | RationalCoordinates B}) := by
    rw [closure_prod_eq]
    exact ⟨hp,rational_matrices_dense r r A⟩
  let f : Matrix (Fin n) (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ →
      Matrix (Fin n) (Fin r) ℝ := fun z => z.1*z.2
  have hf : Continuous f := continuous_fst.matrix_mul continuous_snd
  have hcl := mem_closure_image hf.continuousAt hprod
  apply closure_mono (s := f '' _) ?_ hcl
  rintro _ ⟨⟨q,B⟩,⟨hq,hB⟩,rfl⟩
  exact ⟨rationalCoordinates_mul hq.1 hB,
    right_mul_preserves_zero_minors p q A B hA hq.2⟩

theorem scale_zero_density {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (a : Fin n → ℝ) (b : Fin r → ℝ) (ha : ∀i,a i≠0) (hb : ∀j,b j≠0)
    (hp : p∈closure (ZeroRationalRealizations p)) :
    scaleRowsColumns p a b∈closure (ZeroRationalRealizations (scaleRowsColumns p a b)) := by
  have hprod : (p,a,b)∈closure (ZeroRationalRealizations p ×ˢ
      ({a : Fin n → ℝ | ∀i,RatScalar (a i)} ×ˢ
       {b : Fin r → ℝ | ∀j,RatScalar (b j)})) := by
    rw [closure_prod_eq,closure_prod_eq]
    exact ⟨hp,rational_scalars_dense n a,rational_scalars_dense r b⟩
  let f : Matrix (Fin n) (Fin r) ℝ × (Fin n → ℝ) × (Fin r → ℝ) →
      Matrix (Fin n) (Fin r) ℝ := fun z => scaleRowsColumns z.1 z.2.1 z.2.2
  have hcl := mem_closure_image (continuous_scaleRowsColumns n r).continuousAt hprod
  apply closure_mono (s := f '' _) ?_ hcl
  rintro _ ⟨⟨q,c,d⟩,⟨hq,hc,hd⟩,rfl⟩
  refine ⟨scaleRowsColumns_rational q c d hq.1 hc hd,?_⟩
  intro s hs
  have hz := (scaleRowsColumns_zero_minor_iff p a b ha hb s).mp hs
  rw [scaleRowsColumns_minor,hq.2 s hz,mul_zero,zero_mul]

theorem restrict_rows_zero_density {n m r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (e : Fin m → Fin n) (hp : p∈closure (ZeroRationalRealizations p)) :
    p.submatrix e id∈closure (ZeroRationalRealizations (p.submatrix e id)) := by
  let f : Matrix (Fin n) (Fin r) ℝ → Matrix (Fin m) (Fin r) ℝ :=
    fun q => q.submatrix e id
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply j).comp (continuous_apply (e i))
  have hcl := mem_closure_image hf.continuousAt hp
  apply closure_mono (s := f '' _) ?_ hcl
  rintro _ ⟨q,hq,rfl⟩
  refine ⟨fun i j => hq.1 (e i) j,?_⟩
  intro s hs
  exact hq.2 (e∘s) hs

theorem density_of_permuted_rows {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (e : Equiv.Perm (Fin n))
    (hp : p.submatrix e id∈closure (ZeroRationalRealizations (p.submatrix e id))) :
    p∈closure (ZeroRationalRealizations p) := by
  have h := restrict_rows_zero_density (p.submatrix e id) e.symm hp
  have heq : (p.submatrix e id).submatrix e.symm id=p := by
    ext i j
    simp [Matrix.submatrix]
  simpa only [heq] using h

/-- A rationally dense normalised chart gives rational density at the original
matrix. The original real basis and all original real gauges are approximated
as part of the construction, rather than silently assumed rational. -/
theorem density_of_normalized_chart {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (b : Fin r → Fin n)
    (hb : (basisMatrix p b).det≠0)
    (a : Fin n → ℝ) (c : Fin r → ℝ) (ha : ∀i,a i≠0) (hc : ∀j,c j≠0)
    (hchart : scaleRowsColumns (normalizeBasis p b) a c∈closure
      (ZeroRationalRealizations (scaleRowsColumns (normalizeBasis p b) a c))) :
    p∈closure (ZeroRationalRealizations p) := by
  have hundo := scale_zero_density (scaleRowsColumns (normalizeBasis p b) a c)
    (fun i => (a i)⁻¹) (fun j => (c j)⁻¹)
    (fun i => inv_ne_zero (ha i)) (fun j => inv_ne_zero (hc j)) hchart
  rw [scaleRowsColumns_inverse _ a c ha hc] at hundo
  have hfinal := right_mul_zero_density (normalizeBasis p b) (basisMatrix p b) hb hundo
  simpa only [normalizeBasis_reconstruct p b hb] using hfinal

end Papers.MatrixGaugeNormalization

end
end
end BundlePart1
