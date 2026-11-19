module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

open Set Filter Topology

namespace Papers.RationalityTen.ResidualCurves

def RationalPoint (p : ℝ × ℝ) : Prop :=
  (∃ a : ℚ, (a : ℝ)=p.1) ∧ (∃ b : ℚ, (b : ℝ)=p.2)

def conicPolynomial (p : ℝ × ℝ) : ℝ :=
  p.1^2+p.1*p.2+p.2^2-p.1-p.2

def conicDenominator (u : ℝ) : ℝ := 1+u+u^2

def conicParam (u : ℝ) : ℝ × ℝ :=
  ((1+u)/conicDenominator u,u*(1+u)/conicDenominator u)

theorem conicDenominator_pos (u : ℝ) : 0<conicDenominator u := by
  dsimp [conicDenominator]
  nlinarith [sq_nonneg (2*u+1)]

theorem conicParam_equation (u : ℝ) :
    conicPolynomial (conicParam u)=0 := by
  have hd := ne_of_gt (conicDenominator_pos u)
  dsimp [conicPolynomial,conicParam]
  field_simp [hd]
  dsimp [conicDenominator]
  ring

theorem conicParam_rational (u : ℚ) : RationalPoint (conicParam u) := by
  refine ⟨⟨(1+u)/(1+u+u^2),?_⟩,⟨u*(1+u)/(1+u+u^2),?_⟩⟩ <;>
    simp [conicParam,conicDenominator]

theorem continuous_conicParam : Continuous conicParam := by
  have hd : Continuous conicDenominator := by
    unfold conicDenominator
    fun_prop
  have hn₁ : Continuous (fun u : ℝ => 1+u) := by fun_prop
  have hn₂ : Continuous (fun u : ℝ => u*(1+u)) := by fun_prop
  exact (hn₁.div hd (fun u => ne_of_gt (conicDenominator_pos u))).prodMk
    (hn₂.div hd (fun u => ne_of_gt (conicDenominator_pos u)))

theorem conicParam_inverse (x y : ℝ) (hx : x≠0)
    (h : conicPolynomial (x,y)=0) :
    conicParam (y/x)=(x,y) := by
  let u := y/x
  have hy : u*x=y := div_mul_cancel₀ y hx
  have heq : x*conicDenominator u=1+u := by
    apply mul_right_cancel₀ hx
    calc
      (x*conicDenominator u)*x=x^2+x*y+y^2 := by
        rw [← hy]
        dsimp [conicDenominator]
        ring
      _ = x+y := by
        dsimp [conicPolynomial] at h
        linarith
      _ = (1+u)*x := by rw [add_mul,one_mul,hy]
  have hd : conicDenominator u≠0 := ne_of_gt (conicDenominator_pos u)
  have hfirst : (1+u)/conicDenominator u=x :=
    (div_eq_iff hd).mpr heq.symm
  apply Prod.ext
  · exact hfirst
  · change u*(1+u)/conicDenominator u=y
    rw [mul_div_assoc,hfirst,hy]

theorem conic_rational_density (p : ℝ × ℝ) (hp : conicPolynomial p=0) :
    p∈closure {q | RationalPoint q ∧ conicPolynomial q=0} := by
  rcases p with ⟨x,y⟩
  by_cases hx : x=0
  · subst x
    have hy : y*(y-1)=0 := by
      dsimp [conicPolynomial] at hp
      nlinarith
    rcases mul_eq_zero.mp hy with hy|hy
    · subst y
      apply subset_closure
      exact ⟨⟨⟨0,by simp⟩,⟨0,by simp⟩⟩,hp⟩
    · have hyone : y=1 := by linarith
      subst y
      apply subset_closure
      exact ⟨⟨⟨0,by simp⟩,⟨1,by simp⟩⟩,hp⟩
  · have hd : y/x∈closure (Set.range ((↑) : ℚ → ℝ)) :=
      Rat.denseRange_cast _
    have hi := mem_closure_image continuous_conicParam.continuousAt hd
    have hsub : conicParam '' Set.range ((↑) : ℚ → ℝ) ⊆
        {q | RationalPoint q ∧ conicPolynomial q=0} := by
      rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨conicParam_rational a,conicParam_equation a⟩
    have hh := closure_mono hsub hi
    rwa [conicParam_inverse x y hx hp] at hh

def quarticPolynomial (p : ℝ × ℝ) : ℝ :=
  p.1^2*p.2^2-2*p.1*p.2^2+3*p.1*p.2-p.1+p.2^2-2*p.2+1

def quarticParam (u : ℝ) : ℝ × ℝ :=
  (u^2-u+1,-u/(u-1)^2)

theorem quarticParam_equation (u : ℝ) :
    quarticPolynomial (quarticParam u)=0 := by
  by_cases hu : u=1
  · subst u
    norm_num [quarticParam,quarticPolynomial]
  · have hd : u-1≠0 := sub_ne_zero.mpr hu
    dsimp [quarticPolynomial,quarticParam]
    field_simp [hd]
    ring

theorem quarticParam_rational (u : ℚ) : RationalPoint (quarticParam u) := by
  refine ⟨⟨u^2-u+1,?_⟩,⟨-u/(u-1)^2,?_⟩⟩ <;> simp [quarticParam]

theorem continuousAt_quarticParam (u : ℝ) (hu : u≠1) :
    ContinuousAt quarticParam u := by
  have h₁ : ContinuousAt (fun t : ℝ => t^2-t+1) u := by fun_prop
  have hn : ContinuousAt (fun t : ℝ => -t) u := by fun_prop
  have hd : ContinuousAt (fun t : ℝ => (t-1)^2) u := by fun_prop
  exact h₁.prodMk (hn.div hd (pow_ne_zero 2 (sub_ne_zero.mpr hu)))

/-- The inverse parameter is justified at every point of the literal
allowed chart; no generic smoothness or additional denominator is assumed. -/
theorem quarticParam_inverse (x y : ℝ) (hy : y≠1)
    (h : quarticPolynomial (x,y)=0) :
    let u := x*y/(y-1)
    u≠1 ∧ quarticParam u=(x,y) := by
  let u := x*y/(y-1)
  have hden : y-1≠0 := sub_ne_zero.mpr hy
  have hu : u*(y-1)=x*y := div_mul_cancel₀ (x*y) hden
  have hxmul : (u^2-u+1-x)*(y-1)^2=0 := by
    calc
      (u^2-u+1-x)*(y-1)^2 =
          (u*(y-1))^2-(u*(y-1))*(y-1)+(1-x)*(y-1)^2 := by ring
      _ = quarticPolynomial (x,y) := by rw [hu]; dsimp [quarticPolynomial]; ring
      _ = 0 := h
  have hx : u^2-u+1=x :=
    sub_eq_zero.mp ((mul_eq_zero.mp hxmul).resolve_right (pow_ne_zero 2 hden))
  have hyparam : y*(u-1)^2 = -u := by
    rw [← hx] at hu
    nlinarith [hu]
  have hune : u≠1 := by
    intro huone
    rw [huone] at hyparam
    norm_num at hyparam
  refine ⟨hune,?_⟩
  apply Prod.ext
  · exact hx
  · change -u/(u-1)^2=y
    exact (div_eq_iff (pow_ne_zero 2 (sub_ne_zero.mpr hune))).mpr hyparam.symm

/-- The exceptional point outside the inverse chart is itself rational,
so the entire real quartic, including that point, has rational density. -/
theorem quartic_rational_density (p : ℝ × ℝ) (hp : quarticPolynomial p=0) :
    p∈closure {q | RationalPoint q ∧ quarticPolynomial q=0} := by
  rcases p with ⟨x,y⟩
  by_cases hy : y=1
  · subst y
    have hxmul : x*x=0 := by
      dsimp [quarticPolynomial] at hp
      nlinarith
    have hx : x=0 := mul_self_eq_zero.mp hxmul
    subst x
    apply subset_closure
    exact ⟨⟨⟨0,by simp⟩,⟨1,by simp⟩⟩,hp⟩
  · obtain ⟨hu,heq⟩ := quarticParam_inverse x y hy hp
    have hd : x*y/(y-1)∈closure (Set.range ((↑) : ℚ → ℝ)) :=
      Rat.denseRange_cast _
    have hi := mem_closure_image (continuousAt_quarticParam _ hu) hd
    have hsub : quarticParam '' Set.range ((↑) : ℚ → ℝ) ⊆
        {q | RationalPoint q ∧ quarticPolynomial q=0} := by
      rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨quarticParam_rational a,quarticParam_equation a⟩
    have hh := closure_mono hsub hi
    rwa [heq] at hh

theorem restrict_rational_zero_density_to_open
    (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (h : p∈closure {q | RationalPoint q ∧ f q=0})
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hpU : p∈U) :
    p∈closure {q | RationalPoint q ∧ f q=0 ∧ q∈U} := by
  rw [mem_closure_iff_frequently] at h ⊢
  exact (h.and_eventually (hU.mem_nhds hpU)).mono
    (fun _ hq => ⟨hq.1.1,hq.1.2,hq.2⟩)

theorem conic_rational_density_in_open
    (p : ℝ × ℝ) (hp : conicPolynomial p=0)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hpU : p∈U) :
    p∈closure {q | RationalPoint q ∧ conicPolynomial q=0 ∧ q∈U} :=
  restrict_rational_zero_density_to_open conicPolynomial p
    (conic_rational_density p hp) U hU hpU

theorem quartic_rational_density_in_open
    (p : ℝ × ℝ) (hp : quarticPolynomial p=0)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hpU : p∈U) :
    p∈closure {q | RationalPoint q ∧ quarticPolynomial q=0 ∧ q∈U} :=
  restrict_rational_zero_density_to_open quarticPolynomial p
    (quartic_rational_density p hp) U hU hpU


/-- The residual nonsplit quadratic cannot have an allowed real point.
This uses the exact discriminant identity and does not assume that a
particular quadratic coefficient is nonzero. -/
theorem nonsplit_quadratic_impossible
    (a b c x y : ℝ) (hy0 : y≠0) (hy1 : y≠1)
    (hroot : a*x^2+b*x+c=0)
    (hdisc : b^2-4*a*c = -3*y^2*(y-1)^2) : False := by
  have hid : (2*a*x+b)^2=b^2-4*a*c := by
    calc
      (2*a*x+b)^2 = b^2-4*a*c+4*a*(a*x^2+b*x+c) := by ring
      _ = b^2-4*a*c := by rw [hroot]; ring
  have hypos : 0<y^2 := sq_pos_of_ne_zero hy0
  have hyone : 0<(y-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hy1)
  have hdneg : b^2-4*a*c<0 := by
    rw [hdisc]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num : (-3 : ℝ)<0) hypos) hyone
  rw [← hid] at hdneg
  exact (not_lt_of_ge (sq_nonneg (2*a*x+b))) hdneg

end Papers.RationalityTen.ResidualCurves
