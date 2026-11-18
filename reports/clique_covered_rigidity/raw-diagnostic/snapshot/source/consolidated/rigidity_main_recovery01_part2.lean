module
public import consolidated.rigidity_main_recovery01_part1
import all consolidated.rigidity_main_recovery01_part1
set_option Elab.async false
section BundleSource0048
/- Source: Papers/RigiditySameCenterDiscrepancy.lean -/



@[expose] public section

/-!
# The actual rank-one discrepancy for a common finite center

The two-row quotient is constructed from the literal four-dimensional
angular image.  Its affine determinant equations force one scalar.
The discrepancy has rank one and its kernel maps onto the full center
space in the first body.  These are exactly the data required by the
already-derived Maurer--Cartan distribution obstruction.

The discrepancy is derived from the actual joint-pin rank bound.
-/

noncomputable section
namespace Papers.Rigidity

open CofactorKernel Matrix
open scoped Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem eq_of_angular_eq_mem_finiteCenter (a : Vec3) (X Y : Twist)
    (hX : X ∈ finiteCenterSpace a) (hY : Y ∈ finiteCenterSpace a)
    (hω : X.1 = Y.1) : X = Y := by
  apply Prod.ext hω
  have htx : X.2 = -(X.1 ⨯₃ a) := eq_neg_of_add_eq_zero_left hX
  have hty : Y.2 = -(Y.1 ⨯₃ a) := eq_neg_of_add_eq_zero_left hY
  rw [htx, hty, hω]

/-- No distribution, scalar regularity, or rank-one relation is assumed:
all three are pointwise algebraic consequences of the actual pin bound. -/
theorem sameCenter_scalar_discrepancy
    (A B : E →ₗ[ℝ] Twist) (hdim : Module.finrank ℝ E = 4) (a : Vec3)
    (hA : A.range = finiteCenterSpace a) (hB : B.range = finiteCenterSpace a)
    (hinj : Function.Injective (A.prod B))
    (hrank : ∀ p, Module.finrank ℝ (bodyJointPin A B p).range ≤ 3) :
    ∃ lam : ℝ, lam ≠ 0 ∧ B - lam • A ≠ 0 ∧
      Module.finrank ℝ (B - lam • A).range ≤ 1 ∧
      finiteCenterSpace a ≤ (A.comp (B - lam • A).ker.subtype).range := by
  let W := (angularPair A B).range
  have hW : Module.finrank ℝ W = 4 := by
    rw [LinearMap.finrank_range_of_inj
      (angularPair_injective_of_finiteCenters A B a a hA hB hinj)]
    exact hdim
  have hsurj₁ : Function.Surjective ((LinearMap.fst ℝ Vec3 Vec3).comp W.subtype) := by
    intro ω
    obtain ⟨u, hu⟩ := angular_surjective_of_finiteCenter_range A a hA ω
    exact ⟨⟨angularPair A B u, u, rfl⟩, hu⟩
  have hsurj₂ : Function.Surjective ((LinearMap.snd ℝ Vec3 Vec3).comp W.subtype) := by
    intro ω
    obtain ⟨u, hu⟩ := angular_surjective_of_finiteCenter_range B a hB ω
    exact ⟨⟨angularPair A B u, u, rfl⟩, hu⟩
  obtain ⟨Q, R, hQ, hR, hkernel⟩ := four_dimensional_two_body_quotient W hW hsurj₁ hsurj₂
  obtain ⟨O, hOdense, hpin⟩ := exists_dense_finiteCenters_angular_common_pins
    A B hdim a a hA hB hinj hrank
  have hdet : ∀ p, determinantTwo (Q (p - a)) (R (p - a)) = 0 := by
    apply determinantTwo_eq_zero_of_dense_common_pins Q R a a O hOdense
    intro p hp
    obtain ⟨s, t, hs, ht, hst⟩ := hpin p hp
    change (s • (p - a), t • (p - a)) ∈ W at hst
    rw [hkernel] at hst
    exact ⟨s, t, hs, ht, hst⟩
  obtain ⟨γ, hγ, hRγ, _⟩ := affine_determinantTwo_classification Q R hQ hR a a hdet
  let lam : ℝ := -γ⁻¹
  let D : E →ₗ[ℝ] Twist := B - lam • A
  have hlam : lam ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hγ)
  have hγlam : γ * lam = -1 := by simp [lam, hγ]
  have hlamγ : lam * γ = -1 := by simp [lam, hγ]
  have hmemA (u : E) : A u ∈ finiteCenterSpace a := by rw [← hA]; exact ⟨u, rfl⟩
  have hmemB (u : E) : B u ∈ finiteCenterSpace a := by rw [← hB]; exact ⟨u, rfl⟩
  have hmemD (u : E) : D u ∈ finiteCenterSpace a :=
    (finiteCenterSpace a).sub_mem (hmemB u) ((finiteCenterSpace a).smul_mem lam (hmemA u))
  have hconstraint (u : E) : Q (A u).1 + γ • Q (B u).1 = 0 := by
    have hm : angularPair A B u ∈ W := ⟨u, rfl⟩
    rw [hkernel] at hm
    change Q (A u).1 + R (B u).1 = 0 at hm
    rw [hRγ, LinearMap.smul_apply] at hm
    exact hm
  have hQD (u : E) : Q (D u).1 = 0 := by
    have hfirst : Q (A u).1 = -(γ • Q (B u).1) := eq_neg_of_add_eq_zero_left (hconstraint u)
    change Q ((B u).1 - lam • (A u).1) = 0
    rw [map_sub, map_smul, hfirst, smul_neg, smul_smul, hlamγ]
    simp
  have hQker : Module.finrank ℝ Q.ker = 1 := by
    have hn := Q.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hQ] at hn
    have hdim₂ : Module.finrank ℝ Vec2 = 2 := by simp [Vec2]
    have hdim₃ : Module.finrank ℝ Vec3 = 3 := by simp [Vec3]
    rw [finrank_top, hdim₂, hdim₃] at hn
    omega
  let L : D.range →ₗ[ℝ] Q.ker :=
    ((LinearMap.fst ℝ Vec3 Vec3).comp D.range.subtype).codRestrict Q.ker (by
      rintro ⟨X, u, rfl⟩
      exact hQD u)
  have hLinj : Function.Injective L := by
    intro X Y hXY
    apply Subtype.ext
    obtain ⟨u, hu⟩ := X.property
    obtain ⟨v, hv⟩ := Y.property
    apply eq_of_angular_eq_mem_finiteCenter a X.val Y.val
    · rw [← hu]
      exact hmemD u
    · rw [← hv]
      exact hmemD v
    · exact congrArg Subtype.val hXY
  have hDrank : Module.finrank ℝ D.range ≤ 1 := by
    have hh := LinearMap.finrank_le_finrank_of_injective hLinj
    rwa [hQker] at hh
  have hcenter : finiteCenterSpace a ≤ (A.comp D.ker.subtype).range := by
    intro X hX
    have hpair : (X.1, lam • X.1) ∈ W := by
      rw [hkernel]
      change Q X.1 + R (lam • X.1) = 0
      rw [hRγ, LinearMap.smul_apply, map_smul, smul_smul, hγlam]
      simp
    obtain ⟨u, hu⟩ := hpair
    change ((A u).1, (B u).1) = (X.1, lam • X.1) at hu
    have huA := congrArg (fun Z : Vec3 × Vec3 => Z.1) hu
    have huB := congrArg (fun Z : Vec3 × Vec3 => Z.2) hu
    have hAu : A u = X :=
      eq_of_angular_eq_mem_finiteCenter a (A u) X (hmemA u) hX huA
    have hBu : B u = lam • X :=
      eq_of_angular_eq_mem_finiteCenter a (B u) (lam • X) (hmemB u)
        ((finiteCenterSpace a).smul_mem lam hX) huB
    have hDu : D u = 0 := by simp only [D, LinearMap.sub_apply, LinearMap.smul_apply, hAu, hBu, sub_self]
    exact ⟨⟨u, hDu⟩, hAu⟩
  have hDne : D ≠ 0 := by
    intro hz
    have hArank : Module.finrank ℝ A.range = 3 := by rw [hA, finrank_finiteCenterSpace]
    have hk : 0 < Module.finrank ℝ A.ker := by
      have hh := A.finrank_range_add_finrank_ker
      omega
    obtain ⟨u, hu⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := A.ker)).mp hk
    have hAu : A u.val = 0 := u.property
    have hBu : B u.val = 0 := by
      have hh := congrArg (fun T : E →ₗ[ℝ] Twist => T u.val) hz
      simpa only [D, LinearMap.sub_apply, LinearMap.smul_apply,
        hAu, smul_zero, sub_zero, LinearMap.zero_apply] using hh
    exact hu (Subtype.ext (hinj (by
      change (A u.val, B u.val) = (A 0, B 0)
      simp only [hAu, hBu, map_zero])))
  exact ⟨lam, hlam, hDne, hDrank, hcenter⟩

end Papers.Rigidity

end
end
end BundleSource0048

section BundleSource0049
/- Source: Papers/RigiditySameCenterMerger.lean -/





@[expose] public section

/-!
# The actual merger for two rank-three bodies with a common center

A nonzero vector in the first projection's kernel is constructed smoothly.
The second angular image of that vector gives the actual discrepancy
axis.  A fixed cross-product coordinate then recovers the pointwise
scalar as a differentiable quotient.  The full center-space distribution
obstruction forces that scalar to be one.  Dense pins consequently force
the two actual twists to agree in every surviving common-pin motion.

The same-center merger supplies the remaining coupled case of Proposition 4.1.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter Matrix CofactorKernel CommonPinLowRank
open scoped Topology Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_differentiable_sameCenter_scalar
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (a : E → Vec3) (x : E)
    (hdim : Module.finrank ℝ E = 4)
    (hθ₁ : DifferentiableAt ℝ θ₁ x) (hθ₂ : DifferentiableAt ℝ θ₂ x)
    (hcenters : ∀ᶠ y in 𝓝 x,
      (θ₁ y).toLinearMap.range = finiteCenterSpace (a y) ∧
      (θ₂ y).toLinearMap.range = finiteCenterSpace (a y))
    (hinj : ∀ᶠ y in 𝓝 x, Function.Injective ((θ₁ y).toLinearMap.prod (θ₂ y).toLinearMap))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap p).range ≤ 3) :
    ∃ lam : E → ℝ, DifferentiableAt ℝ lam x ∧
      ∀ᶠ y in 𝓝 x, lam y ≠ 0 ∧ θ₂ y - lam y • θ₁ y ≠ 0 ∧
        Module.finrank ℝ (θ₂ y - lam y • θ₁ y).toLinearMap.range ≤ 1 ∧
        finiteCenterSpace (a y) ≤
          ((θ₁ y).toLinearMap.comp (θ₂ y - lam y • θ₁ y).toLinearMap.ker.subtype).range := by
  let A : E → (E →L[ℝ] Vec3) := fun y => angularForm (θ₁ y)
  have hA : DifferentiableAt ℝ A x := (differentiableAt_const (ContinuousLinearMap.fst ℝ Vec3 Vec3)).clm_comp hθ₁
  have hsurj : Function.Surjective (A x) :=
    angular_surjective_of_finiteCenter_range (θ₁ x).toLinearMap (a x) hcenters.self_of_nhds.1
  obtain ⟨v, hv, hvker⟩ := exists_differentiable_kernel_vector A x hdim hA hsurj
  have hfirstzero : ∀ᶠ y in 𝓝 x, θ₁ y (v y) = 0 := by
    filter_upwards [hvker, hcenters] with y hy hcy
    apply eq_of_angular_eq_mem_finiteCenter (a y) (θ₁ y (v y)) 0
    · rw [← hcy.1]
      exact ⟨v y, rfl⟩
    · exact (finiteCenterSpace (a y)).zero_mem
    · exact hy.2
  let d : E → Vec3 := fun y => (θ₂ y (v y)).1
  have hd : DifferentiableAt ℝ d x := (hθ₂.clm_apply hv).fst
  have hdne : d x ≠ 0 := by
    intro hz
    have hsecond : θ₂ x (v x) = 0 := by
      apply eq_of_angular_eq_mem_finiteCenter (a x) (θ₂ x (v x)) 0
      · rw [← hcenters.self_of_nhds.2]
        exact ⟨v x, rfl⟩
      · exact (finiteCenterSpace (a x)).zero_mem
      · exact hz
    exact hvker.self_of_nhds.1 (hinj.self_of_nhds (by
      change (θ₁ x (v x), θ₂ x (v x)) = (θ₁ x 0, θ₂ x 0)
      simp only [hfirstzero.self_of_nhds, hsecond, map_zero]))
  have hcross : ∃ ω : Vec3, d x ⨯₃ ω ≠ 0 := by
    by_contra hn
    push_neg at hn
    have h0 := congrFun (hn ![1, 0, 0]) (2 : Fin 3)
    have h1 := congrFun (hn ![1, 0, 0]) (1 : Fin 3)
    have h2 := congrFun (hn ![0, 1, 0]) (2 : Fin 3)
    simp [cross_apply] at h0 h1 h2
    apply hdne
    funext i
    fin_cases i <;> simp_all
  obtain ⟨ω, hω⟩ := hcross
  obtain ⟨u₀, hu₀⟩ := hsurj ω
  have hcrossvalue : d x ⨯₃ (θ₁ x u₀).1 ≠ 0 := by rwa [← hu₀] at hω
  obtain ⟨j, hj⟩ := not_forall.mp (fun h => hcrossvalue (funext h))
  let f₁ : E → ℝ := fun y => (d y ⨯₃ (θ₁ y u₀).1) j
  let f₂ : E → ℝ := fun y => (d y ⨯₃ (θ₂ y u₀).1) j
  let lam : E → ℝ := fun y => f₂ y / f₁ y
  have hf₁ : DifferentiableAt ℝ f₁ x :=
    differentiableAt_pi.mp (differentiableAt_cross d (fun y => (θ₁ y u₀).1) x hd
      (hθ₁.clm_apply (differentiableAt_const u₀)).fst) j
  have hf₂ : DifferentiableAt ℝ f₂ x :=
    differentiableAt_pi.mp (differentiableAt_cross d (fun y => (θ₂ y u₀).1) x hd
      (hθ₂.clm_apply (differentiableAt_const u₀)).fst) j
  have hf₁ne : f₁ x ≠ 0 := hj
  have hprod : DifferentiableAt ℝ (fun y => f₂ y * (f₁ y)⁻¹) x :=
    hf₂.mul (hf₁.inv hf₁ne)
  have hquot : DifferentiableAt ℝ lam x := by
    simpa only [lam, div_eq_mul_inv] using hprod
  refine ⟨lam, hquot, ?_⟩
  filter_upwards [hf₁.continuousAt.eventually_ne hf₁ne,
    hd.continuousAt.eventually_ne hdne, hfirstzero, hcenters, hinj, hrank]
      with y hy hdy hAy hcy hiy hry
  obtain ⟨γ, hγ, hDγne, hDγrank, hDγcenter⟩ :=
    sameCenter_scalar_discrepancy (θ₁ y).toLinearMap (θ₂ y).toLinearMap
      hdim (a y) hcy.1 hcy.2 hiy hry
  let D : E →ₗ[ℝ] Twist := (θ₂ y).toLinearMap - γ • (θ₁ y).toLinearMap
  have hDv : D (v y) = θ₂ y (v y) := by
    change θ₂ y (v y) - γ • θ₁ y (v y) = θ₂ y (v y)
    rw [hAy, smul_zero, sub_zero]
  have hDvne : D (v y) ≠ 0 := by
    intro hz
    apply hdy
    exact congrArg Prod.fst (hDv.symm.trans hz)
  have hDrank : Module.finrank ℝ D.range = 1 := by
    have hnonbot : D.range ≠ ⊥ := by
      intro hz
      have hm : D (v y) ∈ D.range := ⟨v y, rfl⟩
      rw [hz] at hm
      exact hDvne hm
    have hlow := Submodule.one_le_finrank_iff.mpr hnonbot
    change Module.finrank ℝ D.range ≤ 1 at hDγrank
    omega
  have hDspan : D.range = Submodule.span ℝ {D (v y)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hDrank ⟨v y, rfl⟩ hDvne
  have hcrossD : d y ⨯₃ (D u₀).1 = 0 := by
    have hm : D u₀ ∈ Submodule.span ℝ {D (v y)} := by rw [← hDspan]; exact ⟨u₀, rfl⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hm
    rw [← hr, hDv]
    change d y ⨯₃ (r • d y) = 0
    rw [map_smul, cross_self, smul_zero]
  have hcoordinate : f₂ y - γ * f₁ y = 0 := by
    have hh := congrFun hcrossD j
    change (d y ⨯₃ ((θ₂ y u₀).1 - γ • (θ₁ y u₀).1)) j = 0 at hh
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hh
    exact hh
  have hlamy : lam y = γ := by
    apply (div_eq_iff hy).mpr
    linarith
  rw [hlamy]
  refine ⟨hγ, ?_, ?_, ?_⟩
  · intro hz
    apply hDγne
    have hh := congrArg ContinuousLinearMap.toLinearMap hz
    change (θ₂ y).toLinearMap - γ • (θ₁ y).toLinearMap = 0 at hh
    exact hh
  · change Module.finrank ℝ ((θ₂ y).toLinearMap - γ • (θ₁ y).toLinearMap).range ≤ 1
    exact hDγrank
  · change finiteCenterSpace (a y) ≤
      ((θ₁ y).toLinearMap.comp ((θ₂ y).toLinearMap - γ • (θ₁ y).toLinearMap).ker.subtype).range
    exact hDγcenter

/-- The actual common-center branch gives equality of the two surviving
twists for an open dense set of new pins.  The first body need not be an
immersion of the four-dimensional configuration chart. -/
theorem actual_sameCenter_dense_pin_merger
    {x : E} (A₁ A₂ : LocalTwistRepresentation (E := E) x)
    (hdim : Module.finrank ℝ E = 4) (a : E → Vec3)
    (hcenters : ∀ᶠ y in 𝓝 x,
      (A₁.form y).toLinearMap.range = finiteCenterSpace (a y) ∧
      (A₂.form y).toLinearMap.range = finiteCenterSpace (a y))
    (hinj : ∀ᶠ y in 𝓝 x,
      Function.Injective ((A₁.form y).toLinearMap.prod (A₂.form y).toLinearMap))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p,
      Module.finrank ℝ (bodyJointPin (A₁.form y).toLinearMap (A₂.form y).toLinearMap p).range ≤ 3) :
    ∃ U : Set Vec3, IsOpen U ∧ Dense U ∧
      ∀ p ∈ U, ∀ u : E,
        evaluateTwist p (A₁.form x u) = 0 → evaluateTwist p (A₂.form x u) = 0 →
          A₂.form x u = A₁.form x u := by
  obtain ⟨lam, hlam, hnear⟩ := exists_differentiable_sameCenter_scalar A₁.form A₂.form a x
    hdim A₁.form_differentiable A₂.form_differentiable hcenters hinj hrank
  have hx := hnear.self_of_nhds
  have hone : lam x = 1 :=
    proportional_center_discrepancy_eq_one A₁ A₂ lam hlam hx.1 hx.2.1
      (hnear.mono fun _ h => h.2.2.1) (Or.inl ⟨a x, hx.2.2.2⟩)
  let D := (A₂.form x - A₁.form x).toLinearMap
  have hD : Module.finrank ℝ D.range ≤ 1 := by
    have hh := hx.2.2.1
    rw [hone, one_smul] at hh
    exact hh
  let U := {p : Vec3 | Function.Injective (restrictEvaluation D.range p)}
  refine ⟨U, isOpen_injective_evaluation D.range,
    dense_injective_evaluation_of_finrank_le_one D.range hD, ?_⟩
  intro p hp u hu₁ hu₂
  let X : D.range := ⟨D u, u, rfl⟩
  have hX : X = 0 := hp (by
    change evaluateTwist p (A₂.form x u - A₁.form x u) = evaluateTwist p 0
    simp only [map_sub, hu₁, hu₂, sub_self, map_zero])
  exact sub_eq_zero.mp (congrArg Subtype.val hX)

end Papers.Rigidity.Calculus

end
end
end BundleSource0049

section BundleSource0050
/- Source: Papers/RigidityRankThreePair.lean -/





@[expose] public section

/-!
# The local four-dimensional chart with two rank-three body images

The center functions are recovered from actual angular frames.  Their
differentiability on a neighborhood is proved by the frame formulas.
The two centers then agree on that neighborhood by the moving-center
Maurer--Cartan argument.  Finally the actual common-center discrepancy
forces equality of the two surviving twists at an open dense set of pins.

Angular surjectivity is stated only at the base point; the separate
projective placement transport produces this finite chart, including for
initial centers at infinity.  This lemma does not transport a Euclidean
configuration fiber through a projective map.

The paired rank-three calculation retains both projective center types.
-/

noncomputable section
namespace Papers.Rigidity.Calculus

open Filter CofactorKernel
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem eventually_injective_body_pair
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E)
    (hθ₁ : DifferentiableAt ℝ θ₁ x) (hθ₂ : DifferentiableAt ℝ θ₂ x)
    (hinj : Function.Injective ((θ₁ x).toLinearMap.prod (θ₂ x).toLinearMap)) :
    ∀ᶠ y in 𝓝 x,
      Function.Injective ((θ₁ y).toLinearMap.prod (θ₂ y).toLinearMap) := by
  let P : E → (E →L[ℝ] (Twist × Twist)) := fun y => (θ₁ y).prod (θ₂ y)
  have hP : ContinuousAt P x :=
    (ContinuousLinearMap.prodₗᵢ ℝ).continuous.continuousAt.comp
      (hθ₁.continuousAt.prodMk hθ₂.continuousAt)
  exact hP.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hinj)

/-- This local result has no chosen smooth-center, distribution, or
center-equality premise.  It uses the actual body representations and
the literal joint-pin ranks throughout. -/
theorem actual_rankThree_pair_dense_pin_merger
    (θ₁ θ₂ : E → (E →L[ℝ] Twist)) (x : E)
    (hdim : Module.finrank ℝ E = 4)
    (hactual : ∀ᶠ y in 𝓝 x,
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y)
    (hsingular : ∀ᶠ y in 𝓝 x,
      SingularPinSpace (θ₁ y).toLinearMap.range ∧
      SingularPinSpace (θ₂ y).toLinearMap.range)
    (hω₁ : Function.Surjective (angularForm (θ₁ x)))
    (hω₂ : Function.Surjective (angularForm (θ₂ x)))
    (hinj : Function.Injective ((θ₁ x).toLinearMap.prod (θ₂ x).toLinearMap))
    (hrank : ∀ᶠ y in 𝓝 x, ∀ p,
      Module.finrank ℝ (bodyJointPin (θ₁ y).toLinearMap (θ₂ y).toLinearMap p).range ≤ 3) :
    ∃ U : Set Vec3, IsOpen U ∧ Dense U ∧
      ∀ p ∈ U, ∀ u : E,
        evaluateTwist p (θ₁ x u) = 0 → evaluateTwist p (θ₂ x u) = 0 →
          θ₂ x u = θ₁ x u := by
  have hd₁ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ θ₁ y := by
    filter_upwards [hactual] with y hy
    obtain ⟨A, hA⟩ := hy.1
    simpa only [hA] using A.form_differentiable
  have hd₂ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ θ₂ y := by
    filter_upwards [hactual] with y hy
    obtain ⟨A, hA⟩ := hy.2
    simpa only [hA] using A.form_differentiable
  have hipair := eventually_injective_body_pair θ₁ θ₂ x
    hd₁.self_of_nhds hd₂.self_of_nhds hinj
  obtain ⟨a, ha⟩ := exists_differentiable_finite_center_locally θ₁ x hd₁
    (hsingular.mono fun _ h => h.1) hω₁
  obtain ⟨b, hb⟩ := exists_differentiable_finite_center_locally θ₂ x hd₂
    (hsingular.mono fun _ h => h.2) hω₂
  have hcenters : ∀ᶠ y in 𝓝 x,
      (θ₁ y).toLinearMap.range = finiteCenterSpace (a y) ∧
      (θ₂ y).toLinearMap.range = finiteCenterSpace (b y) := by
    filter_upwards [ha, hb] with y hay hby
    exact ⟨hay.2, hby.2⟩
  have heq : ∀ᶠ y in 𝓝 x, a y = b y := by
    filter_upwards [hactual, ha, hb, eventually_eventually_nhds.mpr hcenters,
      eventually_eventually_nhds.mpr hipair, eventually_eventually_nhds.mpr hrank]
        with y hy hay hby hcy hiy hry
    obtain ⟨A₁, hA₁⟩ := hy.1
    obtain ⟨A₂, hA₂⟩ := hy.2
    subst θ₁
    subst θ₂
    exact actual_two_finite_centers_equal A₁ A₂ hdim a b hay.1 hby.1 hcy hiy hry
  have hcommon : ∀ᶠ y in 𝓝 x,
      (θ₁ y).toLinearMap.range = finiteCenterSpace (a y) ∧
      (θ₂ y).toLinearMap.range = finiteCenterSpace (a y) := by
    filter_upwards [hcenters, heq] with y hcy hey
    exact ⟨hcy.1, by simpa only [hey] using hcy.2⟩
  obtain ⟨A₁, hA₁⟩ := hactual.self_of_nhds.1
  obtain ⟨A₂, hA₂⟩ := hactual.self_of_nhds.2
  subst θ₁
  subst θ₂
  obtain ⟨U, hU, hUdense, hmerge⟩ := actual_sameCenter_dense_pin_merger A₁ A₂ hdim a
    hcommon hipair hrank
  exact ⟨U, hU, hUdense, hmerge⟩

end Papers.Rigidity.Calculus

end
end
end BundleSource0050

section BundleSource0051
/- Source: Papers/RigidityOwnedLocalSingular.lean -/




@[expose] public section

/-!
# Actual singular body images throughout the deleted configuration fiber

The derivative of the chart is an actual grounded bar motion at each
nearby configuration.  Its body image is contained in the original
relative-twist image there.  Genericity is open.  The already derived
global exclusion of rank-four projections consequently supplies singular
images throughout a neighborhood, without assuming body-rank constancy
or imposing an additional center hypothesis.

The singularity statement concerns the actual local body forms.
-/

noncomputable section
namespace Papers.Rigidity

theorem SingularPinSpace.mono {W U : Submodule ℝ Twist}
    (hU : SingularPinSpace U) (hWU : W ≤ U) : SingularPinSpace W := by
  intro p
  have hle : (restrictEvaluation W p).range ≤ (restrictEvaluation U p).range := by
    rintro _ ⟨X, rfl⟩
    exact ⟨⟨X.val, hWU X.property⟩, rfl⟩
  exact (Submodule.finrank_mono hle).trans (hU p)

namespace VertexPin.IncidentTetrahedra

open BarJoint Calculus Calculus.GroundedConfiguration Filter
open scoped Classical Topology

variable {V B : Type} [Fintype V] [Fintype B] {G : SimpleGraph V} {v : V}
variable (T : IncidentTetrahedra G v B) (p : Placement V 3)
  (hp : GeneralPosition.InGeneralPosition p) (base : B)
variable (C : SmoothLevelChart
  (groundedLengthMap (deletedGraph G v) (T.triangleEmbedding base))
  (deletedPlacement p v) (T.IncidentGroundedMotions p base))

theorem incidentBodyForm_range_le_relative_eventually (hgen : IsGenericPlacement p) :
    ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base),
      let P := restoreDeletedPlacement v (p v) (C.parametrization y)
      ∃ hgen' : IsGenericPlacement P,
        ∃ hgeom' : GeneralPosition.InGeneralPosition P, ∀ b : B,
          ((T.incidentBodyRepresentation p hp base C b).form y).toLinearMap.range ≤
            (T.relativeTwists P
              (GeneralPosition.InGeneralPosition.incident_noncollinear P hgeom' T) base b).range := by
  let P : T.IncidentGroundedMotions p base → Placement V 3 :=
    fun y => restoreDeletedPlacement v (p v) (C.parametrization y)
  have hP : ContinuousAt P 0 :=
    (continuous_restoreDeletedPlacement v (p v)).continuousAt.comp
      C.smooth_parametrization.continuousAt
  have hP0 : P 0 = p := by simp [P, C.parametrization_zero]
  have hgeneric : ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base), IsGenericPlacement (P y) := by
    apply hP.eventually
    rw [hP0]
    exact isOpen_isGenericPlacement.mem_nhds hgen
  have hgeometry : ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions p base),
      GeneralPosition.InGeneralPosition (P y) := by
    apply hP.eventually
    rw [hP0]
    exact GeneralPosition.isOpen_generalPosition.mem_nhds hp
  have hvelocity := bodyRepresentation_velocity (deletedGraph G v) (T.triangleEmbedding base)
    (deletedPlacement p v) C T.triangleVertices T.triangleVertices_clique T.triangleEmbedding
    T.triangleEmbedding_mem (deletedGeneralPosition p hp v)
  have hground := bodyRepresentation_grounded (deletedGraph G v) (T.triangleEmbedding base)
    (deletedPlacement p v) C T.triangleVertices T.triangleVertices_clique T.triangleEmbedding
    T.triangleEmbedding_mem (deletedGeneralPosition p hp v) base (T.triangleEmbedding_mem base)
  filter_upwards [hgeneric, hgeometry, hvelocity, hground,
    C.smooth_parametrization.eventually (by simp),
    eventually_eventually_nhds.mpr C.level] with y hgy hpy hvel hzero hsmooth hlevel
  refine ⟨hgy, hpy, ?_⟩
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear (P y) hpy T
  let F : T.IncidentGroundedMotions p base →ₗ[ℝ] DeletedMotions G (P y) v :=
    (fderiv ℝ C.parametrization y).toLinearMap.codRestrict _ (by
      intro u
      have hu := derivative_mem_groundedMotions (deletedGraph G v) (T.triangleEmbedding base)
        (deletedPlacement p v) C.parametrization y u
        (hsmooth.differentiableAt (by norm_num)) hlevel
      change (fderiv ℝ C.parametrization y) u ∈
        (rigidityOperator (deletedGraph G v)
          (deletedPlacement (restoreDeletedPlacement v (p v) (C.parametrization y)) v)).ker
      rw [deletedPlacement_restore]
      exact hu.1)
  have htwist (b : B) (u : T.IncidentGroundedMotions p base) :
      T.bodyTwist (P y) hn b (F u) =
        (T.incidentBodyRepresentation p hp base C b).form y u := by
    apply sub_eq_zero.mp
    apply twist_eq_zero_of_fixing_triangle (T.trianglePoints (P y) b) (hn b)
    intro i
    rw [map_sub, sub_eq_zero, T.bodyTwist_fit]
    have hv := hvel u b (T.triangle b i) (T.triangleEmbedding_mem b i)
    simpa only [F, LinearMap.codRestrict_apply, ContinuousLinearMap.coe_coe,
      P, trianglePoints, restoreDeletedPlacement_other, incidentBodyRepresentation] using hv
  intro b X hX
  obtain ⟨u, rfl⟩ := hX
  refine ⟨F u, ?_⟩
  change T.bodyTwist (P y) hn b (F u) - T.bodyTwist (P y) hn base (F u) = _
  rw [htwist, htwist]
  change (T.incidentBodyRepresentation p hp base C b).form y u -
      (T.incidentBodyRepresentation p hp base C base).form y u =
    (T.incidentBodyRepresentation p hp base C b).form y u
  have hbase : (T.incidentBodyRepresentation p hp base C base).form y u = 0 := hzero u
  rw [hbase, sub_zero]

end VertexPin.IncidentTetrahedra

open BarJoint VertexPin Calculus Filter
open scoped Classical Topology

variable {V : Type} [Fintype V]

theorem MinimalCounterexample.hypervertex_owned_body_singular_eventually
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v)
    (hdrop : deletionRankDrop M.graph v = 6)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (base b : OwnedIncidentTriangle M.graph v)
    (hne : b.owner ≠ base.owner)
    (C : SmoothLevelChart
      (groundedLengthMap (deletedGraph M.graph v)
        ((ownedIncidentTetrahedra M.graph v M.covered).triangleEmbedding base))
      (deletedPlacement p v)
      ((ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base)) :
    ∀ᶠ y in 𝓝 (0 : (ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base),
      SingularPinSpace
        (((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form y).toLinearMap.range := by
  let T := ownedIncidentTetrahedra M.graph v M.covered
  filter_upwards [T.incidentBodyForm_range_le_relative_eventually p hp base C hgen] with y hy
  obtain ⟨hgy, hpy, hle⟩ := hy
  let P := restoreDeletedPlacement v (p v) (C.parametrization y)
  have hlow := Papers.Rigidity.VertexPin.MinimalCounterexample.owned_relative_rank_ge_three M v P hgy hpy base b hne
  have hhigh := M.hypervertex_relative_rank_le_three v hh hdrop P hgy hpy base b
  have hdim := Nat.le_antisymm hhigh hlow
  exact (Papers.Rigidity.VertexPin.MinimalCounterexample.owned_rankThree_singular M v P hgy hpy base b hne hdim).mono (hle b)

end Papers.Rigidity

end
end
end BundleSource0051

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0051/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0051.json"

section BundleSource0052
/- Source: Papers/RigidityIncidentPairSelection.lean -/



@[expose] public section

/-!
# Selecting the genuine coupled pair from the incident body map

On a four-dimensional tangent space a rank-three projection has a
one-dimensional kernel.  Joint injectivity of all actual incident-body
forms supplies a second projection nonzero on that kernel.  The paired
projection is therefore injective.  Maximal-owner equality is excluded
using the already proved actual twist dictionary.

The selected pair retains its original maximal-body owners.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint VertexPin Calculus
open scoped Classical

theorem exists_injective_pair_of_rank_three
    {E B : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A : B → E →ₗ[ℝ] Twist) (hdim : Module.finrank ℝ E = 4)
    (hinj : Function.Injective (LinearMap.pi A)) (b : B)
    (hb : Module.finrank ℝ (A b).range = 3) :
    ∃ c : B, ∃ u : E, u ≠ 0 ∧ A b u = 0 ∧ A c u ≠ 0 ∧
      Function.Injective ((A b).prod (A c)) := by
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := E) (V₂ := Twist) (A b)
  have hkdim : Module.finrank ℝ (A b).ker = 1 := by omega
  have hpositive : 0 < Module.finrank ℝ (A b).ker := by omega
  obtain ⟨u, hu⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := (A b).ker)).mp hpositive
  have hune : (u : E) ≠ 0 := fun hz => hu (Subtype.ext hz)
  have hAu : A b (u : E) = 0 := u.property
  have hex : ∃ c, A c (u : E) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hune
    apply hinj
    funext c
    simpa only [LinearMap.pi_apply, map_zero] using hn c
  obtain ⟨c, hc⟩ := hex
  have hspan : (A b).ker = Submodule.span ℝ {(u : E)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hkdim u.property hune
  refine ⟨c, u, hune, hAu, hc, ?_⟩
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro z hz
    have hz0 := LinearMap.mem_ker.mp hz
    have hbz : A b z = 0 := congrArg Prod.fst hz0
    have hcz : A c z = 0 := congrArg Prod.snd hz0
    have hzm : z ∈ Submodule.span ℝ {(u : E)} := by
      rw [← hspan]
      exact hbz
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hzm
    have hrzero : r = 0 := by
      have h : r • A c (u : E) = 0 := by rw [← map_smul, hr, hcz]
      exact (smul_eq_zero.mp h).resolve_right hc
    change z = 0
    rw [← hr, hrzero, zero_smul]
  · exact bot_le

namespace VertexPin.IncidentTetrahedra

variable {V : Type} [Fintype V] {G : SimpleGraph V} {v : V}

theorem owned_incident_forms_eq_of_owner_eq (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (base b c : OwnedIncidentTriangle G v)
    (hbc : b.owner = c.owner)
    (C : SmoothLevelChart
      (groundedLengthMap (deletedGraph G v)
        ((ownedIncidentTetrahedra G v hG).triangleEmbedding base))
      (deletedPlacement p v)
      ((ownedIncidentTetrahedra G v hG).IncidentGroundedMotions p base)) :
    ((ownedIncidentTetrahedra G v hG).incidentBodyRepresentation p hp base C b).form 0 =
      ((ownedIncidentTetrahedra G v hG).incidentBodyRepresentation p hp base C c).form 0 := by
  let T := ownedIncidentTetrahedra G v hG
  apply ContinuousLinearMap.ext
  intro u
  rw [T.incidentBodyForm_at_zero, T.incidentBodyForm_at_zero]
  exact owned_bodyTwist_eq_of_owner_eq hG p hp b c hbc (T.groundedDeletedInclusion p base u)

end VertexPin.IncidentTetrahedra

variable {V : Type} [Fintype V]

theorem MinimalCounterexample.hypervertex_select_injective_pair
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v)
    (hdrop : deletionRankDrop M.graph v = 6)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (base b : OwnedIncidentTriangle M.graph v)
    (hbbase : b.owner ≠ base.owner)
    (C : SmoothLevelChart
      (groundedLengthMap (deletedGraph M.graph v)
        ((ownedIncidentTetrahedra M.graph v M.covered).triangleEmbedding base))
      (deletedPlacement p v)
      ((ownedIncidentTetrahedra M.graph v M.covered).IncidentGroundedMotions p base)) :
    ∃ c : OwnedIncidentTriangle M.graph v, c.owner ≠ base.owner ∧ c.owner ≠ b.owner ∧
      Function.Injective
        ((((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C b).form 0).toLinearMap.prod
          (((ownedIncidentTetrahedra M.graph v M.covered).incidentBodyRepresentation p hp base C c).form 0).toLinearMap) := by
  let T := ownedIncidentTetrahedra M.graph v M.covered
  let A := fun c : OwnedIncidentTriangle M.graph v =>
    ((T.incidentBodyRepresentation p hp base C c).form 0).toLinearMap
  have hE : Module.finrank ℝ (T.IncidentGroundedMotions p base) = 4 := by
    have h := M.grounded_incident_finrank v T p hgen hp base
    omega
  have hall : Function.Injective (LinearMap.pi A) :=
    T.incidentBodyFormOperator_injective p hp base C hgen
      (M.neighborCompletion_isGenericallyRigid v)
  have hlow : 3 ≤ Module.finrank ℝ (A b).range := by
    rw [show (A b).range = (T.relativeTwists p
      (GeneralPosition.InGeneralPosition.incident_noncollinear p hp T) base b).range from
      T.incidentBodyForm_range_at_zero p hp base C b]
    exact Papers.Rigidity.VertexPin.MinimalCounterexample.owned_relative_rank_ge_three M v p hgen hp base b hbbase
  have hhigh := M.hypervertex_bodyForm_rank_le_three v hh hdrop p hgen hp base b C
  obtain ⟨c, u, hu, hbu, hcu, hpair⟩ := exists_injective_pair_of_rank_three A hE hall b
    (Nat.le_antisymm hhigh hlow)
  refine ⟨c, ?_, ?_, hpair⟩
  · intro hcbase
    have he := IncidentTetrahedra.owned_incident_forms_eq_of_owner_eq M.covered p hp
      base c base hcbase C
    apply hcu
    change (T.incidentBodyRepresentation p hp base C c).form 0 u = 0
    rw [he, T.incidentBodyForm_at_zero, T.bodyTwist_grounded_base]
  · intro hcb
    have he := IncidentTetrahedra.owned_incident_forms_eq_of_owner_eq M.covered p hp
      base c b hcb C
    apply hcu
    change (T.incidentBodyRepresentation p hp base C c).form 0 u = 0
    rw [he]
    exact hbu

end Papers.Rigidity

end
end
end BundleSource0052

section BundleSource0053
/- Source: Papers/RigidityProjectiveTransport.lean -/




@[expose] public section

/-!
# Actual projective transport of bar velocities and virtual centers

The special projective transformation used here is
`p ↦ p / (1 + c · p)`.  Its velocity transport is not the derivative of
that map: it is the contragredient transport appropriate to the bar
equations.  Every equation is multiplied by an explicit nonzero edge
factor, and the motion-kernel equivalence is constructed in both
directions.  The twist and homogeneous-center maps are genuine linear
equivalences, including for centers at infinity.

This module supplies the change of placement made before choosing a
Euclidean length fiber in Section 4. It does not transport an existing
Euclidean configuration manifold.
-/

noncomputable section
namespace Papers.Rigidity.ProjectiveTransport

open Matrix BarJoint
open scoped Matrix

def denominator (c p : Vec3) : ℝ := 1 + c ⬝ᵥ p

def point (c p : Vec3) : Vec3 := (denominator c p)⁻¹ • p

def velocity (c p : Vec3) : Vec3 →ₗ[ℝ] Vec3 :=
  (denominator c p)⁻¹ •
    ((LinearMap.id : Vec3 →ₗ[ℝ] Vec3) + (dotProductBilin ℝ ℝ p).smulRight c)

@[simp] theorem velocity_apply (c p u : Vec3) :
    velocity c p u = (denominator c p)⁻¹ • (u + (p ⬝ᵥ u) • c) := rfl

theorem denominator_inverse (c p : Vec3) (hp : denominator c p ≠ 0) :
    denominator (-c) (point c p) = (denominator c p)⁻¹ := by
  simp only [denominator, point, neg_dotProduct, dotProduct_smul, smul_eq_mul] at *
  field_simp
  ring

theorem denominator_inverse_ne_zero (c p : Vec3) (hp : denominator c p ≠ 0) :
    denominator (-c) (point c p) ≠ 0 := by
  rw [denominator_inverse c p hp]
  exact inv_ne_zero hp

theorem point_inverse (c p : Vec3) (hp : denominator c p ≠ 0) :
    point (-c) (point c p) = p := by
  rw [point, denominator_inverse c p hp, inv_inv, point, smul_smul,
    mul_inv_cancel₀ hp, one_smul]

theorem velocity_inverse (c p u : Vec3) (hp : denominator c p ≠ 0) :
    velocity (-c) (point c p) (velocity c p u) = u := by
  rw [velocity_apply, denominator_inverse c p hp, inv_inv, velocity_apply]
  ext i
  simp only [point, Pi.smul_apply, Pi.add_apply, Pi.neg_apply,
    smul_eq_mul, dotProduct, Fin.sum_univ_succ]
  dsimp [denominator] at hp ⊢
  field_simp
  norm_num [dotProduct, Fin.sum_univ_succ] <;> ring

/-- Each pointwise velocity map is invertible on its actual affine chart. -/
def velocityEquiv (c p : Vec3) (hp : denominator c p ≠ 0) : Vec3 ≃ₗ[ℝ] Vec3 where
  toLinearMap := velocity c p
  invFun := velocity (-c) (point c p)
  left_inv := fun u => velocity_inverse c p u hp
  right_inv := by
    intro u
    have hh := velocity_inverse (-c) (point c p) u (denominator_inverse_ne_zero c p hp)
    rw [neg_neg, point_inverse c p hp] at hh
    exact hh

/-- The literal transported twist; this is the alternating-matrix
congruence in the special projective chart. -/
def twistEquiv (c : Vec3) : Twist ≃ₗ[ℝ] Twist where
  toFun X := (X.1 + X.2 ⨯₃ c, X.2)
  invFun X := (X.1 - X.2 ⨯₃ c, X.2)
  left_inv X := by simp
  right_inv X := by simp
  map_add' X Y := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
    · rfl
  map_smul' a X := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
    · rfl

def centerEquiv (c : Vec3) : HomogeneousPoint ≃ₗ[ℝ] HomogeneousPoint where
  toFun q := (q.1, q.2 + c ⬝ᵥ q.1)
  invFun q := (q.1, q.2 - c ⬝ᵥ q.1)
  left_inv q := by simp
  right_inv q := by simp
  map_add' q r := by simp [dotProduct_add, add_assoc, add_left_comm, add_comm]
  map_smul' a q := by simp [dotProduct_smul, smul_add] <;> ring

def covectorEquiv (c : Vec3) : HomogeneousPoint ≃ₗ[ℝ] HomogeneousPoint where
  toFun q := (q.1 - q.2 • c, q.2)
  invFun q := (q.1 + q.2 • c, q.2)
  left_inv q := by simp
  right_inv q := by simp
  map_add' q r := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, add_smul]
      abel
    · rfl
  map_smul' a q := by
    apply Prod.ext
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_sub, smul_smul,
        RingHom.id_apply, smul_eq_mul]
    · rfl

/-- The fourth contraction coordinate is retained.  It is exactly the
orthogonality equation needed to transport a center at infinity. -/
theorem homogeneousEvaluation_transport (c : Vec3) (q : HomogeneousPoint) (X : Twist) :
    homogeneousEvaluation (centerEquiv c q) (twistEquiv c X) =
      covectorEquiv c (homogeneousEvaluation q X) := by
  apply Prod.ext
  · ext i
    fin_cases i <;>
      simp [homogeneousEvaluation_apply, centerEquiv, twistEquiv, covectorEquiv,
        cross_apply, Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_succ] <;> ring
  · simp [homogeneousEvaluation_apply, centerEquiv, twistEquiv, covectorEquiv]

theorem homogeneousEvaluation_transport_eq_zero_iff
    (c : Vec3) (q : HomogeneousPoint) (X : Twist) :
    homogeneousEvaluation (centerEquiv c q) (twistEquiv c X) = 0 ↔
      homogeneousEvaluation q X = 0 := by
  rw [homogeneousEvaluation_transport]
  exact (covectorEquiv c).map_eq_zero_iff

theorem centerSpace_map (c : Vec3) (q : HomogeneousPoint) :
    (homogeneousCenterSpace q).map (twistEquiv c).toLinearMap =
      homogeneousCenterSpace (centerEquiv c q) := by
  ext Y
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact (homogeneousEvaluation_transport_eq_zero_iff c q X).mpr hX
  · intro hY
    refine ⟨(twistEquiv c).symm Y, ?_, by simp⟩
    apply (homogeneousEvaluation_transport_eq_zero_iff c q ((twistEquiv c).symm Y)).mp
    rw [LinearEquiv.apply_symm_apply]
    exact hY

/-- A transported body twist evaluates to the transported bar velocity. -/
theorem evaluateTwist_transport (c p : Vec3) (hp : denominator c p ≠ 0) (X : Twist) :
    evaluateTwist (point c p) (twistEquiv c X) = velocity c p (evaluateTwist p X) := by
  ext i
  fin_cases i <;>
    simp [evaluateTwist_apply, twistEquiv, point, velocity_apply, cross_apply,
      Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_succ] <;>
    dsimp [denominator] at hp ⊢ <;> field_simp <;>
    norm_num [dotProduct, Fin.sum_univ_succ] <;> ring

/-- Exact scaling of an arbitrary bar equation, before any graph or rank
condition is imposed. -/
theorem bar_constraint_transport (c p q u v : Vec3)
    (hp : denominator c p ≠ 0) (hq : denominator c q ≠ 0) :
    (point c p - point c q) ⬝ᵥ (velocity c p u - velocity c q v) =
      (denominator c p * denominator c q)⁻¹ * ((p - q) ⬝ᵥ (u - v)) := by
  simp only [point, velocity_apply, dotProduct, Fin.sum_univ_succ,
    Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  dsimp [denominator] at hp hq ⊢
  field_simp
  norm_num [dotProduct, Fin.sum_univ_succ] <;> ring

variable {V : Type}

def placement (c : Vec3) (p : Placement V 3) : Placement V 3 := fun v => point c (p v)

def placementVelocity (c : Vec3) (p : Placement V 3) :
    Velocity V 3 →ₗ[ℝ] Velocity V 3 :=
  LinearMap.pi fun v => (velocity c (p v)).comp (LinearMap.proj v)

@[simp] theorem placementVelocity_apply (c : Vec3) (p : Placement V 3)
    (u : Velocity V 3) (v : V) : placementVelocity c p u v = velocity c (p v) (u v) := rfl

theorem edgeConstraint_transport (c : Vec3) (p : Placement V 3) (u : Velocity V 3)
    (hp : ∀ v, denominator c (p v) ≠ 0) (v w : V) :
    edgeConstraint (placement c p) (placementVelocity c p u) v w =
      (denominator c (p v) * denominator c (p w))⁻¹ * edgeConstraint p u v w :=
  bar_constraint_transport c (p v) (p w) (u v) (u w) (hp v) (hp w)

theorem isInfinitesimalMotion_transport_iff (G : SimpleGraph V) (c : Vec3)
    (p : Placement V 3) (hp : ∀ v, denominator c (p v) ≠ 0) (u : Velocity V 3) :
    IsInfinitesimalMotion G (placement c p) (placementVelocity c p u) ↔
      IsInfinitesimalMotion G p u := by
  rw [isInfinitesimalMotion_iff, isInfinitesimalMotion_iff]
  simp only [edgeConstraint_transport c p u hp,
    mul_eq_zero, inv_eq_zero, mul_eq_zero, hp, false_or]

def motionKernelEquiv (G : SimpleGraph V) (c : Vec3) (p : Placement V 3)
    (hp : ∀ v, denominator c (p v) ≠ 0) :
    (rigidityOperator G p).ker ≃ₗ[ℝ] (rigidityOperator G (placement c p)).ker where
  toFun u := ⟨placementVelocity c p u.val,
    (isInfinitesimalMotion_transport_iff G c p hp u.val).mpr u.property⟩
  invFun u := ⟨placementVelocity (-c) (placement c p) u.val, by
    have hh := (isInfinitesimalMotion_transport_iff G (-c) (placement c p)
      (fun v => denominator_inverse_ne_zero c (p v) (hp v)) u.val).mpr u.property
    have hpoint : placement (-c) (placement c p) = p := by
      funext v
      exact point_inverse c (p v) (hp v)
    rw [hpoint] at hh
    exact hh⟩
  left_inv u := by
    apply Subtype.ext
    funext v
    exact velocity_inverse c (p v) (u.val v) (hp v)
  right_inv u := by
    apply Subtype.ext
    funext v
    have hh := velocity_inverse (-c) (point c (p v)) (u.val v)
      (denominator_inverse_ne_zero c (p v) (hp v))
    rw [neg_neg, point_inverse c (p v) (hp v)] at hh
    exact hh
  map_add' u w := Subtype.ext (map_add _ _ _)
  map_smul' a u := Subtype.ext (map_smul _ _ _)

/-- Projective transport preserves the actual rank of every graph on
the given vertex set, with no genericity hypothesis. -/
theorem rigidityRank_transport [Fintype V] (G : SimpleGraph V) (c : Vec3)
    (p : Placement V 3) (hp : ∀ v, denominator c (p v) ≠ 0) :
    rigidityRank G (placement c p) = rigidityRank G p := by
  have hk := (motionKernelEquiv G c p hp).finrank_eq
  have h₁ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := Velocity V 3) (V₂ := V × V → ℝ) (rigidityOperator G p)
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := Velocity V 3) (V₂ := V × V → ℝ)
    (rigidityOperator G (placement c p))
  change Module.finrank ℝ (rigidityOperator G (placement c p)).range =
    Module.finrank ℝ (rigidityOperator G p).range
  omega

end Papers.Rigidity.ProjectiveTransport

end
end
end BundleSource0053

section BundleSource0054
/- Source: Papers/RigidityFiniteProjectiveChart.lean -/




@[expose] public section

/-!
# A finite chart for finitely many actual virtual centers

The allowed special projective transformations contain arbitrarily small
parameters making any finite family of nonzero homogeneous centers finite.
All actual vertices remain finite as well.  The construction uses an open
dense intersection of genuine affine rank conditions; it assumes no
genericity of the virtual centers themselves.

Together with the exact rank transport, this permits choosing a new
placement before constructing its own Euclidean length fiber.
-/

noncomputable section
namespace Papers.Rigidity.ProjectiveTransport

open Matrix BarJoint Filter
open scoped Matrix Topology

def heightConstant (q : HomogeneousPoint) : ℝ →ₗ[ℝ] ℝ :=
  q.2 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

def heightLinear (q : HomogeneousPoint) : Vec3 →ₗ[ℝ] (ℝ →ₗ[ℝ] ℝ) :=
  (dotProductBilin ℝ ℝ q.1).smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

theorem heightFamily_apply (q : HomogeneousPoint) (c : Vec3) (r : ℝ) :
    AffineRank.family (heightConstant q) (heightLinear q) c r =
      (centerEquiv c q).2 * r := by
  change q.2 * r + (q.1 ⬝ᵥ c) * r = (q.2 + c ⬝ᵥ q.1) * r
  rw [dotProduct_comm q.1 c]
  ring

theorem height_rank_iff (q : HomogeneousPoint) (c : Vec3) :
    1 ≤ AffineRank.rankAt (heightConstant q) (heightLinear q) c ↔
      (centerEquiv c q).2 ≠ 0 := by
  by_cases h : (centerEquiv c q).2 = 0
  · have hzero : AffineRank.family (heightConstant q) (heightLinear q) c = 0 := by
      ext r
      simp only [heightFamily_apply, h, zero_mul, LinearMap.zero_apply]
    simp [AffineRank.rankAt, hzero, h]
  · have hinj : Function.Injective (AffineRank.family (heightConstant q) (heightLinear q) c) := by
      intro r s hrs
      rw [heightFamily_apply, heightFamily_apply] at hrs
      exact mul_left_cancel₀ h hrs
    have hrank : AffineRank.rankAt (heightConstant q) (heightLinear q) c = 1 := by
      rw [AffineRank.rankAt, LinearMap.finrank_range_of_inj hinj]
      simp
    simp [hrank, h]

theorem exists_nonzero_center_height (q : HomogeneousPoint) (hq : q ≠ 0) :
    ∃ c : Vec3, (centerEquiv c q).2 ≠ 0 := by
  by_cases hs : q.2 = 0
  · have ha : q.1 ≠ 0 := fun h => hq (Prod.ext h hs)
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => ha (funext h))
    refine ⟨Pi.single i 1, ?_⟩
    change q.2 + Pi.single i 1 ⬝ᵥ q.1 ≠ 0
    rw [hs, zero_add, single_one_dotProduct]
    exact hi
  · exact ⟨0, by simpa [centerEquiv] using hs⟩

theorem isOpen_nonzero_center_height (q : HomogeneousPoint) :
    IsOpen {c : Vec3 | (centerEquiv c q).2 ≠ 0} := by
  have h := AffineRank.isOpen_setOf_le_rankAt (heightConstant q) (heightLinear q) 1
  simpa only [height_rank_iff] using h

theorem dense_nonzero_center_height (q : HomogeneousPoint) (hq : q ≠ 0) :
    Dense {c : Vec3 | (centerEquiv c q).2 ≠ 0} := by
  have hw : ∃ c, 1 ≤ AffineRank.rankAt (heightConstant q) (heightLinear q) c := by
    obtain ⟨c, hc⟩ := exists_nonzero_center_height q hq
    exact ⟨c, (height_rank_iff q c).mpr hc⟩
  have h := AffineRank.dense_setOf_le_rankAt (heightConstant q) (heightLinear q) 1 hw
  simpa only [height_rank_iff] using h

/-- Every nonempty open set of chart parameters contains one making the
whole finite family of nonzero homogeneous points finite. -/
theorem exists_finite_chart_in_open
    {I : Type*} [Finite I] (q : I → HomogeneousPoint) (hq : ∀ i, q i ≠ 0)
    (O : Set Vec3) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ c ∈ O, ∀ i, (centerEquiv c (q i)).2 ≠ 0 := by
  have hdense : Dense (⋂ i : I, {c : Vec3 | (centerEquiv c (q i)).2 ≠ 0}) :=
    dense_iInter_of_isOpen (fun i => isOpen_nonzero_center_height (q i))
      (fun i => dense_nonzero_center_height (q i) (hq i))
  obtain ⟨c, hc, hcO⟩ := hdense.exists_mem_open hO hne
  exact ⟨c, hcO, Set.mem_iInter.mp hc⟩

theorem point_continuousAt_zero (p : Vec3) :
    ContinuousAt (fun c : Vec3 => point c p) 0 := by
  have hden : Continuous (fun c : Vec3 => denominator c p) := by
    exact continuous_const.add ((dotProductBilin ℝ ℝ p).continuous_of_finiteDimensional.congr
      (fun c => dotProduct_comm p c))
  have hnonzero : denominator 0 p ≠ 0 := by simp [denominator]
  exact (hden.continuousAt.inv₀ hnonzero).smul continuousAt_const

theorem placement_continuousAt_zero {V : Type} (p : Placement V 3) :
    ContinuousAt (fun c : Vec3 => placement c p) 0 :=
  continuousAt_pi.mpr fun v => point_continuousAt_zero (p v)

@[simp] theorem placement_zero {V : Type} (p : Placement V 3) : placement 0 p = p := by
  funext v
  simp [placement, point, denominator]

/-- Actual vertices and finitely many virtual centers are simultaneously
finite after a transformation arbitrarily close to the original placement.
The open neighborhood can encode every required general-position condition. -/
theorem exists_finite_chart_preserving_neighborhood
    {V I : Type} [Finite V] [Finite I]
    (p : Placement V 3) (q : I → HomogeneousPoint) (hq : ∀ i, q i ≠ 0)
    (U : Set (Placement V 3)) (hU : U ∈ 𝓝 p) :
    ∃ c : Vec3, placement c p ∈ U ∧
      (∀ v, denominator c (p v) ≠ 0) ∧
      ∀ i, (centerEquiv c (q i)).2 ≠ 0 := by
  let r : V ⊕ I → HomogeneousPoint := Sum.elim (fun v => (p v, 1)) q
  have hr : ∀ j, r j ≠ 0 := by
    intro j
    cases j with
    | inl v => simp [r]
    | inr i => exact hq i
  have hpre : (fun c : Vec3 => placement c p) ⁻¹' U ∈ 𝓝 (0 : Vec3) := by
    apply (placement_continuousAt_zero p).preimage_mem_nhds
    simpa only [placement_zero] using hU
  obtain ⟨O, hOsub, hOopen, hzero⟩ := mem_nhds_iff.mp hpre
  obtain ⟨c, hcO, hc⟩ := exists_finite_chart_in_open r hr O hOopen ⟨0, hzero⟩
  refine ⟨c, hOsub hcO, ?_, ?_⟩
  · intro v
    exact hc (Sum.inl v)
  · intro i
    exact hc (Sum.inr i)

/-- Every maximal-rank condition is preserved by the same actual
transport. This conclusion holds for each graph on the vertex set. -/
theorem genericRank_preserved {V : Type} [Fintype V] (G : SimpleGraph V) (c : Vec3)
    (p : Placement V 3) (hp : ∀ v, denominator c (p v) ≠ 0)
    (hgeneric : rigidityRank G p = genericRigidityRank G 3) :
    rigidityRank G (placement c p) = genericRigidityRank G 3 := by
  rw [rigidityRank_transport G c p hp]
  exact hgeneric

/-- The simultaneous genericity used in the graph proof is preserved for
all graphs, rather than only for the particular graph currently studied. -/
theorem genericPlacement_preserved {V : Type} [Fintype V] (c : Vec3)
    (p : Placement V 3) (hp : ∀ v, denominator c (p v) ≠ 0)
    (hgeneric : IsGenericPlacement p) : IsGenericPlacement (placement c p) := by
  intro G
  exact genericRank_preserved G c p hp (hgeneric G)

end Papers.Rigidity.ProjectiveTransport

end
end
end BundleSource0054

section BundleSource0055
/- Source: Papers/RigidityProjectiveBodies.lean -/




@[expose] public section

/-!
# Projective transport of the graph's actual extracted body twists

The triangle extraction maps come from the deleted graph's bar motions.
Their transport is proved by uniqueness on the same three actual body
vertices.  Hence relative-twist images, their projective centers, and
equality of bodies transport through literal linear equivalences.

The two noncollinearity hypotheses are retained explicitly here.  In the
chart-selection application they are provided by the open neighborhood
of the original general-position placement.  No body-motion space is
postulated independently of the graph.
-/

noncomputable section
namespace Papers.Rigidity.ProjectiveTransport

open BarJoint VertexPin

variable {V B : Type} [Fintype V] [Fintype B]
variable {G : SimpleGraph V} {v : V}

def deletedMotionEquiv (G : SimpleGraph V) (v : V) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0) :
    DeletedMotions G p v ≃ₗ[ℝ] DeletedMotions G (placement c p) v :=
  motionKernelEquiv (deletedGraph G v) c (deletedPlacement p v) (fun w => hp w.val)

@[simp] theorem deletedMotionEquiv_apply (c : Vec3) (p : Placement V 3)
    (hp : ∀ w, denominator c (p w) ≠ 0) (u : DeletedMotions G p v)
    (w : DeletedVertex v) :
    (deletedMotionEquiv G v c p hp u).val w = velocity c (p w.val) (u.val w) := rfl

theorem bodyTwist_transport (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p))
    (b : B) (u : DeletedMotions G p v) :
    T.bodyTwist (placement c p) hn' b (deletedMotionEquiv G v c p hp u) =
      twistEquiv c (T.bodyTwist p hn b u) := by
  apply triangleTwistOperator_injective (T.trianglePoints (placement c p) b) (hn' b)
  funext ij
  change evaluateTwist (T.trianglePoints (placement c p) b ij.1)
      (T.bodyTwist (placement c p) hn' b (deletedMotionEquiv G v c p hp u)) ij.2 =
    evaluateTwist (point c (T.trianglePoints p b ij.1))
      (twistEquiv c (T.bodyTwist p hn b u)) ij.2
  rw [T.bodyTwist_fit,
    evaluateTwist_transport c (T.trianglePoints p b ij.1) (hp (T.triangle b ij.1).val),
    T.bodyTwist_fit]
  rfl

theorem relativeTwists_transport (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p))
    (base b : B) (u : DeletedMotions G p v) :
    T.relativeTwists (placement c p) hn' base b (deletedMotionEquiv G v c p hp u) =
      twistEquiv c (T.relativeTwists p hn base b u) := by
  change T.bodyTwist (placement c p) hn' b (deletedMotionEquiv G v c p hp u) -
      T.bodyTwist (placement c p) hn' base (deletedMotionEquiv G v c p hp u) =
    twistEquiv c (T.bodyTwist p hn b u - T.bodyTwist p hn base u)
  rw [bodyTwist_transport T c p hp hn hn', bodyTwist_transport T c p hp hn hn', map_sub]

/-- The whole relative-twist image transforms, including motions in the
kernel of individual body projections. -/
theorem relativeTwists_range_transport (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p))
    (base b : B) :
    (T.relativeTwists (placement c p) hn' base b).range =
      (T.relativeTwists p hn base b).range.map (twistEquiv c).toLinearMap := by
  ext X
  constructor
  · rintro ⟨u, rfl⟩
    let u₀ := (deletedMotionEquiv G v c p hp).symm u
    refine ⟨T.relativeTwists p hn base b u₀, ⟨u₀, rfl⟩, ?_⟩
    change twistEquiv c (T.relativeTwists p hn base b u₀) =
      T.relativeTwists (placement c p) hn' base b u
    rw [← relativeTwists_transport T c p hp hn hn']
    simp only [u₀, LinearEquiv.apply_symm_apply]
  · rintro ⟨Y, ⟨u, rfl⟩, rfl⟩
    refine ⟨deletedMotionEquiv G v c p hp u, ?_⟩
    exact relativeTwists_transport T c p hp hn hn' base b u

theorem relative_center_transport (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p))
    (base b : B) (q : HomogeneousPoint)
    (hq : (T.relativeTwists p hn base b).range = homogeneousCenterSpace q) :
    (T.relativeTwists (placement c p) hn' base b).range =
      homogeneousCenterSpace (centerEquiv c q) := by
  rw [relativeTwists_range_transport T c p hp hn hn', hq, centerSpace_map]

/-- Equality or inequality of two body projections in all deleted
motions is retained; the transport introduces no merger assumption. -/
theorem body_agreement_transport_iff (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p))
    (b₁ b₂ : B) :
    (∀ u : DeletedMotions G (placement c p) v,
      T.bodyTwist (placement c p) hn' b₁ u = T.bodyTwist (placement c p) hn' b₂ u) ↔
    (∀ u : DeletedMotions G p v, T.bodyTwist p hn b₁ u = T.bodyTwist p hn b₂ u) := by
  constructor
  · intro h u
    apply (twistEquiv c).injective
    rw [← bodyTwist_transport T c p hp hn hn', ← bodyTwist_transport T c p hp hn hn']
    exact h _
  · intro h u
    obtain ⟨u₀, rfl⟩ := (deletedMotionEquiv G v c p hp).surjective u
    rw [bodyTwist_transport T c p hp hn hn', bodyTwist_transport T c p hp hn hn', h]

theorem restrictFullMotion_transport (T : IncidentTetrahedra G v B) (c : Vec3)
    (p : Placement V 3) (hp : ∀ w, denominator c (p w) ≠ 0)
    (u : (rigidityOperator G p).ker) :
    T.restrictFullMotion (placement c p) (motionKernelEquiv G c p hp u) =
      deletedMotionEquiv G v c p hp (T.restrictFullMotion p u) := by
  apply Subtype.ext
  rfl

/-- The no-merger condition used for the surviving flex of the original
graph transports through the full graph kernel, not just its deletion. -/
theorem body_agreement_on_full_motions_transport_iff
    (T : IncidentTetrahedra G v B) (c : Vec3) (p : Placement V 3)
    (hp : ∀ w, denominator c (p w) ≠ 0)
    (hn : T.NoncollinearAt p) (hn' : T.NoncollinearAt (placement c p)) (b₁ b₂ : B) :
    (∀ u : (rigidityOperator G (placement c p)).ker,
      T.bodyTwist (placement c p) hn' b₁ (T.restrictFullMotion (placement c p) u) =
        T.bodyTwist (placement c p) hn' b₂ (T.restrictFullMotion (placement c p) u)) ↔
    (∀ u : (rigidityOperator G p).ker,
      T.bodyTwist p hn b₁ (T.restrictFullMotion p u) =
        T.bodyTwist p hn b₂ (T.restrictFullMotion p u)) := by
  constructor
  · intro h u
    have hh := h (motionKernelEquiv G c p hp u)
    rw [restrictFullMotion_transport T c p hp,
      bodyTwist_transport T c p hp hn hn', bodyTwist_transport T c p hp hn hn'] at hh
    exact (twistEquiv c).injective hh
  · intro h u
    obtain ⟨u₀, rfl⟩ := (motionKernelEquiv G c p hp).surjective u
    rw [restrictFullMotion_transport T c p hp,
      bodyTwist_transport T c p hp hn hn', bodyTwist_transport T c p hp hn hn', h]

/-- The finite-center reduction for any finite family of the graph's
actual singular relative-body images.  Infinite centers are included in
the input classification and are made finite by the constructed change
of placement.  Genericity and general position refer to the new placement
on which its own length fiber may subsequently be built. -/
theorem exists_generic_placement_with_finite_relative_centers
    {I : Type} [Finite I] (T : IncidentTetrahedra G v B)
    (p : Placement V 3) (hgeneric : IsGenericPlacement p)
    (hgeom : GeneralPosition.InGeneralPosition p) (base : B) (b : I → B)
    (hsingular : ∀ i, SingularPinSpace
      (T.relativeTwists p (GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom T)
        base (b i)).range)
    (hdim : ∀ i, 3 ≤ Module.finrank ℝ
      (T.relativeTwists p (GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom T)
        base (b i)).range) :
    ∃ c : Vec3, (∀ w, denominator c (p w) ≠ 0) ∧
      IsGenericPlacement (placement c p) ∧
      ∃ hgeom' : GeneralPosition.InGeneralPosition (placement c p),
        ∀ i, ∃ a : Vec3,
          (T.relativeTwists (placement c p)
            (GeneralPosition.InGeneralPosition.incident_noncollinear (placement c p) hgeom' T)
            base (b i)).range = finiteCenterSpace a := by
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hgeom T
  have hex (i : I) : ∃ q : HomogeneousPoint, q ≠ 0 ∧
      (T.relativeTwists p hn base (b i)).range = homogeneousCenterSpace q := by
    obtain ⟨q, hq, hWq, _⟩ := singularPinSpace_unique_projective_center
      (T.relativeTwists p hn base (b i)).range (hsingular i) (hdim i)
    exact ⟨q, hq, hWq⟩
  choose q hq hWq using hex
  obtain ⟨c, hgeom', hc, hfinite⟩ := exists_finite_chart_preserving_neighborhood
    p q hq {p' | GeneralPosition.InGeneralPosition p'}
      (GeneralPosition.isOpen_generalPosition.mem_nhds hgeom)
  refine ⟨c, hc, genericPlacement_preserved c p hc hgeneric, hgeom', ?_⟩
  intro i
  refine ⟨(centerEquiv c (q i)).2⁻¹ • (centerEquiv c (q i)).1, ?_⟩
  rw [relative_center_transport T c p hc hn
    (GeneralPosition.InGeneralPosition.incident_noncollinear (placement c p) hgeom' T)
      base (b i) (q i) (hWq i)]
  exact homogeneousCenterSpace_normalize _ (hfinite i)

end Papers.Rigidity.ProjectiveTransport

end
end
end BundleSource0055

section BundleSource0056
/- Source: Papers/RigidityHypervertexDeletion.lean -/




@[expose] public section

/-!
# The complete intended hypervertex deletion bound

This assembles the actual graph and differential arguments for
Proposition 4.1.  In the four-dimensional case rank-four projections
have already been excluded at every generic placement.  Every remaining
nonreference maximal body has a three-dimensional singular image.  One
fixed projective placement change makes all finitely many such centers
finite.  The transformed placement's own Euclidean fiber is then built.
Neighbor-completion rigidity selects a genuinely injective pair, and
the two-center Maurer--Cartan argument forces an impossible merger.

The proof retains centers at infinity before the actual chart change.
No covariance of Euclidean length fibers or Maurer--Cartan forms is
assumed. The assembly combines the actual body forms and chart transport.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint VertexPin Calculus
open scoped Classical Topology

variable {V : Type} [Fintype V]

theorem MinimalCounterexample.hypervertex_deletionRankDrop_ne_six
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v) :
    deletionRankDrop M.graph v ≠ 6 := by
  intro hdrop
  obtain ⟨b, hb⟩ := hh.exists_three_owned
  obtain ⟨p, hgen, hp⟩ := GeneralPosition.exists_generic_generalPosition (V := V)
  let T := ownedIncidentTetrahedra M.graph v M.covered
  let base := b 0
  let hn := GeneralPosition.InGeneralPosition.incident_noncollinear p hp T
  let I := {c : OwnedIncidentTriangle M.graph v // c.owner ≠ base.owner}
  have hthree (i : I) : Module.finrank ℝ (T.relativeTwists p hn base i.val).range = 3 := by
    exact Nat.le_antisymm
      (M.hypervertex_relative_rank_le_three v hh hdrop p hgen hp base i.val)
      (Papers.Rigidity.VertexPin.MinimalCounterexample.owned_relative_rank_ge_three M v p hgen hp base i.val i.property)
  have hsingular (i : I) : SingularPinSpace (T.relativeTwists p hn base i.val).range :=
    Papers.Rigidity.VertexPin.MinimalCounterexample.owned_rankThree_singular M v p hgen hp base i.val i.property (hthree i)
  obtain ⟨c, hc, hgq, hq, hfinite⟩ :=
    ProjectiveTransport.exists_generic_placement_with_finite_relative_centers
      T p hgen hp base (fun i : I => i.val) hsingular (fun i => (hthree i).ge)
  let q := ProjectiveTransport.placement c p
  let hnq := GeneralPosition.InGeneralPosition.incident_noncollinear q hq T
  let C := groundedLengthFiberChart (deletedGraph M.graph v) (T.triangleEmbedding base)
    (T.clique base) (deletedPlacement q v)
    (generic_deletedPlacement q hgq v (deletedGraph M.graph v)) (hnq base)
  have hE : Module.finrank ℝ (T.IncidentGroundedMotions q base) = 4 := by
    have h := M.grounded_incident_finrank v T q hgq hq base
    omega
  let b₁ := b 1
  have hb₁ : b₁.owner ≠ base.owner := hb.ne (by decide)
  obtain ⟨b₂, hb₂, hb₂₁, hpair⟩ :=
    M.hypervertex_select_injective_pair v hh hdrop q hgq hq base b₁ hb₁ C
  let θ₁ := (T.incidentBodyRepresentation q hq base C b₁).form
  let θ₂ := (T.incidentBodyRepresentation q hq base C b₂).form
  have hω₁ : Function.Surjective (angularForm (θ₁ 0)) := by
    obtain ⟨a, ha⟩ := hfinite (⟨b₁, hb₁⟩ : I)
    apply angular_surjective_of_finiteCenter_range (θ₁ 0).toLinearMap a
    rw [show (θ₁ 0).toLinearMap.range = (T.relativeTwists q hnq base b₁).range from
      T.incidentBodyForm_range_at_zero q hq base C b₁]
    exact ha
  have hω₂ : Function.Surjective (angularForm (θ₂ 0)) := by
    obtain ⟨a, ha⟩ := hfinite (⟨b₂, hb₂⟩ : I)
    apply angular_surjective_of_finiteCenter_range (θ₂ 0).toLinearMap a
    rw [show (θ₂ 0).toLinearMap.range = (T.relativeTwists q hnq base b₂).range from
      T.incidentBodyForm_range_at_zero q hq base C b₂]
    exact ha
  have hactual : ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions q base),
      HasLocalTwistRepresentation θ₁ y ∧ HasLocalTwistRepresentation θ₂ y :=
    (T.incidentBodyRepresentation_locallyRepresented q hq base C).mono
      (fun _ hy => ⟨hy b₁, hy b₂⟩)
  have hsnear : ∀ᶠ y in 𝓝 (0 : T.IncidentGroundedMotions q base),
      SingularPinSpace (θ₁ y).toLinearMap.range ∧ SingularPinSpace (θ₂ y).toLinearMap.range := by
    filter_upwards [M.hypervertex_owned_body_singular_eventually v hh hdrop q hgq hq base b₁ hb₁ C,
      M.hypervertex_owned_body_singular_eventually v hh hdrop q hgq hq base b₂ hb₂ C]
        with y hy₁ hy₂
    exact ⟨hy₁, hy₂⟩
  have hrank := T.incidentBody_joint_rank_le_three q hq base C hgq (by omega) b₁ b₂
  obtain ⟨U, hU, hUdense, hmerge⟩ := actual_rankThree_pair_dense_pin_merger θ₁ θ₂ 0 hE
    hactual hsnear hω₁ hω₂ hpair hrank
  exact Papers.Rigidity.VertexPin.MinimalCounterexample.owned_dense_pin_merger_contradiction M v q hq base C hgq b₂ b₁ hb₂₁ U hUdense
    (fun pin hpin u h₂ h₁ => hmerge pin hpin u h₁ h₂)

/-- Proposition 4.1 with the literal maximal-body incidence definition
and the actual generic graph-rank deletion loss. -/
theorem MinimalCounterexample.hypervertex_deletionRankDrop_ge_seven
    (M : MinimalCounterexample V) (v : V) (hh : IsHypervertex M.graph v) :
    7 ≤ deletionRankDrop M.graph v := by
  have hlow := M.five_le_deletionRankDrop v
  have hfive := M.hypervertex_deletionRankDrop_ne_five v hh
  have hsix := M.hypervertex_deletionRankDrop_ne_six v hh
  omega

end Papers.Rigidity

end
end
end BundleSource0056

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0056/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0056.json"

section BundleSource0057
/- Source: Papers/RigidityHypervertexCharges.lean -/





@[expose] public section

/-!
# The final actual hypervertex charge

The integer inequality here is the concluding account of Section 7.4.
Its exceptional-component and core counts are the literal counts from
the original graph. The proof constructs the specified ordinary star
edges and verifies all geometric side conditions of the arithmetic
lemma, including its small boundary cases.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

def neighborIncidentSet (G : SimpleGraph V) (v : V) (S : Finset V) :
    Finset (IncidentEdge G v) :=
  Finset.univ.filter fun e => incidentOther G v e ∈ S

theorem neighborIncidentSet_card
    (G : SimpleGraph V) (v : V) (S : Finset V)
    (hS : S ⊆ G.neighborFinset v) : (neighborIncidentSet G v S).card = S.card := by
  apply Finset.card_bij (fun e _ => incidentOther G v e)
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro e he f hf hef
    exact incidentOther_injective G v hef
  · intro w hw
    have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp (hS hw)
    let e : IncidentEdge G v := ⟨⟨s(v,w),hadj⟩,Sym2.mem_mk_left v w⟩
    have heq : incidentOther G v e = w :=
      Sym2.congr_right.mp (Sym2.other_spec e.property)
    exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq.symm ▸ hw⟩,heq⟩

theorem charged_core_single_residual_bound
    (M : MinimalCounterexample V) (h : V)
    (hcount : (chargedCoresAt M h).card = 1)
    (K : Finset V) (hK : K ⊆ M.graph.neighborFinset h)
    (hKP : Disjoint K (chargedPortsAt M h)) :
    4 + (chargedPortsAt M h).card ≤
      K.card + (M.graph.neighborFinset h \ (K ∪ chargedPortsAt M h)).card := by
  obtain ⟨C,hC⟩ := Finset.card_eq_one.mp hcount
  have hCm : C ∈ chargedCoresAt M h := by rw [hC]; simp
  have heq (v : chargedPortsAt M h) : chargedPortCore M h v = C := by
    have hm := chargedPortCore_mem M h v
    rwa [hC,Finset.mem_singleton] at hm
  let Q : ∀ v : chargedPortsAt M h, CorePort M C.val h v.val := fun v =>
    (heq v) ▸ chargedPortRecord M h v
  have hP : (chargedPortsAt M h).Nonempty := by
    have htwo := ((mem_chargedCoresAt M h C).mp hCm).2.2
    have hcard : (chargedPortsAt M h).card = (bodyTypeBVertices M C.val).card := by
      simp only [chargedPortsAt,hC,Finset.singleton_biUnion]
    exact Finset.card_pos.mp (by omega)
  exact core_ports_residual_neighbor_bound M C.val h (chargedPortsAt M h) K Q hP hK hKP

theorem exists_charged_three_port_core
    (M : MinimalCounterexample V) (h : V) (hpos : 0 < chargedCoreCountAt M h 3) :
    ∃ C : SelectedCore M, C ∈ chargedCoresAt M h ∧
      (bodyTypeBVertices M C.val).card = 3 := by
  obtain ⟨C,hC⟩ := Finset.card_pos.mp hpos
  have hm : bodyHyperVertices M C.val = {h} ∧ bodySoftVertices M C.val = ∅ ∧
      (bodyTypeBVertices M C.val).card = 3 := (Finset.mem_filter.mp hC).2
  exact ⟨C,(mem_chargedCoresAt M h C).mpr ⟨hm.1,hm.2.1,by omega⟩,hm.2.2⟩

theorem exceptional_and_three_port_residual_nonempty
    (L : SoftScalarSystem M p) (h : Hypervertex M.graph)
    (ha : exceptionalCountAt L h = 1) (hq3 : 0 < chargedCoreCountAt M h.val 3) :
    1 ≤ (M.graph.neighborFinset h.val \
      (exceptionalNeighborsAt L h ∪ chargedPortsAt M h.val)).card := by
  obtain ⟨c,hc,hK⟩ := exceptionalNeighbors_subset_of_count_one L h ha
  obtain ⟨C,hC,hthree⟩ := exists_charged_three_port_core M h.val hq3
  have hfiber : (Finset.univ.filter fun v : chargedPortsAt M h.val =>
      (chargedPortCore M h.val v).val = C.val).card = 3 := by
    rw [← core_port_family_inter_card M h.val (chargedPortsAt M h.val)
      (fun v => (chargedPortCore M h.val v).val) (chargedPortRecord M h.val)
      C.val (by rw [C.property.1]),chargedPorts_inter_core M h.val C hC,hthree]
  exact L.three_port_core_has_residual_neighbor c h hc
    (chargedPortsAt M h.val) (exceptionalNeighborsAt L h)
    (fun v => (chargedPortCore M h.val v).val) (chargedPortRecord M h.val)
    C.val C.property.1 (chargedCore_partner_mem M h.val C hC) hfiber hK

/-- The actual specified star consists of all exceptional-component
neighbors and all charged type-B ports. The included zero coordinates
cause no problem: the proved joint-kernel rank bound applies to them
as well. -/
theorem exceptional_charged_star_deletion_bound
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph) :
    (exceptionalNeighborsAt L h).card + (chargedPortsAt M h.val).card +
      min 3 (M.graph.neighborFinset h.val \
        (exceptionalNeighborsAt L h ∪ chargedPortsAt M h.val)).card ≤
      deletionRankDrop M.graph h.val + exceptionalCountAt L h + (chargedCoresAt M h.val).card := by
  let K := exceptionalNeighborsAt L h
  let P := chargedPortsAt M h.val
  let G := maskedGraph M.graph Finset.univ
  let A := neighborIncidentSet G h.val (K ∪ P)
  have hG : G = M.graph := by ext v w; simp [G,maskedGraph]
  have hKP : Disjoint K P := exceptional_charged_neighbors_disjoint L h
  have hsub : K ∪ P ⊆ M.graph.neighborFinset h.val :=
    Finset.union_subset (exceptionalNeighbors_subset_neighbors L h)
      (chargedPorts_subset_neighbors M h.val)
  have hsubG : K ∪ P ⊆ G.neighborFinset h.val := by
    intro w hw
    apply (G.mem_neighborFinset h.val w).mpr
    rw [hG]
    exact (M.graph.mem_neighborFinset h.val w).mp (hsub hw)
  have hAcard : A.card = K.card + P.card := by
    rw [neighborIncidentSet_card G h.val (K ∪ P) hsubG,
      Finset.card_union_of_disjoint hKP]
  have hD : M.graph.degree h.val - A.card =
      (M.graph.neighborFinset h.val \ (K ∪ P)).card := by
    rw [Finset.card_sdiff_of_subset hsub,Finset.card_union_of_disjoint hKP,
      M.graph.card_neighborFinset_eq_degree,hAcard]
  have hb := L.exceptional_core_star_deletion_bound hgen hp h
    (fun c : exceptionalComponentsAt L h => c.val)
    (fun c => (mem_exceptionalComponentsAt L h c.val).mp c.property)
    (fun c => c.val.out) (fun c => c.val.out_eq)
    (fun C : chargedCoresAt M h.val => C.val.val)
    (fun C => selectedCoreMode hgen C.val)
    (fun C => chargedCore_no_soft M h.val C.val C.property)
    (fun C => chargedCore_sole_hyper M h.val C.val C.property)
    A (by
      intro e he
      have hmem : incidentOther G h.val e ∈ K ∪ P := (Finset.mem_filter.mp he).2
      rcases Finset.mem_union.mp hmem with hmem | hmem
      · obtain ⟨c,hc,hvc⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hmem).2
        exact Or.inl ⟨⟨c,hc⟩,hvc⟩
      · let v : P := ⟨incidentOther G h.val e,hmem⟩
        exact Or.inr ⟨⟨chargedPortCore M h.val v,chargedPortCore_mem M h.val v⟩,
          ⟨chargedPortRecord M h.val v⟩⟩)
  rw [hD, hAcard] at hb
  simp only [Fintype.card_coe] at hb
  exact hb

/-- The concluding inequality of Section 7.4, in exact integer units.
Every count refers to a proved actual graph family. -/
theorem SoftScalarSystem.remaining_hypervertex_charges
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph) :
    12 + 2 * exceptionalCountAt L h + chargedCoreCountAt M h.val 3 +
      2 * chargedCoreCountAt M h.val 4 ≤ 2 * deletionRankDrop M.graph h.val := by
  let a := exceptionalCountAt L h
  let q2 := chargedCoreCountAt M h.val 2
  let q3 := chargedCoreCountAt M h.val 3
  let q4 := chargedCoreCountAt M h.val 4
  let K := exceptionalNeighborsAt L h
  let P := chargedPortsAt M h.val
  let D := (M.graph.neighborFinset h.val \ (K ∪ P)).card
  have hPcard : P.card = 2*q2 + 3*q3 + 4*q4 := chargedPorts_card M h.val
  have hCcard : (chargedCoresAt M h.val).card = q2+q3+q4 := (chargedCore_counts M h.val).1
  have hKsub : K ⊆ M.graph.neighborFinset h.val := exceptionalNeighbors_subset_neighbors L h
  have hKP : Disjoint K P := exceptional_charged_neighbors_disjoint L h
  apply Budget.remaining_hypervertex_charges a q2 q3 q4 K.card D
    (deletionRankDrop M.graph h.val)
  · exact M.hypervertex_deletionRankDrop_ge_seven h.val h.property
  · exact exceptionalNeighbors_card_ge L hgen hp h
  · have hb := exceptional_charged_star_deletion_bound L hgen hp h
    rw [hPcard,hCcard] at hb
    exact hb
  · intro ha hg
    have hKempty : K = ∅ := exceptionalNeighbors_eq_empty_of_count_zero L h ha
    have hPnonempty : P.Nonempty := Finset.card_pos.mp (by omega)
    have hb := core_port_family_three_unused_neighbors M h.val P hPnonempty
      (fun v => (chargedPortCore M h.val v).val) (chargedPortRecord M h.val)
    simpa only [D,hKempty,Finset.empty_union] using hb
  · intro ha h2 h3 h4
    exact exceptional_and_three_port_residual_nonempty L h ha (by omega)
  · intro ha h2 h3 h4
    have hc : (chargedCoresAt M h.val).card = 1 := by omega
    have hb := charged_core_single_residual_bound M h.val hc K hKsub hKP
    have hp3 : P.card = 3 := by omega
    change 7 ≤ K.card + D
    change 4 + P.card ≤ K.card + D at hb
    omega
  · intro ha h2 h3 h4
    have hc : (chargedCoresAt M h.val).card = 1 := by omega
    have hb := charged_core_single_residual_bound M h.val hc K hKsub hKP
    have hp4 : P.card = 4 := by omega
    change 8 ≤ K.card + D
    change 4 + P.card ≤ K.card + D at hb
    omega

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0057

section BundleSource0058
/- Source: Papers/RigidityLastInSubset.lean -/



@[expose] public section

/-!
# Birth of a locally supported mode

A fixed vertex is last in a nonempty finite support with probability
the reciprocal of its cardinality.  The probability is computed in the
same literal finite space of global orders used for rank contributions.
It applies to every support and does not introduce independent priorities
or assume a law for an induced order.
-/

namespace Papers.Rigidity.UniformOrders
noncomputable section
open scoped Classical BigOperators
variable {V I : Type*} [Fintype V] [Fintype I]

theorem mean_indicator_position (i : I) (q : Fin (Fintype.card I)) :
    mean (fun σ : Outcome I => if σ i = q then (1 : ℝ) else 0) =
      1 / Fintype.card I := by
  let F : I → Outcome I → ℝ := fun j σ => if σ j = q then 1 else 0
  have hsame (j : I) : mean (F j) = mean (F i) := by
    let swap : Outcome I ≃ Outcome I :=
      { toFun := fun σ => (Equiv.swap i j).trans σ
        invFun := fun σ => (Equiv.swap i j).trans σ
        left_inv := by intro σ; ext a; simp
        right_inv := by intro σ; ext a; simp }
    have hsum := Equiv.sum_comp swap (F i)
    simpa [mean, F, swap] using congrArg
      (fun x : ℝ => x / Fintype.card (Outcome I)) hsum
  have hone (σ : Outcome I) : (∑ j : I, F j σ) = 1 := by
    have h := Equiv.sum_comp σ (fun r => if r = q then (1 : ℝ) else 0)
    simpa [F] using h
  have htotal : (Fintype.card I : ℝ) * mean (F i) = 1 := by
    calc
      _ = ∑ j : I, mean (F j) := by simp [hsame]
      _ = mean (fun σ => ∑ j : I, F j σ) := (mean_sum F).symm
      _ = 1 := by rw [mean_congr _ _ hone, mean_const]
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩))
  apply (eq_div_iff hcard).mpr
  simpa [F, mul_comm] using htotal

theorem mean_indicator_last (i : I) :
    mean (fun σ : Outcome I =>
      if ∀ j : I, σ j ≤ σ i then (1 : ℝ) else 0) =
      1 / Fintype.card I := by
  have hn : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  let q : Fin (Fintype.card I) := ⟨Fintype.card I - 1, by omega⟩
  have hmax (σ : Outcome I) : (∀ j : I, σ j ≤ σ i) ↔ σ i = q := by
    constructor
    · intro h
      have hi := h (σ.symm q)
      have hi' : q.val ≤ (σ i).val := by simpa using hi
      apply Fin.ext
      have hil := (σ i).isLt
      change (σ i).val = Fintype.card I - 1
      change Fintype.card I - 1 ≤ (σ i).val at hi'
      omega
    · intro h j
      rw [h]
      change (σ j).val ≤ Fintype.card I - 1
      have hj := (σ j).isLt
      omega
  simp_rw [hmax]
  exact mean_indicator_position i q

theorem restrict_le_iff (e : I ↪ V) (σ : Outcome V) (i j : I) :
    restrict e σ i ≤ restrict e σ j ↔ σ (e i) ≤ σ (e j) := by
  rw [← not_lt, restrict_lt_iff, not_lt]

/-- Exact probability that a specified vertex completes a given finite
vertex support in the actual uniformly random global order. -/
theorem mean_indicator_last_in_finset (S : Finset V) (v : V) (hv : v ∈ S) :
    mean (fun σ : Outcome V =>
      if ∀ w ∈ S, σ w ≤ σ v then (1 : ℝ) else 0) = 1 / S.card := by
  let e : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let i : S := ⟨v, hv⟩
  let F : Outcome S → ℝ := fun τ => if ∀ j : S, τ j ≤ τ i then 1 else 0
  have hpoint (σ : Outcome V) :
      (if ∀ w ∈ S, σ w ≤ σ v then (1 : ℝ) else 0) = F (restrict e σ) := by
    have h : (∀ j : S, restrict e σ j ≤ restrict e σ i) ↔
        ∀ w ∈ S, σ w ≤ σ v := by
      simp only [restrict_le_iff, e, i, Function.Embedding.coeFn_mk]
      constructor
      · intro h w hw
        exact h ⟨w, hw⟩
      · intro h j
        exact h j.val j.property
    simp only [F, h]
  rw [mean_congr _ _ hpoint, mean_restrict]
  simpa [F, i] using mean_indicator_last i

end
end Papers.Rigidity.UniformOrders

end
end BundleSource0058

section BundleSource0059
/- Source: Papers/RigiditySelectedCoreBirth.lean -/






@[expose] public section

/-!
# Exact prefix splitting and the one-fifth core contribution

The coordinate functionals below act on the ordinary ambient edge
coefficient space.  They cut the actual scalar kernel into the selected
local K5 modes and its actual common-kernel remainder.  Every induced
prefix sees exactly the modes whose five actual vertices are present.
The same finite uniform order space as the stress ledger then gives
one fifth at each incident vertex, with no independence assumption.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode UniformOrders ModeSplitting
open scoped Classical BigOperators
variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

def SoftScalarSystem.coreCoefficient (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) (C : SelectedCore M) :
    Module.Dual ℝ (Edge (maskedGraph M.graph Finset.univ) → ℝ) :=
  let B := selectedCoreMode hgen C
  B.unitCoefficient⁻¹ •
    ((LinearMap.proj B.neighbor).comp (starCoordinates (maskedGraph M.graph Finset.univ) B.vertex))

@[simp] theorem SoftScalarSystem.coreCoefficient_on_stress
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p) (C : SelectedCore M)
    (s : StressSpace (maskedGraph M.graph Finset.univ) p) :
    L.coreCoefficient hgen C s.val = (selectedCoreMode hgen C).coefficient s := rfl

def SoftScalarSystem.coreResidual (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) :
    Submodule ℝ (Edge (maskedGraph M.graph Finset.univ) → ℝ) :=
  L.scalarKernel ⊓ nullModes (L.coreCoefficient hgen)

theorem SoftScalarSystem.coreResidual_le_kernel (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) : L.coreResidual hgen ≤ L.scalarKernel := inf_le_left

def availableSelectedCores (M : MinimalCounterexample V) (T : Finset V) :
    Finset (SelectedCore M) := Finset.univ.filter fun C => C.val.val ⊆ T

@[simp] theorem mem_availableSelectedCores
    (M : MinimalCounterexample V) (T : Finset V) (C : SelectedCore M) :
    C ∈ availableSelectedCores M T ↔ C.val.val ⊆ T := by
  simp only [availableSelectedCores,Finset.mem_filter,Finset.mem_univ,true_and]

theorem SoftScalarSystem.core_modes_biorthogonal
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (C D : SelectedCore M) :
    L.coreCoefficient hgen C (selectedCoreMode hgen D).fullStress.val =
      if C = D then 1 else 0 := by
  rw [L.coreCoefficient_on_stress]
  by_cases hCD : C = D
  · subst D
    rw [if_pos rfl]
    exact (selectedCoreMode hgen C).coefficient_fullStress hgen hp
  · rw [if_neg hCD]
    exact (selectedCoreMode hgen C).coefficient_other_fullStress
      (selectedCoreMode hgen D) (fun h => hCD (Subtype.ext h.symm))

/-- Exact equality of the original scalar-kernel prefix dimension with
the available local-mode count and the literal residual prefix. -/
theorem SoftScalarSystem.selectedCore_prefix_finrank
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    Module.finrank ℝ (supportedOn L.scalarKernel
      (vertexEdgeSet (maskedGraph M.graph Finset.univ) T)) =
      (availableSelectedCores M T).card +
      Module.finrank ℝ (supportedOn (L.coreResidual hgen)
        (vertexEdgeSet (maskedGraph M.graph Finset.univ) T)) := by
  let P := supportedOn L.scalarKernel (vertexEdgeSet (maskedGraph M.graph Finset.univ) T)
  have hmem (C : SelectedCore M) (hC : C ∈ availableSelectedCores M T) :
      (selectedCoreMode hgen C).fullStress.val ∈ P := by
    refine ⟨(selectedCoreMode hgen C).fullStress_mem_kernel L,?_⟩
    intro e he
    by_contra hn
    exact he ((selectedCoreMode hgen C).fullStress_supported_in_prefix T
      ((mem_availableSelectedCores M T C).mp hC) e hn)
  have habsent (x : Edge (maskedGraph M.graph Finset.univ) → ℝ) (hx : x ∈ P)
      (C : SelectedCore M) (hC : C ∉ availableSelectedCores M T) :
      L.coreCoefficient hgen C x = 0 := by
    let s : StressSpace (maskedGraph M.graph Finset.univ) p :=
      ⟨x,L.scalarKernel_le_stress hx.1⟩
    have hsupport : CoefficientsSupportedOn (maskedGraph M.graph Finset.univ) T x := by
      intro e he v hv
      by_contra hvT
      exact he (hx.2 e (fun heT => hvT (heT v hv)))
    exact (selectedCoreMode hgen C).coefficient_zero_on_incomplete_prefix L hgen hp T
      s hx.1 hsupport (fun h => hC ((mem_availableSelectedCores M T C).mpr h))
  have h := prefix_finrank P (L.coreCoefficient hgen)
    (fun C => (selectedCoreMode hgen C).fullStress.val) (availableSelectedCores M T)
    (by
      intro C D
      have hh := L.core_modes_biorthogonal hgen hp C D
      by_cases hCD : C = D
      · rw [if_pos hCD] at hh ⊢
        exact hh
      · rw [if_neg hCD] at hh ⊢
        exact hh) hmem habsent
  have heq : (P ⊓ nullModes (L.coreCoefficient hgen) :
      Submodule ℝ (Edge (maskedGraph M.graph Finset.univ) → ℝ)) =
      supportedOn (L.coreResidual hgen) (vertexEdgeSet (maskedGraph M.graph Finset.univ) T) := by
    ext x
    change ((x ∈ L.scalarKernel ∧ _) ∧ _) ↔ ((x ∈ L.scalarKernel ∧ _) ∧ _)
    tauto
  rw [heq] at h
  exact h

theorem selectedCore_indicator_birth
    (C : SelectedCore M) (σ : Outcome V) (v : V) :
    (if C.val.val ⊆ verticesThrough σ v then (1 : ℝ) else 0) -
      (if C.val.val ⊆ verticesBefore σ v then (1 : ℝ) else 0) =
      if v ∈ C.val.val then
        (if ∀ w ∈ C.val.val, σ w ≤ σ v then (1 : ℝ) else 0) else 0 := by
  have hthrough : C.val.val ⊆ verticesThrough σ v ↔ ∀ w ∈ C.val.val, σ w ≤ σ v := by
    simp only [Finset.subset_iff,mem_verticesThrough]
  have hbefore : C.val.val ⊆ verticesBefore σ v ↔ ∀ w ∈ C.val.val, σ w < σ v := by
    simp only [Finset.subset_iff,mem_verticesBefore]
  by_cases hv : v ∈ C.val.val
  · have hn : ¬ C.val.val ⊆ verticesBefore σ v := by
      intro hs
      exact (lt_irrefl (σ v)) ((hbefore.mp hs) v hv)
    simp only [hv,if_pos,hn,if_false,hthrough,sub_zero]
  · have heq : (∀ w ∈ C.val.val, σ w ≤ σ v) ↔ ∀ w ∈ C.val.val, σ w < σ v := by
      constructor
      · intro hs w hw
        exact lt_of_le_of_ne (hs w hw) (fun he => hv (σ.injective he ▸ hw))
      · intro hs w hw
        exact (hs w hw).le
    simp only [hv,if_false,hthrough,hbefore,heq,sub_self]

theorem selectedCore_count_birth
    (M : MinimalCounterexample V) (σ : Outcome V) (v : V) :
    ((availableSelectedCores M (verticesThrough σ v)).card : ℝ) -
      (availableSelectedCores M (verticesBefore σ v)).card =
      ∑ C : SelectedCore M, if v ∈ C.val.val then
        (if ∀ w ∈ C.val.val, σ w ≤ σ v then (1 : ℝ) else 0) else 0 := by
  simp only [availableSelectedCores,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun C _ => selectedCore_indicator_birth C σ v

theorem mean_selectedCore_count_birth
    (M : MinimalCounterexample V) (v : V) :
    mean (fun σ : Outcome V =>
      ((availableSelectedCores M (verticesThrough σ v)).card : ℝ) -
        (availableSelectedCores M (verticesBefore σ v)).card) =
      (selectedIncidentCount M v : ℝ) / 5 := by
  rw [mean_congr _ _ (fun σ => selectedCore_count_birth M σ v),mean_sum]
  have hterm (C : SelectedCore M) :
      mean (fun σ : Outcome V => if v ∈ C.val.val then
        (if ∀ w ∈ C.val.val, σ w ≤ σ v then (1 : ℝ) else 0) else 0) =
      if v ∈ C.val.val then (1 : ℝ)/5 else 0 := by
    by_cases hv : v ∈ C.val.val
    · simp only [hv,if_pos]
      rw [mean_indicator_last_in_finset C.val.val v hv,C.property.1]
      norm_num
    · simp only [hv,if_false,mean_const]
  simp only [hterm]
  simp only [selectedIncidentCount,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro C _
  split_ifs <;> norm_num

/-- Equation (7), including the exact one-fifth contribution for every
incident selected core in the original uniformly random vertex order. -/
theorem SoftScalarSystem.selectedCore_stressDimensionContribution
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (v : V) :
    stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel v =
      (selectedIncidentCount M v : ℝ) / 5 +
      stressDimensionContribution (maskedGraph M.graph Finset.univ) (L.coreResidual hgen) v := by
  let G := maskedGraph M.graph Finset.univ
  have hpoint (σ : Outcome V) :
      (Module.finrank ℝ (stressThrough G L.scalarKernel σ v) : ℝ) -
        Module.finrank ℝ (stressBefore G L.scalarKernel σ v) =
      (((availableSelectedCores M (verticesThrough σ v)).card : ℝ) -
        (availableSelectedCores M (verticesBefore σ v)).card) +
      ((Module.finrank ℝ (stressThrough G (L.coreResidual hgen) σ v) : ℝ) -
        Module.finrank ℝ (stressBefore G (L.coreResidual hgen) σ v)) := by
    have ht (W : Submodule ℝ (Edge G → ℝ)) :
        Module.finrank ℝ (stressThrough G W σ v) =
          Module.finrank ℝ (supportedOn W (vertexEdgeSet G (verticesThrough σ v))) :=
      congrArg (fun A : Set (Edge G) => Module.finrank ℝ (supportedOn W A))
        (edgesThrough_eq_vertexEdgeSet G σ v)
    have hb (W : Submodule ℝ (Edge G → ℝ)) :
        Module.finrank ℝ (stressBefore G W σ v) =
          Module.finrank ℝ (supportedOn W (vertexEdgeSet G (verticesBefore σ v))) :=
      congrArg (fun A : Set (Edge G) => Module.finrank ℝ (supportedOn W A))
        (edgesBefore_eq_vertexEdgeSet G σ v)
    have hprefix (T : Finset V) :
        Module.finrank ℝ (supportedOn L.scalarKernel (vertexEdgeSet G T)) =
          (availableSelectedCores M T).card +
          Module.finrank ℝ (supportedOn (L.coreResidual hgen) (vertexEdgeSet G T)) :=
      L.selectedCore_prefix_finrank hgen hp T
    have hT := (ht L.scalarKernel).trans (hprefix (verticesThrough σ v))
    have hB := (hb L.scalarKernel).trans (hprefix (verticesBefore σ v))
    rw [hT, hB, ht, hb]
    push_cast
    ring
  unfold stressDimensionContribution
  rw [mean_congr _ _ hpoint,mean_add,mean_selectedCore_count_birth M v]

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0059

section BundleSource0060
/- Source: Papers/RigidityScalarStarRank.lean -/






@[expose] public section

/-!
# The star rank after imposing the actual soft scalar equations

Vertex-indexed star coordinates have the same image dimension as the
ordinary incident-edge restriction. Their dual row space is exactly
the span used to define the paper's observer credit. Dual annihilator
rank-nullity therefore proves the first rank loss in equation (8).
-/

noncomputable section
namespace Papers.Rigidity.BarJoint
open SupportedCode
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

theorem starCoordinates_eq_zero_iff (G : SimpleGraph V) (v : V)
    (a : Edge G → ℝ) :
    starCoordinates G v a = 0 ↔ starRestriction G v a = 0 := by
  constructor
  · intro h
    ext e
    have he := congrFun h (incidentOther G v e)
    change a e.val = 0
    simpa only [starCoordinates_incidentOther,Pi.zero_apply] using he
  · intro h
    ext w
    by_cases hadj : G.Adj v w
    · rw [starCoordinates_of_adj _ _ _ _ hadj]
      exact congrFun h ⟨⟨s(v,w),hadj⟩,Sym2.mem_mk_left v w⟩
    · exact starCoordinates_of_not_adj G v w a hadj

theorem starCoordinates_range_finrank (G : SimpleGraph V) (v : V)
    (W : Submodule ℝ (Edge G → ℝ)) :
    Module.finrank ℝ ((starCoordinates G v).domRestrict W).range =
      Module.finrank ℝ (stressStarCode G v W) := by
  have hk : ((starCoordinates G v).domRestrict W).ker =
      ((starRestriction G v).domRestrict W).ker := by
    ext a
    exact starCoordinates_eq_zero_iff G v a.val
  have hC := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := W) (V₂ := V → ℝ) ((starCoordinates G v).domRestrict W)
  have hS := LinearMap.finrank_range_add_finrank_ker
    (K := ℝ) (V := W) (V₂ := IncidentEdge G v → ℝ)
    ((starRestriction G v).domRestrict W)
  rw [hk] at hC
  rw [LinearMap.range_domRestrict] at hS
  change Module.finrank ℝ ((starCoordinates G v).domRestrict W).range =
    Module.finrank ℝ (W.map (starRestriction G v))
  omega

theorem starCoordinates_map_finrank (G : SimpleGraph V) (v : V)
    (W : Submodule ℝ (Edge G → ℝ)) :
    Module.finrank ℝ (W.map (starCoordinates G v)) =
      Module.finrank ℝ (stressStarCode G v W) := by
  rw [← LinearMap.range_domRestrict]
  exact starCoordinates_range_finrank G v W

def stressStarMeasurement (G : SimpleGraph V) (p : Placement V 3) (v : V) :
    StressSpace G p →ₗ[ℝ] (V → ℝ) := (starCoordinates G v).domRestrict (StressSpace G p)

end Papers.Rigidity.BarJoint

namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode AnnihilatorRank VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V] {M : MinimalCounterexample V} {p : Placement V 3}

theorem SoftScalarSystem.hyperStarSpan_coannihilator (L : SoftScalarSystem M p)
    (h : Hypervertex M.graph) :
    (L.hyperStarSpan h).dualCoannihilator =
      (stressStarMeasurement (maskedGraph M.graph Finset.univ) p h.val).ker := by
  ext s
  rw [Submodule.mem_dualCoannihilator,LinearMap.mem_ker]
  constructor
  · intro hs
    ext w
    exact hs _ (Submodule.subset_span ⟨w,rfl⟩)
  · intro hs
    have hle : L.hyperStarSpan h ≤
        ((Module.Dual.eval ℝ (StressSpace (maskedGraph M.graph Finset.univ) p)) s).ker := by
      apply Submodule.span_le.mpr
      rintro φ ⟨w,rfl⟩
      exact congrFun hs w
    intro φ hφ
    exact hle hφ

theorem SoftScalarSystem.hyperStarSpan_eq_readable (L : SoftScalarSystem M p)
    (h : Hypervertex M.graph) :
    L.hyperStarSpan h = readable
      (stressStarMeasurement (maskedGraph M.graph Finset.univ) p h.val) := by
  rw [readable,← L.hyperStarSpan_coannihilator h,
    Subspace.dualCoannihilator_dualAnnihilator_eq]

theorem SoftScalarSystem.scalarKernel_star_range (L : SoftScalarSystem M p)
    (v : V) :
    ((stressStarMeasurement (maskedGraph M.graph Finset.univ) p v).domRestrict L.scalarSpan.dualCoannihilator).range =
        L.scalarKernel.map (starCoordinates (maskedGraph M.graph Finset.univ) v) := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.val.val,⟨x.val,x.property,rfl⟩,rfl⟩
  · rintro ⟨x,⟨s,hs,rfl⟩,rfl⟩
    exact ⟨⟨s,hs⟩,rfl⟩

/-- Imposing the soft point-pin equations removes exactly the readable
scalar dimension from each hypervertex star. -/
theorem SoftScalarSystem.scalarKernel_star_rank (L : SoftScalarSystem M p)
    (h : Hypervertex M.graph) :
    Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        L.scalarKernel) + L.hyperCredit h =
      Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        (StressSpace (maskedGraph M.graph Finset.univ) p)) := by
  have ha := finrank_restrict_coannihilator
    (stressStarMeasurement (maskedGraph M.graph Finset.univ) p h.val) L.scalarSpan
  rw [L.scalarKernel_star_range,starCoordinates_map_finrank,
    ← L.hyperStarSpan_eq_readable] at ha
  change _ + L.hyperCredit h =
    Module.finrank ℝ ((starCoordinates (maskedGraph M.graph Finset.univ) h.val).domRestrict (StressSpace (maskedGraph M.graph Finset.univ) p)).range at ha
  rw [starCoordinates_range_finrank] at ha
  exact ha

theorem SoftScalarSystem.scalarKernel_star_rank_add_drop (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) (h : Hypervertex M.graph) :
    Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        L.scalarKernel) + L.hyperCredit h + deletionRankDrop M.graph h.val =
      M.graph.degree h.val := by
  rw [L.scalarKernel_star_rank,maskedGraph_univ]
  exact stressStar_finrank_add_deletionRankDrop M.graph p hgen h.val

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0060

section BundleSource0061
/- Source: Papers/RigidityHypervertexContribution.lean -/






@[expose] public section

/-!
# Equation (8): the actual hypervertex contribution

The selected core coordinates are readable on exactly their incident
hypervertex stars. Biorthogonal actual modes remove precisely that many
dimensions. Combined with the scalar-annihilator rank identity, the
one-fifth prefix birth formula, and Corollary 2.2, this gives all credits
in the paper's hypervertex estimate.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads
open BarJoint SupportedCode UniformOrders ModeSplitting VertexPin
open scoped Classical BigOperators
variable {V : Type} [Fintype V] {M : MinimalCounterexample V} {p : Placement V 3}

theorem SoftScalarSystem.coreResidual_star_rank (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (h : Hypervertex M.graph) :
    Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        (L.coreResidual hgen)) + selectedIncidentCount M h.val =
      Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        L.scalarKernel) := by
  let G := maskedGraph M.graph Finset.univ
  let f : L.scalarKernel →ₗ[ℝ] (V → ℝ) :=
    (starCoordinates G h.val).domRestrict L.scalarKernel
  let ρ : SelectedCore M → L.scalarKernel →ₗ[ℝ] ℝ := fun C =>
    (L.coreCoefficient hgen C).comp L.scalarKernel.subtype
  let s : SelectedCore M → L.scalarKernel := fun C =>
    ⟨(selectedCoreMode hgen C).fullStress.val,
      (selectedCoreMode hgen C).fullStress_mem_kernel L⟩
  let A : Finset (SelectedCore M) := Finset.univ.filter fun C => h.val ∈ C.val.val
  have hdual (C D : SelectedCore M) : ρ C (s D) = if C = D then 1 else 0 :=
    L.core_modes_biorthogonal hgen hp C D
  have hread (C : SelectedCore M) (hC : C ∈ A) (x : L.scalarKernel)
      (hx : f x = 0) : ρ C x = 0 := by
    have hhC : h.val ∈ C.val.val := (Finset.mem_filter.mp hC).2
    let B := selectedCoreMode hgen C
    obtain ⟨c,hc,hread⟩ := B.hypervertex_reads_coefficient L hgen hp h.val hhC h.property
    let a : StressSpace G p := ⟨x.val,L.scalarKernel_le_stress x.property⟩
    have he := hread a x.property
    have hz := congrFun hx B.vertex
    change starCoordinates G h.val x.val B.vertex = 0 at hz
    rw [hz] at he
    have hco : B.coefficient a = 0 := (mul_eq_zero.mp he.symm).resolve_left hc
    exact hco
  have hinvisible (C : SelectedCore M) (hC : C ∉ A) : f (s C) = 0 := by
    have hhC : h.val ∉ C.val.val := by simpa only [A,Finset.mem_filter,Finset.mem_univ,
      true_and] using hC
    let B := selectedCoreMode hgen C
    change starCoordinates G h.val B.fullStress.val = 0
    ext w
    rw [B.fullStress_star]
    apply starCoordinates_of_not_adj
    intro hadj
    exact hhC (Finset.mem_inter.mp hadj.2.1).1
  have hd := measured_nullModes_finrank f ρ s A (by
    intro C D
    have hh := hdual C D
    by_cases hCD : C = D
    · rw [if_pos hCD] at hh ⊢
      exact hh
    · rw [if_neg hCD] at hh ⊢
      exact hh) hread hinvisible
  have himage : (f.domRestrict (nullModes ρ)).range =
      (L.coreResidual hgen).map (starCoordinates G h.val) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val.val,⟨x.val.property,x.property⟩,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨⟨x,hx.1⟩,hx.2⟩,rfl⟩
  rw [himage,starCoordinates_map_finrank] at hd
  change _ + A.card =
    Module.finrank ℝ ((starCoordinates G h.val).domRestrict L.scalarKernel).range at hd
  rw [starCoordinates_range_finrank] at hd
  exact hd

/-- The rank parameter R in equation (8) is the actual residual star
image dimension, and its additive identity has no truncated subtraction. -/
theorem SoftScalarSystem.coreResidual_star_rank_add_drop (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (h : Hypervertex M.graph) :
    Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
        (L.coreResidual hgen)) + selectedIncidentCount M h.val + L.hyperCredit h +
        deletionRankDrop M.graph h.val = M.graph.degree h.val := by
  rw [L.coreResidual_star_rank hgen hp]
  exact L.scalarKernel_star_rank_add_drop hgen h

/-- Equation (8), for every actual hypervertex of the original minimal
counterexample and the literal fixed scalar-annihilator stress space. -/
theorem SoftScalarSystem.hypervertex_contribution_bound (L : SoftScalarSystem M p)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p)
    (h : Hypervertex M.graph) :
    (L.hyperCredit h : ℝ) / 2 + 3 * (selectedIncidentCount M h.val : ℝ) / 10 +
        ((deletionRankDrop M.graph h.val : ℝ) - 6) / 2 ≤
      (M.graph.degree h.val : ℝ) / 2 -
        stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel h.val - 3 := by
  let R := Module.finrank ℝ (stressStarCode (maskedGraph M.graph Finset.univ) h.val
    (L.coreResidual hgen))
  have hstar := L.coreResidual_star_rank_add_drop hgen hp h
  have hstarR := congrArg (fun n : ℕ => (n : ℝ)) hstar
  push_cast at hstarR
  have hdim : (M.graph.degree h.val : ℝ) = (R : ℝ) +
      deletionRankDrop M.graph h.val + L.hyperCredit h + selectedIncidentCount M h.val := by
    dsimp [R]
    linarith
  have hb := Budget.hypervertex_contribution_lower_bound
    (M.graph.degree h.val) (deletionRankDrop M.graph h.val)
    (L.hyperCredit h) (selectedIncidentCount M h.val) R (Nat.cast_nonneg _) hdim
  have hexp := corollary_two_two_subspace (maskedGraph M.graph Finset.univ) p hp h.val
    (L.coreResidual hgen) ((L.coreResidual_le_kernel hgen).trans L.scalarKernel_le_stress)
  have hbound : bound 4 R = Budget.supportedBound 4 R := by
    simp only [bound,Budget.supportedBound,Nat.cast_ofNat]
  change _ ≤ bound 4 R at hexp
  rw [hbound] at hexp
  rw [L.selectedCore_stressDimensionContribution hgen hp h.val]
  linarith

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0061

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0061/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0061.json"

section BundleSource0062
/- Source: Papers/RigidityGlobalBudget.lean -/





@[expose] public section

/-!
# The final global rigidity account

Every summand here is attached to the original graph: actual scalar
observers, actual maximal bodies, actual selected cores, and actual
exceptional scalar components. The double counts identify the local
credits exactly. The final contradiction uses the proved local bounds
and the exact scalar-annihilator rank ledger.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint VertexPin SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]
variable {M : MinimalCounterexample V} {p : Placement V 3}

theorem sum_subtype_as_indicator {I A : Type*} [Fintype I] [AddCommMonoid A]
    (P : I → Prop) (f : I → A) :
    (∑ x : {x : I // P x}, f x.val) = ∑ x : I, if P x then f x else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp) f).symm

theorem sum_indicator_predicate {I : Type*} [Fintype I] (P : I → Prop) (c : ℝ) :
    (∑ x : I, if P x then c else 0) =
      ((Finset.univ.filter P).card : ℝ) * c := by
  rw [← Finset.sum_filter]
  simp

theorem sum_largeBodies_eq_sum (f : Body M.graph → ℝ)
    (hzero : ∀ C, ¬ 5 ≤ C.val.card → f C = 0) :
    (∑ C : LargeBody M.graph, f C.val) = ∑ C : Body M.graph, f C := by
  trans ∑ C : Body M.graph, if 5 ≤ C.val.card then f C else 0
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (Finset.univ.filter (fun C : Body M.graph => 5 ≤ C.val.card)) (by simp) f).symm
  · apply Finset.sum_congr rfl
    intro C _
    by_cases hC : 5 ≤ C.val.card
    · rw [if_pos hC]
    · rw [if_neg hC,hzero C hC]

theorem sum_selectedCores_eq_sum (f : Body M.graph → ℝ)
    (hzero : ∀ C, ¬ IsSelectedCore M C → f C = 0) :
    (∑ C : SelectedCore M, f C.val) = ∑ C : Body M.graph, f C := by
  trans ∑ C : Body M.graph, if IsSelectedCore M C then f C else 0
  · exact sum_subtype_as_indicator (IsSelectedCore M) f
  · apply Finset.sum_congr rfl
    intro C _
    by_cases hC : IsSelectedCore M C
    · rw [if_pos hC]
    · rw [if_neg hC,hzero C hC]

/-- Each exceptional scalar component has exactly one hypervertex
observer, so the sum of the local exceptional counts is its actual
global count in Proposition 6.6. -/
theorem SoftScalarSystem.sum_exceptionalCountAt
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p) :
    (∑ h : Hypervertex M.graph, exceptionalCountAt L h) =
      ObserverCover.exceptionalCount L.graph L.seed := by
  have hone (c : L.graph.ConnectedComponent) :
      (∑ h : Hypervertex M.graph, if L.observers c = {Sum.inl h} then 1 else 0) =
        if (L.observers c).card = 1 then 1 else 0 := by
    by_cases hc : (L.observers c).card = 1
    · obtain ⟨h,hh⟩ := L.sole_observer_is_hypervertex hgen hp hpin c hc
      simp [hc,hh,Finset.singleton_inj]
    · have hnone (h : Hypervertex M.graph) : L.observers c ≠ {Sum.inl h} := by
        intro heq
        exact hc (by rw [heq]; simp)
      simp [hc,hnone]
  calc
    _ = ∑ c : L.graph.ConnectedComponent, ∑ h : Hypervertex M.graph,
        if L.observers c = {Sum.inl h} then 1 else 0 := by
          simp only [exceptionalCountAt,exceptionalComponentsAt,
            Finset.card_eq_sum_ones,Finset.sum_filter]
          exact Finset.sum_comm
    _ = ∑ c : L.graph.ConnectedComponent, if (L.observers c).card = 1 then 1 else 0 :=
      Finset.sum_congr rfl (fun c _ => hone c)
    _ = ObserverCover.exceptionalCount L.graph L.seed := by
      change (∑ c : L.graph.ConnectedComponent,
        if (ObserverCover.observers L.graph L.seed c).card = 1 then (1 : ℕ) else 0) =
        Nat.card {c : L.graph.ConnectedComponent //
          (ObserverCover.observers L.graph L.seed c).card = 1}
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact Finset.sum_boole
        (fun c : L.graph.ConnectedComponent =>
          (ObserverCover.observers L.graph L.seed c).card = 1) Finset.univ

/-- Count selected-core/hypervertex incidences in either order. -/
theorem sum_selectedIncidentCount (M : MinimalCounterexample V) :
    (∑ h : Hypervertex M.graph, selectedIncidentCount M h.val) =
      ∑ C : SelectedCore M, (bodyHyperVertices M C.val).card := by
  have hbody (C : SelectedCore M) :
      (∑ h : Hypervertex M.graph, if h.val ∈ C.val.val then 1 else 0) =
        (bodyHyperVertices M C.val).card := by
    have hsum : (∑ h : Hypervertex M.graph, if h.val ∈ C.val.val then (1 : ℕ) else 0) =
        ∑ v : V, if IsHypervertex M.graph v then (if v ∈ C.val.val then 1 else 0) else 0 :=
      sum_subtype_as_indicator (IsHypervertex M.graph)
        (fun v : V => if v ∈ C.val.val then (1 : ℕ) else 0)
    rw [hsum]
    have heq (v : V) :
        (if IsHypervertex M.graph v then (if v ∈ C.val.val then 1 else 0) else 0) =
          if v ∈ bodyHyperVertices M C.val then 1 else 0 := by
      by_cases hh : IsHypervertex M.graph v <;> by_cases hv : v ∈ C.val.val <;>
        simp [bodyHyperVertices,hh,hv]
    calc
      _ = ∑ v : V, if v ∈ bodyHyperVertices M C.val then (1 : ℕ) else 0 :=
        Finset.sum_congr rfl (fun v _ => heq v)
      _ = (Finset.univ.filter (fun v : V => v ∈ bodyHyperVertices M C.val)).card :=
        Finset.sum_boole _ _
      _ = _ := by rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc
    _ = ∑ C : SelectedCore M, ∑ h : Hypervertex M.graph,
        if h.val ∈ C.val.val then 1 else 0 := by
          simp only [selectedIncidentCount,Finset.card_eq_sum_ones,Finset.sum_filter]
          exact Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun C _ => hbody C)

theorem sum_bodyHyperCredit (M : MinimalCounterexample V) :
    (∑ C : Body M.graph, bodyHyperCredit M C) =
      ∑ h : Hypervertex M.graph, 3 * (selectedIncidentCount M h.val : ℝ) / 10 := by
  have hcount : (∑ h : Hypervertex M.graph, (selectedIncidentCount M h.val : ℝ)) =
      ∑ C : SelectedCore M, ((bodyHyperVertices M C.val).card : ℝ) := by
    exact_mod_cast sum_selectedIncidentCount M
  calc
    _ = ∑ C : SelectedCore M, 3 * ((bodyHyperVertices M C.val).card : ℝ) / 10 := by
      exact (sum_subtype_as_indicator (IsSelectedCore M)
        (fun C : Body M.graph => 3 * ((bodyHyperVertices M C).card : ℝ) / 10)).symm
    _ = 3 * (∑ C : SelectedCore M, ((bodyHyperVertices M C.val).card : ℝ)) / 10 := by
      rw [← Finset.sum_div,← Finset.mul_sum]
    _ = 3 * (∑ h : Hypervertex M.graph, (selectedIncidentCount M h.val : ℝ)) / 10 :=
      by rw [hcount]
    _ = _ := by rw [Finset.mul_sum,Finset.sum_div]

theorem bodyShortfall_zero_of_not_selected
    (M : MinimalCounterexample V) (C : Body M.graph) (hC : ¬ IsSelectedCore M C) :
    bodyShortfall M C = 0 := by
  unfold bodyShortfall
  split_ifs with he
  · have hb : (bodyTypeBVertices M C).card = 0 := by
      by_contra h
      exact hC ⟨he.1,Or.inr (Finset.card_pos.mp (by omega))⟩
    simp [hb,coreShortfall]
  · rfl

/-- Each positive core shortfall is assigned to its unique actual
hypervertex, with the coefficient prescribed in Section 7.4. -/
theorem selected_bodyShortfall_eq_hyper_sum
    (M : MinimalCounterexample V) (C : SelectedCore M) :
    bodyShortfall M C.val = ∑ h : Hypervertex M.graph,
      ((if bodyHyperVertices M C.val = {h.val} ∧ bodySoftVertices M C.val = ∅ ∧
          (bodyTypeBVertices M C.val).card = 3 then (1 / 4 : ℝ) else 0) +
      (if bodyHyperVertices M C.val = {h.val} ∧ bodySoftVertices M C.val = ∅ ∧
          (bodyTypeBVertices M C.val).card = 4 then (1 / 2 : ℝ) else 0)) := by
  by_cases he : (bodyHyperVertices M C.val).card = 1 ∧ (bodySoftVertices M C.val).card = 0
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp he.1
    have hmem : v ∈ bodyHyperVertices M C.val := by rw [hv]; simp
    have hh := (Finset.mem_filter.mp hmem).2
    let h : Hypervertex M.graph := ⟨v,hh⟩
    have hsoft : bodySoftVertices M C.val = ∅ := Finset.card_eq_zero.mp he.2
    have hiff (k : Hypervertex M.graph) : bodyHyperVertices M C.val = {k.val} ↔ k = h := by
      rw [hv,Finset.singleton_inj]
      constructor
      · intro heq
        exact Subtype.ext heq.symm
      · intro heq
        exact (congrArg Subtype.val heq).symm
    by_cases hb3 : (bodyTypeBVertices M C.val).card = 3
    · simp [bodyShortfall,C.property.1,he.1,he.2,coreShortfall,hb3,hiff,hsoft]
    · by_cases hb4 : (bodyTypeBVertices M C.val).card = 4
      · simp [bodyShortfall,C.property.1,he.1,he.2,coreShortfall,hb3,hb4,hiff,hsoft]
      · simp [bodyShortfall,C.property.1,he.1,he.2,coreShortfall,hb3,hb4,hiff,hsoft]
  · have hzero : bodyShortfall M C.val = 0 := by
      unfold bodyShortfall
      rw [if_neg (fun h => he h.2)]
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro h _
    by_cases hH : bodyHyperVertices M C.val = {h.val}
    · have hS : bodySoftVertices M C.val ≠ ∅ := by
        intro heq
        exact he ⟨by rw [hH]; simp,by rw [heq]; simp⟩
      simp [hH,hS]
    · simp [hH]

theorem sum_bodyShortfall (M : MinimalCounterexample V) :
    (∑ C : Body M.graph, bodyShortfall M C) = ∑ h : Hypervertex M.graph,
      ((chargedCoreCountAt M h.val 3 : ℝ) / 4 + (chargedCoreCountAt M h.val 4 : ℝ) / 2) := by
  rw [← sum_selectedCores_eq_sum (M := M) (bodyShortfall M) (bodyShortfall_zero_of_not_selected M)]
  simp_rw [selected_bodyShortfall_eq_hyper_sum M]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  unfold chargedCoreCountAt
  ring

theorem small_body_credits_zero (M : MinimalCounterexample V) (C : Body M.graph)
    (hsmall : ¬ 5 ≤ C.val.card) :
    bodyBaseCredit M C = 0 ∧ bodyHyperCredit M C = 0 ∧ bodyShortfall M C = 0 := by
  have hfour : C.val.card = 4 := by have := C.property.1; omega
  have hn : ¬ IsSelectedCore M C := fun h => by have := h.1; omega
  simp [bodyBaseCredit,bodyHyperCredit,bodyShortfall,hfour,hn]

/-- Reindexing the per-body inequalities produces exactly the selected
incidence and exceptional-core charges paid by the hypervertex account. -/
theorem SoftScalarSystem.total_body_budget
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    (∑ C : LargeBody M.graph, (L.largeRank C : ℝ) / 2) ≤
      (∑ C : Body M.graph, bodyBaseCredit M C) +
      (∑ h : Hypervertex M.graph, 3 * (selectedIncidentCount M h.val : ℝ) / 10) +
      (∑ h : Hypervertex M.graph,
        ((chargedCoreCountAt M h.val 3 : ℝ) / 4 + (chargedCoreCountAt M h.val 4 : ℝ) / 2)) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (LargeBody M.graph)))
    (fun C _ => L.large_body_budget hgen hp C)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at h
  rw [sum_largeBodies_eq_sum (M := M) (bodyBaseCredit M)
      (fun C hc => (small_body_credits_zero M C hc).1),
    sum_largeBodies_eq_sum (M := M) (bodyHyperCredit M)
      (fun C hc => (small_body_credits_zero M C hc).2.1),
    sum_largeBodies_eq_sum (M := M) (bodyShortfall M)
      (fun C hc => (small_body_credits_zero M C hc).2.2),
    sum_bodyHyperCredit,sum_bodyShortfall] at h
  exact h

theorem SoftScalarSystem.remaining_charge_le_residual
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph) :
    (exceptionalCountAt L h : ℝ) / 2 + (chargedCoreCountAt M h.val 3 : ℝ) / 4 +
      (chargedCoreCountAt M h.val 4 : ℝ) / 2 ≤
        ((deletionRankDrop M.graph h.val : ℝ) - 6) / 2 := by
  have hnat := L.remaining_hypervertex_charges hgen hp h
  have hreal : (12 : ℝ) + 2 * exceptionalCountAt L h + chargedCoreCountAt M h.val 3 +
      2 * chargedCoreCountAt M h.val 4 ≤ 2 * deletionRankDrop M.graph h.val := by
    exact_mod_cast hnat
  linarith

/-- The actual hypervertex contribution pays scalar observation,
selected-core incidences, and every remaining exceptional charge. -/
theorem SoftScalarSystem.hypervertex_excess_pays
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) (h : Hypervertex M.graph) :
    (L.hyperCredit h : ℝ) / 2 + 3 * (selectedIncidentCount M h.val : ℝ) / 10 +
      (exceptionalCountAt L h : ℝ) / 2 +
      ((chargedCoreCountAt M h.val 3 : ℝ) / 4 + (chargedCoreCountAt M h.val 4 : ℝ) / 2) ≤
        L.vertexExcess h.val := by
  have hcontribution := L.hypervertex_contribution_bound hgen hp h
  have hcharge := L.remaining_charge_le_residual hgen hp h
  change _ ≤ (M.graph.degree h.val : ℝ) / 2 -
    stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel h.val - 3
  linarith

theorem SoftScalarSystem.observer_cost_le_total_excess
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    (∑ h : Hypervertex M.graph, (L.hyperCredit h : ℝ) / 2) +
      (∑ C : LargeBody M.graph, (L.largeRank C : ℝ) / 2) +
      (∑ h : Hypervertex M.graph, (exceptionalCountAt L h : ℝ) / 2) ≤
        ∑ v : V, L.vertexExcess v := by
  have hbody := L.total_body_budget hgen hp
  have htwo := L.two_body_total_excess_bound hgen hp
  have hhyper := Finset.sum_le_sum (s := (Finset.univ : Finset (Hypervertex M.graph)))
    (fun h _ => L.hypervertex_excess_pays hgen hp h)
  simp only [Finset.sum_add_distrib] at hbody hhyper
  have hpartition : (∑ v : V, L.vertexExcess v) =
      (∑ v : V, if IsHypervertex M.graph v then 0 else L.vertexExcess v) +
      (∑ h : Hypervertex M.graph, L.vertexExcess h.val) := by
    rw [sum_subtype_as_indicator,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : IsHypervertex M.graph v <;> simp [hv]
  rw [hpartition]
  linarith

/-- Proposition 6.6 closes the global account for the actual scalar
span, with the exceptional components counted exactly once. -/
theorem SoftScalarSystem.scalar_rank_le_total_excess
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p) :
    (Module.finrank ℝ L.scalarSpan : ℝ) ≤ ∑ v : V, L.vertexExcess v := by
  have hnat := L.proposition_six_six hgen hp hpin
  have hreal : 2 * (Module.finrank ℝ L.scalarSpan : ℝ) ≤
      (∑ h : Hypervertex M.graph, (L.hyperCredit h : ℝ)) +
      (∑ C : LargeBody M.graph, (L.largeRank C : ℝ)) +
      (ObserverCover.exceptionalCount L.graph L.seed : ℝ) := by exact_mod_cast hnat
  have hcount : (ObserverCover.exceptionalCount L.graph L.seed : ℝ) =
      ∑ h : Hypervertex M.graph, (exceptionalCountAt L h : ℝ) := by
    exact_mod_cast (L.sum_exceptionalCountAt hgen hp hpin).symm
  rw [hcount] at hreal
  apply le_trans _ (L.observer_cost_le_total_excess hgen hp)
  rw [← Finset.sum_div,← Finset.sum_div,← Finset.sum_div]
  linarith

theorem SoftScalarSystem.total_excess_ledger
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p) :
    (genericRigidityRank M.graph 3 : ℝ) + Module.finrank ℝ L.scalarSpan =
      3 * (Fintype.card V : ℝ) + ∑ v : V, L.vertexExcess v := by
  have hwhole : maskedGraph M.graph Finset.univ = M.graph := by
    ext a b
    simp [maskedGraph]
  have hdegree (v : V) : (maskedGraph M.graph Finset.univ).degree v = M.graph.degree v := by
    rw [hwhole]
  have hrank : genericRigidityRank (maskedGraph M.graph Finset.univ) 3 =
      genericRigidityRank M.graph 3 := by rw [hwhole]
  have h := scalar_annihilator_rank_ledger (maskedGraph M.graph Finset.univ) p hgen L.scalarSpan
  change (genericRigidityRank (maskedGraph M.graph Finset.univ) 3 : ℝ) =
    (∑ v : V, (((maskedGraph M.graph Finset.univ).degree v : ℝ) / 2 -
      stressDimensionContribution (maskedGraph M.graph Finset.univ) L.scalarKernel v)) -
      Module.finrank ℝ L.scalarSpan at h
  simp only [hrank,hdegree,Finset.sum_sub_distrib] at h
  simp only [SoftScalarSystem.vertexExcess,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  linarith

/-- The final contradiction is an actual rigidity-rank contradiction.
There is no numerical budget or geometric conclusion among its premises. -/
theorem SoftScalarSystem.contradiction
    (L : SoftScalarSystem M p) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hpin : PairPinGraph.UniversalPinGeneric (Body M.graph) p) : False := by
  have hcost := L.scalar_rank_le_total_excess hgen hp hpin
  have hledger := L.total_excess_ledger hgen
  have hcard := M.eight_le_card
  have hcomplete := genericCompleteRank_add_six (V := V) (by omega)
  have hle : genericRigidityRank M.graph 3 ≤
      genericRigidityRank (SimpleGraph.completeGraph V) 3 := genericRigidityRank_mono le_top
  have hcompleteR : (genericRigidityRank (SimpleGraph.completeGraph V) 3 : ℝ) + 6 =
      3 * (Fintype.card V : ℝ) := by exact_mod_cast hcomplete
  have hleR : (genericRigidityRank M.graph 3 : ℝ) ≤
      (genericRigidityRank (SimpleGraph.completeGraph V) 3 : ℝ) := by exact_mod_cast hle
  linarith

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0062

section BundleSource0063
/- Source: Papers/RigidityFinalTheorems.lean -/




@[expose] public section

/-!
# The principal rigidity theorem and its two completion corollaries

These statements retain all finite graphs and the original definitions
of vertex connectivity, K4 coverage, generic rigidity, and ambient
rigid clusters. The proof chooses one placement satisfying all proved
genericity requirements, constructs its actual soft-force coordinates,
and applies the global rank contradiction.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint BodyLoads
open scoped Classical

theorem minimalCounterexample_false {V : Type} [Fintype V]
    (M : MinimalCounterexample V) : False := by
  obtain ⟨p,hgen,hp,hpin⟩ :=
    PairPinGraph.exists_generic_generalPosition_universalPin (V := V) (B := Body M.graph)
  obtain ⟨L⟩ := exists_softScalarSystem M p hgen hp
  exact L.contradiction hgen hp hpin

/-- Theorem 1.1 in precisely the unrestricted form recorded in the
statement module. -/
theorem theorem_one_one : SixConnectedK4RigidityClaim := by
  by_contra hfalse
  obtain ⟨V,hV,⟨M⟩⟩ := exists_minimalCounterexample hfalse
  letI : Fintype V := hV
  exact minimalCounterexample_false M

/-- Theorem 1.1, with the finite graph and hypotheses exposed directly. -/
theorem sixConnected_k4Covered_rigid
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hconn : VertexConnected G 6) (hcover : K4Covered G) :
    IsGenericallyRigidInR3 G := theorem_one_one V G hconn hcover

/-- Corollary 1.2: actual generically rigid edge-covering subgraphs may
have arbitrary order at least four and may omit edges of the induced graph. -/
theorem corollary_one_two_rigid_subgraph_cover : RigidClusterCoveredRigidityClaim :=
  rigidClusterCoveredRigidity_of_sixConnectedK4Rigidity theorem_one_one

/-- The more general spanning-completion assertion of Corollary 1.2,
with rigidity in the ambient graph rather than an induced-clique assumption. -/
theorem corollary_one_two_rigid_cluster_completion : RigidClusterCompletionRigidityClaim :=
  rigidClusterCompletionRigidity_of_sixConnectedK4Rigidity theorem_one_one

theorem sixConnected_rigidSubgraphCovered_rigid
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hconn : VertexConnected G 6) (hcover : RigidSubgraphCovered G) :
    IsGenericallyRigidInR3 G := corollary_one_two_rigid_subgraph_cover V G hconn hcover

theorem rigidCluster_completion_sixConnected_rigid
    {V I : Type} [Fintype V] (G : SimpleGraph V) (C : I → Finset V)
    (hC : ∀ i, 4 ≤ (C i).card ∧ RigidCluster G (C i))
    (hconn : VertexConnected (clusterCompletion C) 6) : IsGenericallyRigidInR3 G :=
  corollary_one_two_rigid_cluster_completion V I G C hC hconn

end Papers.Rigidity

end
end
end BundleSource0063

section BundleSource0064
/- Source: Papers/RigidityLocalRigidity.lean -/



@[expose] public section

/-!
# Local distance rigidity and the actual generic rank

A framework is locally rigid when every sufficiently nearby framework
with the same graph-edge lengths has all the same pairwise distances.
The equivalence below is proved using the genuine length-fiber chart,
not by defining local rigidity in terms of the rigidity matrix.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open Filter
open scoped Topology Classical

variable {V : Type} [Fintype V] {d : ℕ}

/-- Local rigidity stated directly through the real squared distances.
This formulation of congruence includes degenerate finite frameworks. -/
def IsLocallyDistanceRigid (G : SimpleGraph V) (p : Placement V d) : Prop :=
  ∀ᶠ q in 𝓝 p, squaredLengthMap G q = squaredLengthMap G p →
    squaredLengthMap (SimpleGraph.completeGraph V) q =
      squaredLengthMap (SimpleGraph.completeGraph V) p

def lengthMask (G : SimpleGraph V) : (V × V → ℝ) →L[ℝ] (V × V → ℝ) :=
  LinearMap.toContinuousLinearMap <|
    LinearMap.pi fun e => if G.Adj e.1 e.2 then LinearMap.proj e else 0

@[simp] theorem lengthMask_apply (G : SimpleGraph V) (l : V × V → ℝ) (e : V × V) :
    lengthMask G l e = if G.Adj e.1 e.2 then l e else 0 := by
  by_cases h : G.Adj e.1 e.2 <;>
    simp [lengthMask, LinearMap.coe_toContinuousLinearMap', h]

theorem lengthMask_complete (G : SimpleGraph V) (p : Placement V d) :
    lengthMask G (squaredLengthMap (SimpleGraph.completeGraph V) p) =
      squaredLengthMap G p := by
  ext e
  by_cases h : G.Adj e.1 e.2
  · simp [lengthMask_apply, squaredLengthMap, h, h.ne]
  · simp [lengthMask_apply, squaredLengthMap, h]

theorem lengthMask_derivative (G : SimpleGraph V) (p : Placement V d) :
    (lengthMask G).comp (fderiv ℝ (squaredLengthMap (SimpleGraph.completeGraph V)) p) =
      fderiv ℝ (squaredLengthMap G) p := by
  have h := (lengthMask G).hasFDerivAt.comp p
    (squaredLengthMap_hasFDerivAt (SimpleGraph.completeGraph V) p)
  rw [← fderiv_squaredLengthMap] at h
  change HasFDerivAt (fun q : Placement V d =>
    lengthMask G (squaredLengthMap (SimpleGraph.completeGraph V) q)) _ p at h
  have heq : (fun q : Placement V d =>
      lengthMask G (squaredLengthMap (SimpleGraph.completeGraph V) q)) =
      squaredLengthMap G := funext (lengthMask_complete G)
  rw [heq] at h
  exact h.fderiv.symm

/-- At a simultaneous maximum-rank placement, infinitesimal rigidity
forces actual local rigidity of the full Euclidean distance constraints. -/
theorem IsGenericallyRigidInDimension.isLocallyDistanceRigid
    {G : SimpleGraph V} (hG : IsGenericallyRigidInDimension G d)
    (p : Placement V d) (hp : IsGenericPlacement p) :
    IsLocallyDistanceRigid G p := by
  let K := SimpleGraph.completeGraph V
  let P := lengthMask G
  let T := (rigidityOperator G p).ker
  let C := maximumRankLengthFiberChart G p (hp G)
  have heq : (fun q : Placement V d => P (squaredLengthMap K q)) =
      squaredLengthMap G := funext (lengthMask_complete G)
  have C' : Calculus.SmoothLevelChart
      (fun q => P (squaredLengthMap K q)) p T := by
    rw [heq]
    exact C
  have hnear : ∀ᶠ q in 𝓝 p,
      (P.comp (fderiv ℝ (squaredLengthMap K) q)).ker ≤
        (fderiv ℝ (squaredLengthMap K) q).ker := by
    filter_upwards [isOpen_isGenericPlacement.mem_nhds hp] with q hq
    rw [lengthMask_derivative, ker_fderiv_squaredLengthMap,
      ker_fderiv_squaredLengthMap]
    exact (ker_eq_of_le_of_genericRigidityRank_eq
      (show G ≤ K from le_top) hG q hq).symm.le
  let D := C'.of_projection (squaredLengthMap K) P p T
    (squaredLengthMap_contDiff K).contDiffAt hnear
  filter_upwards [C'.fiber_iff, D.fiber_iff] with q hC hD
  intro hq
  apply hD.mpr
  apply hC.mp
  simpa only [P, K, lengthMask_complete] using hq

/-- A real local length-preserving fiber cannot have an infinitesimal
direction changing a complete-graph distance at a maximum-rank point. -/
theorem ker_le_complete_of_isLocallyDistanceRigid
    (G : SimpleGraph V) (p : Placement V d)
    (hp : IsRegularPlacement G p) (hlocal : IsLocallyDistanceRigid G p) :
    (rigidityOperator G p).ker ≤
      (rigidityOperator (SimpleGraph.completeGraph V) p).ker := by
  let K := SimpleGraph.completeGraph V
  let C := maximumRankLengthFiberChart G p hp
  have hψ : Tendsto C.parametrization
      (𝓝 (0 : (rigidityOperator G p).ker)) (𝓝 p) := by
    simpa only [C.parametrization_zero] using
      C.smooth_parametrization.continuousAt.tendsto
  have hlevel : (fun u => squaredLengthMap K (C.parametrization u)) =ᶠ[𝓝 0]
      (fun _ => squaredLengthMap K p) := by
    filter_upwards [C.level, hψ.eventually hlocal] with u hu hlocalu
    exact hlocalu hu
  have hfull : HasFDerivAt (squaredLengthMap K)
      (LinearMap.toContinuousLinearMap ((2 : ℝ) • rigidityOperator K p))
      (C.parametrization 0) := by
    rw [C.parametrization_zero]
    exact squaredLengthMap_hasFDerivAt K p
  have hD := hfull.comp (0 : (rigidityOperator G p).ker) C.tangent.hasFDerivAt
  have hzero : (fderiv ℝ (squaredLengthMap K) p).comp
      (rigidityOperator G p).ker.subtypeL = 0 := by
    rw [fderiv_squaredLengthMap]
    exact hD.fderiv.symm.trans ((Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hlevel).trans (fderiv_const_apply _))
  intro u hu
  rw [← ker_fderiv_squaredLengthMap]
  exact congrArg
    (fun A : (rigidityOperator G p).ker →L[ℝ] (V × V → ℝ) => A ⟨u, hu⟩) hzero

/-- Local distance rigidity and generic rigidity rank are equivalent at
every simultaneous regular placement, in every dimension and for every
finite graph. No affine-spanning or cardinality premise is added. -/
theorem isLocallyDistanceRigid_iff_isGenericallyRigid
    (G : SimpleGraph V) (p : Placement V d) (hp : IsGenericPlacement p) :
    IsLocallyDistanceRigid G p ↔ IsGenericallyRigidInDimension G d := by
  constructor
  · intro hlocal
    have hker := ker_le_complete_of_isLocallyDistanceRigid G p (hp G) hlocal
    have hr := rigidityRank_le_of_ker_le
      (SimpleGraph.completeGraph V) G p hker
    have hGrank : rigidityRank G p = genericRigidityRank G d := hp G
    have hKrank : rigidityRank (SimpleGraph.completeGraph V) p =
        genericRigidityRank (SimpleGraph.completeGraph V) d := hp (SimpleGraph.completeGraph V)
    rw [hGrank, hKrank] at hr
    change genericRigidityRank G d =
      genericRigidityRank (SimpleGraph.completeGraph V) d
    exact le_antisymm (genericRigidityRank_mono le_top) hr
  · intro hG
    exact hG.isLocallyDistanceRigid p hp

theorem isGenericallyRigid_iff_all_generic_locallyDistanceRigid
    (G : SimpleGraph V) :
    IsGenericallyRigidInDimension G d ↔
      ∀ p : Placement V d, IsGenericPlacement p → IsLocallyDistanceRigid G p := by
  constructor
  · exact fun hG p hp => hG.isLocallyDistanceRigid p hp
  · intro h
    obtain ⟨p, hp⟩ := exists_isGenericPlacement (V := V) d
    exact (isLocallyDistanceRigid_iff_isGenericallyRigid G p hp).mp (h p hp)

end

end Papers.Rigidity.BarJoint

end
end BundleSource0064

section BundleSource0065
/- Source: Papers/RigidityFinalSemantics.lean -/





@[expose] public section

/-!
# The principal graph theorems as actual Euclidean rigidity statements

These wrappers use the proved equivalence between the maximum-rank
definition and local preservation of all pairwise distances. The last
statement identifies the actual infinitesimal motion kernel with the
translations and rotations of Euclidean three-space. No equivalence is
assumed as an extra premise.
-/

namespace Papers.Rigidity

open BarJoint

variable {V : Type} [Fintype V]

/-- Theorem 1.1 in the direct local-distance formulation: every sufficiently
nearby placement with the same graph-edge lengths has all the same
pairwise distances. -/
theorem sixConnected_k4Covered_locallyDistanceRigid
    (G : SimpleGraph V) (hconn : VertexConnected G 6) (hcover : K4Covered G)
    (p : Placement V 3) (hgen : IsGenericPlacement p) :
    IsLocallyDistanceRigid G p := by
  exact (isLocallyDistanceRigid_iff_isGenericallyRigid G p hgen).mpr
    (sixConnected_k4Covered_rigid G hconn hcover)

/-- The edge-cover form of Corollary 1.2, with literal local-distance
rigidity as its conclusion. -/
theorem sixConnected_rigidSubgraphCovered_locallyDistanceRigid
    (G : SimpleGraph V) (hconn : VertexConnected G 6)
    (hcover : RigidSubgraphCovered G)
    (p : Placement V 3) (hgen : IsGenericPlacement p) :
    IsLocallyDistanceRigid G p := by
  exact (isLocallyDistanceRigid_iff_isGenericallyRigid G p hgen).mpr
    (sixConnected_rigidSubgraphCovered_rigid G hconn hcover)

/-- The ambient-cluster form of Corollary 1.2, with all labels retained
and literal local-distance rigidity as its conclusion. -/
theorem rigidCluster_completion_sixConnected_locallyDistanceRigid
    {I : Type} (G : SimpleGraph V) (C : I → Finset V)
    (hC : ∀ i, 4 ≤ (C i).card ∧ RigidCluster G (C i))
    (hconn : VertexConnected (clusterCompletion C) 6)
    (p : Placement V 3) (hgen : IsGenericPlacement p) :
    IsLocallyDistanceRigid G p := by
  exact (isLocallyDistanceRigid_iff_isGenericallyRigid G p hgen).mpr
    (rigidCluster_completion_sixConnected_rigid G C hC hconn)

/-- Theorem 1.1 in literal infinitesimal-motion form. At every generic
general-position placement, every graph motion is a global Euclidean
twist, and every global Euclidean twist is a graph motion. -/
theorem sixConnected_k4Covered_motionKernel_eq_globalTwists
    (G : SimpleGraph V) (hconn : VertexConnected G 6) (hcover : K4Covered G)
    (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    (rigidityOperator G p).ker = (globalTwistOperator p).range := by
  have hrig := sixConnected_k4Covered_rigid G hconn hcover
  have hker := ker_eq_of_le_of_genericRigidityRank_eq
    (show G ≤ SimpleGraph.completeGraph V from le_top) hrig p hgen
  exact hker.symm.trans (complete_kernel_eq_twist_range_all p hp)

end Papers.Rigidity

end
end BundleSource0065

section BundleSource0066
/- Source: Papers/RigiditySharpnessGraph.lean -/






@[expose] public section

/-!
# A five-connected flexible graph

This is the instance `t = 7` of Jackson--Jordán--Villányi,
Example 7.5. There are five rows and seven cyclic cells in each row.
Each cell is a complete graph on five vertices. Its first two vertices
are left ports, the next two right ports, and the last its hub.
The right pair of each cell is completely joined to the left pair of
the next cell. The five hubs in each column form another complete graph.

The graph has 175 vertices. The other sharpness modules prove its
five-connectivity and the strict rank bound 518 < 519.
-/

namespace Papers.Rigidity.Sharpness

open BarJoint

abbrev Row := Fin 5
abbrev Cell := Fin 7
abbrev Slot := Fin 5
abbrev Vertex := Row × Cell × Slot

def vertex (r : Row) (c : Cell) (s : Slot) : Vertex := (r, c, s)

def hub (r : Row) (c : Cell) : Vertex := vertex r c 4
def left (r : Row) (c : Cell) (a : Fin 2) : Vertex := vertex r c (a.castLE (by decide))
def right (r : Row) (c : Cell) (a : Fin 2) : Vertex := vertex r c ⟨a.val + 2, by omega⟩

/-- The direct adjacency description keeps every vertex and edge explicit. -/
def graph : SimpleGraph Vertex where
  Adj u v := u ≠ v ∧
    ((u.1 = v.1 ∧ u.2.1 = v.2.1) ∨
      (u.2.2 = 4 ∧ v.2.2 = 4 ∧ u.2.1 = v.2.1) ∨
      (u.1 = v.1 ∧ 2 ≤ u.2.2.val ∧ u.2.2.val < 4 ∧
        v.2.2.val < 2 ∧ v.2.1 = u.2.1 + 1) ∨
      (u.1 = v.1 ∧ 2 ≤ v.2.2.val ∧ v.2.2.val < 4 ∧
        u.2.2.val < 2 ∧ u.2.1 = v.2.1 + 1))
  symm := by
    constructor
    rintro u v ⟨hne, hcell | hhub | hright | hleft⟩
    · exact ⟨hne.symm, Or.inl ⟨hcell.1.symm, hcell.2.symm⟩⟩
    · exact ⟨hne.symm, Or.inr (Or.inl ⟨hhub.2.1, hhub.1, hhub.2.2.symm⟩)⟩
    · exact ⟨hne.symm, Or.inr (Or.inr (Or.inr
        ⟨hright.1.symm, hright.2⟩))⟩
    · exact ⟨hne.symm, Or.inr (Or.inr (Or.inl
        ⟨hleft.1.symm, hleft.2⟩))⟩
  loopless := by constructor; intro u; simp

instance : DecidableRel graph.Adj := fun _ _ => by
  dsimp [graph]
  infer_instance

theorem same_cell_adj (r : Row) (c : Cell) {s t : Slot} (hne : s ≠ t) :
    graph.Adj (vertex r c s) (vertex r c t) := by
  refine ⟨?_, Or.inl ⟨rfl, rfl⟩⟩
  exact fun h => hne (congrArg (fun v : Vertex => v.2.2) h)

theorem hubs_adj {r t : Row} (c : Cell) (hne : r ≠ t) :
    graph.Adj (hub r c) (hub t c) := by
  refine ⟨?_, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  exact fun h => hne (congrArg (fun v : Vertex => v.1) h)

theorem bridge_adj (r : Row) (c : Cell) (a b : Fin 2) :
    graph.Adj (right r c a) (left r (c + 1) b) := by
  refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_, rfl⟩))⟩
  · intro h
    have hs := congrArg (fun v : Vertex => v.2.2.val) h
    change a.val + 2 = b.val at hs
    omega
  · change 2 ≤ a.val + 2
    omega
  · change a.val + 2 < 4
    omega
  · exact b.isLt

def cellVertices (r : Row) (c : Cell) : Finset Vertex :=
  Finset.univ.image (vertex r c)

def hubVertices (c : Cell) : Finset Vertex :=
  Finset.univ.image (fun r => hub r c)

def bridgeVertices (r : Row) (c : Cell) : Finset Vertex :=
  {right r c 0, right r c 1, left r (c + 1) 0, left r (c + 1) 1}

theorem cellVertices_card (r : Row) (c : Cell) : (cellVertices r c).card = 5 := by
  rw [cellVertices, Finset.card_image_of_injective]
  · simp
  · intro s t h
    exact congrArg (fun v : Vertex => v.2.2) h

theorem hubVertices_card (c : Cell) : (hubVertices c).card = 5 := by
  rw [hubVertices, Finset.card_image_of_injective]
  · simp
  · intro r t h
    exact congrArg (fun v : Vertex => v.1) h

theorem cellVertices_clique (r : Row) (c : Cell) :
    graph.IsClique (cellVertices r c : Set Vertex) := by
  rintro u hu v hv hne
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
  exact same_cell_adj r c (fun h => hne (congrArg (vertex r c) h))

theorem hubVertices_clique (c : Cell) :
    graph.IsClique (hubVertices c : Set Vertex) := by
  rintro u hu v hv hne
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
  exact hubs_adj c (fun h => hne (congrArg (fun r => hub r c) h))

theorem bridgeVertices_card (r : Row) (c : Cell) :
    (bridgeVertices r c).card = 4 := by
  simp [bridgeVertices, right, left, vertex]

theorem bridgeVertices_clique (r : Row) (c : Cell) :
    graph.IsClique (bridgeVertices r c : Set Vertex) := by
  intro u hu v hv hne
  simp only [bridgeVertices, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;>
    simp_all [graph, right, left, vertex]

theorem right_mem_bridgeVertices (r : Row) (c : Cell) (a : Fin 2) :
    right r c a ∈ bridgeVertices r c := by
  fin_cases a <;> simp [bridgeVertices]

theorem left_mem_bridgeVertices (r : Row) (c : Cell) (a : Fin 2) :
    left r (c + 1) a ∈ bridgeVertices r c := by
  fin_cases a <;> simp [bridgeVertices]

/-- Every edge has an actual covering clique of order four or five. -/
theorem exists_covering_clique {u v : Vertex} (hadj : graph.Adj u v) :
    ∃ S : Finset Vertex, 4 ≤ S.card ∧ u ∈ S ∧ v ∈ S ∧
      graph.IsClique (S : Set Vertex) := by
  rcases u with ⟨r, c, s⟩
  rcases v with ⟨t, d, k⟩
  change (r, c, s) ≠ (t, d, k) ∧
    ((r = t ∧ c = d) ∨ (s = 4 ∧ k = 4 ∧ c = d) ∨
      (r = t ∧ 2 ≤ s.val ∧ s.val < 4 ∧ k.val < 2 ∧ d = c + 1) ∨
      (r = t ∧ 2 ≤ k.val ∧ k.val < 4 ∧ s.val < 2 ∧ c = d + 1)) at hadj
  rcases hadj with ⟨_, hcell | hhub | hright | hleft⟩
  · rcases hcell with ⟨rfl, rfl⟩
    refine ⟨cellVertices r c, by rw [cellVertices_card]; decide,
      ?_, ?_, cellVertices_clique r c⟩
    · exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · rcases hhub with ⟨rfl, rfl, rfl⟩
    refine ⟨hubVertices c, by rw [hubVertices_card]; decide,
      ?_, ?_, hubVertices_clique c⟩
    · exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  · rcases hright with ⟨rfl, hslo, hshi, hk, rfl⟩
    let a : Fin 2 := ⟨s.val - 2, by omega⟩
    let b : Fin 2 := ⟨k.val, hk⟩
    have heqs : right r c a = vertex r c s := by
      apply congrArg (vertex r c)
      apply Fin.ext
      change s.val - 2 + 2 = s.val
      omega
    have heqk : left r (c + 1) b = vertex r (c + 1) k := rfl
    refine ⟨bridgeVertices r c, by rw [bridgeVertices_card],
      ?_, ?_, bridgeVertices_clique r c⟩
    · change vertex r c s ∈ bridgeVertices r c
      rw [← heqs]
      exact right_mem_bridgeVertices r c a
    · change vertex r (c + 1) k ∈ bridgeVertices r c
      rw [← heqk]
      exact left_mem_bridgeVertices r c b
  · rcases hleft with ⟨rfl, hklo, hkhi, hs, rfl⟩
    let a : Fin 2 := ⟨k.val - 2, by omega⟩
    let b : Fin 2 := ⟨s.val, hs⟩
    have heqk : right r d a = vertex r d k := by
      apply congrArg (vertex r d)
      apply Fin.ext
      change k.val - 2 + 2 = k.val
      omega
    have heqs : left r (d + 1) b = vertex r (d + 1) s := rfl
    refine ⟨bridgeVertices r d, by rw [bridgeVertices_card],
      ?_, ?_, bridgeVertices_clique r d⟩
    · change vertex r (d + 1) s ∈ bridgeVertices r d
      rw [← heqs]
      exact left_mem_bridgeVertices r d b
    · change vertex r d k ∈ bridgeVertices r d
      rw [← heqk]
      exact right_mem_bridgeVertices r d a

theorem k4Covered : K4Covered graph := by
  intro u v hadj
  obtain ⟨S, hcard, hu, hv, hclique⟩ := exists_covering_clique hadj
  have hcovered := clusterCompletion_k4Covered (fun _ : Unit => S) (fun _ => hcard)
  obtain ⟨T, hTcard, huT, hvT, hTclique⟩ := hcovered u v ⟨hadj.1, (), hu, hv⟩
  refine ⟨T, hTcard, huT, hvT, SimpleGraph.IsClique.mono ?_ hTclique⟩
  rintro x y ⟨hne, _, hx, hy⟩
  exact hclique hx hy hne

theorem card_vertex : Fintype.card Vertex = 175 := by
  norm_num [Vertex, Row, Cell, Slot]

end Papers.Rigidity.Sharpness

end
end BundleSource0066

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0066/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0066.json"

section BundleSource0067
/- Source: Papers/RigiditySharpnessConnectivity.lean -/




@[expose] public section

/-!
# Five-connectivity of the sharpness graph

Every vertex has five routes to row hubs whose prescribed vertices are
pairwise disjoint. The initial step to each route stays inside the vertex's
own complete cell. Four deleted vertices cannot meet all five routes.

There is also a row containing no deleted vertex. Its cyclic chain of
complete cells is connected, and the vertical hub cliques connect every
surviving vertex to that row. The proof handles every set of fewer than
five deleted vertices without enumerating such deletion sets.
-/

namespace Papers.Rigidity.Sharpness

private abbrev Remaining (S : Finset Vertex) := graph.induce ((S : Set Vertex)ᶜ)

/-- Offsets and slots of five disjoint routes, including their terminal hubs. -/
private def fanTemplate (i : Fin 5) : Finset (Cell × Slot) :=
  match i.val with
  | 0 => {(0,4)}
  | 1 => {(0,2),(1,0),(1,4)}
  | 2 => {(0,3),(1,1),(1,3),(2,1),(2,4)}
  | 3 => {(0,0),(6,2),(6,4)}
  | _ => {(0,1),(6,3),(6,1),(5,3),(5,4)}

private theorem fanTemplate_disjoint :
    ∀ i j : Fin 5, i ≠ j → Disjoint (fanTemplate i) (fanTemplate j) := by
  decide

private def shiftVertex (r : Row) (c : Cell) (z : Cell × Slot) : Vertex :=
  vertex r (c + z.1) z.2

private theorem shiftVertex_injective (r : Row) (c : Cell) :
    Function.Injective (shiftVertex r c) := by
  intro z w h
  have hc : c + z.1 = c + w.1 := congrArg (fun v : Vertex => v.2.1) h
  have hs : z.2 = w.2 := congrArg (fun v : Vertex => v.2.2) h
  exact Prod.ext (add_left_cancel hc) hs

private def fanVertices (r : Row) (c : Cell) (i : Fin 5) : Finset Vertex :=
  (fanTemplate i).image (shiftVertex r c)

private theorem fanVertices_disjoint (r : Row) (c : Cell) {i j : Fin 5}
    (hij : i ≠ j) : Disjoint (fanVertices r c i) (fanVertices r c j) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨w,hw,heq⟩ := Finset.mem_image.mp hj
  have hwz := shiftVertex_injective r c heq
  exact Finset.disjoint_left.mp (fanTemplate_disjoint i j hij) hz (hwz ▸ hw)

private theorem exists_untouched_fan (S : Finset Vertex) (hS : S.card < 5)
    (r : Row) (c : Cell) : ∃ i : Fin 5, Disjoint (fanVertices r c i) S := by
  classical
  by_contra hnone
  have hex (i : Fin 5) : ∃ v, v ∈ fanVertices r c i ∧ v ∈ S := by
    by_contra hmissing
    apply hnone
    refine ⟨i,Finset.disjoint_left.mpr ?_⟩
    intro v hv hs
    exact hmissing ⟨v,hv,hs⟩
  choose v hv hvs using hex
  let f : Fin 5 → S := fun i => ⟨v i,hvs i⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have heq : v i = v j := congrArg Subtype.val hij
    exact Finset.disjoint_left.mp (fanVertices_disjoint r c hne)
      (hv i) (heq.symm ▸ hv j)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin,Fintype.card_coe] at hcard
  omega

private theorem withinCell (S : Finset Vertex) (r : Row) (c : Cell)
    (s t : Slot) (hs : vertex r c s ∉ S) (ht : vertex r c t ∉ S) :
    (Remaining S).Reachable ⟨vertex r c s,hs⟩ ⟨vertex r c t,ht⟩ := by
  by_cases hst : s = t
  · subst t
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    exact same_cell_adj r c hst

private theorem acrossBridge (S : Finset Vertex) (r : Row) (c d : Cell)
    (hd : d = c + 1) (a b : Fin 2)
    (ha : right r c a ∉ S) (hb : left r d b ∉ S) :
    (Remaining S).Reachable ⟨right r c a,ha⟩ ⟨left r d b,hb⟩ := by
  apply SimpleGraph.Adj.reachable
  change graph.Adj (right r c a) (left r d b)
  subst d
  exact bridge_adj r c a b

private theorem betweenHubs (S : Finset Vertex) (r t : Row) (c : Cell)
    (hr : hub r c ∉ S) (ht : hub t c ∉ S) :
    (Remaining S).Reachable ⟨hub r c,hr⟩ ⟨hub t c,ht⟩ := by
  by_cases hrt : r = t
  · subst t
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    exact hubs_adj c hrt

private theorem next_two (c : Cell) : (c + 1) + 1 = c + 2 := by
  rw [add_assoc]
  rfl

private theorem previous_next (c : Cell) : (c + 6) + 1 = c := by
  rw [add_assoc]
  change c + 0 = c
  exact add_zero c

private theorem previous_two_next (c : Cell) : (c + 5) + 1 = c + 6 := by
  rw [add_assoc]
  rfl

/-- A surviving vertex reaches a surviving hub in its own row. -/
private theorem reachable_row_hub (S : Finset Vertex) (hS : S.card < 5)
    (r : Row) (c : Cell) (s : Slot) (hs : vertex r c s ∉ S) :
    ∃ d : Cell, ∃ hd : hub r d ∉ S,
      (Remaining S).Reachable ⟨vertex r c s,hs⟩ ⟨hub r d,hd⟩ := by
  obtain ⟨i,hi⟩ := exists_untouched_fan S hS r c
  have ha (z : Cell × Slot) (hz : z ∈ fanTemplate i) : shiftVertex r c z ∉ S := by
    intro hzs
    exact Finset.disjoint_left.mp hi (Finset.mem_image.mpr ⟨z,hz,rfl⟩) hzs
  fin_cases i
  · have hh : hub r c ∉ S := by
      change vertex r c 4 ∉ S
      simpa only [shiftVertex,add_zero] using ha (0,4) (by decide)
    exact ⟨c,hh,withinCell S r c s 4 hs hh⟩
  · have h02 : vertex r c 2 ∉ S := by
      simpa only [shiftVertex,add_zero] using ha (0,2) (by decide)
    have h10 : vertex r (c+1) 0 ∉ S := ha (1,0) (by decide)
    have hh : hub r (c+1) ∉ S := ha (1,4) (by decide)
    exact ⟨c+1,hh,(withinCell S r c s 2 hs h02).trans
      ((acrossBridge S r c (c+1) rfl 0 0 h02 h10).trans
        (withinCell S r (c+1) 0 4 h10 hh))⟩
  · have h03 : vertex r c 3 ∉ S := by
      simpa only [shiftVertex,add_zero] using ha (0,3) (by decide)
    have h11 : vertex r (c+1) 1 ∉ S := ha (1,1) (by decide)
    have h13 : vertex r (c+1) 3 ∉ S := ha (1,3) (by decide)
    have h21 : vertex r (c+2) 1 ∉ S := ha (2,1) (by decide)
    have hh : hub r (c+2) ∉ S := ha (2,4) (by decide)
    exact ⟨c+2,hh,(withinCell S r c s 3 hs h03).trans
      ((acrossBridge S r c (c+1) rfl 1 1 h03 h11).trans
        ((withinCell S r (c+1) 1 3 h11 h13).trans
          ((acrossBridge S r (c+1) (c+2) (next_two c).symm 1 1 h13 h21).trans
            (withinCell S r (c+2) 1 4 h21 hh))))⟩
  · have h00 : vertex r c 0 ∉ S := by
      simpa only [shiftVertex,add_zero] using ha (0,0) (by decide)
    have h62 : vertex r (c+6) 2 ∉ S := ha (6,2) (by decide)
    have hh : hub r (c+6) ∉ S := ha (6,4) (by decide)
    exact ⟨c+6,hh,(withinCell S r c s 0 hs h00).trans
      ((acrossBridge S r (c+6) c (previous_next c).symm 0 0 h62 h00).symm.trans
        (withinCell S r (c+6) 2 4 h62 hh))⟩
  · have h01 : vertex r c 1 ∉ S := by
      simpa only [shiftVertex,add_zero] using ha (0,1) (by decide)
    have h63 : vertex r (c+6) 3 ∉ S := ha (6,3) (by decide)
    have h61 : vertex r (c+6) 1 ∉ S := ha (6,1) (by decide)
    have h53 : vertex r (c+5) 3 ∉ S := ha (5,3) (by decide)
    have hh : hub r (c+5) ∉ S := ha (5,4) (by decide)
    exact ⟨c+5,hh,(withinCell S r c s 1 hs h01).trans
      ((acrossBridge S r (c+6) c (previous_next c).symm 1 1 h63 h01).symm.trans
        ((withinCell S r (c+6) 3 1 h63 h61).trans
          ((acrossBridge S r (c+5) (c+6) (previous_two_next c).symm 1 1 h53 h61).symm.trans
            (withinCell S r (c+5) 3 4 h53 hh))))⟩

private theorem exists_intact_row (S : Finset Vertex) (hS : S.card < 5) :
    ∃ r : Row, ∀ c s, vertex r c s ∉ S := by
  have hex : ∃ r : Row, r ∉ S.image (fun v => v.1) := by
    by_contra hnone
    push_neg at hnone
    have hsub : (Finset.univ : Finset Row) ⊆ S.image (fun v => v.1) :=
      fun r _ => hnone r
    have hcard := Finset.card_le_card hsub
    have himage := Finset.card_image_le (s := S) (f := fun v => v.1)
    simp only [Finset.card_univ,Fintype.card_fin] at hcard
    omega
  obtain ⟨r,hr⟩ := hex
  refine ⟨r,?_⟩
  intro c s h
  exact hr (Finset.mem_image.mpr ⟨vertex r c s,h,rfl⟩)

private theorem intact_row_hubs_connected (S : Finset Vertex) (r : Row)
    (hr : ∀ c s, vertex r c s ∉ S) (c : Cell) :
    (Remaining S).Reachable ⟨hub r 0,hr 0 4⟩ ⟨hub r c,hr c 4⟩ := by
  have hstep (d : Cell) :
      (Remaining S).Reachable ⟨hub r d,hr d 4⟩ ⟨hub r (d+1),hr (d+1) 4⟩ :=
    (withinCell S r d 4 2 (hr d 4) (hr d 2)).trans
      ((acrossBridge S r d (d+1) rfl 0 0 (hr d 2) (hr (d+1) 0)).trans
        (withinCell S r (d+1) 0 4 (hr (d+1) 0) (hr (d+1) 4)))
  have hsucc : ∀ i : Fin 6, (i.castSucc + 1 : Cell) = i.succ := by decide
  induction c using Fin.induction with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ i ih =>
    have h := hstep i.castSucc
    rw [hsucc i] at h
    exact ih.trans h

/-- The explicit 175-vertex graph remains connected after every deletion
of at most four vertices. This is the sharpness assertion's full connectivity
hypothesis, not a fixed list of tested separators. -/
theorem sharpness_fiveConnected : VertexConnected graph 5 := by
  refine ⟨?_,?_⟩
  · rw [card_vertex]
    decide
  · intro S hS
    obtain ⟨r,hr⟩ := exists_intact_row S hS
    apply (SimpleGraph.connected_iff_exists_forall_reachable (Remaining S)).mpr
    refine ⟨⟨hub r 0,hr 0 4⟩,?_⟩
    intro v
    obtain ⟨⟨t,c,s⟩,hv⟩ := v
    obtain ⟨d,hd,hpath⟩ := reachable_row_hub S hS t c s hv
    exact (intact_row_hubs_connected S r hr d).trans
      ((betweenHubs S t r d hd (hr d 4)).symm.trans hpath.symm)

end Papers.Rigidity.Sharpness

end
end BundleSource0067

section BundleSource0068
/- Source: Papers/RigiditySharpnessRank.lean -/





@[expose] public section

/-!
# The rank obstruction for the sharpness graph

The argument is uniform in all real placements, not a rank calculation
at a selected realization. Every cell contributes at most nine rows,
every vertical hub clique contributes at most nine, and the remaining
140 cross edges contribute at most 140. Thus the actual rigidity rank
is at most `35 * 9 + 7 * 9 + 140 = 518`. The complete graph on the
same 175 vertices has generic rank 519.
-/

noncomputable section
namespace Papers.Rigidity.Sharpness

open BarJoint
open scoped Classical BigOperators

abbrev CellIndex := Row × Cell
abbrev BridgeIndex := Row × Cell × Fin 2 × Fin 2

def cellRestriction (i : CellIndex) :
    Velocity Vertex 3 →ₗ[ℝ] Velocity Slot 3 :=
  LinearMap.pi fun s => LinearMap.proj (vertex i.1 i.2 s)

def hubRestriction (c : Cell) :
    Velocity Vertex 3 →ₗ[ℝ] Velocity Row 3 :=
  LinearMap.pi fun r => LinearMap.proj (hub r c)

def cellOperator (p : Placement Vertex 3) (i : CellIndex) :
    Velocity Vertex 3 →ₗ[ℝ] (Slot × Slot → ℝ) :=
  (rigidityOperator (SimpleGraph.completeGraph Slot) (fun s => p (vertex i.1 i.2 s))).comp
    (cellRestriction i)

def hubOperator (p : Placement Vertex 3) (c : Cell) :
    Velocity Vertex 3 →ₗ[ℝ] (Row × Row → ℝ) :=
  (rigidityOperator (SimpleGraph.completeGraph Row) (fun r => p (hub r c))).comp
    (hubRestriction c)

def bridgeOperator (p : Placement Vertex 3) (i : BridgeIndex) :
    Velocity Vertex 3 →ₗ[ℝ] ℝ :=
  edgeFunctional p (right i.1 i.2.1 i.2.2.1) (left i.1 (i.2.1 + 1) i.2.2.2)

abbrev CoverageTarget (p : Placement Vertex 3) :=
  (∀ i : CellIndex, (cellOperator p i).range) ×
    (∀ c : Cell, (hubOperator p c).range) × (BridgeIndex → ℝ)

/-- The target consists of the actual component ranges, so its
dimension counts their ranks rather than the number of duplicated rows. -/
def coverageOperator (p : Placement Vertex 3) :
    Velocity Vertex 3 →ₗ[ℝ] CoverageTarget p :=
  (LinearMap.pi fun i => (cellOperator p i).rangeRestrict).prod
    ((LinearMap.pi fun c => (hubOperator p c).rangeRestrict).prod
      (LinearMap.pi fun i => bridgeOperator p i))

theorem cellOperator_rank_le_nine (p : Placement Vertex 3) (i : CellIndex) :
    Module.finrank ℝ (cellOperator p i).range ≤ 9 := by
  have hcomp := Submodule.finrank_mono
    (LinearMap.range_comp_le_range
      (cellRestriction i)
      (rigidityOperator (SimpleGraph.completeGraph Slot) (fun s => p (vertex i.1 i.2 s))))
  have hmax := rigidityRank_le_genericRigidityRank
    (SimpleGraph.completeGraph Slot) 3 (fun s => p (vertex i.1 i.2 s))
  have hcomplete : genericRigidityRank (SimpleGraph.completeGraph Slot) 3 = 9 := by
    rw [genericCompleteRank_eq (V := Slot) (by decide)]
    decide
  exact hcomp.trans (hmax.trans_eq hcomplete)

theorem hubOperator_rank_le_nine (p : Placement Vertex 3) (c : Cell) :
    Module.finrank ℝ (hubOperator p c).range ≤ 9 := by
  have hcomp := Submodule.finrank_mono
    (LinearMap.range_comp_le_range
      (hubRestriction c)
      (rigidityOperator (SimpleGraph.completeGraph Row) (fun r => p (hub r c))))
  have hmax := rigidityRank_le_genericRigidityRank
    (SimpleGraph.completeGraph Row) 3 (fun r => p (hub r c))
  have hcomplete : genericRigidityRank (SimpleGraph.completeGraph Row) 3 = 9 := by
    rw [genericCompleteRank_eq (V := Row) (by decide)]
    decide
  exact hcomp.trans (hmax.trans_eq hcomplete)

theorem coverageTarget_finrank_le (p : Placement Vertex 3) :
    Module.finrank ℝ (CoverageTarget p) ≤ 518 := by
  have hcells : (∑ i : CellIndex, Module.finrank ℝ (cellOperator p i).range) ≤ 315 := by
    calc
      _ ≤ ∑ _ : CellIndex, 9 := Finset.sum_le_sum fun i _ => cellOperator_rank_le_nine p i
      _ = 315 := by norm_num [CellIndex, Row, Cell]
  have hhubs : (∑ c : Cell, Module.finrank ℝ (hubOperator p c).range) ≤ 63 := by
    calc
      _ ≤ ∑ _ : Cell, 9 := Finset.sum_le_sum fun c _ => hubOperator_rank_le_nine p c
      _ = 63 := by norm_num [Cell]
  have hbridges : Module.finrank ℝ (BridgeIndex → ℝ) = 140 := by
    simp [BridgeIndex, Row, Cell, Module.finrank_pi_fintype]
  change Module.finrank ℝ
    ((∀ i : CellIndex, (cellOperator p i).range) ×
      (∀ c : Cell, (hubOperator p c).range) × (BridgeIndex → ℝ)) ≤ 518
  rw [Module.finrank_prod, Module.finrank_prod, hbridges,
    Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  omega

theorem coverage_kernel_le_rigidity_kernel (p : Placement Vertex 3) :
    (coverageOperator p).ker ≤ (rigidityOperator graph p).ker := by
  intro u hu
  have hzero : coverageOperator p u = 0 := hu
  have hcell (r : Row) (c : Cell) : cellOperator p (r, c) u = 0 := by
    exact congrArg (fun y : CoverageTarget p => (y.1 (r, c)).val) hzero
  have hhub (c : Cell) : hubOperator p c u = 0 := by
    exact congrArg (fun y : CoverageTarget p => (y.2.1 c).val) hzero
  have hbridge (r : Row) (c : Cell) (a b : Fin 2) :
      edgeConstraint p u (right r c a) (left r (c + 1) b) = 0 := by
    exact congrArg (fun y : CoverageTarget p => y.2.2 (r, c, a, b)) hzero
  rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
  rintro ⟨r, c, s⟩ ⟨t, d, k⟩ hadj
  change (r, c, s) ≠ (t, d, k) ∧
    ((r = t ∧ c = d) ∨ (s = 4 ∧ k = 4 ∧ c = d) ∨
      (r = t ∧ 2 ≤ s.val ∧ s.val < 4 ∧ k.val < 2 ∧ d = c + 1) ∨
      (r = t ∧ 2 ≤ k.val ∧ k.val < 4 ∧ s.val < 2 ∧ c = d + 1)) at hadj
  rcases hadj with ⟨hne, hsame | hvertical | hforward | hbackward⟩
  · rcases hsame with ⟨rfl, rfl⟩
    have hsk : s ≠ k := fun h => hne (by cases h; rfl)
    have hz := congrFun (hcell r c) (s, k)
    simpa [cellOperator, cellRestriction, rigidityOperator,
      SimpleGraph.completeGraph, SimpleGraph.top_adj, hsk, edgeConstraint, vertex] using hz
  · rcases hvertical with ⟨rfl, rfl, rfl⟩
    have hrt : r ≠ t := fun h => hne (by cases h; rfl)
    have hz := congrFun (hhub c) (r, t)
    simpa [hubOperator, hubRestriction, rigidityOperator,
      SimpleGraph.completeGraph, SimpleGraph.top_adj, hrt, edgeConstraint, hub, vertex] using hz
  · rcases hforward with ⟨rfl, hslo, hshi, hk, rfl⟩
    let a : Fin 2 := ⟨s.val - 2, by omega⟩
    let b : Fin 2 := ⟨k.val, hk⟩
    have hs : right r c a = vertex r c s := by
      apply congrArg (vertex r c)
      apply Fin.ext
      change s.val - 2 + 2 = s.val
      omega
    have hk' : left r (c + 1) b = vertex r (c + 1) k := rfl
    simpa only [hs, hk', vertex] using hbridge r c a b
  · rcases hbackward with ⟨rfl, hklo, hkhi, hs, rfl⟩
    let a : Fin 2 := ⟨k.val - 2, by omega⟩
    let b : Fin 2 := ⟨s.val, hs⟩
    have hk : right r d a = vertex r d k := by
      apply congrArg (vertex r d)
      apply Fin.ext
      change k.val - 2 + 2 = k.val
      omega
    have hs' : left r (d + 1) b = vertex r (d + 1) s := rfl
    rw [edgeConstraint_comm]
    simpa only [hk, hs', vertex] using hbridge r d a b

/-- An operator bound for every placement, including nongeneric ones. -/
theorem rigidityRank_le_518 (p : Placement Vertex 3) :
    rigidityRank graph p ≤ 518 := by
  have hk := Submodule.finrank_mono (coverage_kernel_le_rigidity_kernel p)
  have hgraph := (rigidityOperator graph p).finrank_range_add_finrank_ker
  have hcover := (coverageOperator p).finrank_range_add_finrank_ker
  have htarget := Submodule.finrank_le (coverageOperator p).range
  have htargetBound := coverageTarget_finrank_le p
  unfold rigidityRank
  omega

theorem genericRigidityRank_le_518 : genericRigidityRank graph 3 ≤ 518 := by
  obtain ⟨p, hp⟩ := exists_rigidityRank_eq_genericRigidityRank graph 3
  rw [← hp]
  exact rigidityRank_le_518 p

theorem complete_genericRank_eq_519 :
    genericRigidityRank (SimpleGraph.completeGraph Vertex) 3 = 519 := by
  rw [genericCompleteRank_eq (V := Vertex) (by rw [card_vertex]; decide), card_vertex]

/-- The finite witness is genuinely generically flexible in three dimensions. -/
theorem not_genericallyRigid : ¬ IsGenericallyRigidInR3 graph := by
  intro hrigid
  have hbound := genericRigidityRank_le_518
  change genericRigidityRank graph 3 =
    genericRigidityRank (SimpleGraph.completeGraph Vertex) 3 at hrigid
  rw [hrigid, complete_genericRank_eq_519] at hbound
  omega

end Papers.Rigidity.Sharpness

end
end
end BundleSource0068

section BundleSource0069
/- Source: Papers/RigiditySharpness.lean -/




@[expose] public section

/-!
# Sharpness of the six-connectivity threshold

The example is finite because the sharpness assertion is existential.
Its flexibility proof remains a rank bound valid for every real placement.
The unrestricted six-connectivity theorem is a separate declaration in
`RigidityFinalTheorems`.
-/

namespace Papers.Rigidity

/-- The hypothesis `six-connected` in Theorem 1.1 cannot be replaced
by `five-connected`. This is the 175-vertex instance of
Jackson--Jordán--Villányi, Example 7.5. -/
theorem fiveConnected_k4Covered_flexible_exists :
    ∃ (V : Type) (hV : Fintype V) (G : SimpleGraph V),
      @VertexConnected V hV G 5 ∧ K4Covered G ∧
        ¬ @BarJoint.IsGenericallyRigidInR3 V hV G := by
  exact ⟨Sharpness.Vertex, inferInstance, Sharpness.graph,
    Sharpness.sharpness_fiveConnected, Sharpness.k4Covered,
    Sharpness.not_genericallyRigid⟩

end Papers.Rigidity

end
end BundleSource0069

section BundleSource0070
/- Source: Papers/RigiditySupportedSharpness.lean -/






@[expose] public section

/-!
# Sharpness of the supported-code inequality

Equality holds for every code meeting the Singleton bound with no
inactive coordinates.  Over an infinite field such codes are constructed
as evaluations of polynomials of degree less than `r` at `r+s-1`
distinct points.  Their dimension and minimum support are proved from
the ordinary polynomial root bound.  No representability or MDS-code
existence theorem is assumed.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open scoped Classical BigOperators

theorem bound_recursion (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    ((r : ℝ) + ((r + s - 1 : ℕ) : ℝ) * bound s (r - 1)) /
      (r + s) = bound s r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  have hsub : k + 1 + s - 1 = k + s := by omega
  rw [hsub]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have hs' : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hden : (k : ℝ) + s ≠ 0 := by positivity
  have hden' : (k : ℝ) + 1 + s ≠ 0 := by positivity
  unfold bound
  push_cast
  field_simp
  <;> ring

/-- Every nonzero code attaining the Singleton length has every
coordinate active. -/
theorem activeCoordinates_eq_univ_of_singletonEquality
    {K : Type*} [Field K] {n s : ℕ}
    (W : Submodule K (Fin n → K)) (hs : 1 ≤ s) (hmin : MinimumSupport W s)
    (hW : W ≠ ⊥) (heq : Module.finrank K W + s = n + 1) :
    activeCoordinates W = Finset.univ := by
  apply Finset.eq_univ_of_card
  have hlow := singleton_bound W s hs hmin hW
  have hu := Finset.card_le_univ (activeCoordinates W)
  simp only [Fintype.card_fin] at hu ⊢
  omega

theorem orderMean_eq_bound_of_singletonEquality
    {K : Type*} [Field K] {n s : ℕ}
    (W : Submodule K (Fin n → K)) (hs : 1 ≤ s) (hmin : MinimumSupport W s)
    (heq : Module.finrank K W + s = n + 1) :
    orderMean W = bound s (Module.finrank K W) := by
  induction n with
  | zero =>
    have hzero : Module.finrank K W = 0 := by
      have h := W.finrank_le
      simpa using h
    rw [orderMean_eq_zero_of_finrank_eq_zero W hzero, hzero, bound_zero]
  | succ n ih =>
    by_cases hz : Module.finrank K W = 0
    · rw [orderMean_eq_zero_of_finrank_eq_zero W hz, hz, bound_zero]
    have hW : W ≠ ⊥ := by intro h; simp [h] at hz
    have hactive := activeCoordinates_eq_univ_of_singletonEquality W hs hmin hW heq
    have hshort (i : Fin (n + 1)) :
        Module.finrank K (shorten W i) + 1 = Module.finrank K W :=
      finrank_shorten_of_active W i (by simp [hactive])
    have hmean (i : Fin (n + 1)) :
        orderMean (shorten W i) = bound s (Module.finrank K W - 1) := by
      have hs' := hshort i
      have hd : Module.finrank K (shorten W i) = Module.finrank K W - 1 := by omega
      rw [ih (shorten W i) (minimumSupport_shorten W i hmin) (by omega), hd]
    rw [orderMean_recursion]
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn : n + 1 = Module.finrank K W + s - 1 := by omega
    have hn' : n + 2 = Module.finrank K W + s := by omega
    rw [show (n + 2 : ℝ) = ((Module.finrank K W + s : ℕ) : ℝ) by exact_mod_cast hn',
      show ((n + 1 : ℕ) : ℝ) = ((Module.finrank K W + s - 1 : ℕ) : ℝ) by
        exact_mod_cast hn]
    simpa only [Nat.cast_add] using bound_recursion s (Module.finrank K W) hs (by omega)

variable {K : Type*} [Field K]

def polynomialEvaluationCodeMap {n : ℕ} (r : ℕ) (a : Fin n ↪ K) :
    Polynomial.degreeLT K r →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun i => (Polynomial.leval (a i)).comp (Polynomial.degreeLT K r).subtype

@[simp] theorem polynomialEvaluationCodeMap_apply {n r : ℕ} (a : Fin n ↪ K)
    (p : Polynomial.degreeLT K r) (i : Fin n) :
    polynomialEvaluationCodeMap r a p i = p.val.eval (a i) := rfl

def polynomialEvaluationCode {n : ℕ} (r : ℕ) (a : Fin n ↪ K) :
    Submodule K (Fin n → K) := (polynomialEvaluationCodeMap r a).range

theorem polynomialEvaluationCodeMap_injective {n r : ℕ} (a : Fin n ↪ K) (hrn : r ≤ n) :
    Function.Injective (polynomialEvaluationCodeMap r a) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro p hp
    apply Subtype.ext
    by_contra hne
    have hdeg : p.val.natDegree < r :=
      (Polynomial.natDegree_lt_iff_degree_lt hne).mpr (Polynomial.mem_degreeLT.mp p.property)
    have heval (i : Fin n) : p.val.eval (a i) = 0 :=
      congrFun (LinearMap.mem_ker.mp hp) i
    exact hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p.val
      a.injective heval (by simpa using hdeg.trans_le hrn))
  · exact bot_le

theorem polynomialEvaluationCode_finrank {n r : ℕ} (a : Fin n ↪ K) (hrn : r ≤ n) :
    Module.finrank K (polynomialEvaluationCode r a) = r := by
  rw [polynomialEvaluationCode,
    LinearMap.finrank_range_of_inj (polynomialEvaluationCodeMap_injective a hrn),
    (Polynomial.degreeLTEquiv K r).finrank_eq]
  simp

/-- A nonzero polynomial of degree below `r` has at most `r-1`
zero evaluation coordinates at distinct points. -/
theorem polynomialEvaluationCode_minimumSupport {n r s : ℕ}
    (a : Fin n ↪ K) (hlen : r + s ≤ n + 1) :
    MinimumSupport (polynomialEvaluationCode r a) s := by
  intro w hw hwne
  obtain ⟨p, rfl⟩ := hw
  have hpne : p.val ≠ 0 := by
    intro hp
    apply hwne
    ext i
    simp [hp]
  have hdeg : p.val.natDegree < r :=
    (Polynomial.natDegree_lt_iff_degree_lt hpne).mpr (Polynomial.mem_degreeLT.mp p.property)
  let Z : Finset (Fin n) := Finset.univ \ support (polynomialEvaluationCodeMap r a p)
  have hroots : (Z.map a).val ⊆ p.val.roots := by
    intro x hx
    change x ∈ Z.map a at hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    apply (Polynomial.mem_roots hpne).mpr
    have hi' : i ∉ support (polynomialEvaluationCodeMap r a p) :=
      (Finset.mem_sdiff.mp hi).2
    simpa using hi'
  have hz := Polynomial.card_le_degree_of_subset_roots hroots
  change (Z.map a).card ≤ p.val.natDegree at hz
  rw [Finset.card_map] at hz
  have hcard : Z.card = n - (support (polynomialEvaluationCodeMap r a p)).card := by
    simp [Z, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hle := Finset.card_le_univ (support (polynomialEvaluationCodeMap r a p))
  simp only [Fintype.card_fin] at hle
  rw [hcard] at hz
  omega

/-- The sharpness clause of Lemma 2.1, under the actual uniform finite
order law, for every rank and every positive support threshold. -/
theorem exists_code_attaining_bound [Infinite K] (r s : ℕ) (hs : 1 ≤ s) :
    ∃ W : Submodule K (Fin (r + s - 1) → K),
      Module.finrank K W = r ∧ MinimumSupport W s ∧ precedingMean W = bound s r := by
  let a : Fin (r + s - 1) ↪ K :=
    ⟨fun i => Infinite.natEmbedding K i.val,
      fun i j hij => Fin.ext ((Infinite.natEmbedding K).injective hij)⟩
  let W := polynomialEvaluationCode r a
  have hd : Module.finrank K W = r := polynomialEvaluationCode_finrank a (by omega)
  have hmin : MinimumSupport W s := polynomialEvaluationCode_minimumSupport a (by omega)
  refine ⟨W, hd, hmin, ?_⟩
  rw [← orderMean_eq_precedingMean,
    orderMean_eq_bound_of_singletonEquality W hs hmin (by omega), hd]

end

end Papers.Rigidity.SupportedCode

end
end BundleSource0070

section BundleSource0071
/- Source: Papers/RigidityDuplicateLoadSupport.lean -/





@[expose] public section

/-!
# Duplicate loads respect every induced vertex set

This is equation (4) of Proposition 6.2. Prefix load spaces use different
balanced-fragment subtypes, so we first put their actual coordinate values
in the common ambient space of body-indexed vertex loads. The resulting
intersection is the literal assertion `D(V) ∩ C(T) = D(T)`.

The proof uses the copied-star independence lemma at each omitted vertex.
No conclusion of the main rigidity theorem is imported or used.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- Forget only the balanced-fragment subtype; every actual vertex
coordinate, including its zero extension, is retained. -/
def ambientBodyLoadValues (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    BodyBalancedFamily G p T →ₗ[ℝ] (Body G → Velocity V 3) :=
  LinearMap.pi fun C => (balancedLoadsOn p (C.val ∩ T)).subtype.comp (LinearMap.proj C)

@[simp] theorem ambientBodyLoadValues_apply
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (F : BodyBalancedFamily G p T) (C : Body G) :
    ambientBodyLoadValues G p T F C = (F C).val := rfl

theorem ambientBodyLoadValues_injective
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Function.Injective (ambientBodyLoadValues G p T) := by
  intro F H h
  funext C
  exact Subtype.ext (congrFun h C)

def compatibleLoadsInAmbient (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Submodule ℝ (Body G → Velocity V 3) :=
  (compatibleBodyLoads G p T).map (ambientBodyLoadValues G p T)

def duplicateLoadsInAmbient (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Submodule ℝ (Body G → Velocity V 3) :=
  (duplicateBodyLoads G p T).map (ambientBodyLoadValues G p T)

def ambientCopiedLoads (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    (BodyEdgeOccurrence G T → ℝ) →ₗ[ℝ] (Body G → Velocity V 3) :=
  (ambientBodyLoadValues G p T).comp (bodyCopyForces G p T)

@[simp] theorem ambientCopiedLoads_apply
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (a : BodyEdgeOccurrence G T → ℝ) (C : Body G) :
    ambientCopiedLoads G p T a C = (bodyCopyForces G p T a C).val := rfl

theorem mem_duplicateLoadsInAmbient_iff
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (F : Body G → Velocity V 3) :
    F ∈ duplicateLoadsInAmbient G p T ↔
      ∃ a : BodyEdgeOccurrence G T → ℝ,
        copyAggregate G T a = 0 ∧ ambientCopiedLoads G p T a = F := by
  constructor
  · rintro ⟨H, ⟨a, ha, rfl⟩, hF⟩
    exact ⟨a, LinearMap.mem_ker.mp ha, hF⟩
  · rintro ⟨a, ha, hF⟩
    exact ⟨bodyCopyForces G p T a,
      ⟨a, LinearMap.mem_ker.mpr ha, rfl⟩, hF⟩

private theorem forceOperator_single_eq
    (H : SimpleGraph V) (p : Placement V 3) (e : Edge H) :
    forceOperator H p (Pi.single e 1) = loadWorkEquiv.symm (unorderedFunctional p e.val) := by
  apply loadWorkEquiv.injective
  rw [loadWork_forceOperator, LinearEquiv.apply_symm_apply]
  exact LinearMap.ext fun u => stressOperator_single H p u e

/-- A unit copied coefficient induces the ordinary load of its actual
edge in its actual body, independently of the displayed prefix. -/
theorem ambientCopiedLoads_single
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (i : BodyEdgeOccurrence G T) :
    ambientCopiedLoads G p T (Pi.single i 1) =
      Pi.single i.1 (loadWorkEquiv.symm (unorderedFunctional p i.2.val)) := by
  rcases i with ⟨C, e⟩
  funext D
  by_cases hDC : D = C
  · subst D
    have hr : bodyCopyRestriction G T C (Pi.single (⟨C, e⟩ : BodyEdgeOccurrence G T) 1) =
        Pi.single e 1 := by
      funext f
      by_cases hfe : f = e <;>
        simp [bodyCopyRestriction_apply, Pi.single_apply, hfe]
    rw [ambientCopiedLoads_apply, bodyCopyForces_apply, hr, forceOperator_single_eq]
    simp
  · have hr : bodyCopyRestriction G T D (Pi.single (⟨C, e⟩ : BodyEdgeOccurrence G T) 1) = 0 := by
      funext f
      have hne : (⟨D, f⟩ : BodyEdgeOccurrence G T) ≠ ⟨C, e⟩ :=
        fun h => hDC (congrArg Sigma.fst h)
      simp [bodyCopyRestriction_apply, Pi.single_eq_of_ne hne]
    rw [ambientCopiedLoads_apply, bodyCopyForces_apply, hr, map_zero]
    simp only [Pi.single_eq_of_ne hDC]

/-- The same body-edge occurrence, viewed on another prefix containing
both actual endpoints. -/
def retargetBodyOccurrence (G : SimpleGraph V) {S : Finset V} (T : Finset V)
    (i : BodyEdgeOccurrence G S) (hi : ∀ v, v ∈ i.2.val → v ∈ T) :
    BodyEdgeOccurrence G T :=
  ⟨i.1, ⟨i.2.val, by
    have he : (cliqueOn (i.1.val ∩ S)).Adj i.2.val.out.1 i.2.val.out.2 := by
      rw [← SimpleGraph.mem_edgeSet, Sym2.mk, i.2.val.out_eq]
      exact i.2.property
    rw [← i.2.val.out_eq]
    exact ⟨he.1,
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp he.2.1).1, hi _ (Sym2.out_fst_mem _)⟩,
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp he.2.2).1, hi _ (Sym2.out_snd_mem _)⟩⟩⟩⟩

private theorem retarget_duplicate_mode
    (G : SimpleGraph V) (p : Placement V 3) {S : Finset V} (T : Finset V)
    (i k : BodyEdgeOccurrence G S)
    (hi : ∀ v, v ∈ i.2.val → v ∈ T) (hk : ∀ v, v ∈ k.2.val → v ∈ T)
    (hik : underlyingCopiedEdge G S i = underlyingCopiedEdge G S k) :
    ambientCopiedLoads G p S (Pi.single i 1 - Pi.single k 1) ∈
      duplicateLoadsInAmbient G p T := by
  let j := retargetBodyOccurrence G T i hi
  let l := retargetBodyOccurrence G T k hk
  have he : i.2.val = k.2.val :=
    congrArg (fun e : Edge (maskedGraph G S) => e.val) hik
  have hjl : underlyingCopiedEdge G T j = underlyingCopiedEdge G T l := by
    apply Subtype.ext
    change i.2.val = k.2.val
    exact he
  have hsingle (m : BodyEdgeOccurrence G T) :
      fiberSum (underlyingCopiedEdge G T) (Pi.single m (1 : ℝ)) =
        Pi.single (underlyingCopiedEdge G T m) 1 := by
    rw [fiberSum_apply, Finset.sum_eq_single m]
    · simp [← Pi.single_smul]
      funext e
      by_cases he : e = underlyingCopiedEdge G T m <;> simp [Pi.single_apply, he]
    · intro q _ hqm
      simp [Pi.single_eq_of_ne hqm]
    · simp
  apply (mem_duplicateLoadsInAmbient_iff G p T _).mpr
  refine ⟨Pi.single j 1 - Pi.single l 1, ?_, ?_⟩
  · rw [map_sub]
    change fiberSum (underlyingCopiedEdge G T) (Pi.single j 1) -
      fiberSum (underlyingCopiedEdge G T) (Pi.single l 1) = 0
    rw [hsingle j, hsingle l, hjl, sub_self]
  · rw [map_sub, map_sub, ambientCopiedLoads_single, ambientCopiedLoads_single,
      ambientCopiedLoads_single, ambientCopiedLoads_single]
    rfl

/-- Decompose a cancelling coefficient family into opposite-copy modes.
Only modes starting at a nonzero coefficient need to be considered. -/
private theorem cancelled_copy_image_mem
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3) (T : Finset V)
    (a : BodyEdgeOccurrence G T → ℝ) (ha : copyAggregate G T a = 0)
    (P : Submodule ℝ (Body G → Velocity V 3))
    (hmodes : ∀ i k, a i ≠ 0 →
      underlyingCopiedEdge G T i = underlyingCopiedEdge G T k →
        ambientCopiedLoads G p T (Pi.single i 1 - Pi.single k 1) ∈ P) :
    ambientCopiedLoads G p T a ∈ P := by
  let f := underlyingCopiedEdge G T
  let r : Edge (maskedGraph G T) → BodyEdgeOccurrence G T :=
    fun e => Classical.choose (underlyingCopiedEdge_surjective G hG T e)
  have hr (e) : f (r e) = e :=
    Classical.choose_spec (underlyingCopiedEdge_surjective G hG T e)
  have hunit : (∑ i, a i • Pi.single i 1) = a := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
      Finset.univ_sum_single a
  have heq : (∑ i, a i • (Pi.single i 1 - Pi.single (r (f i)) 1)) = a := by
    calc
      _ = a - fiberSum (r ∘ f) a := by
        simp only [smul_sub, Finset.sum_sub_distrib, hunit,
          fiberSum_apply, Function.comp_apply]
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        apply congrArg (fun b : BodyEdgeOccurrence G T → ℝ => a x • b)
        funext e
        by_cases he : e = r (f x) <;> simp [Pi.single_apply, he]
      _ = a := by
        rw [← fiberSum_comp f r a, show fiberSum f a = 0 from ha, map_zero, sub_zero]
  rw [← heq, map_sum]
  apply Submodule.sum_mem
  intro i _
  by_cases hai : a i = 0
  · simp [hai]
  · rw [map_smul]
    exact P.smul_mem (a i) (hmodes i (r (f i)) hai (hr (f i)).symm)

theorem duplicateLoadsInAmbient_le_whole
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3) (T : Finset V) :
    duplicateLoadsInAmbient G p T ≤ duplicateLoadsInAmbient G p Finset.univ := by
  intro F hF
  obtain ⟨a, ha, rfl⟩ := (mem_duplicateLoadsInAmbient_iff G p T F).mp hF
  apply cancelled_copy_image_mem G hG p T a ha
  intro i k _ hik
  exact retarget_duplicate_mode G p Finset.univ i k
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) hik

/-- If duplicate loads vanish outside a prefix, every copied coefficient
in every representing duplicate family also vanishes there. This is the
specific application of Lemma 6.1 in the paper's proof of equation (4). -/
theorem duplicate_coefficients_supported_of_loads_supported
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V)
    (a : BodyEdgeOccurrence M.graph Finset.univ → ℝ)
    (ha : copyAggregate M.graph Finset.univ a = 0)
    (hF : ∀ C v, v ∉ T → (bodyCopyForces M.graph p Finset.univ a C).val v = 0) :
    CopiedSupportedOn M.graph T a := by
  intro e he
  obtain ⟨v, hve, hvT⟩ := he
  let b : Body M.graph → V → ℝ := fun C =>
    starCoordinates (cliqueOn (C.val ∩ Finset.univ)) v
      (bodyCopyRestriction M.graph Finset.univ C a)
  have hnonzero (C : Body M.graph) (w : V) (h : b C w ≠ 0) :
      v ∈ C.val ∧ w ∈ C.val ∧ w ≠ v := by
    have hadj : (cliqueOn (C.val ∩ Finset.univ)).Adj v w := by
      by_contra hn
      exact h (starCoordinates_of_not_adj _ _ _ _ hn)
    exact ⟨(Finset.mem_inter.mp hadj.2.1).1,
      (Finset.mem_inter.mp hadj.2.2).1, hadj.1.symm⟩
  have hout (C : Body M.graph) (hC : v ∉ C.val) (w : V) : b C w = 0 := by
    by_contra hn
    exact hC (hnonzero C w hn).1
  have hsum (w : V) : (∑ C : Body M.graph, b C w) = 0 := by
    have h := congrArg
      (fun z => starCoordinates (maskedGraph M.graph Finset.univ) v z w) ha
    rw [copyAggregate_eq_sum_extensions, map_sum] at h
    simpa only [Finset.sum_apply, starCoordinates_extendEdgeCoefficients,
      map_zero, Pi.zero_apply, b] using h
  let I := {C : Body M.graph // v ∈ C.val}
  have hcancel (w : V) : (∑ i : I, b i.val w) = 0 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun C : Body M.graph => v ∈ C.val) (fun C => b C w)
    have hz : (∑ C : {C : Body M.graph // v ∉ C.val}, b C.val w) = 0 :=
      Finset.sum_eq_zero (fun C _ => hout C.val C.property w)
    rw [hz, add_zero, hsum] at hsplit
    exact hsplit
  have hbalance (i : I) : (∑ w, b i.val w • (p v - p w)) = 0 := by
    change (∑ w, starCoordinates (cliqueOn (i.val.val ∩ Finset.univ)) v
      (bodyCopyRestriction M.graph Finset.univ i.val a) w • (p v - p w)) = 0
    rw [sum_starCoordinates_eq_incident, ← forceOperator_vertex]
    exact hF i.val v hvT
  have hz := copied_star_coefficients_eq_zero M p hp v (fun i : I => i.val.val)
    (Subtype.val_injective.comp Subtype.val_injective)
    (fun i => i.val.property) (fun i => i.property) (fun i : I => b i.val)
    (fun i w h => Finset.mem_erase.mpr
      ⟨(hnonzero i.val w h).2.2, (hnonzero i.val w h).2.1⟩)
    hcancel hbalance
  have hvC : v ∈ e.1.val := by
    obtain ⟨w, hew⟩ := Sym2.mem_iff_exists.mp hve
    have hadj := e.2.property
    rw [hew] at hadj
    exact (Finset.mem_inter.mp hadj.2.1).1
  have h := hz ⟨e.1, hvC⟩
    (incidentOther (cliqueOn (e.1.val ∩ Finset.univ)) v ⟨e.2, hve⟩)
  simpa only [b, starCoordinates_incidentOther, bodyCopyRestriction_apply] using h

theorem supported_duplicate_loads_mem_prefix
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3) (T : Finset V)
    (a : BodyEdgeOccurrence G Finset.univ → ℝ)
    (ha : copyAggregate G Finset.univ a = 0) (hs : CopiedSupportedOn G T a) :
    ambientCopiedLoads G p Finset.univ a ∈ duplicateLoadsInAmbient G p T := by
  apply cancelled_copy_image_mem G hG p Finset.univ a ha
  intro i k hai hik
  have hi (v : V) (hvi : v ∈ i.2.val) : v ∈ T := by
    by_contra hvT
    exact hai (hs i ⟨v, hvi, hvT⟩)
  have he : i.2.val = k.2.val := congrArg Subtype.val hik
  have hk (v : V) (hvk : v ∈ k.2.val) : v ∈ T := hi v (he.symm ▸ hvk)
  exact retarget_duplicate_mode G p T i k hi hk hik

/-- Proposition 6.2(4), with the original compatible and duplicate
spaces embedded by their actual coordinate values into a common ambient
space. All induced vertex sets, including the empty set, are included. -/
theorem duplicate_loads_prefix_identity
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    duplicateLoadsInAmbient M.graph p Finset.univ ⊓
      compatibleLoadsInAmbient M.graph p T = duplicateLoadsInAmbient M.graph p T := by
  apply le_antisymm
  · intro F hF
    obtain ⟨a, ha, rfl⟩ :=
      (mem_duplicateLoadsInAmbient_iff M.graph p Finset.univ F).mp hF.1
    obtain ⟨H, _, hH⟩ := hF.2
    have hzero (C : Body M.graph) (v : V) (hv : v ∉ T) :
        (bodyCopyForces M.graph p Finset.univ a C).val v = 0 := by
      have hval := congrFun (congrFun hH C) v
      exact hval.symm.trans ((H C).property.2 v
        (fun h => hv (Finset.mem_inter.mp h).2))
    exact supported_duplicate_loads_mem_prefix M.graph M.covered p T a ha
      (duplicate_coefficients_supported_of_loads_supported M p hp T a ha hzero)
  · intro F hF
    exact ⟨duplicateLoadsInAmbient_le_whole M.graph M.covered p T hF,
      Submodule.map_mono (duplicateBodyLoads_le_compatible M.graph p T) hF⟩

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0071

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityMainRecovery01/block_0071/Consolidated/RigidityMainRecovery01.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityMainRecovery01/checkpoint_0071.json"

section BundleSource0072
/- Source: Papers/RigidityCenterDescent.lean -/



@[expose] public section

/-!
# Descent of the virtual center to the prior coefficient field

A unique common center of coefficient-defined alternating forms is itself
defined over that field.  The proof descends a nonzero solution of the
literal common-kernel equations, then uses their three-dimensional center
space to identify the whole twist space.  Projective scalar uniqueness
also descends, by dividing one nonzero coordinate.
-/

namespace Papers.Rigidity

noncomputable section

open Matrix
open scoped Matrix

def coefficientTwistMatrix {K : Type*} [Field K] (X : CoefficientTwist K) :
    Matrix (Fin 4) (Fin 4) K :=
  !![0, -X.1 2, X.1 1, X.2 0;
     X.1 2, 0, -X.1 0, X.2 1;
     -X.1 1, X.1 0, 0, X.2 2;
     -X.2 0, -X.2 1, -X.2 2, 0]

theorem coefficientTwistMatrix_map {K : Type*} [Field K] [Algebra K ℝ]
    (X : CoefficientTwist K) :
    (coefficientTwistMatrix X).map (algebraMap K ℝ) = twistMatrix (realTwist X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientTwistMatrix, twistMatrix, realTwist]

def pointFromHomogeneousVector (v : Fin 4 → ℝ) : HomogeneousPoint :=
  (![v 0, v 1, v 2], v 3)

@[simp] theorem homogeneousVector_pointFromHomogeneousVector (v : Fin 4 → ℝ) :
    homogeneousVector (pointFromHomogeneousVector v) = v := by
  ext i
  fin_cases i <;> rfl

theorem finrank_homogeneousCenterSpace (q : HomogeneousPoint) (hq : q ≠ 0) :
    Module.finrank ℝ (homogeneousCenterSpace q) = 3 := by
  by_cases hs : q.2 = 0
  · have hd : q.1 ≠ 0 := fun h => hq (Prod.ext h hs)
    have he : q = (q.1, 0) := Prod.ext rfl hs
    rw [he, homogeneousCenterSpace_infinite, finrank_infiniteCenterSpace _ hd]
  · rw [homogeneousCenterSpace_normalize q hs, finrank_finiteCenterSpace]

/-- A scalar relating two nonzero coefficient vectors belongs to the
coefficient field: one nonzero coordinate determines it as a quotient. -/
theorem projective_scalar_descent
    {K L J : Type*} [Field K] [Field L] [Algebra K L]
    (u v : J → K) (hu : u ≠ 0) (c : L) (hc : c ≠ 0)
    (hscale : c • (fun j => algebraMap K L (u j)) =
      (fun j => algebraMap K L (v j))) :
    ∃ a : K, a ≠ 0 ∧ a • u = v := by
  have hnot : ¬ ∀ j, u j = 0 := fun h => hu (funext h)
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  have hjmap : algebraMap K L (u j) ≠ 0 := by
    simpa only [map_zero] using (RingHom.injective (algebraMap K L)).ne hj
  let a : K := v j / u j
  have hamap : algebraMap K L a = c := by
    dsimp [a]
    rw [map_div₀]
    apply (div_eq_iff hjmap).mpr
    exact (congrFun hscale j).symm
  have ha : a ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hamap
    exact hc hamap.symm
  refine ⟨a, ha, ?_⟩
  ext i
  apply RingHom.injective (algebraMap K L)
  change algebraMap K L (a * u i) = algebraMap K L (v i)
  rw [map_mul, hamap]
  exact congrFun hscale i

theorem mapped_homogeneousVector_ne_zero
    {K : Type*} [Field K] [Algebra K ℝ]
    (q : Fin 4 → K) (hq : q ≠ 0) :
    pointFromHomogeneousVector (fun i => algebraMap K ℝ (q i)) ≠ 0 := by
  intro hz
  have hv := congrArg homogeneousVector hz
  rw [homogeneousVector_pointFromHomogeneousVector,
    show homogeneousVector (0 : HomogeneousPoint) = 0 from homogeneousVectorLinear.map_zero] at hv
  apply hq
  ext i
  apply RingHom.injective (algebraMap K ℝ)
  change algebraMap K ℝ (q i) = algebraMap K ℝ 0
  rw [map_zero]
  exact congrFun hv i

/-- Lemma 3.4 with its field of definition retained explicitly.  Both
the common homogeneous center and the scalar witnessing its projective
uniqueness belong to the field chosen before the generic new pin.

The literal matrix/kernel conclusion includes finite centers and centers
at infinity, without a chart assumption.
-/
theorem generic_alternating_space_center_defined_over_coefficients
    {K I : Type*} [Field K] [Algebra K ℝ]
    (X : I → CoefficientTwist K) (p : Vec3) (hp : AlgebraicIndependent K p)
    (hdim : 3 ≤ Module.finrank K (Submodule.span K (Set.range X)))
    (hrank : Module.finrank ℝ
      (matrixPinContraction (coefficientTwistSpan X) p).range ≤ 2) :
    ∃ q : Fin 4 → K, q ≠ 0 ∧
      (∀ Y : Twist, Y ∈ coefficientTwistSpan X ↔
        twistMatrix Y *ᵥ (fun j => algebraMap K ℝ (q j)) = 0) ∧
      ∀ r : Fin 4 → K, r ≠ 0 →
        (∀ Y : Twist, Y ∈ coefficientTwistSpan X ↔
          twistMatrix Y *ᵥ (fun j => algebraMap K ℝ (r j)) = 0) →
        ∃ c : K, c ≠ 0 ∧ c • q = r := by
  classical
  obtain ⟨q₀, hq₀, hW₀, hu₀⟩ :=
    generic_alternating_coefficient_space_unique_projective_center X p hp hdim hrank
  let a : (I × Fin 4) → Fin 4 → K := fun ij => coefficientTwistMatrix (X ij.1) ij.2
  have hqvec : homogeneousVector q₀ ≠ 0 := by
    intro hz
    apply hq₀
    apply homogeneousVectorLinear_injective
    rw [map_zero]
    exact hz
  have hrows (ij : I × Fin 4) :
      (fun j => algebraMap K ℝ (a ij j)) ⬝ᵥ homogeneousVector q₀ = 0 := by
    have hm := (hW₀ (realTwist (X ij.1))).mp (Submodule.subset_span ⟨ij.1, rfl⟩)
    rw [← coefficientTwistMatrix_map] at hm
    exact congrFun hm ij.2
  obtain ⟨q, hq, hqa⟩ :=
    exists_nonzero_kernel_over_coefficient_field a (homogeneousVector q₀) hqvec hrows
  let qr := pointFromHomogeneousVector (fun i => algebraMap K ℝ (q i))
  have hqr : qr ≠ 0 := mapped_homogeneousVector_ne_zero q hq
  have hqi (i : I) :
      twistMatrix (realTwist (X i)) *ᵥ homogeneousVector qr = 0 := by
    rw [← coefficientTwistMatrix_map, homogeneousVector_pointFromHomogeneousVector]
    ext j
    have hz := congrArg (algebraMap K ℝ) (hqa (i, j))
    simpa only [map_zero, Pi.zero_apply, dotProduct, map_sum, map_mul, Matrix.mulVec,
      Matrix.map_apply, a] using hz
  have hle : coefficientTwistSpan X ≤ homogeneousCenterSpace qr := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (mem_homogeneousCenterSpace_iff_matrix_kernel qr _).mpr (hqi i)
  have hWq : coefficientTwistSpan X = homogeneousCenterSpace qr := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [finrank_homogeneousCenterSpace qr hqr, finrank_coefficientTwistSpan]
    exact hdim
  have hqform (Y : Twist) : Y ∈ coefficientTwistSpan X ↔
      twistMatrix Y *ᵥ (fun j => algebraMap K ℝ (q j)) = 0 := by
    rw [hWq, mem_homogeneousCenterSpace_iff_matrix_kernel,
      homogeneousVector_pointFromHomogeneousVector]
  refine ⟨q, hq, hqform, ?_⟩
  intro r hr hWr
  let rr := pointFromHomogeneousVector (fun i => algebraMap K ℝ (r i))
  have hrr : rr ≠ 0 := mapped_homogeneousVector_ne_zero r hr
  have hqworld (Y : Twist) : Y ∈ coefficientTwistSpan X ↔
      twistMatrix Y *ᵥ homogeneousVector qr = 0 := by
    simpa only [homogeneousVector_pointFromHomogeneousVector, qr] using hqform Y
  have hrworld (Y : Twist) : Y ∈ coefficientTwistSpan X ↔
      twistMatrix Y *ᵥ homogeneousVector rr = 0 := by
    simpa only [homogeneousVector_pointFromHomogeneousVector, rr] using hWr Y
  obtain ⟨c, hc, hcq⟩ := hu₀ qr hqr hqworld
  obtain ⟨d, hd, hdr⟩ := hu₀ rr hrr hrworld
  have hscale : (d / c) • qr = rr := by
    rw [← hcq, smul_smul, div_mul_cancel₀ d hc, hdr]
  have hcoordinates := congrArg homogeneousVectorLinear hscale
  rw [map_smul] at hcoordinates
  change (d / c) • homogeneousVector qr = homogeneousVector rr at hcoordinates
  have hscaleCoordinates : (d / c) • (fun j => algebraMap K ℝ (q j)) =
      (fun j => algebraMap K ℝ (r j)) := by
    simpa only [qr, rr, homogeneousVector_pointFromHomogeneousVector] using hcoordinates
  exact projective_scalar_descent q r hq (d / c) (div_ne_zero hd hc) hscaleCoordinates

end

end Papers.Rigidity

end
end BundleSource0072

section BundleSource0073
/- Source: Papers/RigidityTypeAStar.lean -/




@[expose] public section

/-!
# Lemma 3.7: the actual stress star at a type-A vertex

A type-A vertex belongs to exactly two maximal bodies, both tetrahedra,
whose intersection consists of that vertex. This definition uses the
actual graph bodies. The star space below is the image of the ordinary
stress space on the actual incident edges.

The deletion-rank identity bounds its dimension by one. A nonzero star
supported on four bars would place the centre and its four neighbours in
an ambient rigid cluster. Closure would then put the centre in a body of
order at least five, contradicting the two tetrahedral bodies.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint SupportedCode
open scoped Classical

variable {V : Type} [Fintype V]

/-- The type-A alternative of Lemma 3.3, expressed using actual maximal
bodies and their exact common vertex. `TwoBodyPin` includes exhaustivity. -/
def TwoBodyPin.IsTypeA {G : SimpleGraph V} {v : V} (Q : TwoBodyPin G v) : Prop :=
  Q.left.val.card = 4 ∧ Q.right.val.card = 4 ∧ Q.IsPoint

theorem TwoBodyPin.IsTypeA.degree_eq_six
    (M : MinimalCounterexample V) {v : V} {Q : TwoBodyPin M.graph v}
    (hA : Q.IsTypeA) : M.graph.degree v = 6 := by
  have hd := TwoBodyPin.degree_add_correction M v Q
  rw [if_pos hA.2.2, add_zero,
    clique_degree _ _ Q.left_mem, clique_degree _ _ Q.right_mem,
    hA.1, hA.2.1] at hd
  exact hd

/-- The bound holds even when the actual stress-star image is zero. -/
theorem TwoBodyPin.typeA_stressStar_finrank_le_one
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hA : Q.IsTypeA) (p : Placement V 3) (hgen : IsGenericPlacement p) :
    Module.finrank ℝ (stressStarCode M.graph v (StressSpace M.graph p)) ≤ 1 := by
  rw [stressStar_finrank_eq_degree_sub_deletionRankDrop M.graph p hgen v,
    hA.degree_eq_six M]
  have hdrop := M.five_le_deletionRankDrop v
  omega

/-- Every nonzero vector in the actual star image has at least five
nonzero incident-edge coordinates. No chosen scalar system is involved. -/
theorem TwoBodyPin.typeA_stressStar_minimumSupport_five
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hA : Q.IsTypeA) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p) :
    MinimumSupport (stressStarCode M.graph v (StressSpace M.graph p)) 5 := by
  intro a ha hane
  have hfour := stressStarCode_minimumSupport_four M.graph p hp v
    (StressSpace M.graph p) le_rfl a ha hane
  obtain ⟨ω, hω, rfl⟩ := Submodule.mem_map.mp ha
  let S := support (starRestriction M.graph v ω)
  let N := S.image (incidentOther M.graph v)
  change 5 ≤ S.card
  change 4 ≤ S.card at hfour
  by_contra hsmall
  have hScard : S.card = 4 := by omega
  have hNcard : N.card = 4 := by
    rw [Finset.card_image_of_injective S (incidentOther_injective M.graph v), hScard]
  have hNadj (w : V) (hw : w ∈ N) : M.graph.Adj v w := by
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    exact incidentOther_adj M.graph v e
  have hout (w : V) (hw : w ∉ N) : starCoordinates M.graph v ω w = 0 := by
    by_cases hadj : M.graph.Adj v w
    · let e : IncidentEdge M.graph v :=
        ⟨⟨s(v,w), hadj⟩, Sym2.mem_mk_left v w⟩
      have hew : incidentOther M.graph v e = w :=
        Sym2.congr_right.mp (Sym2.other_spec e.property)
      have he : e ∉ S := fun he => hw (Finset.mem_image.mpr ⟨e, he, hew⟩)
      have hzero : starRestriction M.graph v ω e = 0 := by
        simpa only [S, mem_support, not_not] using he
      rw [← hew, starCoordinates_incidentOther]
      exact hzero
    · exact starCoordinates_of_not_adj M.graph v w ω hadj
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hcluster := rigidCluster_of_stress_star_four M.graph p hgen hp v N
    hNcard hNadj ⟨ω, hω⟩ hout
    ⟨incidentOther M.graph v e, Finset.mem_image.mpr ⟨e, he, rfl⟩, by
      rw [starCoordinates_incidentOther]
      exact (mem_support _ e).mp he⟩
  have hvN : v ∉ N := fun hv => (hNadj v hv).ne rfl
  have hsize : (insert v N).card = 5 := by
    rw [Finset.card_insert_of_notMem hvN, hNcard]
  have hclique := M.rigidCluster_isClique (insert v N) (by omega) hcluster
  obtain ⟨B, hNB, hB⟩ := exists_body_containing M.graph (insert v N) (by omega) hclique
  have hBfive : 5 ≤ B.card := by
    simpa only [hsize] using Finset.card_le_card hNB
  have hvB : v ∈ B := hNB (Finset.mem_insert_self v N)
  have hBfour : B.card = 4 := by
    rcases Q.exhaustive ⟨B, hB⟩ hvB with h | h
    · have hval : B = Q.left.val := congrArg Subtype.val h
      simpa only [hval] using hA.1
    · have hval : B = Q.right.val := congrArg Subtype.val h
      simpa only [hval] using hA.2.1
  omega

/-- Lemma 3.7 in one statement: the nonzero actual star image is a line,
and every nonzero word in that line has at least five nonzero coordinates. -/
theorem TwoBodyPin.lemma_three_seven
    (M : MinimalCounterexample V) {v : V} (Q : TwoBodyPin M.graph v)
    (hA : Q.IsTypeA) (p : Placement V 3) (hgen : IsGenericPlacement p)
    (hp : GeneralPosition.InGeneralPosition p)
    (hstar : stressStarCode M.graph v (StressSpace M.graph p) ≠ ⊥) :
    Module.finrank ℝ (stressStarCode M.graph v (StressSpace M.graph p)) = 1 ∧
      MinimumSupport (stressStarCode M.graph v (StressSpace M.graph p)) 5 := by
  have hle := Q.typeA_stressStar_finrank_le_one M hA p hgen
  have hpos : Module.finrank ℝ (stressStarCode M.graph v (StressSpace M.graph p)) ≠ 0 :=
    fun hzero => hstar (Submodule.finrank_eq_zero.mp hzero)
  exact ⟨by omega, Q.typeA_stressStar_minimumSupport_five M hA p hgen hp⟩

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0073

section BundleSource0074
/- Source: Papers/RigidityPriorityOrders.lean -/




@[expose] public section

/-!
# Real priorities and their finite ordering

The supported subspace is defined directly by comparing each real priority
with the marker's priority.  Sorting is used only to identify this genuine
subspace with the existing finite-order construction.  The orbit identity
below is the finite part of the independent-priority expectation formula.
No distributional or independence hypothesis is built into these definitions.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open scoped Classical BigOperators

variable {K : Type*} [Field K]

/-- The coordinates whose priorities are strictly before the extra marker.
Ties are excluded from the support, as in the literal strict comparison. -/
def priorityCode {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) : Submodule K (Fin n → K) where
  carrier := {w | w ∈ W ∧ ∀ i : Fin n,
    ¬ x i.castSucc < x (Fin.last n) → w i = 0}
  zero_mem' := ⟨W.zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨W.add_mem hu hv, fun i hi => by simp [hu' i hi, hv' i hi]⟩
  smul_mem' := by
    rintro a w ⟨hw, hw'⟩
    exact ⟨W.smul_mem a hw, fun i hi => by simp [hw' i hi]⟩

@[simp] theorem mem_priorityCode {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) (w : Fin n → K) :
    w ∈ priorityCode W x ↔ w ∈ W ∧ ∀ i : Fin n,
      ¬ x i.castSucc < x (Fin.last n) → w i = 0 := Iff.rfl

theorem priorityCode_le {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) : priorityCode W x ≤ W := fun _ h => h.1

/-- The actual supported-subspace dimension, viewed as a real random variable. -/
def priorityDimension {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) : ℝ := Module.finrank K (priorityCode W x)

theorem priorityDimension_nonneg {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) : 0 ≤ priorityDimension W x := Nat.cast_nonneg _

theorem priorityDimension_le {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Fin (n + 1) → ℝ) : priorityDimension W x ≤ (Module.finrank K W : ℝ) := by
  change (Module.finrank K (priorityCode W x) : ℝ) ≤ (Module.finrank K W : ℝ)
  exact_mod_cast Submodule.finrank_mono (priorityCode_le W x)

/-- A permutation lists the labels in increasing order of their priorities. -/
def priorityOrderMatches {m : ℕ} (x : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) : Prop :=
  ∀ i j : Fin m, σ.symm i < σ.symm j ↔ x i < x j

theorem exists_priorityOrderMatches {m : ℕ} (x : Fin m → ℝ)
    (hx : Function.Injective x) :
    ∃ σ : Equiv.Perm (Fin m), priorityOrderMatches x σ := by
  let e := @Fintype.orderIsoFinOfCardEq (Fin m) (LinearOrder.lift' x hx)
    inferInstance m (Fintype.card_fin m)
  refine ⟨e.toEquiv, ?_⟩
  intro i j
  exact @OrderIso.lt_iff_lt (Fin m) (Fin m)
    (LinearOrder.lift' x hx).toPreorder inferInstance
    (@OrderIso.symm (Fin m) (Fin m) inferInstance (LinearOrder.lift' x hx).toLE e) i j

theorem priorityOrderMatches_unique {m : ℕ} {x : Fin m → ℝ}
    {σ τ : Equiv.Perm (Fin m)}
    (hσ : priorityOrderMatches x σ) (hτ : priorityOrderMatches x τ) : σ = τ := by
  have hm : StrictMono (fun k => τ.symm (σ k)) := by
    intro a b hab
    apply (hτ (σ a) (σ b)).mpr
    apply (hσ (σ a) (σ b)).mp
    simpa only [Equiv.symm_apply_apply] using hab
  apply Equiv.ext
  intro k
  have hk : τ.symm (σ k) = k := congrFun hm.eq_id k
  calc
    σ k = τ (τ.symm (σ k)) := (τ.apply_symm_apply (σ k)).symm
    _ = τ k := congrArg τ hk

theorem priorityCode_eq_precedingCode {n : ℕ}
    (W : Submodule K (Fin n → K)) {x : Fin (n + 1) → ℝ}
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : priorityOrderMatches x σ) :
    priorityCode W x = precedingCode W σ := by
  have hiff (i : Fin n) :
      (¬ x i.castSucc < x (Fin.last n)) ↔
        σ.symm (Fin.last n) < σ.symm i.castSucc := by
    rw [← hσ i.castSucc (Fin.last n)]
    have hne : σ.symm i.castSucc ≠ σ.symm (Fin.last n) :=
      σ.symm.injective.ne (Fin.castSucc_ne_last i)
    constructor
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
    · exact fun h => not_lt_of_ge h.le
  ext w
  constructor
  · rintro ⟨hw, hz⟩
    exact ⟨hw, fun i hi => hz i ((hiff i).mpr hi)⟩
  · rintro ⟨hw, hz⟩
    exact ⟨hw, fun i hi => hz i ((hiff i).mp hi)⟩

theorem priorityDimension_eq_of_matches {n : ℕ}
    (W : Submodule K (Fin n → K)) {x : Fin (n + 1) → ℝ}
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : priorityOrderMatches x σ) :
    priorityDimension W x = (Module.finrank K (precedingCode W σ) : ℝ) :=
  congrArg (fun A : Submodule K (Fin n → K) => (Module.finrank K A : ℝ))
    (priorityCode_eq_precedingCode W hσ)

/-- On distinct priorities, the dimension is a finite sum of chamber values.
The measure-theoretic bridge uses this formula to prove integrability. -/
theorem priorityDimension_eq_chamber_sum {n : ℕ}
    (W : Submodule K (Fin n → K)) (x : Fin (n + 1) → ℝ)
    (hx : Function.Injective x) :
    priorityDimension W x = ∑ σ : Equiv.Perm (Fin (n + 1)),
      if priorityOrderMatches x σ then (Module.finrank K (precedingCode W σ) : ℝ)
      else 0 := by
  obtain ⟨σ, hσ⟩ := exists_priorityOrderMatches x hx
  rw [priorityDimension_eq_of_matches W hσ]
  symm
  calc
    _ = if priorityOrderMatches x σ then
        (Module.finrank K (precedingCode W σ) : ℝ) else 0 := by
      apply Finset.sum_eq_single σ
      · intro τ _ hτσ
        exact if_neg (fun hτ => hτσ (priorityOrderMatches_unique hτ hσ))
      · intro h
        exact (h (Finset.mem_univ σ)).elim
    _ = _ := if_pos hσ

theorem priorityOrderMatches_relabel {m : ℕ} {x : Fin m → ℝ}
    {σ : Equiv.Perm (Fin m)} (hσ : priorityOrderMatches x σ)
    (τ : Equiv.Perm (Fin m)) :
    priorityOrderMatches (x ∘ τ) (σ.trans τ.symm) := by
  intro i j
  simpa only [Function.comp_apply, Equiv.symm_trans, Equiv.trans_apply,
    Equiv.symm_symm] using hσ (τ i) (τ j)

/-- Relabeling the priorities traverses every possible ordering once. -/
def priorityRelabelEquiv {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin m) where
  toFun τ := σ.trans τ.symm
  invFun ρ := ρ.symm.trans σ
  left_inv τ := by ext i; simp
  right_inv ρ := by ext i; simp

/-- The orbit sum of literal priority dimensions is exactly the finite-order
sum. This identity holds for every injective real priority vector. -/
theorem sum_priorityDimension_relabel {n : ℕ}
    (W : Submodule K (Fin n → K)) (x : Fin (n + 1) → ℝ)
    (hx : Function.Injective x) :
    (∑ τ : Equiv.Perm (Fin (n + 1)), priorityDimension W (x ∘ τ)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        (Module.finrank K (precedingCode W σ) : ℝ) := by
  obtain ⟨σ, hσ⟩ := exists_priorityOrderMatches x hx
  calc
    _ = ∑ τ : Equiv.Perm (Fin (n + 1)),
        (Module.finrank K (precedingCode W (σ.trans τ.symm)) : ℝ) := by
      apply Finset.sum_congr rfl
      intro τ _
      exact priorityDimension_eq_of_matches W (priorityOrderMatches_relabel hσ τ)
    _ = _ := Equiv.sum_comp (priorityRelabelEquiv σ)
      (fun ρ => (Module.finrank K (precedingCode W ρ) : ℝ))

end

end Papers.Rigidity.SupportedCode

end
end BundleSource0074

section BundleSource0075
/- Source: Papers/RigidityAlgebraicGeneric.lean -/





@[expose] public section

/-!
# Ordinary algebraically independent bar-joint coordinates

The rational polynomial matrix below is identified entry by entry with
the actual real rigidity operator.  Injective polynomial evaluation
therefore proves that algebraically independent coordinates attain all
graph ranks.  Together with the actual length-fiber theorem, this links
the conventional generic local-rigidity statement to the rank target.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open MvPolynomial
open scoped Classical BigOperators

variable {V : Type} [Fintype V] {d : ℕ}

def placementCoordinates (p : Placement V d) : V × Fin d → ℝ :=
  fun c => p c.1 c.2

def barCoordinateUnit {R : Type*} [CommRing R] (c : V × Fin d) : V → Fin d → R :=
  fun v i => if (v, i) = c then 1 else 0

/-- The literal bar row on a coordinate unit, over any coefficient ring. -/
def barMatrix {R : Type*} [CommRing R] (G : SimpleGraph V) (p : V → Fin d → R) :
    Matrix (V × V) (V × Fin d) R :=
  fun e c => if G.Adj e.1 e.2 then
    ∑ i : Fin d, (p e.1 i - p e.2 i) *
      (barCoordinateUnit c e.1 i - barCoordinateUnit c e.2 i)
    else 0

def velocityCoordinateBasis : Module.Basis (V × Fin d) ℝ (Velocity V d) :=
  Module.Basis.ofEquivFun (LinearEquiv.curry ℝ ℝ V (Fin d)).symm

theorem velocityCoordinateBasis_apply (c : V × Fin d) :
    velocityCoordinateBasis c = barCoordinateUnit (R := ℝ) c := by
  rw [velocityCoordinateBasis, Module.Basis.coe_ofEquivFun]
  funext v i
  simp [barCoordinateUnit, LinearEquiv.coe_curry, Pi.single_apply]

theorem barMatrix_eq_coordinateMatrix (G : SimpleGraph V) (p : Placement V d) :
    barMatrix G p = LinearMap.toMatrix velocityCoordinateBasis
      (Pi.basisFun ℝ (V × V)) (rigidityOperator G p) := by
  ext e c
  rw [LinearMap.toMatrix_apply, velocityCoordinateBasis_apply]
  simp only [Pi.basisFun_repr]
  by_cases he : G.Adj e.1 e.2
  · simp only [barMatrix, he, if_true,
      rigidityOperator_apply_of_adj G p _ e.1 e.2 he, edgeConstraint]
  · simp only [barMatrix, he, if_false,
      rigidityOperator_apply_of_not_adj G p _ e.1 e.2 he]

theorem barMatrix_rank_eq (G : SimpleGraph V) (p : Placement V d) :
    (barMatrix G p).rank = rigidityRank G p := by
  rw [barMatrix_eq_coordinateMatrix,
    Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun ℝ (V × V)) velocityCoordinateBasis,
    Matrix.toLin_toMatrix]
  rfl

theorem map_barMatrix {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (G : SimpleGraph V) (p : V → Fin d → R) :
    (barMatrix G p).map f = barMatrix G (fun v i => f (p v i)) := by
  ext e c
  have hunit (v : V) (i : Fin d) :
      f (barCoordinateUnit (R := R) c v i) = barCoordinateUnit (R := S) c v i := by
    by_cases h : (v, i) = c <;>
      simp only [barCoordinateUnit, h, if_true, if_false, map_zero, map_one]
  by_cases he : G.Adj e.1 e.2
  · simp only [Matrix.map_apply, barMatrix, he, if_true, map_sum, map_mul, map_sub, hunit]
  · simp only [Matrix.map_apply, barMatrix, he, if_false, map_zero]

def rationalBarMatrix (G : SimpleGraph V) :
    Matrix (V × V) (V × Fin d) (MvPolynomial (V × Fin d) ℚ) :=
  barMatrix G (fun v i => X (v, i))

theorem realMatrix_rationalBarMatrix (G : SimpleGraph V) (z : V × Fin d → ℝ) :
    PolynomialRank.realMatrix (rationalBarMatrix (d := d) G) z =
      barMatrix G (fun v i => z (v, i)) := by
  rw [PolynomialRank.realMatrix, rationalBarMatrix, map_barMatrix]
  congr 1
  funext v i
  simp

/-- Ordinary algebraically independent coordinates attain the actual
maximum rigidity rank for every graph on the same labelled vertex set. -/
theorem isGenericPlacement_of_algebraicIndependent
    (p : Placement V d) (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    IsGenericPlacement p := by
  intro G
  have hinj : Function.Injective
      (MvPolynomial.eval₂Hom (Rat.castHom ℝ) (placementCoordinates p)) := by
    intro a b hab
    apply hp
    exact hab
  have hgeneric := PolynomialRank.realMatrix_rank_eq_generic_of_eval_injective
    (rationalBarMatrix (d := d) G) (placementCoordinates p) hinj
  rw [realMatrix_rationalBarMatrix, barMatrix_rank_eq] at hgeneric
  change rigidityRank G p =
    (PolynomialRank.genericMatrix (rationalBarMatrix (d := d) G)).rank at hgeneric
  obtain ⟨q, hq⟩ := exists_rigidityRank_eq_genericRigidityRank G d
  have hqle := PolynomialRank.realMatrix_rank_le_generic
    (rationalBarMatrix (d := d) G) (placementCoordinates q)
  rw [realMatrix_rationalBarMatrix, barMatrix_rank_eq] at hqle
  change rigidityRank G q ≤
    (PolynomialRank.genericMatrix (rationalBarMatrix (d := d) G)).rank at hqle
  change rigidityRank G p = genericRigidityRank G d
  exact le_antisymm (rigidityRank_le_genericRigidityRank G d p)
    (hq ▸ hgeneric.symm ▸ hqle)

/-- The rank definition is equivalent to actual local distance rigidity
at each placement with algebraically independent real coordinates. -/
theorem localRigidity_iff_rank_at_algebraicallyGeneric
    (G : SimpleGraph V) (p : Placement V d)
    (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    IsLocallyDistanceRigid G p ↔ IsGenericallyRigidInDimension G d :=
  isLocallyDistanceRigid_iff_isGenericallyRigid G p
    (isGenericPlacement_of_algebraicIndependent p hp)

end

end Papers.Rigidity.BarJoint

end
end BundleSource0075

section BundleSource0076
/- Source: Papers/RigidityFinalAlgebraic.lean -/





@[expose] public section

/-!
# The graph conclusions at algebraically independent real coordinates

The maximum-rank formulation is connected to the conventional meaning of
generic coordinates by a proved polynomial-matrix comparison.  These
wrappers expose the paper's three graph conclusions with that hypothesis
and with local equality of actual Euclidean distances as the conclusion.
-/

namespace Papers.Rigidity

open BarJoint

variable {V : Type} [Fintype V]

/-- Theorem 1.1 at every real placement whose coordinates are algebraically
independent over the rationals. -/
theorem sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent
    (G : SimpleGraph V) (hconn : VertexConnected G 6) (hcover : K4Covered G)
    (p : Placement V 3)
    (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    IsLocallyDistanceRigid G p :=
  sixConnected_k4Covered_locallyDistanceRigid G hconn hcover p
    (isGenericPlacement_of_algebraicIndependent p hp)

/-- The edge-cover form of Corollary 1.2 at ordinary algebraically
generic real coordinates. -/
theorem sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent
    (G : SimpleGraph V) (hconn : VertexConnected G 6)
    (hcover : RigidSubgraphCovered G) (p : Placement V 3)
    (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    IsLocallyDistanceRigid G p :=
  sixConnected_rigidSubgraphCovered_locallyDistanceRigid G hconn hcover p
    (isGenericPlacement_of_algebraicIndependent p hp)

/-- The ambient-cluster completion form of Corollary 1.2 at ordinary
algebraically generic real coordinates. -/
theorem rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent
    {I : Type} (G : SimpleGraph V) (C : I → Finset V)
    (hC : ∀ i, 4 ≤ (C i).card ∧ RigidCluster G (C i))
    (hconn : VertexConnected (clusterCompletion C) 6)
    (p : Placement V 3)
    (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    IsLocallyDistanceRigid G p :=
  rigidCluster_completion_sixConnected_locallyDistanceRigid G C hC hconn p
    (isGenericPlacement_of_algebraicIndependent p hp)

/-- The literal generic matrix rank in Theorem 1.1. Connectivity supplies
the cardinality needed for the complete-graph rank formula. -/
theorem sixConnected_k4Covered_genericRank
    (G : SimpleGraph V) (hconn : VertexConnected G 6) (hcover : K4Covered G) :
    genericRigidityRank G 3 = 3 * Fintype.card V - 6 := by
  have hrig := sixConnected_k4Covered_rigid G hconn hcover
  change genericRigidityRank G 3 =
    genericRigidityRank (SimpleGraph.completeGraph V) 3 at hrig
  have hcard : 3 ≤ Fintype.card V := by
    have := hconn.1
    omega
  exact hrig.trans (genericCompleteRank_eq hcard)

/-- At every algebraically generic real placement, the actual rigidity
operator has the full rank asserted by Theorem 1.1. -/
theorem sixConnected_k4Covered_rigidityRank_of_algebraicIndependent
    (G : SimpleGraph V) (hconn : VertexConnected G 6) (hcover : K4Covered G)
    (p : Placement V 3)
    (hp : AlgebraicIndependent ℚ (placementCoordinates p)) :
    rigidityRank G p = 3 * Fintype.card V - 6 :=
  (isGenericPlacement_of_algebraicIndependent p hp G).trans
    (sixConnected_k4Covered_genericRank G hconn hcover)

end Papers.Rigidity

end
end BundleSource0076


/- Final endpoint audits; all local proof bodies must be available. -/
set_option maxHeartbeats 0
#print axioms Papers.Rigidity.pairPin_defect_theorem
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.pairPin_defect_theorem to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_pairPin_defect_theorem.json"
#print axioms Papers.Rigidity.PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_PairPinGraph_defect_theorem_at_algebraicallyGeneric_pins.json"
#print axioms Papers.Rigidity.QuantitativeHeight.genericIncidencePrime_height_ge_active_add_sparse
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.QuantitativeHeight.genericIncidencePrime_height_ge_active_add_sparse to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_QuantitativeHeight_genericIncidencePrime_height_ge_active_add_sparse.json"
#print axioms Papers.Rigidity.NullHeight.coefficientMinimalPrime_height_eq_edgeCard
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.NullHeight.coefficientMinimalPrime_height_eq_edgeCard to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_NullHeight_coefficientMinimalPrime_height_eq_edgeCard.json"
#print axioms Papers.Rigidity.PairPinGraph.genericPinRank_eq_genericMotionMatrix_rank
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.PairPinGraph.genericPinRank_eq_genericMotionMatrix_rank to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_PairPinGraph_genericPinRank_eq_genericMotionMatrix_rank.json"
#print axioms Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.PairPinGraph.defect_at_maximal_rank_pins to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_PairPinGraph_defect_at_maximal_rank_pins.json"
#print axioms Papers.Rigidity.minimalCounterexample_false
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.minimalCounterexample_false to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_minimalCounterexample_false.json"
#print axioms Papers.Rigidity.theorem_one_one
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.theorem_one_one to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_theorem_one_one.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_rigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_rigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_rigid.json"
#print axioms Papers.Rigidity.corollary_one_two_rigid_subgraph_cover
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.corollary_one_two_rigid_subgraph_cover to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_corollary_one_two_rigid_subgraph_cover.json"
#print axioms Papers.Rigidity.corollary_one_two_rigid_cluster_completion
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.corollary_one_two_rigid_cluster_completion to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_corollary_one_two_rigid_cluster_completion.json"
#print axioms Papers.Rigidity.sixConnected_rigidSubgraphCovered_rigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_rigidSubgraphCovered_rigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_rigidSubgraphCovered_rigid.json"
#print axioms Papers.Rigidity.rigidCluster_completion_sixConnected_rigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.rigidCluster_completion_sixConnected_rigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_rigidCluster_completion_sixConnected_rigid.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_locallyDistanceRigid.json"
#print axioms Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_rigidSubgraphCovered_locallyDistanceRigid.json"
#print axioms Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_rigidCluster_completion_sixConnected_locallyDistanceRigid.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_motionKernel_eq_globalTwists
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_motionKernel_eq_globalTwists to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_motionKernel_eq_globalTwists.json"
#print axioms Papers.Rigidity.fiveConnected_k4Covered_flexible_exists
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.fiveConnected_k4Covered_flexible_exists to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_fiveConnected_k4Covered_flexible_exists.json"
#print axioms Papers.Rigidity.SupportedCode.exists_code_attaining_bound
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.SupportedCode.exists_code_attaining_bound to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_SupportedCode_exists_code_attaining_bound.json"
#print axioms Papers.Rigidity.BodyLoads.duplicate_loads_prefix_identity
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.BodyLoads.duplicate_loads_prefix_identity to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_BodyLoads_duplicate_loads_prefix_identity.json"
#print axioms Papers.Rigidity.generic_alternating_space_center_defined_over_coefficients
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.generic_alternating_space_center_defined_over_coefficients to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_generic_alternating_space_center_defined_over_coefficients.json"
#print axioms Papers.Rigidity.BodyLoads.TwoBodyPin.lemma_three_seven
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.BodyLoads.TwoBodyPin.lemma_three_seven to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_BodyLoads_TwoBodyPin_lemma_three_seven.json"
#print axioms Papers.Rigidity.SupportedCode.sum_priorityDimension_relabel
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.SupportedCode.sum_priorityDimension_relabel to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_SupportedCode_sum_priorityDimension_relabel.json"
#print axioms Papers.Rigidity.BarJoint.localRigidity_iff_rank_at_algebraicallyGeneric
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.BarJoint.localRigidity_iff_rank_at_algebraicallyGeneric to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_BarJoint_localRigidity_iff_rank_at_algebraicallyGeneric.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_locallyDistanceRigid_of_algebraicIndependent.json"
#print axioms Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_rigidSubgraphCovered_locallyDistanceRigid_of_algebraicIndependent.json"
#print axioms Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_rigidCluster_completion_sixConnected_locallyDistanceRigid_of_algebraicIndependent.json"
#print axioms Papers.Rigidity.sixConnected_k4Covered_rigidityRank_of_algebraicIndependent
set_option maxHeartbeats 0 in
#export_proof_audit Papers.Rigidity.sixConnected_k4Covered_rigidityRank_of_algebraicIndependent to ".lake/reports/audit/recovery01/endpoint_audits/Papers_Rigidity_sixConnected_k4Covered_rigidityRank_of_algebraicIndependent.json"
